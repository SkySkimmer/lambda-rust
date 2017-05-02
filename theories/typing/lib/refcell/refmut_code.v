From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell refmut.
Set Default Proof Using "Type".

Section refmut_functions.
  Context `{typeG Σ, refcellG Σ}.

  (* Turning a refmut into a shared borrow. *)
  Definition refmut_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma refmut_deref_type ty `{!TyWf ty} :
    typed_val refmut_deref (fn (fun '(α, β) =>
       FP_wf ∅ [# &shr{α}(refmut β ty)]%T (&shr{α}ty))).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (lv lrc) "#(Hfrac & #Hshr)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose')";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose'')";
      [solve_typing..|].
    iDestruct (lft_intersect_acc with "Hβ Hα2") as (qβα) "[Hα2β Hcloseβα2]".
    wp_bind (!(LitV lx'))%E. iApply (wp_step_fupd with "[Hα2β]");
         [done| |by iApply ("Hshr" with "[] Hα2β")|]; first done.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. iIntros "[#Hshr' Hα2β] !>". wp_let.
    iDestruct ("Hcloseβα2" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hcloseα1" with "[$H↦1 $H↦2]") as "Hα1".
    iMod ("Hclose''" with "Hβ HL") as "HL". iMod ("Hclose'" with "[$] HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (&shr{α} refmut β ty); #lv ◁ &shr{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr'").
      by iApply lft_incl_glb; last iApply lft_incl_refl. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a refmut into a unique borrow. *)
  Definition refmut_derefmut : val := refmut_deref.

  Lemma refmut_derefmut_type ty `{!TyWf ty} :
    typed_val refmut_derefmut (fn (fun '(α, β) =>
      FP_wf ∅ [# &uniq{α}(refmut β ty)]%T (&uniq{α}ty)%T)).
   Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iMod (bor_exists with "LFT Hx'") as (vl) "H". done.
    iMod (bor_sep with "LFT H") as "[H↦ H]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose')";
      [solve_typing..|].
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent_tok with "LFT H Hα") as "[>[] _]".
    iMod (bor_exists with "LFT H") as (ν) "H". done.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_exists with "LFT H") as (ty') "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ H]". done.
    iMod (bor_persistent_tok with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    rewrite (comm _ (1).[ν])%I. rewrite (assoc _ _ _ (1).[ν])%I.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_fracture (λ q, (1 * q).[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mult_1_l. }
    iDestruct (frac_bor_lft_incl _ _ 1 with "LFT H") as "#Hαν". iClear "H".
    rewrite heap_mapsto_vec_cons. iMod (bor_sep with "LFT H↦") as "[H↦ _]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!(LitV lx'))%E. iApply (wp_step_fupd with "[Hb]");
      [done| |by iApply (bor_unnest with "LFT Hb")|]; first done.
    wp_read. iIntros "Hb !>". wp_let.
    iMod ("Hcloseα" with "[$H↦]") as "[_ Hα]". iMod ("Hclose'" with "Hα HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #lv ◁ &uniq{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (bor_shorten with "[] Hb").
      by iApply lft_incl_glb; [iApply lft_incl_glb|iApply lft_incl_refl]. }
    iApply (type_letalloc_1 (&uniq{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Dropping a refmut and set the count to 0 in the corresponding refcell. *)
  Definition refmut_drop : val :=
    funrec: <> ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      "rc" <- #0;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma refmut_drop_type ty `{!TyWf ty} :
    typed_val refmut_drop (fn(∀ α, ∅; refmut α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk Hx". rewrite tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν γ β ty') "(Hb & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)";
      [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)". wp_write.
    iDestruct (own_valid_2 with "H● H◯") as %[[[=]| (? & [agν st'] & [=<-] & -> &
      [[Hag Heq]|[_ Hle]%prod_included])]%option_included []]%auth_valid_discrete_2;
      last first.
    { by destruct (exclusive_included (Cinl (Excl ())) st'). }
    setoid_subst. iDestruct "INV" as (ν') "(Hνν' & H† & _)".
    iDestruct "Hνν'" as %<-%(inj to_agree)%leibniz_equiv.
    wp_bind Endlft. iApply (wp_mask_mono (↑lftN)); first done.
    iApply (wp_step_fupd with "[H† Hν]");
      [done| |iApply ("H†" with "Hν")|]; first set_solver.
    wp_seq. iIntros "{Hb} Hb !>".
    iMod ("Hcloseβ" with "[> H↦lrc H● H◯ Hb] Hna") as "[Hβ Hna]".
    { iExists None. iFrame. iMod (own_update_2 with "H● H◯") as "$"; last done.
      apply auth_update_dealloc. rewrite -(right_id None _ (Some _)).
      apply cancel_local_update_empty, _. }
    iMod ("Hcloseα" with "Hβ") as "Hα". iMod ("Hclose" with "Hα HL") as "HL". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the refmut, typically for accessing a component. *)
  Definition refmut_map (f : val) : val :=
    funrec: <> ["ref"; "env"] :=
      let: "f" := f in
      Newlft;;
      let: "x'" := !"ref" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "f" ["env"; "x"]%E in
      let: "r'" := !"r" in delete [ #1; "r"];;
      Endlft;;
      "ref" <- "r'";;
      return: ["ref"].

  Lemma refmut_map_type ty1 ty2 f envty `{!TyWf ty1, !TyWf ty2, !TyWf envty} :
    typed_val f (fn(∀ α, ∅; envty, &uniq{α}ty1) → &uniq{α}ty2) →
    typed_val (refmut_map f) (fn(∀ α, ∅; refmut α ty1, envty) → refmut α ty2).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros (α ϝ ret arg).
       inv_vec arg=>ref env. simpl_subst.
    iApply type_let; [apply Hf | solve_typing |]. iIntros (f'). simpl_subst.
    iApply (type_newlft [ϝ]). iIntros (κ tid) "#LFT #HE Hna HL Hk (#Hf' & Href & Henv & _)".
    rewrite (tctx_hasty_val _ ref). destruct ref as [[|lref|]|]; try done.
    iDestruct "Href" as "[Href Href†]".
    iDestruct "Href" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Href";
      try iDestruct "Href" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Href" as "[[Href↦1 Href↦2] Href]".
    iDestruct "Href" as (ν γ β ty') "(Hbor & #Hαβ & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; first done.
    iIntros (lx [|? []]) "(% & H† & Hlx)"; try (simpl in *; lia).
    rewrite heap_mapsto_vec_singleton. wp_let. wp_write.
    match goal with | |- context [(WP (_ [?k']) {{_, _}})%I] =>
      assert (∃ k, to_val k' = Some k) as [k EQk] by (eexists; solve_to_val) end.
    iApply (wp_let' _ _ _ _ k _ EQk). simpl_subst. iNext.
    iDestruct (lctx_lft_incl_incl κ α with "HL HE") as "#Hκα"; [solve_typing..|].
    iMod (bor_create _ κ (1).[ν] with "LFT [$Hν]") as "[Hb Hν]"; first done.
    iAssert (κ ⊑ α ⊓ ν)%I with "[>Hb]" as "#Hκν".
    { iApply (lft_incl_glb with "Hκα"). iApply (frac_bor_lft_incl with "LFT").
      iApply (bor_fracture with "LFT [> -]"); first done. rewrite /= Qp_mult_1_r //. }
    iApply (type_type ((κ ⊑ₑ α ⊓ ν) :: (α ⊓ ν ⊑ₑ α) :: _) _
        [k ◁cont(_, λ x:vec val 1, [ x!!!0 ◁ box (&uniq{α ⊓ ν}ty2)])]
        [ f' ◁ fn(∀ α, ∅; envty, &uniq{α}ty1) → &uniq{α}ty2;
          #lx ◁ box (&uniq{α ⊓ ν}ty1); env ◁ box envty ]
       with "[] LFT [] Hna HL [-H† Hlx Henv Hbor]"); swap 1 2; swap 3 4.
    { iSplitL; last iSplitL; [done|iApply lft_intersect_incl_l|iApply "HE"]. }
    { iApply (type_call (α ⊓ ν)); solve_typing. }
    { rewrite /tctx_interp /=. iFrame "Hf' Henv".
      iApply tctx_hasty_val'; first done. rewrite -freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. auto with iFrame. }
    iIntros (? ->%elem_of_list_singleton arg) "Hna HL Hr". inv_vec arg=>r.
    apply of_to_val in EQk. rewrite EQk. iApply wp_rec; try (done || apply _).
    { repeat econstructor. by rewrite to_of_val. } simpl_subst.
    rewrite /tctx_interp big_sepL_singleton (tctx_hasty_val _ r) ownptr_own.
    iDestruct "Hr" as (lr vr) "(% & Hlr & Hvr & H†)". subst. inv_vec vr=>r'. iNext.
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_] with "[Hlr H†]"). done.
    { rewrite heap_mapsto_vec_singleton freeable_sz_full. iFrame. }
    iIntros "_". wp_seq. wp_bind Endlft. iDestruct "HL" as "[Hκ HL]".
    iDestruct "Hκ" as (κ') "(% & Hκ' & #Hκ'†)". simpl in *. subst κ.
    iSpecialize ("Hκ'†" with "Hκ'").
    iApply wp_mask_mono; last iApply (wp_step_fupd with "Hκ'†"); auto with ndisj.
    wp_seq. iIntros "Hκ'† !>". iMod ("Hν" with "[Hκ'†]") as "Hν";
      first by rewrite -lft_dead_or; auto. wp_seq. wp_write.
    iApply (type_type _ [_] _ [ #lref ◁ box (refmut α ty2) ]
       with "[] LFT HE Hna [HL] Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val. iExists _. iSplit. done.
      iFrame. iExists [_;_]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iFrame. destruct r' as [[]|]=>//=. auto 10 with iFrame. }
    { rewrite /llctx_interp /=; auto. }
    iApply type_jump; solve_typing.
  Qed.
End refmut_functions.
