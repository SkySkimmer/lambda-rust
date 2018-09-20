From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
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
    typed_val refmut_deref (fn(∀ '(α, β), ∅; &shr{α}(refmut β ty)) → &shr{α}ty).
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
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(refmut β ty)); #lv ◁ &shr{α}ty]
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
    typed_val refmut_derefmut
              (fn(∀ '(α, β), ∅; &uniq{α}(refmut β ty)) → &uniq{α}ty).
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
      try by iMod (bor_persistent with "LFT H Hα") as "[>[] _]".
    iMod (bor_exists with "LFT H") as (ν) "H". done.
    iMod (bor_exists with "LFT H") as (q) "H". done.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_exists with "LFT H") as (ty') "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ H]". done.
    iMod (bor_persistent with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_sep with "LFT H") as "[H _]". done.
    iMod (bor_fracture (λ q', (q * q').[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mult_1_r. }
    iDestruct (frac_bor_lft_incl _ _ q with "LFT H") as "#Hαν". iClear "H".
    rewrite heap_mapsto_vec_cons. iMod (bor_sep with "LFT H↦") as "[H↦ _]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!(LitV lx'))%E. iMod (bor_unnest with "LFT Hb") as "Hb"; first done.
    wp_read. wp_let. iMod "Hb".
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
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
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
    iDestruct "Hx" as (ν q γ β ty') "(Hb & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)";
      [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)". wp_read. wp_let. wp_op. wp_write.
    iAssert (|={↑lftN,∅}▷=> refcell_inv tid lrc γ β ty')%I
      with "[H↦lrc H● H◯ Hν INV]" as "INV".
    { iDestruct (own_valid_2 with "H● H◯") as
        %[[[=]|(? & [[? q'] ?] & [= <-] & Hst & INCL)]%option_included _]
         %auth_valid_discrete_2.
      destruct st as [[[[??]?]?]|]; [|done]. move: Hst=>-[= ???]. subst.
      destruct INCL as [[[[ν' ?]%to_agree_inj ?] ?]|
            [[[??]%to_agree_included [q'' Hq'']]%prod_included [n' Hn']]%prod_included].
      - simpl in *. setoid_subst. iExists None. iFrame.
        iMod (own_update_2 with "H● H◯") as "$".
        { apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
          apply cancel_local_update_unit, _. }
        iDestruct "INV" as "(H† & Hq & _)". iApply "H†".
        iDestruct "Hq" as (q) "(<- & ?)". iFrame.
      - simpl in *. setoid_subst. iExists (Some (_, _, _, _)).
        iMod (own_update_2 with "H● H◯") as "$".
        { apply auth_update_dealloc. rewrite -(agree_idemp (to_agree _)) -!pair_op Some_op.
          apply (cancel_local_update_unit (writing_stR q _)), _. }
        iDestruct "INV" as "(H† & Hq & _)".
        rewrite /= (_:Z.neg (1%positive ⋅ n') + 1 = Z.neg n');
          last (rewrite pos_op_plus; lia). iFrame.
        iApply step_fupd_intro; [set_solver+|]. iSplitL; [|done].
        iDestruct "Hq" as (q' ?) "?". iExists (q+q')%Qp. iFrame.
        rewrite assoc (comm _ q'' q) //. }
    wp_bind Endlft. iApply (wp_mask_mono _ (↑lftN)); first done.
    iApply (wp_step_fupd with "INV"); [done|set_solver|]. wp_seq. iIntros "{Hb} Hb !>".
    iMod ("Hcloseβ" with "Hb Hna") as "[Hβ Hna]".
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
  Definition refmut_map (call_once : val) : val :=
    funrec: <> ["ref"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"ref" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "r'" := !"r" in delete [ #1; "r"];;
      "ref" <- "r'";;
      return: ["ref"].

  Lemma refmut_map_type ty1 ty2 call_once fty `{!TyWf ty1, !TyWf ty2, !TyWf fty} :
    (* fty : for<'a>, FnOnce(&'a ty1) -> &'a ty2, as witnessed by the impl call_once *)
    typed_val call_once (fn(∀ α, ∅; fty, &uniq{α}ty1) → &uniq{α}ty2) →
    typed_val (refmut_map call_once) (fn(∀ α, ∅; refmut α ty1, fty) → refmut α ty2).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros (α ϝ ret arg).
       inv_vec arg=>ref env. simpl_subst.
    iApply type_let; [apply Hf | solve_typing |]. iIntros (f'). simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk (#Hf' & Href & Henv & _)".
    rewrite (tctx_hasty_val _ ref). destruct ref as [[|lref|]|]; try done.
    iDestruct "Href" as "[Href Href†]".
    iDestruct "Href" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Href";
      try iDestruct "Href" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Href" as "[[Href↦1 Href↦2] Href]".
    iDestruct "Href" as (ν q γ β ty') "(Hbor & #Hαβ & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; first done. done.
    iIntros (lx) "(H† & Hlx)". rewrite heap_mapsto_vec_singleton.
    wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
            with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H† Hbor]"); [solve_typing|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. by iFrame. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL". iMod ("Hclose1" with "Hα HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as ([|r'[]]) "[Hr Hr']";
      try by iDestruct (ty_size_eq with "Hr'") as "%".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_] with "[Hr Hr†]")=>//.
    { rewrite heap_mapsto_vec_singleton freeable_sz_full. iFrame. } iIntros "_".
    wp_seq. wp_write.
    iApply (type_type _ [_] _ [ #lref ◁ box (refmut α ty2) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame.
      iExists [_;_]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iFrame. destruct r' as [[]|]=>//=. auto 10 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.
End refmut_functions.
