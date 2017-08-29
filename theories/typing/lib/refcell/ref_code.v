From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import lifetime na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell ref.
Set Default Proof Using "Type".

Section ref_functions.
  Context `{typeG Σ, refcellG Σ}.

  Lemma refcell_inv_reading_inv tid l γ α ty q ν :
    refcell_inv tid l γ α ty -∗
    own γ (◯ reading_st q ν) -∗
    ∃ (q' : Qp) n, l ↦ #(Zpos n) ∗ ⌜(q ≤ q')%Qc⌝ ∗
            own γ (● Some (to_agree ν, Cinr (q', n)) ⋅ ◯ reading_st q ν) ∗
            ty.(ty_shr) (α ⊓ ν) tid (l +ₗ 1) ∗
            ((1).[ν] ={↑lftN,∅}▷=∗ &{α}((l +ₗ 1) ↦∗: ty_own ty tid)) ∗
            ∃ q'', ⌜(q' + q'' = 1)%Qp⌝ ∗ q''.[ν].
  Proof.
    iIntros "INV H◯".
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)".
    iAssert (∃ q' n, st ≡ Some (to_agree ν, Cinr (q', n)) ∗ ⌜q ≤ q'⌝%Qc)%I with
       "[#]" as (q' n) "[Hst %]".
    { iDestruct (own_valid_2 with "H● H◯") as %[[[=]|
       (? & [agν st'] & [=<-] & -> & [Heq|Hle])]%option_included Hv]%auth_valid_discrete_2.
      - iExists q, xH. iSplit; iPureIntro. by constructor. done.
      - iClear "∗#".
        revert Hle Hv=>/prod_included [/= /agree_included Hag /csum_included
              [-> [//] | [[?[?[//]]] | [?[[q' n] [Heq [-> Hle]]]]]]] [Hagok _].
        revert Heq. intros [= <-]. revert Hle=>/prod_included [/= Hqq' _].
        iExists q', n. iSplit.
        + iPureIntro. rewrite (agree_op_inv agν) //. by rewrite comm -Hag.
        + by revert Hqq'=>/frac_included_weak. }
    iDestruct "Hst" as %[st' [-> Hst']]%equiv_Some_inv_r'.
    destruct st' as [?[|[]|]]; destruct Hst' as [Hag Hst']; try by inversion Hst'.
    apply (inj Cinr), (inj2 pair) in Hst'.
    destruct Hst' as [<-%leibniz_equiv <-%leibniz_equiv]. simpl in *.
    setoid_rewrite <-Hag. iDestruct "INV" as (ν') "(Hag & Hν & Hshr & Hq')".
    iDestruct "Hag" as %<-%(inj to_agree)%leibniz_equiv.
    iExists q', n. rewrite own_op. by iFrame.
  Qed.

  (* Cloning a ref. We need to increment the counter. *)
  Definition ref_clone : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "rc" := !("x'" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
      letalloc: "r" <-{2} !"x'" in
      delete [ #1; "x"];; return: ["r"].

  (* FIXME : using λ instead of fun triggers an anomaly.
     See: https://coq.inria.fr/bugs/show_bug.cgi?id=5326 *)
  Lemma ref_clone_type ty `{!TyWf ty} :
    typed_val ref_clone (fn (fun '(α, β) =>
                FP_wf ∅ [# &shr{α}(ref β ty)]%T (ref β ty)%T)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hβδ & Hinv & H◯inv)".
    wp_op.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hβδ Hβ") as (qδ) "[Hδ Hcloseβ]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose')";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    iMod (na_bor_acc with "LFT Hinv Hδ Hna") as "(INV & Hna & Hcloseδ)"; [done..|].
    iMod (na_bor_acc with "LFT H◯inv Hα2 Hna") as "(H◯ & Hna & Hcloseα2)"; [solve_ndisj..|].
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iDestruct (refcell_inv_reading_inv with "INV H◯")
      as (q' n) "(H↦lrc & _ & [H● H◯] & Hshr' & H† & Hq')".
    wp_read. wp_let. wp_op. wp_write. iDestruct "Hq'" as (q'') "(Hq'q'' & Hν1 & Hν2)".
    iDestruct "Hq'q''" as %Hq'q''. iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (reading_st (q''/2)%Qp ν))=>-[Hagv _].
      split; [|split; last done].
      - by rewrite /= agree_idemp.
      - apply frac_valid'. rewrite -Hq'q'' comm -{2}(Qp_div_2 q'').
        apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (q''/2)%Qp).
        apply Qcplus_le_mono_r, Qp_ge_0. }
    wp_apply wp_new; [done..|]. iIntros (lr ?) "(%&?&Hlr)".
    iAssert (lx' ↦∗{qlx'} [ #lv; #lrc])%I  with "[H↦1 H↦2]" as "H↦".
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    wp_let. wp_apply (wp_memcpy with "[$Hlr $H↦]"); [done..|].
    iIntros "[Hlr H↦]". wp_seq. iMod ("Hcloseα2" with "[$H◯] Hna") as "[Hα1 Hna]".
    iMod ("Hcloseδ" with "[H↦lrc H● Hν1 Hshr' H†] Hna") as "[Hδ Hna]".
    { iExists _. rewrite Z.add_comm. iFrame. iExists _. iFrame. iSplitR.
      - rewrite /= agree_idemp. auto.
      - iExists _. iFrame.
        rewrite (comm Qp_plus) (assoc Qp_plus) Qp_div_2 (comm Qp_plus). auto. }
    iMod ("Hcloseβ" with "Hδ") as "Hβ". iMod ("Hcloseα1" with "[$H↦]") as "Hα2".
    iMod ("Hclose'" with "[$Hα1 $Hα2] HL") as "HL". iMod ("Hclose" with "Hβ HL") as "HL".
    iApply (type_type _ _ _
           [ x ◁ box (&shr{α}(ref β ty)); #lr ◁ box(ref β ty)]
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      rewrite /= freeable_sz_full. iFrame. iExists _. iFrame. iExists _, _, _, _, _.
      iFrame "∗#". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a ref into a shared borrow. *)
  Definition ref_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma ref_deref_type ty `{!TyWf ty} :
    typed_val ref_deref
      (fn (fun '(α, β) => FP_wf ∅ [# &shr{α}(ref β ty)]%T (&shr{α}ty)%T)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hx')".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα") as (qlx') "[H↦ Hcloseα]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iMod ("Hcloseα" with "[$H↦1 $H↦2]") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _
        [ x ◁ box (&shr{α}(ref β ty)); #lv ◁ &shr{α}ty]
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr"). by iApply lft_incl_glb. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Dropping a ref and decrement the count in the corresponding refcell. *)
  Definition ref_drop : val :=
    funrec: <> ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" - #1;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma ref_drop_type ty `{!TyWf ty} :
    typed_val ref_drop (fn(∀ α, ∅; ref α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk Hx". rewrite tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν q γ β ty') "(_ & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct (refcell_inv_reading_inv with "INV [$H◯]")
      as (q' n) "(H↦lrc & >% & H●◯ & Hshr & H† & Hq')". iDestruct "Hq'" as (q'') ">[% Hν']".
    wp_read. wp_let. wp_op. wp_write.
    iAssert (|={↑lftN,∅}▷=> refcell_inv tid lrc γ β ty')%I
      with "[H↦lrc H●◯ Hν Hν' Hshr H†]" as "INV".
    { iDestruct (own_valid with "H●◯") as %[[ _ [Heq%(inj Cinr)|Hincl%csum_included]
        %Some_included]%Some_pair_included [_ Hv]]%auth_valid_discrete_2.
      - destruct Heq as [?%leibniz_equiv ?%leibniz_equiv]. simpl in *. subst.
        iExists None. iFrame. iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
          apply cancel_local_update_empty, _. }
        iApply "H†". replace 1%Qp with (q'+q'')%Qp by naive_solver. iFrame.
      - destruct Hincl as [ [=] |[ (?&?&[=]&?) | (?&?&[=<-]&[=<-]&[[q0 n']EQ]) ]].
        destruct EQ as [?%leibniz_equiv ?%leibniz_equiv]. simpl in *. subst.
        iAssert (lrc ↦ #(Z.pos n'))%I with "[H↦lrc]" as "H↦lrc".
        { destruct n'; [|done..]. by rewrite /= Pos.pred_double_succ. }
        iExists (Some (_, Cinr (q0, n'))). iFrame. iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc.
          rewrite -(agree_idemp (to_agree _)) -pair_op -Cinr_op -pair_op Some_op.
          apply (cancel_local_update_empty (reading_st q ν)), _. }
        iExists ν. iFrame. iApply step_fupd_intro; first set_solver. iIntros "!>".
        iSplitR; first done. iExists (q+q'')%Qp. iFrame.
        by rewrite assoc (comm _ q0 q). }
    wp_bind Endlft. iApply (wp_mask_mono (↑lftN)); first done.
    iApply (wp_step_fupd with "INV"); [set_solver..|]. wp_seq.
    iIntros "INV !>". wp_seq. iMod ("Hcloseβ" with "[$INV] Hna") as "[Hβ Hna]".
    iMod ("Hcloseα" with "Hβ") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)] with "[] LFT HE Hna HL Hk");
      first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the ref, typically for accessing a component. *)
  Definition ref_map (call_once : val) : val :=
    funrec: <> ["ref"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"ref" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "r'" := !"r" in delete [ #1; "r"];;
      "ref" <- "r'";;
      return: ["ref"].

  Lemma ref_map_type ty1 ty2 call_once fty `{!TyWf ty1, !TyWf ty2, !TyWf fty} :
    (* fty : for<'a>, FnOnce(&'a ty1) -> &'a ty2, as witnessed by the impl call_once *)
    typed_val call_once (fn(∀ α, ∅; fty, &shr{α}ty1) → &shr{α}ty2) →
    typed_val (ref_map call_once) (fn(∀ α, ∅; ref α ty1, fty) → ref α ty2).
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
    iDestruct "Href" as (ν qν γ β ty') "(#Hshr & #Hαβ & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; first done.
    iIntros (lx [|? []]) "(% & H† & Hlx)"; try (simpl in *; lia).
    rewrite heap_mapsto_vec_singleton. wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
       with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H†]"); [solve_typing|solve_to_val|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. by iFrame. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL". iMod ("Hclose1" with "Hα HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as ([|r'[]]) "[Hr #Hr']";
      try by iDestruct (ty_size_eq with "Hr'") as "%".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_] with "[Hr Hr†]")=>//.
    { rewrite heap_mapsto_vec_singleton freeable_sz_full. iFrame. } iIntros "_".
    wp_seq. wp_write.
    iApply (type_type _ [_] _ [ #lref ◁ box (ref α ty2) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame.
      iExists [_;_]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iFrame. destruct r' as [[]|]=>//=. auto 10 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.
End ref_functions.
