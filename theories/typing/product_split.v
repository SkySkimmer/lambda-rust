From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context lft_contexts product own uniq_bor shr_bor.
Set Default Proof Using "Type".

Section product_split.
  Context `{typeG Σ}.

  (** General splitting / merging for pointer types *)
  Fixpoint hasty_ptr_offsets (p : path) (ptr: type → type) tyl (off : nat) : tctx :=
    match tyl with
    | [] => []
    | ty :: tyl =>
      (p +ₗ #off ◁ ptr ty)%TC :: hasty_ptr_offsets p ptr tyl (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_offset (l : loc) p (off1 off2 : nat) ptr tyl tid :
    eval_path p = Some #l →
    tctx_interp tid $ hasty_ptr_offsets (p +ₗ #off1) ptr tyl off2 ≡
    tctx_interp tid $ hasty_ptr_offsets p ptr tyl (off1 + off2)%nat.
  Proof.
    intros Hp.
    revert off1 off2; induction tyl; intros off1 off2; simpl; first done.
    rewrite !tctx_interp_cons. f_equiv; last first.
    { rewrite IHtyl plus_assoc. done. } (* FIXME RJ: Using assoc, even with a pattern, is pretty slow here. *)
    apply tctx_elt_interp_hasty_path. clear Hp. simpl.
    clear. destruct (eval_path p); last done. destruct v; try done.
    destruct l; try done. rewrite shift_loc_assoc Nat2Z.inj_add //.
  Qed.

  Lemma tctx_split_ptr_prod E L ptr tyl :
    (∀ p ty1 ty2,
        tctx_incl E L [p ◁ ptr $ product2 ty1 ty2]
                      [p ◁ ptr ty1; p +ₗ #ty1.(ty_size) ◁ ptr ty2]) →
    (∀ tid ty vl, (ptr ty).(ty_own) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝) →
    ∀ p, tctx_incl E L [p ◁ ptr $ product tyl] (hasty_ptr_offsets p ptr tyl 0).
  Proof.
    iIntros (Hsplit Hloc p tid q1 q2) "#LFT HE HL H".
    iInduction tyl as [|ty tyl IH] "IH" forall (p).
    { iFrame "HE HL". rewrite tctx_interp_nil. done. }
    rewrite product_cons. iMod (Hsplit with "LFT HE HL H") as "(HE & HL & H)".
    cbn -[tctx_elt_interp]. rewrite tctx_interp_cons tctx_interp_singleton tctx_interp_cons.
    iDestruct "H" as "[Hty Htyl]". iDestruct "Hty" as (v) "[Hp Hty]". iDestruct "Hp" as %Hp. 
    iDestruct (Hloc with "Hty") as %[l [=->]].
    iAssert (tctx_elt_interp tid (p +ₗ #0 ◁ ptr ty)) with "[Hty]" as "$".
    { iExists #l. iSplit; last done. simpl; by rewrite Hp shift_loc_0. }
    iMod ("IH" with "* HE HL [Htyl]") as "($ & $ & Htyl)".
    { rewrite tctx_interp_singleton //. }
    iClear "IH". rewrite (hasty_ptr_offsets_offset l) // -plus_n_O //.
  Qed.

  Lemma tctx_merge_ptr_prod E L ptr tyl :
    (Proper (eqtype E L ==> eqtype E L ) ptr) → tyl ≠ [] →
    (∀ p ty1 ty2,
        tctx_incl E L [p ◁ ptr ty1; p +ₗ #ty1.(ty_size) ◁ ptr ty2]
                      [p ◁ ptr $ product2 ty1 ty2]) →
    (∀ tid ty vl, (ptr ty).(ty_own) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝) →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p ptr tyl 0) [p ◁ ptr $ product tyl].
  Proof.
    iIntros (Hptr Htyl Hmerge Hloc p tid q1 q2) "#LFT HE HL H".
    iInduction tyl as [|ty tyl IH] "IH" forall (p Htyl); first done.
    rewrite product_cons. rewrite /= tctx_interp_singleton tctx_interp_cons.
    iDestruct "H" as "[Hty Htyl]". iDestruct "Hty" as (v) "[Hp Hty]". iDestruct "Hp" as %Hp. 
    iDestruct (Hloc with "Hty") as %[l [=->]].
    assert (eval_path p = Some #l) as Hp'.
    { move:Hp. simpl. clear. destruct (eval_path p); last done.
      destruct v; try done. destruct l0; try done. rewrite shift_loc_0. done. }
    clear Hp. destruct tyl.
    { iDestruct (elctx_interp_persist with "HE") as "#HE'".
      iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL". 
      iClear "IH Htyl". simpl. iExists #l. rewrite product_nil. iSplitR; first done.
      assert (eqtype E L (ptr ty) (ptr (product2 ty unit))) as [Hincl _].
      { rewrite right_id. done. }
      iDestruct (Hincl with "LFT HE' HL'") as "#(_ & #Heq & _)". by iApply "Heq". }
    iMod ("IH" with "* [] HE HL [Htyl]") as "(HE & HL & Htyl)"; first done.
    { change (ty_size ty) with (0+ty_size ty)%nat at 1.
      rewrite plus_comm -hasty_ptr_offsets_offset //. }
    iClear "IH". iMod (Hmerge with "LFT HE HL [Hty Htyl]") as "($ & $ & ?)";
                   last by rewrite tctx_interp_singleton.
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton. iFrame.
    iExists #l. iSplit; done.
  Qed.

  (** Owned pointers *)
  Lemma tctx_split_own_prod2 E L p n ty1 ty2 :
    tctx_incl E L [p ◁ own n $ product2 ty1 ty2]
                  [p ◁ own n ty1; p +ₗ #ty1.(ty_size) ◁ own n ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as (v) "[Hp H]". iDestruct "Hp" as %Hp. iDestruct "H" as (l) "(EQ & H & >H†)".
    iDestruct "EQ" as %[=->]. iDestruct "H" as (vl) "[>H↦ H]".
    iDestruct "H" as (vl1 vl2) "(>% & H1 & H2)". subst.
    rewrite heap_mapsto_vec_app -freeable_sz_split.
    iDestruct "H†" as "[H†1 H†2]". iDestruct "H↦" as "[H↦1 H↦2]".
    iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
    { iNext. by iApply ty_size_eq. }
    iDestruct "EQ" as %->. iSplitL "H↦1 H†1 H1".
    + iExists _. iSplitR. done. iExists _. iFrame. iSplitL ""; first done.
      iExists _. iFrame. done.
    + iExists _. iSplitR. simpl. by rewrite Hp. iExists _. iFrame. iSplitR; first done.
      iExists _. iFrame. done.
  Qed.

  Lemma tctx_merge_own_prod2 E L p n ty1 ty2 :
    tctx_incl E L [p ◁ own n ty1; p +ₗ #ty1.(ty_size) ◁ own n ty2]
                  [p ◁ own n $ product2 ty1 ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as (v1) "(Hp1 & H1)".
    iDestruct "Hp1" as %Hp1. iDestruct "H1" as (l) "(EQ & H↦1 & H†1)".
    iDestruct "EQ" as %[=->]. iDestruct "H2" as (v2) "(Hp2 & H2)".
    rewrite /= Hp1. iDestruct "Hp2" as %[=<-]. iDestruct "H2" as (l') "(EQ & H↦2 & H†2)".
    iDestruct "EQ" as %[=<-]. iExists #l. iSplitR; first done. iExists l. iSplitR; first done.
    rewrite -freeable_sz_split. iFrame.
    iDestruct "H↦1" as (vl1) "[H↦1 H1]". iDestruct "H↦2" as (vl2) "[H↦2 H2]".
    iExists (vl1 ++ vl2). rewrite heap_mapsto_vec_app. iFrame.
    iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
    { iNext. by iApply ty_size_eq. }
    iDestruct "EQ" as %->. iFrame. iExists vl1, vl2. iFrame. auto.
  Qed.

  Lemma own_is_ptr n ty tid (vl : list val) :
    ty_own (own n ty) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof.
    iIntros "H". iDestruct "H" as (l) "[% _]". iExists l. done.
  Qed.

  Lemma tctx_split_own_prod E L n tyl p :
    tctx_incl E L [p ◁ own n $ product tyl] (hasty_ptr_offsets p (own n) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_own_prod2.
    - intros. apply own_is_ptr.
  Qed.

  Lemma tctx_merge_own_prod E L n tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (own n) tyl 0)
                   [p ◁ own n $ product tyl].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_own_prod2.
    - intros. apply own_is_ptr.
  Qed.

  (** Unique borrows *)
  Lemma tctx_split_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ} product2 ty1 ty2]
                  [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as (v) "[Hp H]". iDestruct "Hp" as %Hp.
    iDestruct "H" as (l P) "[[EQ #HPiff] HP]". iDestruct "EQ" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "Hown". set_solver. by eauto.
    rewrite /= split_prod_mt. iMod (bor_sep with "LFT Hown") as "[H1 H2]".
    set_solver. rewrite /tctx_elt_interp /=.
    iSplitL "H1"; iExists _; (iSplitR; first by rewrite Hp);
                  iExists _, _; erewrite <-uPred.iff_refl; auto.
  Qed.

  Lemma tctx_merge_uniq_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &uniq{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2]
                  [p ◁ &uniq{κ} product2 ty1 ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as (v1) "(Hp1 & H1)".
    iDestruct "Hp1" as %Hp1. iDestruct "H1" as (l P) "[[EQ #HPiff] HP]".
    iDestruct "EQ" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "Hown1". set_solver. by eauto.
    iDestruct "H2" as (v2) "(Hp2 & H2)". rewrite /= Hp1. iDestruct "Hp2" as %[=<-].
    iDestruct "H2" as (l' Q) "[[EQ #HQiff] HQ]". iDestruct "EQ" as %[=<-].
    iMod (bor_iff with "LFT [] HQ") as "Hown2". set_solver. by eauto.
    iExists #l. iSplitR; first done. iExists l, _. iSplitR.
    { iSplitR; first done. erewrite <-uPred.iff_refl; auto. }
    rewrite split_prod_mt. iApply (bor_combine with "LFT Hown1 Hown2"). set_solver.
  Qed.

  Lemma uniq_is_ptr κ ty tid (vl : list val) :
    ty_own (&uniq{κ} ty) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof.
    iIntros "H". iDestruct "H" as (l P) "[[% _] _]". iExists l. done.
  Qed.

  Lemma tctx_split_uniq_prod E L κ tyl p :
    tctx_incl E L [p ◁ &uniq{κ} product tyl]
                  (hasty_ptr_offsets p (uniq_bor κ) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.

  Lemma tctx_merge_uniq_prod E L κ tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (uniq_bor κ) tyl 0)
                   [p ◁ &uniq{κ} product tyl].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_uniq_prod2.
    - intros. apply uniq_is_ptr.
  Qed.

  (** Shared borrows *)
  Lemma tctx_split_shr_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &shr{κ} product2 ty1 ty2]
                  [p ◁ &shr{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &shr{κ} ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as (v) "[Hp H]". iDestruct "Hp" as %Hp.
    iDestruct "H" as (l) "[EQ [H1 H2]]". iDestruct "EQ" as %[=->].
    iSplitL "H1"; iExists _; (iSplitR; first by rewrite /= Hp);
      iExists _; iSplitR; done.
  Qed.

  Lemma tctx_merge_shr_prod2 E L p κ ty1 ty2 :
    tctx_incl E L [p ◁ &shr{κ} ty1; p +ₗ #ty1.(ty_size) ◁ &shr{κ} ty2]
                  [p ◁ &shr{κ} product2 ty1 ty2].
  Proof.
    iIntros (tid q1 q2) "#LFT $ $ H".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as "[H1 H2]". iDestruct "H1" as (v1) "(Hp1 & H1)".
    iDestruct "Hp1" as %Hp1. iDestruct "H1" as (l) "[EQ Hown1]".
    iDestruct "EQ" as %[=->]. iDestruct "H2" as (v2) "(Hp2 & H2)".
    rewrite /= Hp1. iDestruct "Hp2" as %[=<-].
    iDestruct "H2" as (l') "[EQ Hown2]". iDestruct "EQ" as %[=<-].
    iExists #l. iSplitR; first done. iExists l. iSplitR; first done.
    by iFrame.
  Qed.

  Lemma shr_is_ptr κ ty tid (vl : list val) :
    ty_own (&shr{κ} ty) tid vl -∗ ⌜∃ l : loc, vl = [(#l) : val]⌝.
  Proof.
    iIntros "H". iDestruct "H" as (l) "[% _]". iExists l. done.
  Qed.

  Lemma tctx_split_shr_prod E L κ tyl p :
    tctx_incl E L [p ◁ &shr{κ} product tyl]
                  (hasty_ptr_offsets p (shr_bor κ) tyl 0).
  Proof.
    apply tctx_split_ptr_prod.
    - intros. apply tctx_split_shr_prod2.
    - intros. apply shr_is_ptr.
  Qed.

  Lemma tctx_merge_shr_prod E L κ tyl :
    tyl ≠ [] →
    ∀ p, tctx_incl E L (hasty_ptr_offsets p (shr_bor κ) tyl 0)
                   [p ◁ &shr{κ} product tyl].
  Proof.
    intros. apply tctx_merge_ptr_prod; try done.
    - apply _.
    - intros. apply tctx_merge_shr_prod2.
    - intros. apply shr_is_ptr.
  Qed.

  (* Splitting with [tctx_extract]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)
  Lemma tctx_extract_split_own_prod2 E L p p' n ty ty1 ty2 T T' :
    tctx_extract_hasty E L p' ty [p ◁ own n ty1; p +ₗ #ty1.(ty_size) ◁ own n ty2] T' →
    tctx_extract_hasty E L p' ty ((p ◁ own n $ product2 ty1 ty2) :: T) (T' ++ T) .
  Proof.
    unfold tctx_extract_hasty. intros ?. apply (tctx_incl_frame_r T [_] (_::_)).
    by rewrite tctx_split_own_prod2.
  Qed.

  Lemma tctx_extract_split_uniq_prod2 E L p p' κ ty ty1 ty2 T T' :
    tctx_extract_hasty E L p' ty
            [p ◁ &uniq{κ}ty1; p +ₗ #ty1.(ty_size) ◁ &uniq{κ}ty2] T' →
    tctx_extract_hasty E L p' ty ((p ◁ &uniq{κ} product2 ty1 ty2) :: T) (T' ++ T) .
  Proof.
    unfold tctx_extract_hasty=>?. apply (tctx_incl_frame_r T [_] (_::_)).
    by rewrite tctx_split_uniq_prod2.
  Qed.

  Lemma tctx_extract_split_shr_prod2 E L p p' κ ty ty1 ty2 T T' :
    tctx_extract_hasty E L p' ty
                  [p ◁ &shr{κ}ty1; p +ₗ #ty1.(ty_size) ◁ &shr{κ}ty2] T' →
    tctx_extract_hasty E L p' ty ((p ◁ &shr{κ} product2 ty1 ty2) :: T)
                                 ((p ◁ &shr{κ} product2 ty1 ty2) :: T).
  Proof.
    unfold tctx_extract_hasty=>?. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite {1}copy_tctx_incl. apply (tctx_incl_frame_r _ [_] [_]).
    rewrite tctx_split_shr_prod2 -(contains_tctx_incl _ _ [p' ◁ ty]%TC) //.
    apply contains_skip, contains_nil_l.
  Qed.

  Lemma tctx_extract_split_own_prod E L p p' n ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (own n) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ own n $ Π tyl) :: T) (T' ++ T).
  Proof.
    unfold tctx_extract_hasty=>?. apply (tctx_incl_frame_r T [_] (_::_)).
    by rewrite tctx_split_own_prod.
  Qed.

  Lemma tctx_extract_split_uniq_prod E L p p' κ ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (uniq_bor κ) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ &uniq{κ} Π tyl) :: T) (T' ++ T).
  Proof.
    unfold tctx_extract_hasty=>?. apply (tctx_incl_frame_r T [_] (_::_)).
    by rewrite tctx_split_uniq_prod.
  Qed.

  Lemma tctx_extract_split_shr_prod E L p p' κ ty tyl T T' :
    tctx_extract_hasty E L p' ty (hasty_ptr_offsets p (shr_bor κ) tyl 0) T' →
    tctx_extract_hasty E L p' ty ((p ◁ &shr{κ} Π tyl) :: T) ((p ◁ &shr{κ} Π tyl) :: T).
  Proof.
    unfold tctx_extract_hasty=>?. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite {1}copy_tctx_incl. apply (tctx_incl_frame_r _ [_] [_]).
    rewrite tctx_split_shr_prod -(contains_tctx_incl _ _ [p' ◁ ty]%TC) //.
    apply contains_skip, contains_nil_l.
  Qed.

  (* Merging with [tctx_extract]. *)

  Lemma tctx_extract_merge_own_prod2 E L p n ty1 ty2 T1 T2 T3 :
    tctx_extract_hasty E L p (own n ty1) T1 T2 →
    tctx_extract_hasty E L (p +ₗ #ty1.(ty_size)) (own n ty2) T2 T3 →
    tctx_extract_hasty E L p (own n (product2 ty1 ty2)) T1 T3.
  Proof.
    unfold tctx_extract_hasty=>->->.
    apply (tctx_incl_frame_r _ [_;_] [_]), tctx_merge_own_prod2.
  Qed.

  Lemma tctx_extract_merge_uniq_prod2 E L p κ ty1 ty2 T1 T2 T3 :
    tctx_extract_hasty E L p (&uniq{κ}ty1) T1 T2 →
    tctx_extract_hasty E L (p +ₗ #ty1.(ty_size)) (&uniq{κ}ty2) T2 T3 →
    tctx_extract_hasty E L p (&uniq{κ}product2 ty1 ty2) T1 T3.
  Proof.
    unfold tctx_extract_hasty=>->->.
    apply (tctx_incl_frame_r _ [_;_] [_]), tctx_merge_uniq_prod2.
  Qed.

  Lemma tctx_extract_merge_shr_prod2 E L p κ ty1 ty2 T1 T2 T3 :
    tctx_extract_hasty E L p (&shr{κ}ty1) T1 T2 →
    tctx_extract_hasty E L (p +ₗ #ty1.(ty_size)) (&shr{κ}ty2) T2 T3 →
    tctx_extract_hasty E L p (&shr{κ}product2 ty1 ty2) T1 T3.
  Proof.
    unfold tctx_extract_hasty=>->->.
    apply (tctx_incl_frame_r _ [_;_] [_]), tctx_merge_shr_prod2.
  Qed.

  Fixpoint extract_tyl E L p (ptr: type → type) tyl (off : nat) T T' : Prop :=
    match tyl with
    | [] => T = T'
    | ty :: tyl => ∃ T'',
        tctx_extract_hasty E L (p +ₗ #off) (ptr ty) T T'' ∧
        extract_tyl E L p ptr tyl (off + ty.(ty_size)) T'' T'
    end.

  Lemma tctx_extract_merge_ptr_prod E L p ptr tyl T T' :
    tctx_incl E L (hasty_ptr_offsets p ptr tyl 0) [p ◁ ptr $ product tyl] →
    extract_tyl E L p ptr tyl 0 T T' →
    tctx_extract_hasty E L p (ptr (Π tyl)) T T'.
  Proof.
    unfold tctx_extract_hasty=>Hi Htyl.
    etrans. 2:by eapply (tctx_incl_frame_r T' _ [_]). revert T Htyl. clear.
    generalize 0%nat. induction tyl=>[T n /= -> //|T n /=].
    unfold tctx_extract_hasty=>-[T'' [-> Htyl]]. f_equiv. auto.
  Qed.

  Lemma tctx_extract_merge_own_prod E L p n tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (own n) tyl 0 T T' →
    tctx_extract_hasty E L p (own n (Π tyl)) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_own_prod. Qed.

  Lemma tctx_extract_merge_uniq_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (uniq_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&uniq{κ}Π tyl) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_uniq_prod. Qed.

  Lemma tctx_extract_merge_shr_prod E L p κ tyl T T' :
    tyl ≠ [] →
    extract_tyl E L p (shr_bor κ) tyl 0 T T' →
    tctx_extract_hasty E L p (&shr{κ}Π tyl) T T'.
  Proof. auto using tctx_extract_merge_ptr_prod, tctx_merge_shr_prod. Qed.
End product_split.

(* We make sure that this is applied after [tctx_extract_hasty_here] but before
   [tctx_extract_hasty_cons]. *)
Hint Resolve tctx_extract_split_own_prod2 tctx_extract_split_uniq_prod2
             tctx_extract_split_shr_prod2 tctx_extract_split_own_prod
             tctx_extract_split_uniq_prod tctx_extract_split_shr_prod
     | 60 : lrust_typing.

(* We make sure that this is applied after everything. *)
Hint Resolve tctx_extract_merge_own_prod2 tctx_extract_merge_uniq_prod2
             tctx_extract_merge_shr_prod2 tctx_extract_merge_own_prod
             tctx_extract_merge_uniq_prod tctx_extract_merge_shr_prod
     | 150 : lrust_typing.

Hint Extern 0
     (tctx_extract_hasty _ _ _ _ (hasty_ptr_offsets _ _ _ _) _) =>
        cbn[hasty_ptr_offsets].

Hint Unfold extract_tyl : lrust_typing.
