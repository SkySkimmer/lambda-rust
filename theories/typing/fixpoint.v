From lrust.lang Require Import proofmode.
From lrust.typing Require Export lft_contexts type bool.
Set Default Proof Using "Type".

Section fixpoint.
  Context `{typeG Σ}.

  Global Instance type_inhabited : Inhabited type := populate bool.

  Context (T : type → type) `{Contractive T}.

  Global Instance fixpoint_copy :
    (∀ `(!Copy ty), Copy (T ty)) → Copy (fixpoint T).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros ??[[EQsz%leibniz_equiv EQown]EQshr].
      specialize (λ tid vl, EQown tid vl). specialize (λ κ tid l, EQshr κ tid l).
      simpl in *=>-[Hp Hsh]; (split; [intros ??|intros ???]).
      + revert Hp. by rewrite /PersistentP -EQown.
      + intros F l q. rewrite -EQsz -EQshr. setoid_rewrite <-EQown. auto.
    - exists bool. apply _.
    - done.
    - intros c Hc. split.
      + intros tid vl. apply uPred.equiv_entails, equiv_dist=>n.
        by rewrite conv_compl uPred.always_always.
      + intros κ tid E F l q ? ?.
        apply uPred.entails_equiv_and, equiv_dist=>n. etrans.
        { apply equiv_dist, uPred.entails_equiv_and, (copy_shr_acc κ tid E F)=>//.
            by rewrite -conv_compl. }
        symmetry.               (* FIXME : this is too slow *)
        do 2 f_equiv; first by rewrite conv_compl. set (cn:=c n).
        repeat (apply (conv_compl n c) || f_contractive || f_equiv);
          by rewrite conv_compl.
  Qed.

  Global Instance fixpoint_send :
    (∀ `(!Send ty), Send (T ty)) → Send (fixpoint T).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros ?? EQ ????. by rewrite -EQ.
    - exists bool. apply _.
    - done.
    - intros c Hc ???. apply uPred.entails_equiv_and, equiv_dist=>n.
      rewrite conv_compl. apply equiv_dist, uPred.entails_equiv_and; apply Hc.
  Qed.

  Global Instance fixpoint_sync :
    (∀ `(!Sync ty), Sync (T ty)) → Sync (fixpoint T).
  Proof.
    intros ?. apply fixpoint_ind.
    - intros ?? EQ ?????. by rewrite -EQ.
    - exists bool. apply _.
    - done.
    - intros c Hc ????. apply uPred.entails_equiv_and, equiv_dist=>n.
      rewrite conv_compl. apply equiv_dist, uPred.entails_equiv_and; apply Hc.
  Qed.

  Lemma fixpoint_unfold_eqtype E L : eqtype E L (fixpoint T) (T (fixpoint T)).
  Proof.
    unfold eqtype, subtype, type_incl. setoid_rewrite <-fixpoint_unfold.
    split; iIntros "_ _ _"; (iSplit; first done); iSplit; iIntros "!#*$".
  Qed.
End fixpoint.

Section subtyping.
  Context `{typeG Σ} (E : elctx) (L : llctx).

  (* TODO : is there a way to declare these as a [Proper] instances ? *)
  Lemma fixpoint_mono T1 `{Contractive T1} T2 `{Contractive T2} :
    (∀ ty1 ty2, subtype E L ty1 ty2 → subtype E L (T1 ty1) (T2 ty2)) →
    subtype E L (fixpoint T1) (fixpoint T2).
  Proof.
    intros H12. apply fixpoint_ind.
    - intros ?? EQ ?. etrans; last done. by apply equiv_subtype.
    - by eexists _.
    - intros. rewrite (fixpoint_unfold_eqtype T2). by apply H12.
    - intros c Hc.
      assert (Hsz : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                ⌜(compl c).(ty_size) = (fixpoint T2).(ty_size)⌝).
      { iIntros "LFT HE HL". iDestruct (Hc 0%nat with "LFT HE HL") as "[$ _]". }
      assert (Hown : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                □ (∀ tid vl, (compl c).(ty_own) tid vl -∗ (fixpoint T2).(ty_own) tid vl)).
      { apply uPred.entails_equiv_and, equiv_dist=>n.
        destruct (conv_compl (S n) c) as [[_ Heq] _]. setoid_rewrite (λ tid vl, Heq tid vl).
        apply equiv_dist, uPred.entails_equiv_and. iIntros "LFT HE HL".
        iDestruct (Hc (S n) with "LFT HE HL") as "[_ [$ _]]". }
      assert (Hshr : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                □ (∀ κ tid l,
                   (compl c).(ty_shr) κ tid l -∗ (fixpoint T2).(ty_shr) κ tid l)).
      { apply uPred.entails_equiv_and, equiv_dist=>n.
        destruct (conv_compl n c) as [_ Heq]. setoid_rewrite (λ κ tid l, Heq κ tid l).
        apply equiv_dist, uPred.entails_equiv_and. iIntros "LFT HE HL".
        iDestruct (Hc n with "LFT HE HL") as "[_ [_ $]]". }
      iIntros "LFT HE HL". iSplit; [|iSplit].
      + iApply (Hsz with "LFT HE HL").
      + iApply (Hown with "LFT HE HL").
      + iApply (Hshr with "LFT HE HL").
  Qed.

  Lemma fixpoint_proper T1 `{Contractive T1} T2 `{Contractive T2} :
    (∀ ty1 ty2, eqtype E L ty1 ty2 → eqtype E L (T1 ty1) (T2 ty2)) →
    eqtype E L (fixpoint T1) (fixpoint T2).
  Proof.
    intros H12. apply fixpoint_ind.
    - intros ?? EQ ?. etrans; last done. by apply equiv_eqtype.
    - by eexists _.
    - intros. rewrite (fixpoint_unfold_eqtype T2). by apply H12.
    - intros c Hc. setoid_rewrite eqtype_unfold in Hc. rewrite eqtype_unfold.
      assert (Hsz : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                ⌜(compl c).(ty_size) = (fixpoint T2).(ty_size)⌝).
      { iIntros "LFT HE HL". iDestruct (Hc 0%nat with "LFT HE HL") as "[$ _]". }
      assert (Hown : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                □ (∀ tid vl, (compl c).(ty_own) tid vl ↔ (fixpoint T2).(ty_own) tid vl)).
      { apply uPred.entails_equiv_and, equiv_dist=>n.
        destruct (conv_compl (S n) c) as [[_ Heq] _]. setoid_rewrite (λ tid vl, Heq tid vl).
        apply equiv_dist, uPred.entails_equiv_and. iIntros "LFT HE HL".
        iDestruct (Hc (S n) with "LFT HE HL") as "[_ [$ _]]". }
      assert (Hshr : lft_ctx -∗ lft_contexts.elctx_interp_0 E -∗
                ⌜lft_contexts.llctx_interp_0 L⌝ -∗
                □ (∀ κ tid l,
                   (compl c).(ty_shr) κ tid l ↔ (fixpoint T2).(ty_shr) κ tid l)).
      { apply uPred.entails_equiv_and, equiv_dist=>n.
        destruct (conv_compl n c) as [_ Heq]. setoid_rewrite (λ κ tid l, Heq κ tid l).
        apply equiv_dist, uPred.entails_equiv_and. iIntros "LFT HE HL".
        iDestruct (Hc n with "LFT HE HL") as "[_ [_ $]]". }
      iIntros "LFT HE HL". iSplit; [|iSplit].
      + iApply (Hsz with "LFT HE HL").
      + iApply (Hown with "LFT HE HL").
      + iApply (Hshr with "LFT HE HL").
  Qed.

  Lemma fixpoint_unfold_subtype_l ty T `{Contractive T} :
    subtype E L ty (T (fixpoint T)) → subtype E L ty (fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_subtype_r ty T `{Contractive T} :
    subtype E L (T (fixpoint T)) ty → subtype E L (fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_l ty T `{Contractive T} :
    eqtype E L ty (T (fixpoint T)) → eqtype E L ty (fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_r ty T `{Contractive T} :
    eqtype E L (T (fixpoint T)) ty → eqtype E L (fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
End subtyping.

Hint Resolve fixpoint_mono fixpoint_proper : lrust_typing.

(* These hints can loop if [fixpoint_mono] and [fixpoint_proper] have
   not been tried before, so we give them a high cost *)
Hint Resolve fixpoint_unfold_subtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_subtype_r|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_r|100 : lrust_typing.
