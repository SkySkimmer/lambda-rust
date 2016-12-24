From lrust.lifetime Require Import definitions.
From lrust.typing Require Export type bool.

Section fixpoint.
  Context `{typeG Σ}.

  Global Instance type_inhabited : Inhabited type := populate bool.

  Context (T : type → type) `{Contractive T}.

  (* FIXME : Contrarily to the rule on paper, these rules are
     coinductive: they let one assume [ty] is [Copy]/[Send]/[Sync] to
     prove that [T ty] is [Copy]/[Send]/[Sync]. *)
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
        do 2 f_equiv; first by rewrite conv_compl. do 8 (f_contractive || f_equiv).
        * by rewrite -conv_compl.
        * destruct n. done. by setoid_rewrite conv_compl.
        * by rewrite -conv_compl.
        * f_equiv. f_contractive. unfold dist_later. destruct n=>//.
          by setoid_rewrite conv_compl.
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
