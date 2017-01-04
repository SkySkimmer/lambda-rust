From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import product.

Section uninit.
  Context `{typeG Σ}.

  Program Definition uninit_1 : type :=
    {| st_own tid vl := ⌜length vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Global Instance uninit_1_send : Send uninit_1.
  Proof. iIntros (tid1 tid2 vl) "H". done. Qed.

  Definition uninit0 (n : nat) : type :=
    Π (replicate n uninit_1).

  Lemma uninit0_sz n : ty_size (uninit0 n) = n.
  Proof. induction n. done. simpl. by f_equal. Qed.

  (* We redefine uninit as an alias of uninit0, so that the size
     computes directly to [n] *)
  Program Definition uninit (n : nat) : type :=
    {| ty_size := n; ty_own := (uninit0 n).(ty_own);
       ty_shr := (uninit0 n).(ty_shr) |}.
  Next Obligation. intros. by rewrite ty_size_eq uninit0_sz. Qed.
  Next Obligation. intros. by apply ty_share. Qed.
  Next Obligation. intros. by apply ty_shr_mono. Qed.

  Global Instance uninit_copy n : Copy (uninit n).
  Proof.
    destruct (product_copy (replicate n uninit_1)) as [A B].
      by apply Forall_replicate, _.
    rewrite uninit0_sz in B. by split.
  Qed.

  Global Instance uninit_send n : Send (uninit n).
  Proof. apply product_send, Forall_replicate, _. Qed.

  Global Instance uninit_sync n : Sync (uninit n).
  Proof. apply product_sync, Forall_replicate, _. Qed.

  Lemma uninit_uninit0_eqtype E L n :
    eqtype E L (uninit0 n) (uninit n).
  Proof. apply equiv_eqtype; (split; first split)=>//=. apply uninit0_sz. Qed.

  Lemma uninit_product_eqtype E L ns :
    eqtype E L (uninit (foldr plus 0%nat ns)) (Π(uninit <$> ns)).
  Proof.
    rewrite -uninit_uninit0_eqtype. etrans; last first.
    { apply product_proper. eapply Forall2_fmap, Forall_Forall2, Forall_forall.
      intros. by rewrite -uninit_uninit0_eqtype. }
    induction ns as [|n ns IH]=>//=. revert IH.
    by rewrite /= /uninit0 replicate_plus prod_flatten_l -!prod_app=>->.
  Qed.
  Lemma uninit_product_eqtype' E L ns :
    eqtype E L (Π(uninit <$> ns)) (uninit (foldr plus 0%nat ns)).
  Proof. symmetry; apply uninit_product_eqtype. Qed.
  Lemma uninit_product_subtype E L ns :
    subtype E L (uninit (foldr plus 0%nat ns)) (Π(uninit <$> ns)).
  Proof. apply uninit_product_eqtype'. Qed.
  Lemma uninit_product_subtype' E L ns :
    subtype E L (Π(uninit <$> ns)) (uninit (foldr plus 0%nat ns)).
  Proof. apply uninit_product_eqtype. Qed.

  Lemma uninit_own n tid vl :
    (uninit n).(ty_own) tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    iSplit.
    - rewrite ty_size_eq. auto.
    - iInduction vl as [|v vl] "IH" forall (n).
      + iIntros "%". destruct n; done.
      + iIntros (Heq). destruct n; first done. simpl.
        iExists [v], vl. iSplit; first done. iSplit; first done.
        iApply "IH". by inversion Heq.
  Qed.
End uninit.

Hint Resolve uninit_product_eqtype uninit_product_eqtype'
     uninit_product_subtype uninit_product_subtype' : lrust_typing.
