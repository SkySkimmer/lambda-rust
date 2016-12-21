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
    
  Definition uninit (n : nat) : type :=
    Π (replicate n uninit_1).

  Global Instance uninit_copy n : Copy (uninit n).
  Proof. apply product_copy, Forall_replicate, _. Qed.

  Global Instance uninit_send n : Send (uninit n).
  Proof. apply product_send, Forall_replicate, _. Qed.

  Global Instance uninit_sync n : Sync (uninit n).
  Proof. apply product_sync, Forall_replicate, _. Qed.

  Lemma uninit_sz n : ty_size (uninit n) = n.
  Proof. induction n. done. simpl. by f_equal. Qed.

  Lemma uninit_product E L ns :
    eqtype E L (uninit (foldr plus 0%nat ns)) (Π(uninit <$> ns)).
  Proof.
    induction ns as [|n ns IH]. done. revert IH.
    by rewrite /= /uninit replicate_plus prod_flatten_l -!prod_app=>->.
  Qed.

  Lemma uninit_own n tid vl :
    (uninit n).(ty_own) tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    iSplit.
    - iIntros "?". rewrite -{2}(uninit_sz n). by iApply ty_size_eq.
    - iInduction vl as [|v vl] "IH" forall (n).
      + iIntros "%". destruct n; done.
      + iIntros (Heq). destruct n; first done. simpl.
        iExists [v], vl. iSplit; first done. iSplit; first done.
        iApply "IH". by inversion Heq.
  Qed. 
End uninit.
