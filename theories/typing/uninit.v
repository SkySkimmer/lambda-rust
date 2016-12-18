From lrust.typing Require Export type.
From lrust.typing Require Import product.

Section uninit.
  Context `{typeG Σ}.

  Program Definition uninit_1 : type :=
    {| st_own tid vl := ⌜length vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Definition uninit (n : nat) : type :=
    Π (replicate n uninit_1).

  Global Instance uninit_copy n : Copy (uninit n).
  Proof. apply product_copy, Forall_replicate, _. Qed.

  Lemma uninit_sz n : ty_size (uninit n) = n.
  Proof. induction n. done. simpl. by f_equal. Qed.

  Lemma uninit_product E L ns :
    eqtype E L (uninit (foldr plus 0%nat ns)) (Π(uninit <$> ns)).
  Proof.
    induction ns as [|n ns IH]. done. revert IH.
    by rewrite /= /uninit replicate_plus prod_flatten_l -!prod_app=>->.
  Qed.
End uninit.
