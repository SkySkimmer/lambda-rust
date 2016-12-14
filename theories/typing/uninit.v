From lrust.typing Require Export type.
From lrust.typing Require Import product.

Section uninit.
  Context `{typeG Σ}.

  Program Definition uninit_1 : type :=
    {| st_own tid vl := ⌜length vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Definition uninit (n : nat) : type :=
    Π (replicate n uninit_1).

  Lemma eqtype_uninit_product E L ns :
    eqtype E L (uninit (foldr plus 0%nat ns)) (Π(uninit <$> ns)).
  Proof.
    induction ns as [|n ns IH]. done.
    rewrite /= /uninit replicate_plus (eqtype_prod_flatten E L []).
    induction n. done. rewrite /product /=. by f_equiv.
  Qed.

  Lemma uninit_sz n : ty_size (uninit n) = n.
  Proof. induction n. done. simpl. by f_equal. Qed.
End uninit.