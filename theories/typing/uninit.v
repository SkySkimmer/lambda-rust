From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

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

  Lemma uninit_product_subtype_cons {E L} (ntot n : nat) tyl :
    n ≤ ntot →
    subtype E L (uninit (ntot-n)) (Π tyl) →
    subtype E L (uninit ntot) (Π(uninit n :: tyl)).
  Proof.
    intros ?%Nat2Z.inj_le Htyl. rewrite (le_plus_minus n ntot) // -!uninit_uninit0_eqtype
      /uninit0 replicate_plus prod_flatten_l -!prod_app. do 3 f_equiv.
    by rewrite <-Htyl, <-uninit_uninit0_eqtype.
  Qed.
  Lemma uninit_product_subtype_cons' {E L} (ntot n : nat) tyl :
    n ≤ ntot →
    subtype E L (Π tyl) (uninit (ntot-n)) →
    subtype E L (Π(uninit n :: tyl)) (uninit ntot).
  Proof.
    intros ?%Nat2Z.inj_le Htyl. rewrite (le_plus_minus n ntot) // -!uninit_uninit0_eqtype
      /uninit0 replicate_plus prod_flatten_l -!prod_app. do 3 f_equiv.
    by rewrite ->Htyl, <-uninit_uninit0_eqtype.
  Qed.
  Lemma uninit_product_eqtype_cons {E L} (ntot n : nat) tyl :
    n ≤ ntot →
    eqtype E L (uninit (ntot-n)) (Π tyl) →
    eqtype E L (uninit ntot) (Π(uninit n :: tyl)).
  Proof.
    intros ? []. split.
    - by apply uninit_product_subtype_cons.
    - by apply uninit_product_subtype_cons'.
  Qed.
  Lemma uninit_product_eqtype_cons' {E L} (ntot n : nat) tyl :
    n ≤ ntot →
    eqtype E L (Π tyl) (uninit (ntot-n)) →
    eqtype E L (Π(uninit n :: tyl)) (uninit ntot).
  Proof. symmetry. by apply uninit_product_eqtype_cons. Qed.

  Lemma uninit_unit_eqtype E L :
    eqtype E L (uninit 0) unit.
  Proof. by rewrite -uninit_uninit0_eqtype. Qed.
  Lemma uninit_unit_eqtype' E L :
    eqtype E L unit (uninit 0).
  Proof. by rewrite -uninit_uninit0_eqtype. Qed.
  Lemma uninit_unit_subtype E L :
    subtype E L (uninit 0) unit.
  Proof. by rewrite -uninit_uninit0_eqtype. Qed.
  Lemma uninit_unit_subtype' E L :
    subtype E L unit (uninit 0).
  Proof. by rewrite -uninit_uninit0_eqtype. Qed.

  Lemma uninit_own n tid vl :
    (uninit n).(ty_own) tid vl ⊣⊢ ⌜length vl = n⌝.
  Proof.
    iSplit.
    - rewrite ty_size_eq. auto.
    - iInduction vl as [|v vl] "IH" forall (n).
      + iIntros "%". by destruct n; simpl.
      + iIntros (Heq). destruct n; first done. simpl.
        iExists [v], vl. iSplit; first done. iSplit; first done.
        unfold uninit0, product. iApply "IH". by inversion Heq.
  Qed.
End uninit.

Hint Resolve uninit_product_eqtype_cons uninit_product_eqtype_cons'
             uninit_product_subtype_cons uninit_product_subtype_cons'
             uninit_unit_eqtype uninit_unit_eqtype'
             uninit_unit_subtype uninit_unit_subtype' : lrust_typing.
