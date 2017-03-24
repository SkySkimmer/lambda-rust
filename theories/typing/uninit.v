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
  Proof. induction n=>//=. by f_equal. Qed.

  (* We redefine uninit as an alias of uninit0, so that the size
     computes directly to [n] *)
  Program Definition uninit (n : nat) : type :=
    {| ty_size := n; ty_own := (uninit0 n).(ty_own);
       ty_shr := (uninit0 n).(ty_shr) |}.
  Next Obligation. intros. by rewrite ty_size_eq uninit0_sz. Qed.
  Next Obligation. intros. by apply ty_share. Qed.
  Next Obligation. intros. by apply ty_shr_mono. Qed.

  Global Instance uninit_wf n : TyWf (uninit n) :=
    { ty_lfts := []; ty_wf_E := [] }.

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
  Proof. apply equiv_eqtype; constructor=>//=. apply uninit0_sz. Qed.

  Lemma uninit_product_subtype_cons {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L (uninit ty.(ty_size)) ty →
    subtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    subtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ?%Nat2Z.inj_le. rewrite -!uninit_uninit0_eqtype /uninit0=>Hty Htyl.
    rewrite (le_plus_minus ty.(ty_size) n) // replicate_plus
           -(prod_flatten_r _ _ [_]) /= -prod_app. repeat (done || f_equiv).
  Qed.
  Lemma uninit_product_subtype_cons' {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L ty (uninit ty.(ty_size)) →
    subtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    subtype E L (Π(ty :: tyl)) (uninit n).
  Proof.
    intros ?%Nat2Z.inj_le. rewrite -!uninit_uninit0_eqtype /uninit0=>Hty Htyl.
    rewrite (le_plus_minus ty.(ty_size) n) // replicate_plus
           -(prod_flatten_r _ _ [_]) /= -prod_app. repeat (done || f_equiv).
  Qed.
  Lemma uninit_product_eqtype_cons {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L (uninit ty.(ty_size)) ty →
    eqtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    eqtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ? [] []. split.
    - by apply uninit_product_subtype_cons.
    - by apply uninit_product_subtype_cons'.
  Qed.
  Lemma uninit_product_eqtype_cons' {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L ty (uninit ty.(ty_size)) →
    eqtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    eqtype E L (Π(ty :: tyl)) (uninit n).
  Proof. symmetry. by apply uninit_product_eqtype_cons. Qed.

  Lemma uninit_unit_eqtype E L n :
    n = 0%nat →
    eqtype E L (uninit n) unit.
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_eqtype' E L n :
    n = 0%nat →
    eqtype E L unit (uninit n).
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_subtype E L n :
    n = 0%nat →
    subtype E L (uninit n) unit.
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.
  Lemma uninit_unit_subtype' E L n :
    n = 0%nat →
    subtype E L unit (uninit n).
  Proof. rewrite -uninit_uninit0_eqtype=>->//. Qed.

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
