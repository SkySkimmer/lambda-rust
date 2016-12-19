From lrust.lang Require Export lifting.
From iris.proofmode Require Import tactics.
Import uPred.

(** Define some derived forms, and derived lemmas about them. *)
Notation Lam xl e := (Rec BAnon xl e).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV xl e := (RecV BAnon xl e).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Coercion lit_of_bool : bool >-> base_lit.
Notation If e0 e1 e2 := (Case e0 [e2;e1]).
Definition Newlft := Lit LitUnit.
Definition Endlft := Skip.

Section derived.
Context `{ownPG lrust_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E xl e e' el Φ :
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (xl +b+ []) e →
  subst_l xl el e = Some e' →
  ▷ WP e' @ E {{ Φ }} -∗ WP App (Lam xl e) el @ E {{ Φ }}.
Proof. iIntros (???) "?". by iApply (wp_rec _ _ BAnon). Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. eauto using wp_lam. Qed.

Lemma wp_let' E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x (of_val v) e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. intros ?. rewrite (of_to_val e1) //. eauto using wp_let. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} -∗ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros (??) "?". by iApply (wp_let _ BAnon). Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) -∗ WP Skip @ E {{ Φ }}.
Proof. iIntros. iApply wp_seq. done. iNext. by iApply wp_value. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P -∗ ▷ |={E}=> Φ (LitV true)) →
  (n2 < n1 → P -∗ ▷ |={E}=> Φ (LitV false)) →
  P -∗ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hg) "HP". iApply wp_fupd.
  destruct (bool_decide_reflect (n1 ≤ n2)); [rewrite Hl //|rewrite Hg; last omega];
    clear Hl Hg; (iApply wp_bin_op_pure; first by econstructor); iNext; iIntros (?? Heval);
    inversion_clear Heval; [rewrite bool_decide_true //|rewrite bool_decide_false //].
Qed.

Lemma wp_offset E l z Φ :
  ▷ (|={E}=> Φ (LitV $ LitLoc $ shift_loc l z)) -∗
    WP BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_fupd. iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_plus E z1 z2 Φ :
  ▷ (|={E}=> Φ (LitV $ LitInt $ z1 + z2)) -∗
    WP BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_fupd. iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_minus E z1 z2 Φ :
  ▷ (|={E}=> Φ (LitV $ LitInt $ z1 - z2)) -∗
    WP BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_fupd. iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

(* TODO: Add lemmas for equality test. *)

Lemma wp_if E (b : bool) e1 e2 Φ :
  (if b then ▷ WP e1 @ E {{ Φ }} else ▷ WP e2 @ E {{ Φ }})%I -∗
  WP If (Lit b) e1 e2 @ E {{ Φ }}.
Proof. iIntros "?". by destruct b; iApply wp_case. Qed.
End derived.
