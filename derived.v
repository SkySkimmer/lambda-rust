From lrust Require Export lifting.
From iris.proofmode Require Import weakestpre.
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
Notation Newlft := (Lit LitUnit) (only parsing).
Notation Endlft := (Seq Skip Skip) (only parsing).

Section derived.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp lrust_lang Σ.
Implicit Types Φ : val → iProp lrust_lang Σ.

(** Proof rules for the sugar *)
Lemma wp_lam E xl e e' el Φ :
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (xl +b+ []) e →
  subst_l xl el e = Some e' →
  ▷ WP e' @ E {{ Φ }} ⊢ WP App (Lam xl e) el @ E {{ Φ }}.
Proof. iIntros (???) "?". by iApply (wp_rec _ BAnon). Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ E {{ Φ }} ⊢ WP Let x e1 e2 @ E {{ Φ }}.
Proof. eauto using wp_lam. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros (??) "?". by iApply (wp_let _ BAnon). Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊢ WP Skip @ E {{ Φ }}.
Proof. iIntros. iApply wp_seq. done. iNext. by iApply wp_value. Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P ⊢ ▷ |={E}=> Φ (LitV true)) →
  (n2 < n1 → P ⊢ ▷ |={E}=> Φ (LitV false)) →
  P ⊢ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  intros. rewrite -wp_bin_op //; [].
  destruct (bool_decide_reflect (n1 ≤ n2)); by eauto with omega.
Qed.

Lemma wp_if E (b : bool) e1 e2 Φ :
  (if b then ▷ WP e1 @ E {{ Φ }} else ▷ WP e2 @ E {{ Φ }})%I
  ⊢ WP If (Lit b) e1 e2 @ E {{ Φ }}.
Proof. iIntros "?". by destruct b; iApply wp_case. Qed.
End derived.
