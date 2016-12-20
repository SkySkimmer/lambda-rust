From lrust.lang Require Export lifting.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
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

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind {n} (Q : nat → val → iProp Σ) E f (el : vec expr n) (vs : list val) Φ :
  is_Some (to_val f) →
   ([∗ list] k ↦ e ∈ el, WP e @ E {{ Q k }}) -∗
   (∀ vl : vec val n, ([∗ list] k ↦ v ∈ vl, Q k v) -∗
                    WP App f (map of_val (vs ++ vl)) @ E {{ Φ }}) -∗
    WP App f (map of_val vs ++ el) @ E {{ Φ }}.
Proof.
  iIntros (Hf) "Hel HΦ". iInduction el as [|e n el] "IH" forall (vs Q).
  - iSpecialize ("HΦ" $! [#]). rewrite !app_nil_r. iApply "HΦ".
    by rewrite !big_sepL_nil.
  - destruct Hf as [vf Hf]. set (K := AppRCtx vf vs el).
    rewrite (_ : App f ((map of_val vs) ++ e ::: el) = fill_item K e); last first.
    { simpl. f_equal. by erewrite of_to_val. }
    iApply wp_bindi. rewrite vec_to_list_cons big_sepL_cons. iDestruct "Hel" as "[He Hel]".
    iApply (wp_wand with "He"). iIntros (v) "HQ".
    simpl. erewrite of_to_val by done. iSpecialize ("IH" $! (vs ++ [v])).
    rewrite [map of_val (vs ++ [#v])]map_app /= -app_assoc /=.
    iApply ("IH" with "Hel"). iIntros (vl) "Hvl".
    iSpecialize ("HΦ" $! (v ::: vl)). rewrite -app_assoc /=. iApply "HΦ".
    rewrite big_sepL_cons. iFrame.
Qed.

Lemma wp_app {n} (Q : nat → val → iProp Σ) E f (el : vec expr n) Φ :
  is_Some (to_val f) →
  ([∗ list] k ↦ e ∈ el, WP e @ E {{ Q k }}) -∗
    (∀ vl : vec val n, ([∗ list] k ↦ v ∈ vl, Q k v) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hf). iApply (wp_app_ind _ _ _ _ []). done.
Qed.

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
