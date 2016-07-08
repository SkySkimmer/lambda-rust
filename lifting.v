From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ownership ectx_lifting. (* for ownP *)
From lrust Require Export lang.
From lrust Require Import tactics.
From iris.proofmode Require Import weakestpre.
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.

Section lifting.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp lrust_lang Σ.
Implicit Types Φ : val → iProp lrust_lang Σ.
Implicit Types ef : option (expr []).

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ n Φ :
  0 < n →
  ▷ ownP σ ★
  ▷ (∀ l σ', ■ (∀ m, σ !! (shift_loc l m) = None) ★
             ■ (∃ vl, n = length vl ∧ init_mem l vl σ = σ') ★
             ownP σ' ={E}=★ Φ (LitV $ LitLoc l))
  ⊢ WP Alloc (Lit $ LitInt n) @ E {{ Φ }}.
Proof.
  iIntros {?}  "[HP HΦ]". iApply (wp_lift_atomic_head_step _ σ); eauto.
  iFrame "HP". iNext. iIntros {v2 σ2 ef} "[% HP]". inv_head_step.
  rewrite right_id. iApply "HΦ". iFrame. eauto.
Qed.

Lemma wp_free_pst E σ l n Φ :
  0 < n →
  (∀ m, is_Some (σ !! (shift_loc l m)) ↔ (0 ≤ m < n)) →
  ▷ ownP σ ★
  ▷ (ownP (free_mem l (Z.to_nat n) σ) ={E}=★ Φ (LitV $ LitUnit))
  ⊢ WP Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros {??}  "[HP HΦ]". iApply (wp_lift_atomic_head_step _ σ); eauto.
  iFrame "HP". iNext. iIntros {v2 σ2 ef} "[% HP]". inv_head_step.
  rewrite right_id. by iApply "HΦ".
Qed.

Lemma wp_read_sc_pst E σ l n v Φ :
  σ !! l = Some (RSt n, v) →
  ▷ ownP σ ★ ▷ (ownP σ ={E}=★ Φ v) ⊢ WP Read ScOrd (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros {?} "[??]". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto using to_of_val. by rewrite right_id; iFrame.
Qed.

Lemma wp_read_in_pst E σ l n v Φ :
  σ !! l = Some(RSt $ S n, v) →
  ▷ ownP σ ★ ▷ (ownP (<[l:=(RSt n, v)]>σ) ={E}=★ Φ v)
  ⊢ WP Read Na2Ord (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros {?} "[??]". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto using to_of_val. by rewrite right_id; iFrame.
Qed.

Lemma wp_read_na_pst E1 E2 l Φ :
  E2 ⊆ E1 →
  (|={E1,E2}=> ∃ σ n v, σ !! l = Some(RSt $ n, v) ∧
     ▷ ownP σ ★
     ▷ (ownP (<[l:=(RSt $ S n, v)]>σ) ={E2,E1}=★
          WP Read Na2Ord (Lit $ LitLoc l) @ E1 {{ Φ }}))
  ⊢ WP Read Na1Ord (Lit $ LitLoc l) @ E1 {{ Φ }}.
Proof.
  iIntros {?} "HΦP". iApply (wp_lift_head_step E1 E2); auto.
  iPvs "HΦP" as {σ n v} "(%&HΦ&HP)"; first set_solver. iPvsIntro.
  iExists σ. iSplit. done. iFrame. iNext. iIntros {e2 σ2 ef} "[% HΦ]".
  inv_head_step. rewrite right_id. iApply ("HP" with "HΦ").
Qed.

Lemma wp_write_sc_pst E σ l e v v' Φ :
  to_val e = Some v →
  σ !! l = Some (RSt 0, v') →
  ▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, v)]>σ) ={E}=★ Φ (LitV LitUnit))
  ⊢ WP Write ScOrd (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  iIntros {??} "[??]". iApply wp_lift_atomic_det_head_step; simpl; eauto.
  by intros; inv_head_step; eauto. by rewrite right_id; iFrame.
Qed.

Lemma wp_write_in_pst E σ l e v v' Φ :
  to_val e = Some v →
  σ !! l = Some(WSt, v') →
  ▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, v)]>σ) ={E}=★ Φ (LitV LitUnit))
  ⊢ WP Write Na2Ord (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  iIntros {??} "[??]". iApply wp_lift_atomic_det_head_step; simpl; eauto.
  by intros; inv_head_step; eauto. by rewrite right_id; iFrame.
Qed.

Lemma wp_write_na_pst E1 E2 l e v Φ :
  to_val e = Some v →
  E2 ⊆ E1 →
  (|={E1,E2}=> ∃ σ v', σ !! l = Some(RSt 0, v') ∧
     ▷ ownP σ ★
     ▷ (ownP (<[l:=(WSt, v')]>σ) ={E2,E1}=★
       WP Write Na2Ord (Lit $ LitLoc l) e @ E1 {{ Φ }}))
  ⊢ WP Write Na1Ord (Lit $ LitLoc l) e @ E1 {{ Φ }}.
Proof.
  iIntros {??} "HΦP".
  iApply (wp_lift_head_step E1 E2); auto.
  iPvs "HΦP" as {σ v'} "(%&HΦ&HP)"; first set_solver. iPvsIntro.
  iExists σ. iSplit. done. iFrame. iNext. iIntros {e2 σ2 ef} "[% HΦ]".
  inv_head_step. rewrite right_id. iApply ("HP" with "HΦ").
Qed.

Lemma wp_cas_fail_pst E σ l n e1 v1 e2 v2 vl Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  σ !! l = Some (RSt n, vl) →
  value_eq σ v1 vl = Some false →
  ▷ ownP σ ★ ▷ (ownP σ ={E}=★ Φ (LitV $ LitInt 0))
  ⊢ WP CAS (Lit $ LitLoc l) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros {????} "[HP HΦ]".
  iApply wp_lift_atomic_det_head_step; try by simpl; eauto 10.
    by intros; inv_head_step; eauto.
  iFrame. iNext. by rewrite right_id.
Qed.

Lemma wp_cas_suc_pst E σ l e1 v1 e2 v2 vl Φ :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  σ !! l = Some (RSt 0, vl) →
  value_eq σ v1 vl = Some true →
  ▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, v2)]>σ) ={E}=★ Φ (LitV $ LitInt 1))
  ⊢ WP CAS (Lit $ LitLoc l) e1 e2 @ E {{ Φ }}.
Proof.
  iIntros {????} "[HP HΦ]".
  iApply wp_lift_atomic_det_head_step; try by simpl; eauto 10.
    by intros; inv_head_step; eauto.
  iFrame. iNext. by rewrite right_id.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  ▷ Φ (LitV LitUnit) ★ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  iIntros "[??]". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext. iFrame. by iApply wp_value.
Qed.

Lemma wp_rec E f xl erec erec' e el Φ :
  e = Rec f xl erec →
  Forall (λ ei, is_Some (to_val ei)) el →
  subst_l xl el erec = Some erec' →
  ▷ WP subst' f e erec' @ E {{ Φ }} ⊢ WP App e el @ E {{ Φ }}.
Proof.
  iIntros {???} "?". iApply wp_lift_pure_det_head_step; subst; eauto.
  by intros; inv_head_step; eauto. iNext. by iFrame.
Qed.

Lemma wp_bin_op E op l1 l2 l' Φ :
  bin_op_eval op l1 l2 = Some l' →
  ▷ Φ (LitV l') ⊢ WP BinOp op (Lit l1) (Lit l2) @ E {{ Φ }}.
Proof.
  iIntros {?} "?". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext. rewrite right_id. by iApply wp_value.
Qed.

Lemma wp_case E i e el Φ :
  0 ≤ i →
  nth_error el (Z.to_nat i) = Some e →
  ▷ WP e @ E {{ Φ }} ⊢ WP Case (Lit $ LitInt i) el @ E {{ Φ }}.
Proof.
  iIntros {??} "?". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext. by iFrame.
Qed.
End lifting.
