From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang.
From lrust.lang Require Import tactics.
From iris.proofmode Require Import tactics.
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.

Section lifting.
Context `{irisG lrust_lang Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types ef : option expr.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} -∗ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} -∗
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ n:
  0 < n →
  {{{ ▷ ownP σ }}} Alloc (Lit $ LitInt n) @ E
  {{{ l σ', RET LitV $ LitLoc l;
      ⌜∀ m, σ !! (shift_loc l m) = None⌝ ∗
      ⌜∃ vl, n = length vl ∧ init_mem l vl σ = σ'⌝ ∗
      ownP σ' }}}.
Proof.
  iIntros (? Φ) "HP HΦ". iApply (wp_lift_atomic_head_step _ σ); eauto.
  iFrame "HP". iNext. iIntros (v2 σ2 ef) "% HP". inv_head_step.
  rewrite big_sepL_nil right_id. by iApply "HΦ"; iFrame; eauto.
Qed.

Lemma wp_free_pst E σ l n :
  0 < n →
  (∀ m, is_Some (σ !! (shift_loc l m)) ↔ (0 ≤ m < n)) →
  {{{ ▷ ownP σ }}} Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV $ LitUnit; ownP (free_mem l (Z.to_nat n) σ) }}}.
Proof.
  iIntros (???)  "HP HΦ". iApply (wp_lift_atomic_head_step _ σ); eauto.
  iFrame "HP". iNext. iIntros (v2 σ2 ef) "% HP". inv_head_step.
  rewrite big_sepL_nil right_id. by iApply "HΦ".
Qed.

Lemma wp_read_sc_pst E σ l n v :
  σ !! l = Some (RSt n, v) →
  {{{ ▷ ownP σ }}} Read ScOrd (Lit $ LitLoc l) @ E {{{ RET v; ownP σ }}}.
Proof.
  iIntros (??) "?HΦ". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto using to_of_val.
  rewrite big_sepL_nil right_id; iFrame.
Qed.

Lemma wp_read_na2_pst E σ l n v :
  σ !! l = Some(RSt $ S n, v) →
  {{{ ▷ ownP σ }}} Read Na2Ord (Lit $ LitLoc l) @ E
  {{{ RET v; ownP (<[l:=(RSt n, v)]>σ) }}}.
Proof.
  iIntros (??) "?HΦ". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto using to_of_val.
  rewrite big_sepL_nil right_id; iFrame.
Qed.

Lemma wp_read_na1_pst E l Φ :
  (|={E,∅}=> ∃ σ n v, ⌜σ !! l = Some(RSt $ n, v)⌝ ∧
     ▷ ownP σ ∗
     ▷ (ownP (<[l:=(RSt $ S n, v)]>σ) ={∅,E}=∗
          WP Read Na2Ord (Lit $ LitLoc l) @ E {{ Φ }})) -∗
  WP Read Na1Ord (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros "HΦP". iApply (wp_lift_head_step E); auto.
  iMod "HΦP" as (σ n v) "(%&HΦ&HP)". iModIntro. iExists σ. iSplit. done. iFrame.
  iNext. iIntros (e2 σ2 ef) "% HΦ". inv_head_step.
  rewrite big_sepL_nil right_id. iApply ("HP" with "HΦ").
Qed.

Lemma wp_write_sc_pst E σ l v v' :
  σ !! l = Some (RSt 0, v') →
  {{{ ▷ ownP σ }}} Write ScOrd (Lit $ LitLoc l) (of_val v) @ E
  {{{ RET LitV LitUnit; ownP (<[l:=(RSt 0, v)]>σ) }}}.
Proof.
  iIntros (??) "?HΦ". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto. rewrite big_sepL_nil right_id; iFrame.
Qed.

Lemma wp_write_na2_pst E σ l v v' :
  σ !! l = Some(WSt, v') →
  {{{ ▷ ownP σ }}} Write Na2Ord (Lit $ LitLoc l) (of_val v) @ E
  {{{ RET LitV LitUnit; ownP (<[l:=(RSt 0, v)]>σ) }}}.
Proof.
  iIntros (??) "?HΦ". iApply wp_lift_atomic_det_head_step; eauto.
  by intros; inv_head_step; eauto. rewrite big_sepL_nil right_id; iFrame.
Qed.

Lemma wp_write_na1_pst E l v Φ :
  (|={E,∅}=> ∃ σ v', ⌜σ !! l = Some(RSt 0, v')⌝ ∧
     ▷ ownP σ ∗
     ▷ (ownP (<[l:=(WSt, v')]>σ) ={∅,E}=∗
       WP Write Na2Ord (Lit $ LitLoc l) (of_val v) @ E {{ Φ }})) -∗
  WP Write Na1Ord (Lit $ LitLoc l) (of_val v) @ E {{ Φ }}.
Proof.
  iIntros "HΦP". iApply (wp_lift_head_step E); auto.
  iMod "HΦP" as (σ v') "(%&HΦ&HP)". iModIntro. iExists σ. iSplit. done. iFrame.
  iNext. iIntros (e2 σ2 ef) "% HΦ". inv_head_step.
  rewrite big_sepL_nil right_id. iApply ("HP" with "HΦ").
Qed.

Lemma wp_cas_pst E n σ l e1 lit1 lit2 litl :
  to_val e1 = Some $ LitV lit1 →
  σ !! l = Some (RSt n, LitV litl) →
  (lit_eq σ lit1 litl ∨ lit_neq σ lit1 litl) →
  (lit_eq σ lit1 litl → n = 0%nat) →
  {{{ ▷ ownP σ }}} CAS (Lit $ LitLoc l) e1 (Lit lit2) @ E
  {{{ b, RET LitV $ lit_of_bool b;
      if b is true then ⌜lit_eq σ lit1 litl⌝ ∗ ownP (<[l:=(RSt 0, LitV lit2)]>σ)
      else ⌜lit_neq σ lit1 litl⌝ ∗ ownP σ }}}.
Proof.
  iIntros (?%of_to_val ? Hdec Hn ?) "HP HΦ". subst.
  iApply wp_lift_atomic_head_step; eauto.
  { destruct Hdec as [Heq|Hneq].
    - specialize (Hn Heq). subst. do 3 eexists. by eapply CasSucS.
    - do 3 eexists. by eapply CasFailS. }
  iFrame. iNext. iIntros (e2 σ2 efs Hs) "Ho".
  inv_head_step; rewrite big_sepL_nil right_id.
  - iApply ("HΦ" $! false). eauto.
  - iApply ("HΦ" $! true). eauto.
  - exfalso. refine (_ (Hn _)); last done. intros. omega.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  {{{ ▷ WP e {{ _, True }} }}} Fork e @ E {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext.
  rewrite big_sepL_singleton. iFrame. iApply wp_value. done. by iApply "HΦ".
Qed.

Lemma wp_rec E e f xl erec erec' el Φ :
  e = Rec f xl erec → (* to avoids recursive calls being unfolded *)
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (f :b: xl +b+ []) erec →
  subst_l xl el erec = Some erec' →
  ▷ WP subst' f e erec' @ E {{ Φ }} -∗
  WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "?". iApply wp_lift_pure_det_head_step; subst; eauto.
  by intros; inv_head_step; eauto. iNext. rewrite big_sepL_nil. by iFrame.
Qed.

Lemma wp_bin_op_heap E σ op l1 l2 l' :
  bin_op_eval σ op l1 l2 l' →
  {{{ ▷ ownP σ }}} BinOp op (Lit l1) (Lit l2) @ E
  {{{ l'', RET LitV l''; ⌜bin_op_eval σ op l1 l2 l''⌝ ∗ ownP σ }}}.
Proof.
  iIntros (? Φ) "HP HΦ". iApply wp_lift_atomic_head_step; eauto.
  iFrame "HP". iNext. iIntros (e2 σ2 efs Hs) "Ho". 
  inv_head_step; rewrite big_sepL_nil right_id.
  iApply "HΦ". eauto.
Qed.

Lemma wp_bin_op_pure E op l1 l2 l' :
  (∀ σ, bin_op_eval σ op l1 l2 l') →
  {{{ True }}} BinOp op (Lit l1) (Lit l2) @ E
  {{{ l'' σ, RET LitV l''; ⌜bin_op_eval σ op l1 l2 l''⌝ }}}.
Proof.
  iIntros (? Φ) "HΦ". iApply wp_lift_pure_head_step; eauto.
  { intros. inv_head_step. done. }
  iNext. iIntros (e2 efs σ Hs). 
  inv_head_step; rewrite big_sepL_nil right_id.
  rewrite -wp_value //. iApply "HΦ". eauto.
Qed.

Lemma wp_case E i e el Φ :
  0 ≤ i →
  nth_error el (Z.to_nat i) = Some e →
  ▷ WP e @ E {{ Φ }} -∗ WP Case (Lit $ LitInt i) el @ E {{ Φ }}.
Proof.
  iIntros (??) "?". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext. rewrite big_sepL_nil. by iFrame.
Qed.
End lifting.
