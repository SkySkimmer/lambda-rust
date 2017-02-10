From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap.
From lrust.lang Require Import tactics.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.
Hint Constructors lit_neq lit_eq.

Class lrustG Σ := LRustG {
  lrustG_invG : invG Σ;
  lrustG_gen_heapG :> heapG Σ
}.

Instance lrustG_irisG `{lrustG Σ} : irisG lrust_lang Σ := {
  iris_invG := lrustG_invG;
  state_interp := heap_ctx
}.
Global Opaque iris_invG.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_eq/=
  | H : lit_neq _ ?x ?y |- _ => inversion H; clear H; simplify_eq/=
  end.

Section lifting.
Context `{lrustG Σ}.
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

Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l sz (vl : vec val sz), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…(Z.to_nat n) ∗ l ↦∗ vl }}}.
Proof.
  iIntros (? Φ) "HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [done..|].
  iModIntro; iSplit=> //. iFrame.
  (* FIXME: Merging these two into one "iApply" doesn't work. *)
  iSpecialize ("HΦ" $! _ (length init)). iApply ("HΦ" $! (list_to_vec init)).
  rewrite vec_to_list_of_list. auto.
Qed.

Lemma wp_free E (n:Z) l vl :
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc E l q v :
  {{{ ▷ l ↦{q} v }}} Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (?) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[n ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. rewrite to_of_val. iFrame. by iApply "HΦ".
Qed.

Lemma wp_read_na E l q v :
  {{{ ▷ l ↦{q} v }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hv HΦ". iApply wp_lift_head_step; auto. iIntros (σ1) "Hσ".
  iMod (heap_read_na with "Hσ Hv") as (n) "(% & Hσ & Hσclose)".
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; [|by iApply big_sepL_nil].
  clear dependent σ1 n.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iMod ("Hσclose" with "Hσ") as (n) "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step. rewrite to_of_val /=.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_write_sc E l e v v' :
  to_val e = Some v →
  {{{ ▷ l ↦ v' }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iMod (heap_write _ _ _  v with "Hσ Hv") as "[Hσ Hv]".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_write_na E l e v v' :
  to_val e = Some v →
  {{{ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ".
  iApply wp_lift_head_step; auto. iIntros (σ1) "Hσ".
  iMod (heap_write_na with "Hσ Hv") as "(% & Hσ & Hσclose)".
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; [|by iApply big_sepL_nil].
  clear dependent σ1. iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iMod ("Hσclose" with "Hσ") as "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_cas_int_fail E l q z1 e2 lit2 zl :
  to_val e2 = Some (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦{q} LitV (LitInt zl) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 0; l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[n ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc E l lit1 e2 lit2 :
  to_val e2 = Some (LitV lit2) → lit1 ≠ LitUnit →
  {{{ ▷ l ↦ LitV lit1 }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct lit1; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; [inv_lit|].
  iMod (heap_write with "Hσ Hv") as "[$ Hv]".
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_int_suc E l z1 e2 lit2 :
  to_val e2 = Some (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_suc E l l1 e2 lit2 :
  to_val e2 = Some (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
  to_val e2 = Some (LitV lit2) → l1 ≠ l' →
  {{{ ▷ l ↦{q} LitV (LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 0);
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) "(>Hl & >Hl' & >Hl1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hl") as %[nl ?].
  iDestruct (heap_read with "Hσ Hl'") as %[nl' ?].
  iDestruct (heap_read with "Hσ Hl1") as %[nl1 ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; iFrame.
Qed.

Lemma wp_cas_loc_nondet E l l1 e2 l2 ll :
  to_val e2 = Some (LitV $ LitLoc l2) →
  {{{ ▷ l ↦ LitV (LitLoc ll) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ b, RET LitV (lit_of_bool b);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct (decide (ll = l1)) as [->|]; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; last lia.
  - inv_lit. iModIntro; iSplit; [done|]; iFrame "Hσ".
    iApply "HΦ"; simpl; auto.
  - iMod (heap_write with "Hσ Hv") as "[$ Hv]".
    iModIntro; iSplit; [done|]. iApply "HΦ"; iFrame.
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
  e = Rec f xl erec →
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (f :b: xl +b+ []) erec →
  subst_l (f::xl) (e::el) erec = Some erec' →
  ▷ WP erec' @ E {{ Φ }} -∗ WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "?". iApply wp_lift_pure_det_head_step; subst; eauto.
  by intros; inv_head_step; eauto. iNext. rewrite big_sepL_nil. by iFrame.
Qed.

(* TODO: wp_eq for locations, if needed.
Lemma wp_bin_op_heap E σ op l1 l2 l' :
  bin_op_eval σ op l1 l2 l' →
  {{{ ▷ ownP σ }}} BinOp op (Lit l1) (Lit l2) @ E
  {{{ l'', RET LitV l''; ⌜bin_op_eval σ op l1 l2 l''⌝ ∗ ownP σ }}}.
Proof.
  iIntros (? Φ) "HP HΦ". iApply ownP_lift_atomic_head_step; eauto.
  iFrame "HP". iNext. iIntros (e2 σ2 efs Hs) "Ho".
  inv_head_step; rewrite big_sepL_nil right_id.
  iApply "HΦ". eauto.
Qed.
*)

Lemma wp_bin_op_pure E op l1 l2 l' :
  (∀ σ, bin_op_eval σ op l1 l2 l') →
  {{{ True }}} BinOp op (Lit l1) (Lit l2) @ E
  {{{ l'' σ, RET LitV l''; ⌜bin_op_eval σ op l1 l2 l''⌝ }}}.
Proof.
  iIntros (? Φ) "HΦ". iApply wp_lift_pure_head_step; eauto.
  { intros. by inv_head_step. }
  iNext. iIntros (e2 efs σ Hs).
  inv_head_step; rewrite big_sepL_nil right_id.
  rewrite -wp_value //. iApply "HΦ". eauto.
Qed.

Lemma wp_case E i e el Φ :
  0 ≤ i →
  el !! (Z.to_nat i) = Some e →
  ▷ WP e @ E {{ Φ }} -∗ WP Case (Lit $ LitInt i) el @ E {{ Φ }}.
Proof.
  iIntros (??) "?". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iNext. rewrite big_sepL_nil. by iFrame.
Qed.
End lifting.
