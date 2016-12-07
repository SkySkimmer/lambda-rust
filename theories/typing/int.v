From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import typing bool.

Section int.
  Context `{iris_typeG Σ}.

  Program Definition int : type :=
    {| st_size := 1; st_own tid vl := (∃ z:Z, ⌜vl = [ #z ]⌝)%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Lemma typed_int ρ (z:Datatypes.nat) :
    typed_step_ty ρ #z int.
  Proof. iIntros (tid) "!#(_&_&_&$)". wp_value. by iExists _. Qed.

  Lemma typed_plus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 + e2) int.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#ĽFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. by iExists _.
  Qed.

  Lemma typed_minus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 - e2) int.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#LFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. by iExists _.
  Qed.

  Lemma typed_le e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 ≤ e2) bool.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#LFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op; intros _; by iExists _.
  Qed.
End int.