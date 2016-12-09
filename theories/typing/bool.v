From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import typing perm.

Section bool.
  Context `{typeG Σ}.

  Program Definition bool : type :=
    {| st_size := 1; st_own tid vl := (∃ z:bool, ⌜vl = [ #z ]⌝)%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Lemma typed_bool ρ (b:Datatypes.bool): typed_step_ty ρ #b bool.
  Proof. iIntros (tid) "!#(_&_&_&$)". wp_value. by iExists _. Qed.

  Lemma typed_if ρ e1 e2 ν:
    typed_program ρ e1 → typed_program ρ e2 →
    typed_program (ρ ∗ ν ◁ bool) (if: ν then e1 else e2).
  Proof.
    iIntros (He1 He2 tid) "!#(#HEAP & #LFT & [Hρ H◁] & Htl)".
    wp_bind ν. iApply (has_type_wp with "H◁"). iIntros (v) "% H◁!>".
    rewrite has_type_value. iDestruct "H◁" as (b) "Heq". iDestruct "Heq" as %[= ->].
    wp_if. destruct b; iNext. iApply He1; iFrame "∗#". iApply He2; iFrame "∗#".
  Qed.
End bool.