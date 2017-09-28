From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From lrust.lang Require Import lang proofmode notation.
Set Default Proof Using "Type".

Section tests.
  Context `{!lrustG Σ}.

  Lemma test_location_cmp E (l1 l2 : loc) q1 q2 v1 v2 :
    {{{ ▷ l1 ↦{q1} v1 ∗ ▷ l2 ↦{q2} v2 }}}
      #l1 = #l2 @ E
    {{{ (b: bool), RET LitV (lit_of_bool b); (if b then ⌜l1 = l2⌝ else ⌜l1 ≠ l2⌝) ∗
                                     l1 ↦{q1} v1 ∗ l2 ↦{q2} v2 }}}.
  Proof.
    iIntros (Φ) "[Hl1 Hl2] HΦ". wp_op; try (by eauto); [|];
      intros ?; iApply "HΦ"; by iFrame.
  Qed.
End tests.
