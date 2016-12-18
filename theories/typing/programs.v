From iris.program_logic Require Import hoare.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context cont_context.
From lrust.lang Require Import proofmode.
From lrust.lifetime Require Import frac_borrow reborrow borrow creation.

Section typing.
  Context `{typeG Σ}.

  Definition typed_body (E : elctx) (L : llctx) (C : cctx) (T : tctx)
                        (e : expr) : iProp Σ :=
    (∀ tid qE, lft_ctx -∗ elctx_interp E qE -∗ llctx_interp L 1 -∗
               (elctx_interp E qE -∗ cctx_interp tid C) -∗ tctx_interp tid T -∗
               WP e {{ _, cont_postcondition }})%I.

  Instance typed_body_llctx_permut E :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> (⊢)) (typed_body E).
  Proof.
    intros L1 L2 HL C ? <- T ? <- e ? <-. rewrite /typed_body. by setoid_rewrite HL.
  Qed.

  Instance typed_body_mono E L:
    Proper (flip (cctx_incl E) ==> flip (tctx_incl E L) ==> eq ==> (⊢)) (typed_body E L).
  Proof.
    intros C1 C2 HC T1 T2 HT e ? <-. iIntros "H".
    iIntros (tid qE) "#LFT HE HL HC HT".
    iMod (HT with "LFT HE HL HT") as "(HE & HL & HT)".
    iApply ("H" with "LFT HE HL [HC] HT").
    iIntros "HE". by iApply (HC with "LFT HC").
  Qed.

End typing.
