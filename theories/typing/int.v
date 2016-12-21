From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.

Section int.
  Context `{typeG Σ}.

  Program Definition int : type :=
    {| st_own tid vl := (∃ z:Z, ⌜vl = [ #z ]⌝)%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Global Instance int_send : Send int.
  Proof. iIntros (tid1 tid2 vl). done. Qed.
End int.

Section typing.
  Context `{typeG Σ}.

  Lemma type_int (z : Z) E L :
    typed_instruction_ty E L [] #z int.
  Proof.
    iIntros (tid qE) "!# _ $ $ _". wp_value. rewrite tctx_interp_singleton.
    iExists _. iSplitR; first done. iExists _. done.
  Qed.

  Lemma type_plus E L p1 p2 :
    typed_instruction_ty E L [TCtx_hasty p1 int; TCtx_hasty p2 int] (p1 + p2) int.
  Proof.
    iIntros (tid qE) "!# _ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "% Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op. rewrite tctx_interp_singleton. iExists _. iSplitR; first done.
    iExists _. done.
  Qed.

  Lemma type_minus E L p1 p2 :
    typed_instruction_ty E L [TCtx_hasty p1 int; TCtx_hasty p2 int] (p1 - p2) int.
  Proof.
    iIntros (tid qE) "!# _ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "% Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op. rewrite tctx_interp_singleton. iExists _. iSplitR; first done.
    iExists _. done.
  Qed.

  Lemma type_le E L p1 p2 :
    typed_instruction_ty E L [TCtx_hasty p1 int; TCtx_hasty p2 int] (p1 ≤ p2) bool.
  Proof.
    iIntros (tid qE) "!# _ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "% Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op; intros _; rewrite tctx_interp_singleton; iExists _; (iSplitR; first done);
      iExists _; done.
  Qed.
  
End typing.
