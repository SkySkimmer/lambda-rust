From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".

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

  Lemma type_int_instr (z : Z) E L :
    typed_instruction_ty E L [] #z int.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $ _". wp_value.
    rewrite tctx_interp_singleton tctx_hasty_val. iExists _. done.
  Qed.

  Lemma type_int (z : Z) E L C T x e :
    Closed (x :b: []) e →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T) (subst' x v e)) →
    typed_body E L C T (let: x := #z in e).
  Proof.
    intros. eapply type_let; [done|apply type_int_instr|solve_typing|done].
  Qed.

  Lemma type_plus_instr E L p1 p2 :
    typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 + p2) int.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "_ Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "_ Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op. rewrite tctx_interp_singleton tctx_hasty_val' //.
    iExists _. done.
  Qed.

  Lemma type_plus E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T') (subst' x v e)) →
    typed_body E L C T (let: x := p1 + p2 in e).
  Proof.
    intros. eapply type_let; [done|apply type_plus_instr|solve_typing|done].
  Qed.

  Lemma type_minus_instr E L p1 p2 :
    typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 - p2) int.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "_ Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "_ Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op. rewrite tctx_interp_singleton tctx_hasty_val' //.
    iExists _. done.
  Qed.

  Lemma type_minus E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T') (subst' x v e)) →
    typed_body E L C T (let: x := p1 - p2 in e).
  Proof.
    intros. eapply type_let; [done|apply type_minus_instr|solve_typing|done].
  Qed.

  Lemma type_le_instr E L p1 p2 :
    typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $". rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "_ Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "_ Hown2".
    iDestruct "Hown1" as (z1) "EQ". iDestruct "EQ" as %[=->].
    iDestruct "Hown2" as (z2) "EQ". iDestruct "EQ" as %[=->].
    wp_op; intros _; rewrite tctx_interp_singleton tctx_hasty_val' //;
      iExists _; done.
  Qed.

  Lemma type_le E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ bool) :: T') (subst' x v e)) →
    typed_body E L C T (let: x := p1 ≤ p2 in e).
  Proof.
    intros. eapply type_let; [done|apply type_le_instr|solve_typing|done].
  Qed.
End typing.
