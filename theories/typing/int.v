From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".

Section int.
  Context `{typeG Σ}.

  Program Definition int : type :=
    {| st_own tid vl :=
         match vl return _ with
         | [ #(LitInt z)] => True
         | _ => False
         end%I |}.
  Next Obligation. intros ? [|[[]|] []]; try iIntros "[]". auto. Qed.
  Next Obligation. intros ? [|[[]|] []]; apply _. Qed.

  Global Instance int_send : Send int.
  Proof. done. Qed.
End int.

Section typing.
  Context `{typeG Σ}.

  Lemma type_int_instr (z : Z) E L :
    typed_instruction_ty E L [] #z int.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $ _". wp_value.
    by rewrite tctx_interp_singleton tctx_hasty_val.
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
    wp_bind p1. iApply (wp_hasty with "Hp1").
    iIntros ([[]|]) "_ H1"; try iDestruct "H1" as "[]".
    wp_bind p2. iApply (wp_hasty with "Hp2").
    iIntros ([[]|]) "_ H2"; try iDestruct "H2" as "[]".
    wp_op. by rewrite tctx_interp_singleton tctx_hasty_val' //.
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
    wp_bind p1. iApply (wp_hasty with "Hp1").
    iIntros ([[]|]) "_ H1"; try iDestruct "H1" as "[]".
    wp_bind p2. iApply (wp_hasty with "Hp2").
    iIntros ([[]|]) "_ H2"; try iDestruct "H2" as "[]".
    wp_op. by rewrite tctx_interp_singleton tctx_hasty_val' //.
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
    wp_bind p1. iApply (wp_hasty with "Hp1").
    iIntros ([[]|]) "_ H1"; try iDestruct "H1" as "[]".
    wp_bind p2. iApply (wp_hasty with "Hp2").
    iIntros ([[]|]) "_ H2"; try iDestruct "H2" as "[]".
    wp_op; intros _; by rewrite tctx_interp_singleton tctx_hasty_val' //.
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
