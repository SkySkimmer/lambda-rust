From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section bool.
  Context `{typeG Σ}.

  Program Definition bool : type :=
    {| st_own tid vl := (∃ z:bool, ⌜vl = [ #z ]⌝)%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Global Instance bool_send : Send bool.
  Proof. iIntros (tid1 tid2 vl). done. Qed.
End bool.

Section typing.
  Context `{typeG Σ}.

  Lemma type_bool_instr (b : Datatypes.bool) E L :
    typed_instruction_ty E L [] #b bool.
  Proof.
    iAlways. iIntros (tid qE) "_ _ $ $ $ _". wp_value.
    rewrite tctx_interp_singleton tctx_hasty_val. iExists _. done.
  Qed.

  Lemma type_bool (b : Datatypes.bool) E L C T x e :
    Closed (x :b: []) e →
    (∀ (v : val), typed_body E L C ((v ◁ bool) :: T) (subst' x v e)) →
    typed_body E L C T (let: x := #b in e).
  Proof.
    intros. eapply type_let; [done|apply type_bool_instr|solve_typing|done].
  Qed.

  Lemma type_if E L C T e1 e2 p:
    (p ◁ bool)%TC ∈ T →
    typed_body E L C T e1 → typed_body E L C T e2 →
    typed_body E L C T (if: p then e1 else e2).
  Proof.
    iIntros (Hp He1 He2) "!#". iIntros (tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iDestruct (big_sepL_elem_of _ _ _ Hp with "HT") as "#Hp".
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (b) "Hv". iDestruct "Hv" as %[=->].
    destruct b; wp_if.
    - iApply (He1 with "HEAP LFT Htl HE HL HC HT").
    - iApply (He2 with "HEAP LFT Htl HE HL HC HT").
  Qed.
End typing.
