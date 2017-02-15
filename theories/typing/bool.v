From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section bool.
  Context `{typeG Σ}.

  Program Definition bool : type :=
    {| st_own tid vl :=
         match vl return _ with
         | [ #(LitInt (0|1))] => True
         | _ => False
         end%I |}.
  Next Obligation. intros ? [|[[| |[|[]|]]|] []]; auto. Qed.
  Next Obligation. intros ? [|[[| |[|[]|]]|] []]; apply _. Qed.

  Global Instance bool_send : Send bool.
  Proof. done. Qed.
End bool.

Section typing.
  Context `{typeG Σ}.

  Lemma type_bool_instr (b : Datatypes.bool) E L :
    typed_instruction_ty E L [] #b bool.
  Proof.
    iAlways. iIntros (tid qE) "_ $ $ $ _". wp_value.
    rewrite tctx_interp_singleton tctx_hasty_val. by destruct b.
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
    iIntros (Hp He1 He2) "!#". iIntros (tid qE) "#LFT Htl HE HL HC HT".
    iDestruct (big_sepL_elem_of _ _ _ Hp with "HT") as "#Hp".
    wp_bind p. iApply (wp_hasty with "Hp").
    iIntros ([[| |[|[]|]]|]) "_ H1"; try done; (iApply wp_case; [done..|iNext]).
    - iApply (He2 with "LFT Htl HE HL HC HT").
    - iApply (He1 with "LFT Htl HE HL HC HT").
  Qed.
End typing.
