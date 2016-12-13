From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import notation.
From lrust.lifetime Require Import definitions.
From lrust.typing Require Import type lft_contexts type_context.

Section cont_context.
  Context `{typeG Σ}.

  Definition cont_postcondition : iProp Σ := False%I.

  Record cctx_elt : Type :=
    CctxElt { cctxe_k : val; cctxe_L : llctx;
              cctxe_n : nat; cctxe_T : vec val cctxe_n → tctx }.
  Definition cctx := list cctx_elt.

  Definition cctx_elt_interp (tid : thread_id) (x : cctx_elt) : iProp Σ :=
    let 'CctxElt k L n T := x in
    (∀ args, llctx_interp L 1 -∗ tctx_interp tid (T args) -∗
         WP k (of_val <$> (args : list _)) {{ _, cont_postcondition }})%I.
  Definition cctx_interp (tid : thread_id) (C : cctx) : iProp Σ :=
    (∀ (x : cctx_elt), ⌜x ∈ C⌝ -∗ cctx_elt_interp tid x)%I.

  Global Instance cctx_interp_permut tid:
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid).
  Proof. solve_proper. Qed.

  Lemma fupd_cctx_interp tid C :
    (|={⊤}=> cctx_interp tid C) -∗ cctx_interp tid C.
  Proof.
    rewrite /cctx_interp. iIntros "H". iIntros ([k L n T]) "%".
    iIntros (args) "HL HT". iMod "H".
    by iApply ("H" $! (CctxElt k L n T) with "[%] * HL HT").
  Qed.

  Definition cctx_incl (E : elctx) (C1 C2 : cctx): Prop :=
    ∀ tid, lft_ctx -∗ elctx_interp_0 E -∗
               cctx_interp tid C1 -∗ cctx_interp tid C2.

  Global Instance cctx_incl_preorder E : PreOrder (cctx_incl E).
  Proof.
    split.
    - iIntros (??) "_ _ $".
    - iIntros (??? H1 H2 ?) "#LFT #HE H".
      iApply (H2 with "LFT HE"). by iApply (H1 with "LFT HE").
  Qed.

  Lemma incl_cctx_incl E C1 C2 : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    rewrite /cctx_incl /cctx_interp. iIntros (HC1C2 tid) "_ _ H * %".
    iApply ("H" with "* [%]"). by apply HC1C2.
  Qed.

  Lemma cctx_incl_cons E k L n T1 T2 C1 C2:
    cctx_incl E C1 C2 → (∀ args, tctx_incl E L (T2 args) (T1 args)) →
    cctx_incl E (CctxElt k L n T1 :: C1) (CctxElt k L n T2 :: C2).
  Proof.
    iIntros (HC1C2 HT1T2 ?) "#LFT #HE H". rewrite /cctx_interp.
    iIntros (x) "Hin". iDestruct "Hin" as %[->|Hin]%elem_of_cons.
    - iIntros (args) "HL' HT".
      iDestruct (llctx_interp_persist with "HL'") as "#HL".
      iMod (HT1T2 with "LFT HE HL HT") as "HT".
      iApply ("H" $! (CctxElt _ _ _ _) with "[%] * HL' HT").
        by apply elem_of_cons; auto.
    - iApply (HC1C2 with "LFT HE [H] * [%]"); last done.
      iIntros (x') "%". iApply ("H" with "[%]"). by apply elem_of_cons; auto.
  Qed.
End cont_context.
