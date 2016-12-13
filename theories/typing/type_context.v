From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import notation.
From lrust.lifetime Require Import definitions.
From lrust.typing Require Import type lft_contexts.

Section type_context.
  Context `{typeG Σ}.

  Definition path := expr.

  Fixpoint eval_path (ν : path) : option val :=
    match ν with
    | BinOp OffsetOp e (Lit (LitInt n)) =>
      match eval_path e with
      | Some (#(LitLoc l)) => Some (#(shift_loc l n))
      | _ => None
      end
    | e => to_val e
    end.

  Inductive tctx_elt : Type :=
  | TCtx_holds (p : path) (ty : type)
  | TCtx_guarded (p : path) (κ : lft) (ty : type).
  Definition tctx := list tctx_elt.

  Definition tctx_elt_interp (tid : thread_id) (x : tctx_elt) : iProp Σ :=
    match x with
    | TCtx_holds p ty => ∃ v, ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) tid [v]
    | TCtx_guarded p κ ty => ∃ v, ⌜eval_path p = Some v⌝ ∗
                             ([†κ] ={⊤}=∗ ▷ ty.(ty_own) tid [v])
    end%I.
  Definition tctx_interp (tid : thread_id) (T : tctx) : iProp Σ :=
    ([∗ list] x ∈ T, tctx_elt_interp tid x)%I.

  Global Instance tctx_interp_permut tid:
    Proper ((≡ₚ) ==> (⊣⊢)) (tctx_interp tid).
  Proof. intros ???. by apply big_opL_permutation. Qed.

  Definition tctx_incl (E : elctx) (L : llctx) (T1 T2 : tctx): Prop :=
    ∀ tid, lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
              tctx_interp tid T1 ={⊤}=∗ tctx_interp tid T2.

  Global Instance tctx_incl_preorder E L : PreOrder (tctx_incl E L).
  Proof.
    split.
    - by iIntros (??) "_ _ _ $".
    - iIntros (??? H1 H2 ?) "#LFT #HE #HL H".
      iApply (H2 with "LFT HE HL >"). by iApply (H1 with "LFT HE HL").
  Qed.

  Lemma contains_tctx_incl E L T1 T2 : T1 `contains` T2 → tctx_incl E L T2 T1.
  Proof.
    rewrite /tctx_incl. iIntros (Hc ?) "_ _ _ H". by iApply big_sepL_contains.
  Qed.

  Lemma tctx_incl_frame E L T T1 T2 :
    tctx_incl E L T2 T1 → tctx_incl E L (T++T2) (T++T1).
  Proof.
    intros Hincl ?. rewrite /tctx_interp !big_sepL_app. iIntros "#LFT #HE #HL [$ ?]".
    by iApply (Hincl with "LFT HE HL").
  Qed.

  Lemma copy_tctx_incl E L p `(!Copy ty) :
    tctx_incl E L [TCtx_holds p ty] [TCtx_holds p ty; TCtx_holds p ty].
  Proof.
    iIntros (?) "_ _ _ *". rewrite /tctx_interp !big_sepL_cons big_sepL_nil.
    by iIntros "[#$ $]".
  Qed.

  Lemma subtype_tctx_incl E L p ty1 ty2 :
    subtype E L ty1 ty2 → tctx_incl E L [TCtx_holds p ty1] [TCtx_holds p ty2].
  Proof.
    iIntros (Hst ?) "#LFT #HE #HL H". rewrite /tctx_interp !big_sepL_singleton /=.
    iDestruct "H" as (v) "[% H]". iExists _. iFrame "%".
    by iApply (Hst.(subtype_own _ _ _ _) with "LFT HE HL").
  Qed.

  Definition deguard_tctx_elt κ x :=
    match x with
    | TCtx_guarded p κ' ty =>
      if decide (κ = κ') then TCtx_holds p ty else x
    | _ => x
    end.

  Lemma deguard_tctx_elt_interp tid κ x :
    [†κ] -∗ tctx_elt_interp tid x ={⊤}=∗
        ▷ tctx_elt_interp tid (deguard_tctx_elt κ x).
  Proof.
    iIntros "H† H". destruct x as [|? κ' ?]; simpl. by auto.
    destruct (decide (κ = κ')) as [->|]; simpl; last by auto.
    iDestruct "H" as (v) "[% H]". iExists v. iSplitR. by auto.
    by iApply ("H" with "H†").
  Qed.

  Definition deguard_tctx κ (T : tctx) : tctx :=
    deguard_tctx_elt κ <$> T.

  Lemma deguard_tctx_interp tid κ T :
    [†κ] -∗ tctx_interp tid T ={⊤}=∗
        ▷ tctx_interp tid (deguard_tctx κ T).
  Proof.
    iIntros "#H† H". rewrite /tctx_interp big_sepL_fmap.
    iApply (big_opL_forall (λ P Q, [†κ] -∗ P ={⊤}=∗ ▷ Q) with "H† H").
    { by iIntros (?) "_ $". }
    { iIntros (?? A ?? B) "#H† [H1 H2]". iSplitL "H1".
        by iApply (A with "H†"). by iApply (B with "H†"). }
    move=>/= _ ? _. by apply deguard_tctx_elt_interp.
  Qed.
End type_context.
