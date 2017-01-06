From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import notation.
From lrust.typing Require Import type lft_contexts type_context.
Set Default Proof Using "Type".

Section cont_context_def.
  Context `{typeG Σ}.

  Definition cont_postcondition : iProp Σ := True%I.

  Record cctx_elt : Type :=
    CCtx_iscont { cctxe_k : val; cctxe_L : llctx;
                  cctxe_n : nat; cctxe_T : vec val cctxe_n → tctx }.
End cont_context_def.
Add Printing Constructor cctx_elt.

Notation cctx := (list cctx_elt).

Delimit Scope lrust_cctx_scope with CC.
Bind Scope lrust_cctx_scope with cctx_elt.

Notation "k ◁cont( L , T )" := (CCtx_iscont k L _ T%TC)
  (at level 70, format "k  ◁cont( L ,  T )") : lrust_cctx_scope.
Notation "a :: b" := (@cons cctx_elt a%CC b%CC)
  (at level 60, right associativity) : lrust_cctx_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons cctx_elt x1%CC (@cons cctx_elt x2%CC
        (..(@cons cctx_elt xn%CC (@nil cctx_elt))..))) : lrust_cctx_scope.
Notation "[ x ]" := (@cons cctx_elt x%CC (@nil cctx_elt)) : lrust_cctx_scope.

Section cont_context.
  Context `{typeG Σ}.

  Definition cctx_elt_interp (tid : thread_id) (x : cctx_elt) : iProp Σ :=
    let '(k ◁cont(L, T))%CC := x in
    (∀ args, na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid (T args) -∗
         WP k (of_val <$> (args : list _)) {{ _, cont_postcondition }})%I.
  Definition cctx_interp (tid : thread_id) (C : cctx) : iProp Σ :=
    (∀ (x : cctx_elt), ⌜x ∈ C⌝ -∗ cctx_elt_interp tid x)%I.
  Global Arguments cctx_interp _ _%CC.

  Global Instance cctx_interp_permut tid:
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid).
  Proof. solve_proper. Qed.

  Lemma cctx_interp_cons tid x T :
    cctx_interp tid (x :: T) ≡ (cctx_elt_interp tid x ∧ cctx_interp tid T)%I.
  Proof.
    iSplit.
    - iIntros "H". iSplit; [|iIntros (??)]; iApply "H"; rewrite elem_of_cons; auto.
    - iIntros "H". iIntros (? Hin). revert Hin. rewrite elem_of_cons=>-[->|?].
      + by iDestruct "H" as "[H _]".
      + iDestruct "H" as "[_ H]". by iApply "H".
  Qed.

  Lemma cctx_interp_nil tid : cctx_interp tid [] ≡ True%I.
  Proof. iSplit; first by auto. iIntros "_". iIntros (? Hin). inversion Hin. Qed.

  Lemma cctx_interp_app tid T1 T2 :
    cctx_interp tid (T1 ++ T2) ≡ (cctx_interp tid T1 ∧ cctx_interp tid T2)%I.
  Proof.
    induction T1 as [|?? IH]; first by rewrite /= cctx_interp_nil left_id.
    by rewrite /= !cctx_interp_cons IH assoc.
  Qed.

  Lemma cctx_interp_singleton tid x :
    cctx_interp tid [x] ≡ cctx_elt_interp tid x.
  Proof. rewrite cctx_interp_cons cctx_interp_nil right_id //. Qed.

  Lemma fupd_cctx_interp tid C :
    (|={⊤}=> cctx_interp tid C) -∗ cctx_interp tid C.
  Proof.
    rewrite /cctx_interp. iIntros "H". iIntros ([k L n T]) "%".
    iIntros (args) "HL HT". iMod "H".
    by iApply ("H" $! (k ◁cont(L, T)%CC) with "[%] * HL HT").
  Qed.

  Definition cctx_incl (E : elctx) (C1 C2 : cctx): Prop :=
    ∀ tid q, lft_ctx -∗ (elctx_interp E q -∗ cctx_interp tid C1) -∗
                       (elctx_interp E q -∗ cctx_interp tid C2).
  Global Arguments cctx_incl _%EL _%CC _%CC.

  Global Instance cctx_incl_preorder E : PreOrder (cctx_incl E).
  Proof.
    split.
    - iIntros (???) "_ $".
    - iIntros (??? H1 H2 ??) "#LFT HE".
      iApply (H2 with "LFT"). by iApply (H1 with "LFT").
  Qed.

  Lemma incl_cctx_incl E C1 C2 : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    rewrite /cctx_incl /cctx_interp. iIntros (HC1C2 tid ?) "_ H HE * %".
    iApply ("H" with "HE * [%]"). by apply HC1C2.
  Qed.

  Lemma cctx_incl_cons_match E k L n (T1 T2 : vec val n → tctx) C1 C2 :
    cctx_incl E C1 C2 → (∀ args, tctx_incl E L (T2 args) (T1 args)) →
    cctx_incl E (k ◁cont(L, T1) :: C1) (k ◁cont(L, T2) :: C2).
  Proof.
    iIntros (HC1C2 HT1T2 ??) "#LFT H HE". rewrite /cctx_interp.
    iIntros (x) "Hin". iDestruct "Hin" as %[->|Hin]%elem_of_cons.
    - iIntros (args) "Htl HL HT".
      iMod (HT1T2 with "LFT HE HL HT") as "(HE & HL & HT)".
      iSpecialize ("H" with "HE").
      iApply ("H" $! (_ ◁cont(_, _))%CC with "[%] * Htl HL HT").
      constructor.
    - iApply (HC1C2 with "LFT [H] HE * [%]"); last done.
      iIntros "HE". iIntros (x') "%".
      iApply ("H" with "HE * [%]"). by apply elem_of_cons; auto.
  Qed.

  Lemma cctx_incl_nil E C : cctx_incl E C [].
  Proof. apply incl_cctx_incl. by set_unfold. Qed.

  Lemma cctx_incl_cons E k L n (T1 T2 : vec val n → tctx) C1 C2 :
    (k ◁cont(L, T1))%CC ∈ C1 →
    (∀ args, tctx_incl E L (T2 args) (T1 args)) →
    cctx_incl E C1 C2 →
    cctx_incl E C1 (k ◁cont(L, T2) :: C2).
  Proof.
    intros Hin ??. rewrite <-cctx_incl_cons_match; try done.
    iIntros (??) "_ HC HE". iSpecialize ("HC" with "HE").
    rewrite cctx_interp_cons. iSplit; last done. clear -Hin.
    iInduction Hin as [] "IH"; rewrite cctx_interp_cons;
      [iDestruct "HC" as "[$ _]" | iApply "IH"; iDestruct "HC" as "[_ $]"].
  Qed.
End cont_context.

Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
