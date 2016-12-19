From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import notation.
From lrust.lifetime Require Import definitions.
From lrust.typing Require Import type lft_contexts.

Definition path := expr.
Bind Scope expr_scope with path.

Section type_context.
  Context `{typeG Σ}.

  Fixpoint eval_path (p : path) : option val :=
    match p with
    | BinOp OffsetOp e (Lit (LitInt n)) =>
      match eval_path e with
      | Some (#(LitLoc l)) => Some (#(shift_loc l n))
      | _ => None
      end
    | e => to_val e
    end.

  (* TODO: Consider mking this a pair of a path and the rest. We could
     then e.g. formulate tctx_elt_hasty_path more generally. *)
  Inductive tctx_elt : Type :=
  | TCtx_hasty (p : path) (ty : type)
  | TCtx_blocked (p : path) (κ : lft) (ty : type).
  Definition tctx := list tctx_elt.

  Definition tctx_elt_interp (tid : thread_id) (x : tctx_elt) : iProp Σ :=
    match x with
    | TCtx_hasty p ty => ∃ v, ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) tid [v]
    | TCtx_blocked p κ ty => ∃ v, ⌜eval_path p = Some v⌝ ∗
                             ([†κ] ={⊤}=∗ ▷ ty.(ty_own) tid [v])
    end%I.
  (* Block tctx_elt_interp from reducing with simpl when x is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.
  Definition tctx_interp (tid : thread_id) (T : tctx) : iProp Σ :=
    ([∗ list] x ∈ T, tctx_elt_interp tid x)%I.

  Global Instance tctx_interp_permut tid:
    Proper ((≡ₚ) ==> (⊣⊢)) (tctx_interp tid).
  Proof. intros ???. by apply big_opL_permutation. Qed.

  Lemma tctx_interp_cons tid x T :
    tctx_interp tid (x :: T) ≡ (tctx_elt_interp tid x ∗ tctx_interp tid T)%I.
  Proof. rewrite /tctx_interp big_sepL_cons //. Qed.

  Lemma tctx_interp_app tid T1 T2 :
    tctx_interp tid (T1 ++ T2) ≡ (tctx_interp tid T1 ∗ tctx_interp tid T2)%I.
  Proof. rewrite /tctx_interp big_sepL_app //. Qed.

  Definition tctx_interp_nil tid :
    tctx_interp tid [] = True%I := eq_refl _.

  Lemma tctx_interp_singleton tid x :
    tctx_interp tid [x] ≡ tctx_elt_interp tid x.
  Proof. rewrite tctx_interp_cons tctx_interp_nil right_id //. Qed.

  Class CopyC (T : tctx) := {
    copyc_persistent tid : PersistentP (tctx_interp tid T);
  }.
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy : CopyC [].
  Proof. split. apply _. Qed.

  Global Instance tctx_ty_copy T p ty :
    CopyC T → Copy ty → CopyC (TCtx_hasty p ty :: T).
  Proof.
    (* TODO RJ: Should we have instances that PersistentP respects equiv? *)
    intros ??. split=>?. rewrite /PersistentP tctx_interp_cons.
    apply uPred.sep_persistent; by apply _.
  Qed.

  Definition tctx_incl (E : elctx) (L : llctx) (T1 T2 : tctx): Prop :=
    ∀ tid q1 q2, lft_ctx -∗ elctx_interp E q1 -∗ llctx_interp L q2 -∗
              tctx_interp tid T1 ={⊤}=∗ elctx_interp E q1 ∗ llctx_interp L q2 ∗
                                     tctx_interp tid T2.

  Global Instance tctx_incl_preorder E L : PreOrder (tctx_incl E L).
  Proof.
    split.
    - by iIntros (????) "_ $ $ $".
    - iIntros (??? H1 H2 ???) "#LFT HE HL H".
      iMod (H1 with "LFT HE HL H") as "(HE & HL & H)".
      by iMod (H2 with "LFT HE HL H") as "($ & $ & $)".
  Qed.

  Lemma tctx_elt_interp_hasty_path p1 p2 ty tid :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (TCtx_hasty p1 ty) ≡
    tctx_elt_interp tid (TCtx_hasty p2 ty).
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma wp_eval_path p v :
    eval_path p = Some v → (WP p {{ v', ⌜v' = v⌝ }})%I.
  Proof.
    revert v; induction p; intros v; cbn -[to_val];
      try (intros ?; by iApply wp_value); [].
    destruct op; try discriminate; [].
    destruct p2; try (intros ?; by iApply wp_value); [].
    destruct l; try (intros ?; by iApply wp_value); [].
    destruct (eval_path p1); try (intros ?; by iApply wp_value); [].
    destruct v0; try discriminate; [].
    destruct l; try discriminate; [].
    intros [=<-]. iStartProof. wp_bind p1.
    iApply (wp_wand with "[]").
    { iApply IHp1. done. }
    iIntros (v) "%". subst v. wp_op. done.
  Qed.

  Lemma wp_hasty tid p ty Φ :
    tctx_elt_interp tid (TCtx_hasty p ty) -∗
    (∀ v, ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) tid [v] -∗ Φ v) -∗
    WP p {{ Φ }}.
  Proof.
    iIntros "Hty HΦ". iDestruct "Hty" as (v) "[% Hown]".
    iApply (wp_wand with "[]").
    { iApply wp_eval_path. done. }
    iIntros (v') "%". subst v'. iApply "HΦ". by auto.
  Qed.

  Lemma contains_tctx_incl E L T1 T2 : T1 `contains` T2 → tctx_incl E L T2 T1.
  Proof.
    rewrite /tctx_incl. iIntros (Hc ???) "_ $ $ H". by iApply big_sepL_contains.
  Qed.

  Lemma tctx_incl_frame E L T T1 T2 :
    tctx_incl E L T2 T1 → tctx_incl E L (T++T2) (T++T1).
  Proof.
    intros Hincl ???. rewrite /tctx_interp !big_sepL_app. iIntros "#LFT HE HL [$ ?]".
    by iApply (Hincl with "LFT HE HL").
  Qed.

  Lemma copy_tctx_incl E L T `{!CopyC T} :
    tctx_incl E L T (T ++ T).
  Proof.
    iIntros (???) "_ $ $ * #?". rewrite tctx_interp_app. by iSplitL.
  Qed.

  Lemma subtype_tctx_incl E L p ty1 ty2 :
    subtype E L ty1 ty2 → tctx_incl E L [TCtx_hasty p ty1] [TCtx_hasty p ty2].
  Proof.
    iIntros (Hst ???) "#LFT HE HL H". rewrite /tctx_interp !big_sepL_singleton /=.
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'".
    iFrame "HE HL". iDestruct "H" as (v) "[% H]". iExists _. iFrame "%".
    iDestruct (Hst with "* [] [] []") as "(_ & #Ho & _)"; [done..|].
    iApply ("Ho" with "*"). done.
  Qed.

  Definition deguard_tctx_elt κ x :=
    match x with
    | TCtx_blocked p κ' ty =>
      if decide (κ = κ') then TCtx_hasty p ty else x
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
