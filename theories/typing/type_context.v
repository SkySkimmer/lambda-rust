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

  Lemma eval_path_of_val (v : val) :
    eval_path v = Some v.
  Proof. destruct v. done. simpl. rewrite (decide_left _). done. Qed.

  Lemma wp_eval_path E p v :
    eval_path p = Some v → (WP p @ E {{ v', ⌜v' = v⌝ }})%I.
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

  (** Type context element *)
  (* TODO: Consider mking this a pair of a path and the rest. We could
     then e.g. formulate tctx_elt_hasty_path more generally. *)
  Inductive tctx_elt : Type :=
  | TCtx_hasty (p : path) (ty : type)
  | TCtx_blocked (p : path) (κ : lft) (ty : type).

  Definition tctx_elt_interp (tid : thread_id) (x : tctx_elt) : iProp Σ :=
    match x with
    | TCtx_hasty p ty => ∃ v, ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) tid [v]
    | TCtx_blocked p κ ty => ∃ v, ⌜eval_path p = Some v⌝ ∗
                             ([†κ] ={⊤}=∗ ty.(ty_own) tid [v])
    end%I.
  (* Block tctx_elt_interp from reducing with simpl when x is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

  Lemma tctx_hasty_val tid (v : val) ty :
    tctx_elt_interp tid (TCtx_hasty v ty) ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (?) "[EQ ?]".
      iDestruct "EQ" as %[=->]. done.
    - iIntros "?". iExists _. auto.
  Qed.

  Lemma tctx_elt_interp_hasty_path p1 p2 ty tid :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (TCtx_hasty p1 ty) ≡
    tctx_elt_interp tid (TCtx_hasty p2 ty).
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma tctx_hasty_val' tid p (v : val) ty :
    eval_path p = Some v →
    tctx_elt_interp tid (TCtx_hasty p ty) ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    intros ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    rewrite eval_path_of_val. done.
  Qed.

  Lemma wp_hasty E tid p ty Φ :
    tctx_elt_interp tid (TCtx_hasty p ty) -∗
    (∀ v, ⌜eval_path p = Some v⌝ -∗ ty.(ty_own) tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "Hty HΦ". iDestruct "Hty" as (v) "[% Hown]".
    iApply (wp_wand with "[]"). { iApply wp_eval_path. done. }
    iIntros (v') "%". subst v'. iApply ("HΦ" with "* [] Hown"). by auto.
  Qed.

  (** Type context *)
  Definition tctx := list tctx_elt.

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

  (** Copy typing contexts *)
  Class CopyC (T : tctx) :=
    copyc_persistent tid : PersistentP (tctx_interp tid T).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy : CopyC [].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_ty_copy T p ty :
    CopyC T → Copy ty → CopyC (TCtx_hasty p ty :: T).
  Proof.
    (* TODO RJ: Should we have instances that PersistentP respects equiv? *)
    intros ???. rewrite /PersistentP tctx_interp_cons.
    apply uPred.sep_persistent; by apply _.
  Qed.

  (** Send typing contexts *)
  Class SendC (T : tctx) :=
    sendc_change_tid tid1 tid2 : tctx_interp tid1 T -∗ tctx_interp tid2 T.

  Global Instance tctx_nil_send : SendC [].
  Proof. done. Qed.

  Global Instance tctx_ty_send T p ty :
    SendC T → Send ty → SendC (TCtx_hasty p ty :: T).
  Proof.
    iIntros (HT Hty ??). rewrite !tctx_interp_cons.
    iIntros "[Hty HT]". iSplitR "HT".
    - iDestruct "Hty" as (?) "[% Hty]". iExists _. iSplit; first done.
      by iApply Hty.
    - by iApply HT.
  Qed.

  (** Type context inclusion *)
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

  Lemma copy_tctx_incl E L p `{!Copy ty} :
    tctx_incl E L [TCtx_hasty p ty] [TCtx_hasty p ty; TCtx_hasty p ty].
   Proof.
    iIntros (???) "_ $ $ *". rewrite /tctx_interp !big_sepL_cons big_sepL_nil.
    by iIntros "[#$ $]".
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

  Class UnblockTctx (κ : lft) (T1 T2 : tctx) : Prop :=
    unblock_tctx : ∀ tid, [†κ] -∗ tctx_interp tid T1 ={⊤}=∗ tctx_interp tid T2.

  Global Instance unblock_tctx_nil κ : UnblockTctx κ [] [].
  Proof. by iIntros (tid) "_ $". Qed.

  Global Instance unblock_tctx_cons_unblock T1 T2 p κ ty :
    UnblockTctx κ T1 T2 →
    UnblockTctx κ (TCtx_blocked p κ ty::T1) (TCtx_hasty p ty::T2).
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[H HT1]".
    iMod (H12 with "H† HT1") as "$". iDestruct "H" as (v) "[% H]".
    iExists (v). by iMod ("H" with "H†") as "$".
  Qed.

  Global Instance unblock_tctx_cons κ T1 T2 x :
    UnblockTctx κ T1 T2 → UnblockTctx κ (x::T1) (x::T2) | 100.
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[$ HT1]".
    by iMod (H12 with "H† HT1") as "$".
  Qed.
End type_context.
