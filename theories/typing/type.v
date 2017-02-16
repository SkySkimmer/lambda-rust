From iris.base_logic.lib Require Export na_invariants.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export proofmode notation.
From lrust.lifetime Require Export frac_borrow.
From lrust.typing Require Import lft_contexts.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_heapG :> lrustG Σ;
  type_lftG :> lftG Σ;
  type_na_invG :> na_invG Σ;
  type_frac_borrowG :> frac_borG Σ
}.

Definition lftE := ↑lftN.
Definition lrustN := nroot .@ "lrust".
Definition shrN  := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

Record type `{typeG Σ} :=
  { ty_size : nat;
    ty_own : thread_id → list val → iProp Σ;
    ty_shr : lft → thread_id → loc → iProp Σ;

    ty_shr_persistent κ tid l : PersistentP (ty_shr κ tid l);

    ty_size_eq tid vl : ty_own tid vl -∗ ⌜length vl = ty_size⌝;
    (* The mask for starting the sharing does /not/ include the
       namespace N, for allowing more flexibility for the user of
       this type (typically for the [own] type). AFAIK, there is no
       fundamental reason for this.
       This should not be harmful, since sharing typically creates
       invariants, which does not need the mask.  Moreover, it is
       more consistent with thread-local tokens, which we do not
       give any.

       The lifetime token is needed (a) to make the definition of simple types
       nicer (they would otherwise require a "∨ □|=>[†κ]"), and (b) so that
       we can have emp == sum [].
     *)
    ty_share E κ l tid q : lftE ⊆ E →
      lft_ctx -∗ &{κ} (l ↦∗: ty_own tid) -∗ q.[κ] ={E}=∗
      ty_shr κ tid l ∗ q.[κ];
    ty_shr_mono κ κ' tid l :
      lft_ctx -∗ κ' ⊑ κ -∗ ty_shr κ tid l -∗ ty_shr κ' tid l
  }.
Existing Instance ty_shr_persistent.
Instance: Params (@ty_size) 2.
Instance: Params (@ty_own) 2.
Instance: Params (@ty_shr) 2.

Record simple_type `{typeG Σ} :=
  { st_own : thread_id → list val → iProp Σ;
    st_size_eq tid vl : st_own tid vl -∗ ⌜length vl = 1%nat⌝;
    st_own_persistent tid vl : PersistentP (st_own tid vl) }.
Existing Instance st_own_persistent.
Instance: Params (@st_own) 2.

Section type.
  Context `{typeG Σ}.

  (** Copy types *)
  Fixpoint shr_locsE (l : loc) (n : nat) : coPset :=
    match n with
    | 0%nat => ∅
    | S n => ↑shrN.@l ∪ shr_locsE (shift_loc l 1%nat) n
    end.

  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (shift_loc l n) m.
  Proof.
    revert l; induction n; intros l.
    - rewrite shift_loc_0. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /= IHn shift_loc_assoc.
      set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m :
    shr_locsE l n ⊥ shr_locsE (shift_loc l n) m.
  Proof.
    revert l; induction n; intros l.
    - simpl. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /=.
      apply disjoint_union_l. split; last (rewrite -shift_loc_assoc; exact: IHn).
      clear IHn. revert n; induction m; intros n; simpl; first set_solver+.
      rewrite shift_loc_assoc. apply disjoint_union_r. split.
      + apply ndot_ne_disjoint. destruct l. intros [=]. omega.
      + rewrite -Z.add_assoc. move:(IHm (n + 1)%nat). rewrite Nat2Z.inj_add //.
  Qed.

  Lemma shr_locsE_shrN l n :
    shr_locsE l n ⊆ ↑shrN.
  Proof.
    revert l; induction n=>l /=; first by set_solver+.
    apply union_least; last by auto. solve_ndisj.
  Qed.

  Lemma shr_locsE_subseteq l n m :
    (n ≤ m)%nat → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done. etrans; first done.
    rewrite -Nat.add_1_l [(_ + _)%nat]comm_L shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
      na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (shift_loc l n) m).
  Proof.
    rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj.
  Qed.

  Class Copy (t : type) := {
    copy_persistent tid vl : PersistentP (t.(ty_own) tid vl);
    copy_shr_acc κ tid E F l q :
      lftE ∪ ↑shrN ⊆ E → shr_locsE l (t.(ty_size) + 1) ⊆ F →
      lft_ctx -∗ t.(ty_shr) κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗
         ∃ q', na_own tid (F ∖ shr_locsE l t.(ty_size)) ∗
           ▷(l ↦∗{q'}: t.(ty_own) tid) ∗
        (na_own tid (F ∖ shr_locsE l t.(ty_size)) -∗ ▷l ↦∗{q'}: t.(ty_own) tid
                                    ={E}=∗ na_own tid F ∗ q.[κ])
  }.
  Global Existing Instances copy_persistent.

  Class LstCopy (tys : list type) := lst_copy : Forall Copy tys.
  Global Instance lst_copy_nil : LstCopy [] := List.Forall_nil _.
  Global Instance lst_copy_cons ty tys :
    Copy ty → LstCopy tys → LstCopy (ty::tys) := List.Forall_cons _ _ _.

  (** Send and Sync types *)
  Class Send (t : type) :=
    send_change_tid tid1 tid2 vl : t.(ty_own) tid1 vl -∗ t.(ty_own) tid2 vl.

  Class LstSend (tys : list type) := lst_send : Forall Send tys.
  Global Instance lst_send_nil : LstSend [] := List.Forall_nil _.
  Global Instance lst_send_cons ty tys :
    Send ty → LstSend tys → LstSend (ty::tys) := List.Forall_cons _ _ _.

  Class Sync (t : type) :=
    sync_change_tid κ tid1 tid2 l : t.(ty_shr) κ tid1 l -∗ t.(ty_shr) κ tid2 l.

  Class LstSync (tys : list type) := lst_sync : Forall Sync tys.
  Global Instance lst_sync_nil : LstSync [] := List.Forall_nil _.
  Global Instance lst_sync_cons ty tys :
    Sync ty → LstSync tys → LstSync (ty::tys) := List.Forall_cons _ _ _.

  (** Simple types *)
  Program Definition ty_of_st (st : simple_type) : type :=
    {| ty_size := 1; ty_own := st.(st_own);

       (* [st.(st_own) tid vl] needs to be outside of the fractured
          borrow, otherwise I do not know how to prove the shr part of
          [subtype_shr_mono]. *)
       ty_shr := λ κ tid l,
                 (∃ vl, (&frac{κ} λ q, l ↦∗{q} vl) ∗
                        ▷ st.(st_own) tid vl)%I
    |}.
  Next Obligation. intros. apply st_size_eq. Qed.
  Next Obligation.
    iIntros (st E κ l tid ??) "#LFT Hmt Hκ".
    iMod (bor_exists with "LFT Hmt") as (vl) "Hmt". set_solver.
    iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]". set_solver.
    iMod (bor_persistent with "LFT Hown") as "[Hown|#H†]". set_solver.
    - iFrame "Hκ".
      iMod (bor_fracture with "LFT [Hmt]") as "Hfrac"; by eauto with iFrame.
    - iExFalso. by iApply (lft_tok_dead with "Hκ").
  Qed.
  Next Obligation.
    intros st κ κ' tid l. iIntros "#LFT #Hord H".
    iDestruct "H" as (vl) "[#Hf #Hown]".
    iExists vl. iFrame "Hown". by iApply (frac_bor_shorten with "Hord").
  Qed.

  Global Program Instance ty_of_st_copy st : Copy (ty_of_st st).
  Next Obligation.
    iIntros (st κ tid E ? l q ? HF) "#LFT #Hshr Htok Hlft".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first set_solver+.
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first set_solver.
    iModIntro. iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iSplitL "Hmt1"; first by auto with iFrame.
    iIntros "Htok2 Hmt1". iDestruct "Hmt1" as (vl') "[Hmt1 #Hown']".
    iDestruct ("Htok" with "Htok2") as "$".
    iAssert (▷ ⌜length vl = length vl'⌝)%I as ">%".
    { iNext. iDestruct (st_size_eq with "Hown") as %->.
      iDestruct (st_size_eq with "Hown'") as %->. done. }
    iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op // Qp_div_2.
    iDestruct "Hmt" as "[>% Hmt]". subst. by iApply "Hclose".
  Qed.

  Global Instance ty_of_st_sync st :
    Send (ty_of_st st) → Sync (ty_of_st st).
  Proof.
    iIntros (Hsend κ tid1 tid2 l). iDestruct 1 as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply Hsend.
  Qed.
End type.

Coercion ty_of_st : simple_type >-> type.

Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(* OFE and COFE structures on types and simple types. *)
Section ofe.
  Context `{typeG Σ}.

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      ty1.(ty_size) = ty2.(ty_size) →
      (∀ tid vs, ty1.(ty_own) tid vs ≡ ty2.(ty_own) tid vs) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡ ty2.(ty_shr) κ tid l) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv type := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist :
      ty1.(ty_size) = ty2.(ty_size) →
      (∀ tid vs, dist_later n (ty1.(ty_own) tid vs) (ty2.(ty_own) tid vs)) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist type := type_dist'.

  Let T := prodC
    (prodC natC (thread_id -c> list val -c> laterC (iProp Σ)))
    (lft -c> thread_id -c> loc -c> iProp Σ).
  Let P (x : T) : Prop :=
    (∀ κ tid l, PersistentP (x.2 κ tid l)) ∧
    (∀ tid vl, (later_car (x.1.2 tid vl) : iProp Σ) -∗ ⌜length vl = x.1.1⌝) ∧
    (∀ E κ l tid q, lftE ⊆ E →
      lft_ctx -∗ &{κ} (l ↦∗: λ vs, later_car (x.1.2 tid vs)) -∗
      q.[κ] ={E}=∗ x.2 κ tid l ∗ q.[κ]) ∧
    (∀ κ κ' tid l, lft_ctx -∗ κ' ⊑ κ -∗ x.2 κ tid l -∗ x.2 κ' tid l).

  Definition type_unpack (ty : type) : T :=
    (ty.(ty_size), λ tid vl, Next (ty.(ty_own) tid vl), ty.(ty_shr)).
  Program Definition type_pack (x : T) (H : P x) : type :=
    {| ty_size := x.1.1; ty_own tid vl := later_car (x.1.2 tid vl); ty_shr := x.2 |}.
  Solve Obligations with by intros [[??] ?] (?&?&?&?).

  Definition type_ofe_mixin : OfeMixin type.
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - split; [by destruct 1|by intros [[??] ?]; constructor].
    - split; [by destruct 1|by intros [[??] ?]; constructor].
  Qed.
  Canonical Structure typeC : ofeT := OfeT type type_ofe_mixin.

  Global Instance ty_size_ne n : Proper (dist n ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_size_proper : Proper ((≡) ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_own_ne n:
    Proper (dist (S n) ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_ne n :
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper :
    Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.

  Global Instance type_cofe : Cofe typeC.
  Proof.
    apply: (iso_cofe_subtype P type_pack type_unpack).
    - split; [by destruct 1|by intros [[??] ?]; constructor].
    - by intros [].
    - intros ? c. rewrite /P /=. split_and!.
      + intros κ tid l. apply uPred.entails_equiv_and, equiv_dist=>n.
        setoid_rewrite conv_compl; simpl.
        apply equiv_dist, uPred.entails_equiv_and, ty_shr_persistent.
      + intros tid vl. apply uPred.entails_equiv_and, equiv_dist=>n.
        rewrite !conv_compl /=.
        apply equiv_dist, uPred.entails_equiv_and, ty_size_eq.
      + intros E κ l tid q ?. apply uPred.entails_equiv_and, equiv_dist=>n.
        setoid_rewrite conv_compl; simpl.
        rewrite -(c.(chain_cauchy) n (S n)); last lia.
        by apply equiv_dist, uPred.entails_equiv_and, ty_share.
      + intros κ κ' tid l. apply uPred.entails_equiv_and, equiv_dist=>n.
        setoid_rewrite conv_compl; simpl.
        apply equiv_dist, uPred.entails_equiv_and, ty_shr_mono.
  Qed.

  Inductive st_equiv' (ty1 ty2 : simple_type) : Prop :=
    St_equiv :
      (∀ tid vs, ty1.(ty_own) tid vs ≡ ty2.(ty_own) tid vs) →
      st_equiv' ty1 ty2.
  Instance st_equiv : Equiv simple_type := st_equiv'.
  Inductive st_dist' (n : nat) (ty1 ty2 : simple_type) : Prop :=
    St_dist :
      (∀ tid vs, dist_later n (ty1.(ty_own) tid vs) (ty2.(ty_own) tid vs)) →
      st_dist' n ty1 ty2.
  Instance st_dist : Dist simple_type := st_dist'.

  Definition st_unpack (ty : simple_type) : thread_id -c> list val -c> laterC (iProp Σ) :=
    λ tid vl, Next (ty.(ty_own) tid vl).

  Definition st_ofe_mixin : OfeMixin simple_type.
  Proof.
    apply (iso_ofe_mixin st_unpack).
    - split; [by destruct 1|by constructor].
    - split; [by destruct 1|by constructor].
  Qed.
  Canonical Structure stC : ofeT := OfeT simple_type st_ofe_mixin.

  Global Instance st_own_ne n :
    Proper (dist (S n) ==> eq ==> eq ==> dist n) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance st_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.

  Global Instance ty_of_st_ne : NonExpansive ty_of_st.
  Proof.
    intros n ?? EQ. constructor. done. simpl.
    - intros tid l. apply EQ.
    - simpl. intros; repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance ty_of_st_proper : Proper ((≡) ==> (≡)) ty_of_st.
  Proof. apply (ne_proper _). Qed.
End ofe.

Section subtyping.
  Context `{typeG Σ}.
  Definition type_incl (ty1 ty2 : type) : iProp Σ :=
    (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
     (□ ∀ tid vl, ty1.(ty_own) tid vl -∗ ty2.(ty_own) tid vl) ∗
     (□ ∀ κ tid l, ty1.(ty_shr) κ tid l -∗ ty2.(ty_shr) κ tid l))%I.

  Global Instance type_incl_persistent ty1 ty2 : PersistentP (type_incl ty1 ty2) := _.
  (*  Typeclasses Opaque type_incl. *)

  Lemma type_incl_refl ty : type_incl ty ty.
  Proof. iSplit; first done. iSplit; iAlways; iIntros; done. Qed.

  Lemma type_incl_trans ty1 ty2 ty3 :
    type_incl ty1 ty2 -∗ type_incl ty2 ty3 -∗ type_incl ty1 ty3.
  Proof.
    iIntros "(% & #Ho12 & #Hs12) (% & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplit; iAlways; iIntros.
    - iApply "Ho23". iApply "Ho12". done.
    - iApply "Hs23". iApply "Hs12". done.
  Qed.

  Context (E : elctx) (L : llctx).

  Definition subtype (ty1 ty2 : type) : Prop :=
    lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗ type_incl ty1 ty2.
  (* TODO RJ: I'd really like to get rid of this definition. *)
  Definition ctx_eq {A} (x1 x2 : A) : Prop :=
    lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗ ⌜x1 = x2⌝.

  Lemma subtype_refl ty : subtype ty ty.
  Proof. iIntros. iApply type_incl_refl. Qed.
  Global Instance subtype_preorder : PreOrder subtype.
  Proof.
    split; first by intros ?; apply subtype_refl.
    intros ty1 ty2 ty3 H12 H23. iIntros.
    iApply (type_incl_trans with "[] []").
    - iApply (H12 with "[] []"); done.
    - iApply (H23 with "[] []"); done.
  Qed.

  Lemma ctx_eq_refl {A} (x : A) : ctx_eq x x.
  Proof. by iIntros "_ _ _". Qed.
  Global Instance ctx_eq_equivalent {A} : Equivalence (@ctx_eq A).
  Proof.
    split.
    - by iIntros (?) "_ _ _".
    - iIntros (x y Hxy) "LFT HE HL". by iDestruct (Hxy with "LFT HE HL") as %->.
    - iIntros (x y z Hxy Hyz) "LFT HE HL".
      iDestruct (Hxy with "LFT HE HL") as %->. by iApply (Hyz with "LFT HE HL").
  Qed.

  Lemma equiv_subtype ty1 ty2 : ty1 ≡ ty2 → subtype ty1 ty2.
  Proof. unfold subtype, type_incl=>EQ. setoid_rewrite EQ. apply subtype_refl. Qed.

  Global Instance ty_size_subtype : Proper (subtype ==> ctx_eq) ty_size.
  Proof. iIntros (?? Hst) "LFT HE HL". iDestruct (Hst with "LFT HE HL") as "[$ ?]". Qed.
  Global Instance ty_size_subtype_flip : Proper (flip subtype ==> ctx_eq) ty_size.
  Proof. by intros ?? ->. Qed.
  Lemma ty_size_subtype' ty1 ty2 :
    subtype ty1 ty2 → ctx_eq (ty_size ty1) (ty_size ty2).
  Proof. apply ty_size_subtype. Qed.
  Lemma ty_size_subtype_flip' ty1 ty2 :
    subtype ty2 ty1 → ctx_eq (ty_size ty1) (ty_size ty2).
  Proof. apply ty_size_subtype_flip. Qed.

  (* TODO: The prelude should have a symmetric closure. *)
  Definition eqtype (ty1 ty2 : type) : Prop :=
    subtype ty1 ty2 ∧ subtype ty2 ty1.

  Lemma eqtype_unfold ty1 ty2 :
    eqtype ty1 ty2 ↔
    (lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
      (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
      (□ ∀ tid vl, ty1.(ty_own) tid vl ↔ ty2.(ty_own) tid vl) ∗
      (□ ∀ κ tid l, ty1.(ty_shr) κ tid l ↔ ty2.(ty_shr) κ tid l))%I).
  Proof.
    split.
    - iIntros ([EQ1 EQ2]) "#LFT #HE #HL".
      iDestruct (EQ1 with "LFT HE HL") as "[#Hsz [#H1own #H1shr]]".
      iDestruct (EQ2 with "LFT HE HL") as "[_ [#H2own #H2shr]]".
      iSplit; last iSplit.
      + done.
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1own"|iApply "H2own"].
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1shr"|iApply "H2shr"].
    - intros EQ. split; iIntros "#LFT #HE #HL"; (iSplit; last iSplit);
      iDestruct (EQ with "LFT HE HL") as "[% [#Hown #Hshr]]".
      + done.
      + iIntros "!#* H". by iApply "Hown".
      + iIntros "!#* H". by iApply "Hshr".
      + done.
      + iIntros "!#* H". by iApply "Hown".
      + iIntros "!#* H". by iApply "Hshr".
  Qed.

  Lemma eqtype_refl ty : eqtype ty ty.
  Proof. by split. Qed.

  Lemma equiv_eqtype ty1 ty2 : ty1 ≡ ty2 → eqtype ty1 ty2.
  Proof. by split; apply equiv_subtype. Qed.

  Global Instance subtype_proper :
    Proper (eqtype ==> eqtype ==> iff) subtype.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance eqtype_equivalence : Equivalence eqtype.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Global Instance ty_size_proper_eq : Proper (eqtype ==> ctx_eq) ty_size.
  Proof. by intros ?? [-> _]. Qed.

  Lemma subtype_simple_type (st1 st2 : simple_type) :
    (∀ tid vl, lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
                 st1.(st_own) tid vl -∗ st2.(st_own) tid vl) →
    subtype st1 st2.
  Proof.
    intros Hst. iIntros. iSplit; first done. iSplit; iAlways.
    - iIntros. iApply (Hst with "[] [] []"); done.
    - iIntros (???) "H".
      iDestruct "H" as (vl) "[Hf Hown]". iExists vl. iFrame "Hf".
      by iApply (Hst with "[] [] []").
  Qed.
End subtyping.

Section weakening.
  Context `{typeG Σ}.

  Lemma subtype_weaken E1 E2 L1 L2 ty1 ty2 :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 ty1 ty2 → subtype E2 L2 ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub) "#LFT HE HL".
    iApply (Hsub with "LFT [HE] [HL]").
    - rewrite /elctx_interp_0. by iApply big_sepL_submseteq.
    - iDestruct "HL" as %HL. iPureIntro. intros ??. apply HL.
      eauto using elem_of_submseteq.
  Qed.
End weakening.

Hint Resolve subtype_refl eqtype_refl ctx_eq_refl ty_size_subtype'
             ty_size_subtype_flip': lrust_typing.
Hint Opaque ctx_eq subtype eqtype : lrust_typing.
