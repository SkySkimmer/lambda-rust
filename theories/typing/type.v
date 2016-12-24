From iris.base_logic.lib Require Export na_invariants.
From lrust.lang Require Export proofmode notation.
From lrust.lifetime Require Import borrow frac_borrow reborrow.
From lrust.typing Require Import lft_contexts.

Class typeG Σ := TypeG {
  type_heapG :> heapG Σ;
  type_lftG :> lftG Σ;
  type_na_invG :> na_invG Σ;
  type_frac_borrowG Σ :> frac_borG Σ
}.

Definition lftE := ↑lftN.
Definition lrustN := nroot .@ "lrust".
Definition shrN  := lrustN .@ "shr".

Section type.
  Context `{typeG Σ}.

  Definition thread_id := na_inv_pool_name.

  Record type :=
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
  Global Existing Instances ty_shr_persistent.

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
    revert l; induction n; intros l.
    - simpl. set_solver+.
    - simpl. apply union_least; last by auto. solve_ndisj.
  Qed.

  Lemma shr_locsE_subseteq l n m :
    (n ≤ m)%nat → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done.
    rewrite ->IHle. rewrite -Nat.add_1_l [(_ + _)%nat]comm.  (* FIXME last rewrite is very slow. *)
    rewrite shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢ na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (shift_loc l n) m).
  Proof.
    rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj.
  Qed.

  (** Copy types *)
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
  (* We are repeating the typeclass parameter here just to make sure
     that simple_type does depend on it. Otherwise, the coercion defined
     bellow will not be acceptable by Coq. *)
  Record simple_type `{typeG Σ} :=
    { st_own : thread_id → list val → iProp Σ;

      st_size_eq tid vl : st_own tid vl -∗ ⌜length vl = 1%nat⌝;
      st_own_persistent tid vl : PersistentP (st_own tid vl) }.

  Global Existing Instance st_own_persistent.

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
    - iFrame "Hκ". iMod (bor_fracture with "LFT [Hmt]") as "Hfrac"; last first.
      { iExists vl. iFrame. auto. }
      done. set_solver.
    - iExFalso. iApply (lft_tok_dead with "Hκ"). done.
  Qed.
  Next Obligation.
    intros st κ κ' tid l. iIntros "#LFT #Hord H".
    iDestruct "H" as (vl) "[#Hf #Hown]".
    iExists vl. iFrame "Hown". by iApply (frac_bor_shorten with "Hord").
  Qed.

  Global Program Instance ty_of_st_copy st : Copy (ty_of_st st).
  Next Obligation.
    intros st κ tid E ? l q ? HF. iIntros "#LFT #Hshr Htok Hlft".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first set_solver+.
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first set_solver.
    iModIntro. iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
    - iNext. iExists _. by iFrame.
    - iIntros "Htok2 Hmt1". iDestruct "Hmt1" as (vl') "[Hmt1 #Hown']".
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
    iIntros (Hsend κ tid1 tid2 l) "H". iDestruct "H" as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply Hsend.
  Qed.
End type.

Coercion ty_of_st : simple_type >-> type.

Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(* OFE and COFE structures on types and simple types. *)
Section ofe.
  Context `{typeG Σ}.

  Section def.
    Definition tuple_of_type (ty : type) : prodC (prodC _ _) _ :=
      (ty.(ty_size),
       Next (ty.(ty_own) : _ -c> _ -c> _),
       ty.(ty_shr) :  _ -c> _ -c> _ -c> _).

    Instance type_equiv : Equiv type := λ ty1 ty2,
       tuple_of_type ty1 ≡ tuple_of_type ty2.
    Instance type_dist : Dist type := λ n ty1 ty2,
       tuple_of_type ty1 ≡{n}≡ tuple_of_type ty2.

    Definition type_ofe_mixin : OfeMixin type.
    Proof.
      split; [|split|]; unfold equiv, dist, type_equiv, type_dist.
      - intros. apply equiv_dist.
      - by intros ?.
      - by intros ???.
      - by intros ???->.
      - by intros ????; apply dist_S.
    Qed.

    Canonical Structure typeC : ofeT := OfeT type type_ofe_mixin.

    Instance st_equiv : Equiv simple_type := λ st1 st2,
      @Next (_ -c> _ -c> _) st1.(st_own) ≡ Next st2.(st_own).
    Instance st_dist : Dist simple_type := λ n st1 st2,
      @Next (_ -c> _ -c> _) st1.(st_own) ≡{n}≡ Next st2.(st_own).

    Definition st_ofe_mixin : OfeMixin simple_type.
    Proof.
      split; [|split|]; unfold equiv, dist, st_equiv, st_dist.
      - intros. apply equiv_dist.
      - by intros ?.
      - by intros ???.
      - by intros ???->.
      - by intros ????; apply dist_S.
    Qed.

    Canonical Structure simple_typeC : ofeT := OfeT simple_type st_ofe_mixin.
  End def.

  Global Instance ty_size_proper_d n:
    Proper (dist n ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_size_proper_e :
    Proper ((≡) ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_own_ne n:
    Proper (dist (S n) ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper_e:
    Proper ((≡) ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper_e :
    Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance st_own_ne n:
    Proper (dist (S n) ==> eq ==> eq ==> dist n) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance st_own_proper_e :
    Proper ((≡) ==> eq ==> eq ==> (≡)) st_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.

  Global Program Instance type_cofe : Cofe typeC :=
    {| compl c :=
         let '(ty_size, Next ty_own, ty_shr) :=
             compl {| chain_car := tuple_of_type ∘ c |}
         in
         {| ty_size := ty_size; ty_own := ty_own; ty_shr := ty_shr |}
    |}.
  Next Obligation. intros [c Hc]. apply Hc. Qed.
  Next Obligation.
    simpl. intros c _ _ shr [=_ _ ->] κ tid l.
    apply uPred.equiv_entails, equiv_dist=>n.
    by rewrite (λ c, conv_compl (A:=_ -c> _ -c> _ -c> _) n c κ tid l) /=
               uPred.always_always.
  Qed.
  Next Obligation.
    simpl. intros c sz own _ [=-> -> _] tid vl.
    apply uPred.entails_equiv_and, equiv_dist=>n.
    rewrite (λ c, conv_compl (A:=_ -c> _ -c> _) n c tid vl) /= conv_compl /=.
    apply equiv_dist, uPred.entails_equiv_and, ty_size_eq.
  Qed.
  Next Obligation.
    simpl. intros c _ own shr [=_ -> ->] E κ l tid q ?.
    apply uPred.entails_equiv_and, equiv_dist=>n.
    rewrite (λ c, conv_compl (A:=_ -c> _ -c> _ -c> _) n c κ tid l) /=.
    setoid_rewrite (λ c vl, conv_compl (A:=_ -c> _ -c> _) n c tid vl). simpl.
    etrans. { by apply equiv_dist, uPred.entails_equiv_and, (c n).(ty_share). }
    simpl. destruct n; repeat (simpl; (f_contractive || f_equiv)).
    rewrite (c.(chain_cauchy) (S n) (S (S n))) //. lia.
  Qed.
  Next Obligation.
    simpl. intros c _ _ shr [=_ _ ->] κ κ' tid l.
    apply uPred.entails_equiv_and, equiv_dist=>n.
    rewrite !(λ c, conv_compl (A:=_ -c> _ -c> _ -c> _) n c _ tid l) /=.
    apply equiv_dist, uPred.entails_equiv_and. apply ty_shr_mono.
  Qed.
  Next Obligation.
    intros n c. split; [split|]; simpl; try by rewrite conv_compl.
    f_contractive. destruct n; first done. rewrite /= conv_compl //.
  Qed.

  Global Program Instance simple_type_cofe : Cofe simple_typeC :=
    {| compl c :=
         let 'Next st_own := compl
                {| chain_car := Next ∘ (st_own : _ -> _ -c> _ -c> _) ∘ c |} in
         {| st_own := st_own |}
    |}.
  Next Obligation. intros [c Hc]. apply Hc. Qed.
  Next Obligation.
    simpl. intros c own [=->] tid vl.
    apply uPred.entails_equiv_and, equiv_dist=>n.
    rewrite (λ c, conv_compl (A:=_ -c> _ -c> _) n c tid vl) /=.
    apply equiv_dist, uPred.entails_equiv_and, st_size_eq.
  Qed.
  Next Obligation.
    simpl. intros c own [=->] tid vl.
    apply uPred.equiv_entails, equiv_dist=>n.
    by rewrite (λ c, conv_compl (A:=_ -c> _ -c> _) n c tid vl) /=
               uPred.always_always.
  Qed.
  Next Obligation.
    intros n c. apply Next_contractive. destruct n=>//=. rewrite conv_compl //.
  Qed.

  Global Instance ty_of_st_ne n : Proper (dist n ==> dist n) ty_of_st.
  Proof.
    intros [][]EQ. split;[split|]=>//= κ tid l.
    repeat (f_contractive || f_equiv). apply EQ.
  Qed.
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
    (* TODO: this iIntros takes suspiciously long. *)
    iIntros "(% & #Ho12 & #Hs12) (% & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplit; iAlways; iIntros.
    - iApply "Ho23". iApply "Ho12". done.
    - iApply "Hs23". iApply "Hs12". done.
  Qed.

  Context (E : elctx) (L : llctx).

  Definition subtype (ty1 ty2 : type) : Prop :=
    lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
            type_incl ty1 ty2.

  Global Instance subtype_preorder : PreOrder subtype.
  Proof.
    split.
    - intros ty. iIntros. iApply type_incl_refl.
    - intros ty1 ty2 ty3 H12 H23. iIntros.
      iApply (type_incl_trans with "[] []").
      + iApply (H12 with "[] []"); done.
      + iApply (H23 with "[] []"); done.
  Qed.

  (* TODO: The prelude should have a symmetric closure. *)
  Definition eqtype (ty1 ty2 : type) : Prop :=
    subtype ty1 ty2 ∧ subtype ty2 ty1.

  Global Instance subtype_equivalence : Equivalence eqtype.
  Proof.
    split.
    - split; done.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma subtype_simple_type (st1 st2 : simple_type) :
    (∀ tid vl, lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
                 st1.(st_own) tid vl -∗ st2.(st_own) tid vl) →
    subtype st1 st2.
  Proof.
    intros Hst. iIntros. iSplit; first done. iSplit; iAlways.
    - iIntros. iApply (Hst with "* [] [] []"); done.
    - iIntros (???) "H".
      iDestruct "H" as (vl) "[Hf Hown]". iExists vl. iFrame "Hf".
      by iApply (Hst with "* [] [] []").
  Qed.
End subtyping.
