From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import hoare thread_local.
From lrust Require Export notation lifetime heap.

Definition mgmtE := nclose tlN ∪ lftN.
Definition lrustN := nroot .@ "lrust".

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* [perm] is defined here instead of perm.v in order to define [cont] *)
  Definition perm := thread_id → iProp Σ.

  Record type :=
    { ty_size : nat; ty_dup : bool;
      ty_own : thread_id → list val → iProp Σ;
      (* TODO : the document says ty_shr takes a mask, but it is never
         used with anything else than namespaces. *)
      ty_shr : lifetime → thread_id → namespace → loc → iProp Σ;

      ty_dup_persistent tid vl : ty_dup → PersistentP (ty_own tid vl);
      ty_shr_persistent κ tid N l : PersistentP (ty_shr κ tid N l);

      ty_size_eq tid vl : ty_own tid vl ⊢ length vl = ty_size;
      (* The mask for starting the sharing does /not/ include the
         namespace N, for allowing more flexibility for the user of
         this type (typically for the [own] type). AFAIK, there is no
         fundamental reason for this.

         This should not be harmful, since sharing typically creates
         invariants, which does not need the mask.  Moreover, it is
         more consistent with thread-local tokens, which we do not
         give any. *)
      ty_share E N κ l tid q : mgmtE ⊥ nclose N → mgmtE ⊆ E →
        &{κ} (l ↦★: ty_own tid) ⊢ [κ]{q} ={E}=★ ty_shr κ tid N l ★ [κ]{q};
      ty_shr_mono κ κ' tid N l :
        κ' ⊑ κ ⊢ ty_shr κ tid N l → ty_shr κ' tid N l;
      ty_shr_acc κ tid N E l q :
        nclose N ⊆ E → mgmtE ⊆ E → ty_dup →
        ty_shr κ tid N l ⊢
          [κ]{q} ★ tl_own tid N ={E}=> ∃ q', ▷l ↦★{q'}: ty_own tid ★
             (▷l ↦★{q'}: ty_own tid ={E}=★ [κ]{q} ★ tl_own tid N)
    }.
  Global Existing Instances ty_shr_persistent ty_dup_persistent.

  Record simple_type :=
    { st_size : nat;
      st_own : thread_id → list val → iProp Σ;

      st_size_eq tid vl : st_own tid vl ⊢ length vl = st_size;
      st_own_persistent tid vl : PersistentP (st_own tid vl) }.
  Global Existing Instance st_own_persistent.

  Program Definition ty_of_st (st : simple_type) : type :=
    {| ty_size := st.(st_size); ty_dup := true;
       ty_own := st.(st_own);
       ty_shr := λ κ tid _ l,
                 (∃ vl, (&frac{κ} λ q, l ↦★{q} vl) ★ ▷ st.(st_own) tid vl)%I
    |}.
  Next Obligation. apply st_size_eq. Qed.
  Next Obligation.
    intros st E N κ l tid q ??. iIntros "Hmt Htok".
    iVs (lft_borrow_exists with "Hmt Htok") as (vl) "[Hmt Htok]". set_solver.
    iVs (lft_borrow_split with "Hmt") as "[Hmt Hown]". set_solver.
    iVs (lft_borrow_persistent with "Hown Htok") as "[Hown $]". set_solver.
    iExists vl. iFrame. by iApply lft_borrow_fracture.
  Qed.
  Next Obligation.
    iIntros (st κ κ' tid N l) "#Hord H". iDestruct "H" as (vl) "[Hf Hown]".
    iExists vl. iFrame. by iApply (lft_frac_borrow_incl with "Hord").
  Qed.
  Next Obligation.
    intros st κ tid N E l q ???.  iIntros "#Hshr!#[Hlft $]".
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iVs (lft_frac_borrow_open with "[] Hf Hlft") as (q') "[Hmt Hclose]";
      first set_solver.
    - iIntros "!#". iIntros (q1 q2). rewrite heap_mapsto_vec_op_eq.
      iSplit; auto.
    - iVsIntro. rewrite {1}heap_mapsto_vec_op_split. iExists _.
      iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
      + iNext. iExists _. by iFrame.
      + iIntros "Hmt1". iDestruct "Hmt1" as (vl') "[Hmt1 #Hown']".
        iAssert (▷ (length vl = length vl'))%I as ">%".
        { iNext.
          iDestruct (st_size_eq with "Hown") as %->.
          iDestruct (st_size_eq with "Hown'") as %->. done. }
        iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op // Qp_div_2.
        iDestruct "Hmt" as "[>% Hmt]". subst. by iApply "Hclose".
  Qed.

End defs.

Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

Module Types.
Section types.
  (* TODO : make ty_of_st work as a coercion. *)

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* [emp] cannot be defined using [ty_of_st], because the least we
     would be able to prove from its [ty_shr] would be [▷ False], but
     we really need [False] to prove [ty_incl_emp]. *)
  Program Definition emp :=
    {| ty_size := 0; ty_dup := true;
       ty_own tid vl := False%I; ty_shr κ tid N l := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation.
    iIntros (????????) "Hb Htok".
    iVs (lft_borrow_exists with "Hb Htok") as (vl) "[Hb Htok]". set_solver.
    iVs (lft_borrow_split with "Hb") as "[_ Hb]". set_solver.
    iVs (lft_borrow_persistent with "Hb Htok") as "[>[] _]". set_solver.
  Qed.
  Next Obligation. iIntros (?????) "_ []". Qed.
  Next Obligation. intros. iIntros "[]". Qed.

  Program Definition unit :=
    ty_of_st {| st_size := 0; st_own tid vl := (vl = [])%I |}.
  Next Obligation. iIntros (tid vl) "%". simpl. by subst. Qed.

  Program Definition bool :=
    ty_of_st {| st_size := 1; st_own tid vl := (∃ z:bool, vl = [ #z ])%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Program Definition int :=
    ty_of_st {| st_size := 1; st_own tid vl := (∃ z:Z, vl = [ #z ])%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  (* TODO own and uniq_borrow are very similar. They could probably
     somehow share some bits..  *)
  Program Definition own (q : Qp) (ty : type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [ty_incl_own].

            Since this assertion is timeless, this should not cause
            problems. *)
         (∃ l:loc, vl = [ #l ] ★ ▷ †{q}l…ty.(ty_size)
                               ★ ▷ l ↦★: ty.(ty_own) tid)%I;
       ty_shr κ tid N l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ★
            ∀ q', [κ]{q'} ={mgmtE ∪ N, mgmtE}▷=> ty.(ty_shr) κ tid N l' ★ [κ]{q'})%I
    |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    intros q ty E N κ l tid q' ?? =>/=. iIntros "Hshr Htok".
    iVs (lft_borrow_exists with "Hshr Htok") as (vl) "[Hb Htok]". set_solver.
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
    iVs (lft_borrow_exists with "Hb2 Htok") as (l') "[Hb2 Htok]". set_solver.
    iVs (lft_borrow_split with "Hb2") as "[EQ Hb2]". set_solver.
    iVs (lft_borrow_persistent with "EQ Htok") as "[>% Htok]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iVs (lft_borrow_split with "Hb2") as "[_ Hb2]". set_solver.
    iVs (lft_borrow_fracture _ _ (λ q, l ↦{q} #l')%I with "Hb1") as "Hbf".
    rewrite lft_borrow_persist. iDestruct "Hb2" as (κ0 i) "(#Hord&#Hpb&Hpbown)".
    iVs (inv_alloc N _ (lft_pers_borrow_own i κ0 ∨ ty_shr ty κ tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!==>{$Htok}". iExists l'. iFrame. iIntros (q'') "!#Htok".
    iVs (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    replace ((mgmtE ∪ N) ∖ N) with mgmtE by set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ}▷ l' ↦★: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { iApply lft_borrow_persist. eauto. }
      iVs (lft_borrow_open with "Hb Htok") as "[Hown Hob]". set_solver.
      iIntros "!==>!>".
      iVs (lft_borrow_close_stronger with "Hown Hob []") as "[Hb Htok]".
        set_solver. eauto 10.
      iVs (ty.(ty_share) with "Hb Htok") as "[#Hshr Htok]"; try done.
      iVs ("Hclose" with "[]") as "_"; by eauto.
    - iIntros "!==>!>". iVs ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    iIntros (_ ty κ κ' tid N l) "#Hκ #H". iDestruct "H" as (l') "[Hfb Hvs]".
    iExists l'. iSplit. by iApply (lft_frac_borrow_incl with "[]").
    iIntros (q') "!#Htok".
    iVs (lft_incl_trade with "Hκ Htok") as (q'') "[Htok Hclose]". set_solver.
    iVs ("Hvs" $! q'' with "Htok") as "Hvs'".
    iIntros "!==>!>". iVs "Hvs'" as "[Hshr Htok]".
    iVs ("Hclose" with "Htok"). iFrame.
    by iApply (ty.(ty_shr_mono) with "Hκ").
  Qed.
  Next Obligation. done. Qed.

  Program Definition uniq_borrow (κ:lifetime) (ty:type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (∃ l:loc, vl = [ #l ] ★ &{κ} l ↦★: ty.(ty_own) tid)%I;
       ty_shr κ' tid N l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ★
            ∀ q' κ'', κ'' ⊑ κ ★ κ'' ⊑ κ' ★ [κ'']{q'}
               ={mgmtE ∪ N, mgmtE}▷=> ty.(ty_shr) κ'' tid N l' ★ [κ'']{q'})%I
    |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    intros κ ty E N κ' l tid q' ?? =>/=. iIntros "Hshr Htok".
    iVs (lft_borrow_exists with "Hshr Htok") as (vl) "[Hb Htok]". set_solver.
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
    iVs (lft_borrow_exists with "Hb2 Htok") as (l') "[Hb2 Htok]". set_solver.
    iVs (lft_borrow_split with "Hb2") as "[EQ Hb2]". set_solver.
    iVs (lft_borrow_persistent with "EQ Htok") as "[>% Htok]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iVs (lft_borrow_fracture _ _ (λ q, l ↦{q} #l')%I with "Hb1") as "Hbf".
    rewrite lft_borrow_persist.
    iDestruct "Hb2" as (κ0 i) "(#Hord&#Hpb&Hpbown)".
    iVs (inv_alloc N _ (lft_pers_borrow_own i κ0 ∨ ty_shr ty κ' tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!==>{$Htok}". iExists l'. iFrame.
    iIntros (q'' κ'') "!#(#Hκ''κ & #Hκ''κ' & Htok)".
    iVs (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    replace ((mgmtE ∪ N) ∖ N) with mgmtE by set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ''}&{κ} l' ↦★: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { iApply lft_borrow_persist. iExists κ0, i. iFrame "★ #".
        iApply lft_incl_trans. eauto. }
      iVs (lft_borrow_open with "Hb Htok") as "[Hown Hob]". set_solver.
      iIntros "!==>!>".
      iVs (lft_borrow_unnest with "Hκ''κ [Hown Hob]") as "[Htok Hb]". set_solver. by iFrame.
      iVs (ty.(ty_share) with "Hb Htok") as "[#Hshr Htok]"; try done.
      iVs ("Hclose" with "[]") as "_".
      (* FIXME : the "global sharing protocol" that we used for [own]
         does not work here, because we do not know at the beginning
         at which lifetime we will need the sharing.

         This seems somewhat similar to the RefCell problem: we would
         need a lifetime that would be the union of κ and κ'. *)
      admit.
      by eauto.
    - iIntros "!==>!>". iVs ("Hclose" with "[]") as "_". by eauto.
      iIntros "!==>{$Htok}". by iApply (ty.(ty_shr_mono) with "Hκ''κ'").
  Admitted.
  Next Obligation.
    iIntros (κ0 ty κ κ' tid N l) "#Hκ #H". iDestruct "H" as (l') "[Hfb Hvs]".
    iExists l'. iSplit. by iApply (lft_frac_borrow_incl with "[]").
    iIntros (q' κ'') "!#(#Hκ0 & #Hκ' & Htok)".
    iVs ("Hvs" $! q' κ'' with "[Htok]") as "Hclose".
    { iFrame. iSplit. done. iApply lft_incl_trans. eauto. }
    iIntros "!==>!>". iVs "Hclose" as "[Hshr Htok]".
    iIntros "!==>{$Htok}". iApply (ty.(ty_shr_mono) with "[] Hshr").
    iApply lft_incl_refl.
  Qed.
  Next Obligation. done. Qed.

  Program Definition shared_borrow (κ : lifetime) (ty : type) :=
    ty_of_st {| st_size := 1;
       st_own tid vl := (∃ l:loc, vl = [ #l ] ★ ty.(ty_shr) κ tid lrustN l)%I;
    |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Fixpoint combine_offs (tyl : list type) (accu : nat) :=
    match tyl with
    | [] => []
    | ty :: q => (ty, accu) :: combine_offs q (accu + ty.(ty_size))
    end.

  Lemma list_ty_type_eq tid (tyl : list type) (vll : list (list val)) :
    length tyl = length vll →
    ([★ list] tyvl ∈ combine tyl vll, ty_own (tyvl.1) tid (tyvl.2))
      ⊢ length (concat vll) = sum_list_with ty_size tyl.
  Proof.
    revert vll; induction tyl as [|ty tyq IH]; destruct vll;
      iIntros (EQ) "Hown"; try done.
    rewrite big_sepL_cons app_length /=. iDestruct "Hown" as "[Hown Hownq]".
    iDestruct (ty.(ty_size_eq) with "Hown") as %->.
    iDestruct (IH with "[-]") as %->; auto.
  Qed.

  Lemma split_prod_mt tid tyl l q :
    (l ↦★{q}: λ vl,
       ∃ vll, vl = concat vll ★ length tyl = length vll
         ★ [★ list] tyvl ∈ combine tyl vll, ty_own (tyvl.1) tid (tyvl.2))%I
    ⊣⊢ [★ list] tyoffs ∈ combine_offs tyl 0,
         shift_loc l (tyoffs.2) ↦★{q}: ty_own (tyoffs.1) tid.
  Proof.
    rewrite -{1}(shift_loc_0 l). change 0%Z with (Z.of_nat 0).
    generalize 0%nat. induction tyl as [|ty tyl IH]=>/= offs.
    - iSplit; iIntros "_". by iApply big_sepL_nil.
      iExists []. iSplit. by iApply heap_mapsto_vec_nil.
      iExists []. repeat iSplit; try done. by iApply big_sepL_nil.
    - rewrite big_sepL_cons -IH. iSplit.
      + iIntros "H". iDestruct "H" as (vl) "[Hmt H]".
        iDestruct "H" as ([|vl0 vll]) "(%&Hlen&Hown)";
          iDestruct "Hlen" as %Hlen; inversion Hlen; subst.
        rewrite big_sepL_cons heap_mapsto_vec_app/=.
        iDestruct "Hmt" as "[Hmth Hmtq]"; iDestruct "Hown" as "[Hownh Hownq]".
        iDestruct (ty.(ty_size_eq) with "Hownh") as %->.
        iSplitL "Hmth Hownh". iExists vl0. by iFrame.
        iExists (concat vll). iSplitL "Hmtq"; last by eauto.
        by rewrite shift_loc_assoc Nat2Z.inj_add.
      + iIntros "[Hmth H]". iDestruct "H" as (vl) "[Hmtq H]".
        iDestruct "H" as (vll) "(%&Hlen&Hownq)". subst.
        iDestruct "Hmth" as (vlh) "[Hmth Hownh]". iDestruct "Hlen" as %->.
        iExists (vlh ++ concat vll).
        rewrite heap_mapsto_vec_app shift_loc_assoc Nat2Z.inj_add.
        iDestruct (ty.(ty_size_eq) with "Hownh") as %->. iFrame.
        iExists (vlh :: vll). rewrite big_sepL_cons. iFrame. auto.
  Qed.

  Fixpoint nat_rec_shift {A : Type} (x : A) (f : nat → A → A) (n0 n : nat) :=
    match n with
    | O => x
    | S n => f n0 (nat_rec_shift x f (S n0) n)
    end.

  Lemma split_prod_namespace tid (N : namespace) n :
    ∃ E, (tl_own tid N ⊣⊢ tl_own tid E
                 ★ nat_rec_shift True (λ i P, tl_own tid (N .@ i) ★ P) 0%nat n)
         ∧ (∀ i, i < 0 → nclose (N .@ i) ⊆ E)%nat.
  Proof.
    generalize 0%nat. induction n as [|n IH].
    - eexists. split. by rewrite right_id. intros. apply nclose_subseteq.
    - intros i. destruct (IH (S i)) as [E [IH1 IH2]].
      eexists (E ∖ (N .@ i))%I. split.
      + simpl. rewrite IH1 assoc -tl_own_union; last set_solver.
        f_equiv; last done. f_equiv. rewrite (comm union).
        apply union_difference_L. apply IH2. lia.
      + intros. assert (i0 ≠ i)%nat by lia. solve_ndisj.
  Qed.

  Program Definition product (tyl : list type) :=
    {| ty_size := sum_list_with ty_size tyl; ty_dup := forallb ty_dup tyl;
       ty_own tid vl :=
         (∃ vll, vl = concat vll ★ length tyl = length vll ★
                 [★ list] tyvl ∈ combine tyl vll, tyvl.1.(ty_own) tid (tyvl.2))%I;
       ty_shr κ tid N l :=
         ([★ list] i ↦ tyoffs ∈ combine_offs tyl 0,
           tyoffs.1.(ty_shr) κ tid (N .@ i) (shift_loc l (tyoffs.2)))%I
    |}.
  Next Obligation.
    intros tyl tid vl Hfa.
    cut (∀ vll, PersistentP ([★ list] tyvl ∈ combine tyl vll,
                             ty_own (tyvl.1) tid (tyvl.2))). by apply _.
    clear vl. induction tyl as [|ty tyl IH]=>[|[|vl vll]]; try by apply _.
    edestruct andb_prop_elim as [Hduph Hdupq]. by apply Hfa.
    rewrite /PersistentP /= big_sepL_cons.
    iIntros "?". by iApply persistentP.
  Qed.
  Next Obligation.
    iIntros (tyl tid vl) "Hown". iDestruct "Hown" as (vll) "(%&%&Hown)".
    subst. by iApply (list_ty_type_eq with "Hown").
  Qed.
  Next Obligation.
    intros tyl E N κ l tid q ??. rewrite split_prod_mt.
    change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat). generalize O at 3.
    induction (combine_offs tyl 0) as [|[ty offs] ll IH].
    - iIntros (?) "_$!==>". by rewrite big_sepL_nil.
    - iIntros (i) "Hown Htoks". rewrite big_sepL_cons.
      iVs (lft_borrow_split with "Hown") as "[Hownh Hownq]". set_solver.
      iVs (IH (S i)%nat with "Hownq Htoks") as "[#Hshrq Htoks]".
      iVs (ty.(ty_share) _ (N .@ (i+0)%nat) with "Hownh Htoks") as "[#Hshrh $]".
        solve_ndisj. done.
      iVsIntro. rewrite big_sepL_cons. iFrame "#".
      iApply big_sepL_mono; last done. intros. by rewrite /= Nat.add_succ_r.
  Qed.
  Next Obligation.
    iIntros (tyl κ κ' tid N l) "#Hκ #H". iApply big_sepL_impl.
    iSplit; last done. iIntros "!#*/=_#H'". by iApply (ty_shr_mono with "Hκ").
  Qed.
  Next Obligation.
    intros tyl κ tid N E l q ?? DUP. setoid_rewrite split_prod_mt.
    generalize 0%nat.
    change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat).
    destruct (split_prod_namespace tid N (length tyl)) as [Ef [EQ _]].
    setoid_rewrite ->EQ. clear EQ. generalize 0%nat.
    revert q. induction tyl as [|tyh tyq IH].
    - iIntros (q i offs) "_!#$!==>". iExists 1%Qp. rewrite big_sepL_nil. auto.
    - simpl in DUP. destruct (andb_prop_elim _ _ DUP) as [DUPh DUPq]. simpl.
      iIntros (q i offs) "#Hshr!#([Htokh Htokq]&Htlf&Htlh&Htlq)".
      rewrite big_sepL_cons Nat.add_0_r.
      iDestruct "Hshr" as "[Hshrh Hshrq]". setoid_rewrite <-Nat.add_succ_comm.
      iVs (IH with "Hshrq [Htokq Htlf Htlq]") as (q'q) "[Hownq Hcloseq]". by iFrame.
      iVs (tyh.(ty_shr_acc) with "Hshrh [Htokh Htlh]") as (q'h) "[Hownh Hcloseh]"; try done.
      by pose proof (nclose_subseteq N i); set_solver. by iFrame.
      destruct (Qp_lower_bound q'h q'q) as (q' & q'0h & q'0q & -> & ->).
      iExists q'. iVsIntro. rewrite big_sepL_cons.
      rewrite -heap_mapsto_vec_prop_op; last apply ty_size_eq.
      iDestruct "Hownh" as "[Hownh0 Hownh1]".
      rewrite (big_sepL_proper (λ _ x, _ ↦★{_}: _)%I); last first.
      { intros. rewrite -heap_mapsto_vec_prop_op; last apply ty_size_eq.
        instantiate (1:=λ _ y, _). simpl. reflexivity. }
      rewrite big_sepL_sepL. iDestruct "Hownq" as "[Hownq0 Hownq1]".
      iSplitL "Hownh0 Hownq0". iNext. by iFrame.
      iIntros "[Hh Hq]". rewrite (lft_own_split κ q).
      iVs ("Hcloseh" with "[Hh Hownh1]") as "($&$)". iNext. by iFrame.
      iVs ("Hcloseq" with "[Hq Hownq1]") as "($&$&$)". iNext. by iFrame.
      done.
  Qed.

  Lemma split_sum_mt l tid q tyl :
    (l ↦★{q}: λ vl,
         ∃ (i : nat) vl', vl = #i :: vl' ★ ty_own (nth i tyl emp) tid vl')%I
    ⊣⊢ ∃ (i : nat), l ↦{q} #i ★ shift_loc l 1 ↦★{q}: ty_own (nth i tyl emp) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl') "(%&Hown)". subst.
      iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[Hmt1 Hown]". iDestruct "Hown" as (vl) "(Hmt2&Hown)".
      iExists (#i::vl). rewrite heap_mapsto_vec_cons. iFrame. eauto.
  Qed.

  Class LstTySize (n : nat) (tyl : list type) :=
    size_eq : Forall ((= n) ∘ ty_size) tyl.
  Instance LstTySize_nil n : LstTySize n nil := List.Forall_nil _.
  Hint Extern 1 (LstTySize _ (_ :: _)) =>
    apply List.Forall_cons; [reflexivity|] : typeclass_instances.

  Lemma sum_size_eq n tid i tyl vl {Hn : LstTySize n tyl} :
    ty_own (nth i tyl emp) tid vl ⊢ length vl = n.
  Proof.
    iIntros "Hown". iDestruct (ty_size_eq with "Hown") as %->.
    revert Hn. rewrite /LstTySize List.Forall_forall /= =>Hn.
    edestruct nth_in_or_default as [| ->]. by eauto.
    iDestruct "Hown" as "[]".
  Qed.

  Program Definition sum {n} (tyl : list type) {_:LstTySize n tyl} :=
    {| ty_size := S n; ty_dup := forallb ty_dup tyl;
       ty_own tid vl :=
         (∃ (i : nat) vl', vl = #i :: vl' ★ (nth i tyl emp).(ty_own) tid vl')%I;
       ty_shr κ tid N l :=
         (∃ (i : nat), (&frac{κ} λ q, l ↦{q} #i) ★
               (nth i tyl emp).(ty_shr) κ tid N (shift_loc l 1))%I
    |}.
  Next Obligation.
    intros n tyl Hn tid vl Hdup%Is_true_eq_true.
    cut (∀ i vl', PersistentP (ty_own (nth i tyl emp) tid vl')). apply _.
    intros. apply ty_dup_persistent. edestruct nth_in_or_default as [| ->]; last done.
    rewrite ->forallb_forall in Hdup. auto using Is_true_eq_left.
  Qed.
  Next Obligation.
    iIntros (n tyl Hn tid vl) "Hown". iDestruct "Hown" as (i vl') "(%&Hown)". subst.
    simpl. by iDestruct (sum_size_eq with "Hown") as %->.
  Qed.
  Next Obligation.
    intros n tyl Hn E N κ l tid q ??. iIntros "Hown Htok". rewrite split_sum_mt.
    iVs (lft_borrow_exists with "Hown Htok") as (i) "[Hown Htok]". set_solver.
    iVs (lft_borrow_split with "Hown") as "[Hmt Hown]". set_solver.
    iVs ((nth i tyl emp).(ty_share) with "Hown Htok") as "[#Hshr Htok]"; try done.
    iFrame. iExists i. iFrame "#". by iApply lft_borrow_fracture.
  Qed.
  Next Obligation.
    intros n tyl Hn κ κ' tid N l. iIntros "#Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i. iSplitL "Hown0".
    by iApply (lft_frac_borrow_incl with "Hord").
    by iApply ((nth i tyl emp).(ty_shr_mono) with "Hord").
  Qed.
  Next Obligation.
    intros n tyl Hn κ tid N E l q ?? Hdup%Is_true_eq_true.
    iIntros "#H!#[[Htok1 Htok2] Htl]".
    setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 Hshr]".
    iVs (lft_frac_borrow_open with "[] Hshr0 Htok1") as (q'1) "[Hown Hclose]". set_solver.
    { iIntros "!#". iIntros (q1 q2). rewrite heap_mapsto_op_eq. iSplit; eauto. }
    iVs ((nth i tyl emp).(ty_shr_acc) with "Hshr [Htok2 Htl]")
      as (q'2) "[Hownq Hclose']"; try done; [|by iFrame|].
    { edestruct nth_in_or_default as [| ->]; last done.
      rewrite ->forallb_forall in Hdup. auto using Is_true_eq_left. }
    destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
    iExists q'. iVsIntro.
    rewrite -{1}heap_mapsto_op_eq -{1}heap_mapsto_vec_prop_op;
      last (by intros; apply sum_size_eq, Hn).
    iDestruct "Hownq" as "[Hownq1 Hownq2]". iDestruct "Hown" as "[Hown1 Hown2]".
    iSplitL "Hown1 Hownq1".
    - iNext. iExists i. by iFrame.
    - iIntros "H". iDestruct "H" as (i') "[Hown1 Hownq1]".
      rewrite (lft_own_split _ q).
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_op.
      iDestruct "Hown" as "[>#Hi Hown]". iDestruct "Hi" as %[= ->%Z_of_nat_inj].
      iVs ("Hclose" with "Hown") as "$".
      iCombine "Hownq1" "Hownq2" as "Hownq".
      rewrite heap_mapsto_vec_prop_op; last (by intros; apply sum_size_eq, Hn).
      iApply ("Hclose'" with "Hownq").
  Qed.

  Program Definition uninit (n : nat) :=
    ty_of_st {| st_size := n; st_own tid vl := (length vl = n)%I |}.
  Next Obligation. done. Qed.

  (* TODO : For now, functions and closures are not Sync nor
     Send. This means they cannot be called in another thread than the
     one that created it.
     We will need Send and Sync closures when dealing with
     multithreading (spawn needs a Send closure). *)
  Program Definition cont {n : nat} (ρ : vec val n → @perm Σ) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl := (∃ f, vl = [f] ★
          ∀ vl, ρ vl tid -★ tl_own tid ⊤
                 -★ WP f (map of_val vl) {{λ _, False}})%I;
       ty_shr κ tid N l := True%I |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.
  Next Obligation. intros. by iIntros "_ $". Qed.
  Next Obligation. intros. by iIntros "_ _". Qed.
  Next Obligation. done. Qed.

  Program Definition fn {n : nat} (ρ : vec val n → @perm Σ):=
    ty_of_st {| st_size := 1;
       st_own tid vl := (∃ f, vl = [f] ★
          ∀ vl, {{ ρ vl tid ★ tl_own tid ⊤ }} f (map of_val vl) {{λ _, False}})%I |}.
  Next Obligation.
    iIntros (n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.

  (* TODO *)
  (* Program Definition forall_ty {A : Type} n dup (ty : A -> type) {_:Inhabited A} *)
  (*         (Hsz : ∀ x, (ty x).(ty_size) = n) (Hdup : ∀ x, (ty x).(ty_dup) = dup) := *)
  (*   ty_of_st {| st_size := n; st_dup := dup; *)
  (*               st_own tid vl := (∀ x, (ty x).(ty_own) tid vl)%I |}. *)
  (* Next Obligation. *)
  (*   intros A n dup ty ? Hn Hdup tid vl. iIntros "H". iSpecialize ("H" $! inhabitant). *)
  (*   rewrite -(Hn inhabitant). by iApply ty_size_eq. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros A n [] ty ? Hn Hdup tid vl []. *)
  (*   (* FIXME: A quantified assertion is not necessarilly dupicable if *)
  (*      its contents is.*) *)
  (*   admit. *)
  (* Admitted. *)

End types.

End Types.

Import Types.

Notation "!" := emp : lrust_type_scope.
Notation "&uniq{ κ } ty" := (uniq_borrow κ ty)
  (format "&uniq{ κ } ty", at level 20, right associativity) : lrust_type_scope.
Notation "&shr{ κ } ty" := (shared_borrow κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

(* FIXME : these notations do not work. *)
Notation "( ty1 * ty2 * .. * tyn )" :=
  (product (cons ty1 (cons ty2 ( .. (cons tyn nil) .. ))))
  (format "( ty1  *  ty2  *  ..  *  tyn )") : lrust_type_scope.
Notation "( ty1 + ty2 + .. + tyn )" :=
  (sum (cons ty1 (cons ty2 ( .. (cons tyn nil) .. ))))
  (format "( ty1  +  ty2  +  ..  +  tyn )") : lrust_type_scope.

(* TODO : notation for forall *)