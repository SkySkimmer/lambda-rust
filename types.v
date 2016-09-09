From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export notation.
From lrust Require Import lifetime heap.

Definition mgmtE := nclose tlN ∪ lftN.
Definition lrustN := nroot .@ "lrust".

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Record type :=
    { ty_size : nat; ty_dup : bool;
      ty_own : thread_id → list val → iProp Σ;
      (* TODO : the document says ty_shr takes a mask, but it is never
         used with anything else than namespaces. *)
      ty_shr : lifetime → thread_id → namespace → loc → iProp Σ;

      ty_shr_persistent κ tid N l : PersistentP (ty_shr κ tid N l);

      ty_size_eq tid vl : ty_own tid vl ⊢ length vl = ty_size;
      ty_dup_dup tid vl : ty_dup → ty_own tid vl ⊢ ty_own tid vl ★ ty_own tid vl;
      (* The mask for starting the sharing does /not/ include the
         namespace N, for allowing more flexibility for the user of
         this type (typically for the [own] type). AFAIK, there is no
         fundamental reason for this.

         This should not be harmful, since sharing typically creates
         invariants, which does not need the mask.  Moreover, it is
         more consistent with thread-local tokens, which we do not
         give any. *)
      ty_share E N κ l tid q : mgmtE ⊥ nclose N → mgmtE ⊆ E →
        &{κ} (l ↦★: ty_own tid) ★ [κ]{q} ={E}=> ty_shr κ tid N l ★ [κ]{q};
      ty_shr_mono κ κ' tid N l :
        κ' ⊑ κ ⊢ ty_shr κ tid N l → ty_shr κ' tid N l;
      ty_shr_acc κ tid N E l q :
        nclose N ⊆ E → mgmtE ⊆ E → ty_dup →
        ty_shr κ tid N l ⊢
          [κ]{q} ★ tl_own tid N ={E}=> ∃ q', ▷l ↦★{q'}: ty_own tid ★
             (▷l ↦★{q'}: ty_own tid ={E}=★ [κ]{q} ★ tl_own tid N)
    }.

  Global Existing Instance ty_shr_persistent.

  Definition ty_incl (ty1 ty2 : type) :=
    ((□ ∀ tid vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ∧
     (□ ∀ κ tid E l, ty1.(ty_shr) κ tid E l → ty2.(ty_shr) κ tid E l))%I.

  Record simple_type :=
    { st_size : nat; st_dup : bool;
      st_own : thread_id → list val → iProp Σ;

      st_size_eq tid vl : st_own tid vl ⊢ length vl = st_size;
      st_dup_dup tid vl : st_dup → st_own tid vl ⊢ st_own tid vl ★ st_own tid vl
    }.

  Program Definition ty_of_st (st : simple_type) : type :=
    {| ty_size := st.(st_size); ty_dup := st.(st_dup);
       ty_own := st.(st_own);
       ty_shr := λ κ tid _ l, (&frac{κ} λ q, l ↦★{q}: st.(st_own) tid)%I
    |}.
  Next Obligation. apply st_size_eq. Qed.
  Next Obligation. apply st_dup_dup. Qed.
  Next Obligation.
    intros st E N κ l tid q ??. iIntros "[Hmt Hlft]".
    iVs (lft_borrow_fracture with "[Hmt]"); last by iFrame. done.
  Qed.
  Next Obligation.
    iIntros (st κ κ' tid N l) "#Hord". by iApply lft_frac_borrow_incl.
  Qed.
  Next Obligation.
    intros st κ tid N E l q ???.  iIntros "#Hshr!#[Hlft Htlown]".
    iVs (lft_frac_borrow_open with "[] Hlft"); first set_solver; last by iFrame.
    iSplit; last done. iIntros "!#". iIntros (q1 q2). iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hq1q2 Hown]".
      iDestruct (st_dup_dup with "Hown") as "[Hown1 Hown2]". done.
      rewrite -heap_mapsto_vec_op_eq. iDestruct "Hq1q2" as "[Hq1 Hq2]".
        by iSplitL "Hq1 Hown1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]".
      iDestruct "H1" as (vl1) "[Hq1 Hown1]".
      iDestruct "H2" as (vl2) "[Hq2 Hown2]".
      iAssert (length vl1 = length vl2)%I with "[#]" as "%".
      { iDestruct (st_size_eq with "Hown2") as %->.
        iApply (st_size_eq with "Hown1"). }
      iCombine "Hq1" "Hq2" as "Hq1q2". rewrite heap_mapsto_vec_op; last done.
      iDestruct "Hq1q2" as "[% Hq1q2]". subst vl2. iExists vl1. by iFrame.
  Qed.

End defs.

Module Types.
Section types.
  (* TODO : make ty_of_st work as a coercion. *)

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Program Definition bot :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := False%I
    |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation. iIntros (tid vl _) "[]". Qed.

  Program Definition unit :=
    ty_of_st {| st_size := 0;  st_dup := true;
       st_own tid vl := (vl = [])%I
    |}.
  Next Obligation. iIntros (tid vl) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "%". auto. Qed.

  Program Definition bool :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := (∃ z:bool, vl = [ #z ])%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  Program Definition int :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := (∃ z:Z, vl = [ #z ])%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  (* TODO own and uniq_borrow are very similar. They could probably
     somehow share some bits..  *)
  Program Definition own (q : Qp) (ty : type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (∃ l:loc, vl = [ #l ] ★ †{q}l…ty.(ty_size)
                                 ★ ▷ l ↦★: ty.(ty_own) tid)%I;
       ty_shr κ tid N l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ★
            ∀ q', □ ([κ]{q'} →|={mgmtE ∪ N, mgmtE}▷=> ty.(ty_shr) κ tid N l' ★ [κ]{q'}))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros q ty E N κ l tid q' ?? =>/=. iIntros "[Hshr Hq']".
    iVs (lft_borrow_open with "[Hshr Hq']") as "[Hown Hob]". set_solver. by iFrame.
    iDestruct "Hown" as (vl) "[Hmt Hvl]". iDestruct "Hvl" as (l') "(>%&Hf&Hown)". subst.
    iCombine "Hown" "Hmt" as "Hown". rewrite heap_mapsto_vec_singleton.
    iVs (lft_borrow_close_stronger with "[-]") as "[Hb Htok]". set_solver.
    { iIntros "{$Hown $Hob}!>[Hmt1 Hmt2]!==>!>". iExists [ #l'].
      rewrite heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame. }
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
    iVs (lft_borrow_fracture _ _ (λ q, l ↦{q} #l')%I with "Hb2") as "Hbf".
    rewrite lft_borrow_persist. iDestruct "Hb1" as (κ0 i) "(#Hord&#Hpb&Hpbown)".
    iVs (inv_alloc N _ (lft_pers_borrow_own i κ0 ∨ ty_shr ty κ tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!==>{$Htok}". iExists l'. iFrame. iIntros (q'') "!#Htok".
    iVs (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    replace ((mgmtE ∪ N) ∖ N) with mgmtE by set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ}▷ l' ↦★: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { iApply lft_borrow_persist. eauto. }
      iVs (lft_borrow_open with "[Hb Htok]") as "[Hown Hob]". set_solver. by iFrame.
      iIntros "!==>!>".
      iVs (lft_borrow_close_stronger with "[Hown Hob]") as "Hbtok". set_solver.
      { iFrame "Hown Hob". eauto 10. }
      iVs (ty.(ty_share) with "Hbtok") as "[#Hshr Htok]"; try done.
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
            ∀ q' κ'', □ (κ'' ⊑ κ ★ κ'' ⊑ κ' ★ [κ'']{q'} →
               |={mgmtE ∪ N, mgmtE}▷=> ty.(ty_shr) κ'' tid N l' ★ [κ'']{q'}))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros κ ty E N κ' l tid q' ?? =>/=. iIntros "[Hshr Hq']".
    iVs (lft_borrow_open with "[Hshr Hq']") as "[Hown Hob]". set_solver. by iFrame.
    iDestruct "Hown" as (vl) "[Hmt Hvl]". iDestruct "Hvl" as (l') "(>%&Hown)". subst.
    iCombine "Hmt" "Hown" as "Hown". rewrite heap_mapsto_vec_singleton.
    iVs (lft_borrow_close_stronger with "[-]") as "[Hb Htok]". set_solver.
    { iIntros "{$Hown $Hob}!>[Hmt1 Hmt2]!==>!>". iExists [ #l'].
      rewrite heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame. }
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
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
      iVs (lft_borrow_open with "[Hb Htok]") as "[Hown Hob]". set_solver. by iFrame.
      iIntros "!==>!>".
      iVs (lft_borrow_unnest with "Hκ''κ [Hown Hob]") as "[Htok Hb]". set_solver. by iFrame.
      iVs (ty.(ty_share) with "[Hb Htok]") as "[#Hshr Htok]"; try done. by iFrame.
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
    ty_of_st {| st_size := 1; st_dup := true;
      st_own tid vl := (∃ l:loc, vl = [ #l ] ★ ty.(ty_shr) κ tid lrustN l)%I
    |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation. iIntros (κ ty tid vl _) "H". auto. Qed.

  Fixpoint combine_accu_size (tyl : list type) (accu : nat) :=
    match tyl with
    | [] => []
    | ty :: q => (ty, accu) :: combine_accu_size q (accu + ty.(ty_size))
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
    (∃ vl, l ↦★{q} vl ★ (∃ vll, vl = concat vll ★ length tyl = length vll
       ★ ([★ list] tyvl ∈ combine tyl vll, ty_own (tyvl.1) tid (tyvl.2))))%I
    ≡ ([★ list] tyoffs ∈ combine_accu_size tyl 0,
         shift_loc l (tyoffs.2) ↦★{q}: ty_own (tyoffs.1) tid)%I.
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
        iDestruct (ty.(ty_size_eq) with "#Hownh") as %->.
        iSplitL "Hmth Hownh". iExists vl0. by iFrame.
        iExists (concat vll). iSplitL "Hmtq"; last by eauto.
        by rewrite shift_loc_assoc Nat2Z.inj_add.
      + iIntros "[Hmth H]". iDestruct "H" as (vl) "[Hmtq H]".
        iDestruct "H" as (vll) "(%&Hlen&Hownq)". subst.
        iDestruct "Hmth" as (vlh) "[Hmth Hownh]". iDestruct "Hlen" as %->.
        iExists (vlh ++ concat vll).
        rewrite heap_mapsto_vec_app shift_loc_assoc Nat2Z.inj_add.
        iDestruct (ty.(ty_size_eq) with "#Hownh") as %->. iFrame.
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
         ([★ list] i ↦ tyoffs ∈ combine_accu_size tyl 0,
           tyoffs.1.(ty_shr) κ tid (N .@ i) (shift_loc l (tyoffs.2)))%I
    |}.
  Next Obligation.
    iIntros (tyl tid vl) "Hown". iDestruct "Hown" as (vll) "(%&%&Hown)".
    subst. by iApply (list_ty_type_eq with "Hown").
  Qed.
  Next Obligation.
    induction tyl as [|ty tyq IH]; iIntros (tid vl Hfa) "H";
      iDestruct "H" as ([|vl0 vlq]) "(%&#Hlen&Hown)"; subst vl;
      iDestruct "Hlen" as %Hlen; inversion Hlen; simpl in *.
    - iSplit; iExists []; by repeat iSplit.
    - apply andb_prop_elim in Hfa. destruct Hfa as [Hfah Hfaq].
      iDestruct (big_sepL_cons with "Hown") as "[Hh Hq]".
      iDestruct (ty_dup_dup with "Hh") as "[Hh1 Hh2]". done.
      iDestruct (IH tid (concat vlq) Hfaq with "[Hq]") as "[Hq1 Hq2]". by eauto.
      iSplitL "Hh1 Hq1".
      + iDestruct "Hq1" as (vllq) "(%&%&?)". iExists (vl0::vllq).
        rewrite big_sepL_cons/=. iFrame. iSplit; iPureIntro; congruence.
      + iDestruct "Hq2" as (vllq) "(%&%&?)". iExists (vl0::vllq).
        rewrite big_sepL_cons/=. iFrame. iSplit; iPureIntro; congruence.
  Qed.
  Next Obligation.
    intros tyl E N κ l tid q ??. rewrite split_prod_mt.
    change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat). generalize O at 3.
    induction (combine_accu_size tyl 0) as [|[ty offs] ll IH].
    - iIntros (?) "[_ $] !==>". by rewrite big_sepL_nil.
    - iIntros (i) "[Hown Htoks]". rewrite big_sepL_cons.
      iVs (lft_borrow_split with "Hown") as "[Hownh Hownq]". set_solver.
      iVs (IH (S i)%nat with "[Htoks Hownq]") as "[#Hshrq Htoks]". by iFrame.
      iVs (ty.(ty_share) _ (N .@ (i+0)%nat) with "[Hownh Htoks]") as "[#Hshrh $]".
        solve_ndisj. done. by iFrame.
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
      iVs (IH with "Hshrq [Htokq Htlf Htlq]") as (q'q) "[Hownq Hcloseq]". done. by iFrame.
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

End types.

End Types.
