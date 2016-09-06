From iris.program_logic Require Import thread_local.
From lrust Require Export notation.
From lrust Require Import lifetime heap.

Definition mgmtE := nclose tlN ∪ lftN.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Record type :=
    { ty_size : nat; ty_dup : bool;
      ty_own : thread_id → list val → iProp Σ;
      ty_shr : lifetime → thread_id → coPset → loc → iProp Σ;

      ty_shr_persistent κ tid N l : PersistentP (ty_shr κ tid N l);

      ty_size_eq tid vl : ty_own tid vl ⊢ length vl = ty_size;
      ty_dup_dup tid vl : ty_dup → ty_own tid vl ⊢ ty_own tid vl ★ ty_own tid vl;
      (* The mask for starting the sharing does /not/ include the
         namespace N, because sharing can be triggered in a context
         where N is open. This should not be harmful, since sharing
         typically creates invariants, which does not need the mask. *)
      ty_share E N κ l tid q : nclose N ⊥ mgmtE → mgmtE ⊆ E →
        &{κ} (l ↦★: ty_own tid) ★ [κ]{q} ={E}=> ty_shr κ tid N l ★ [κ]{q};
      ty_shr_mono κ κ' tid E E' l : E ⊆ E' →
        κ' ⊑ κ ⊢ ty_shr κ tid E l → ty_shr κ' tid E' l;
      ty_shr_acc κ tid E E' l q :
        E ⊆ E' → mgmtE ⊆ E' → ty_dup →
        ty_shr κ tid E l ⊢
          [κ]{q} ★ tl_own tid E ={E'}=> ∃ q', ▷l ↦★{q'}: ty_own tid ★
             (▷l ↦★{q'}: ty_own tid ={E'}=★ [κ]{q} ★ tl_own tid E)
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
    iIntros (st κ κ' tid E E' l _) "#Hord". by iApply lft_frac_borrow_incl.
  Qed.
  Next Obligation.
    intros st κ tid E E' l q ???.  iIntros "#Hshr!#[Hlft Htlown]".
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

  Program Definition bot : type :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := False%I
    |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation. iIntros (tid vl _) "[]". Qed.

  Program Definition unit : type :=
    ty_of_st {| st_size := 0;  st_dup := true;
       st_own tid vl := (vl = [])%I
    |}.
  Next Obligation. iIntros (tid vl) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "%". auto. Qed.

  Program Definition bool : type :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := (∃ z:bool, vl = [ #z ])%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  Program Definition int : type :=
    ty_of_st {| st_size := 1; st_dup := true;
       st_own tid vl := (∃ z:Z, vl = [ #z ])%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  (* TODO own and uniq_borrow are very similar. They could probably
     somehow share some bits..  *)
  Program Definition own (q:Qp) (ty:type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (∃ l:loc, vl = [ #l ] ★ †{q}l…ty.(ty_size)
                                 ★ ▷ l ↦★: ty.(ty_own) tid)%I;
       ty_shr κ tid E l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ★
            ∀ q', □ ([κ]{q'} →|={E ∪ mgmtE, mgmtE}▷=> ty.(ty_shr) κ tid E l' ★ [κ]{q'}))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros q ty E N κ l tid q' ?? =>/=. iIntros "[Hshr Hq']".
    iVs (lft_borrow_open with "[Hshr Hq']") as "[Hown Hob]". set_solver. by iFrame.
    iDestruct "Hown" as (vl) "[Hmt Hvl]". iDestruct "Hvl" as (l') "(>%&Hf&Hown)". subst.
    iVs (lft_open_borrow_contravar with "[Hob Hf]") as "Hob". set_solver.
    { iSplitR "Hob"; last done. iIntros "!>[Hmt1 Hmt2]!==>!>". iExists [ #l' ].
      rewrite heap_mapsto_vec_singleton. iSplitL "Hmt1"; first done.
      iExists _. iSplit; [|by iSplitR "Hmt2"]. done. }
    iVs (lft_borrow_close with "[Hmt Hown Hob]") as "[Hb Htok]". set_solver.
    { rewrite heap_mapsto_vec_singleton. iSplitR "Hob"; last done.
      by iIntros "!>{$Hmt$Hown}". }
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
    iVs (lft_borrow_fracture _ _ (λ q, l ↦{q} #l')%I with "Hb1") as "Hbf".
    rewrite lft_borrow_persist.
    iDestruct "Hb2" as (κ0 i) "(#Hord&#Hpb&Hpbown)".
    iVs (inv_alloc N _ (lft_pers_borrow_own i κ0 ∨ ty_shr ty κ tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!==>{$Htok}". iExists l'. iFrame. iIntros (q'') "!#Htok".
    iVs (inv_open with "Hinv") as "[[>Hbtok|#Hshr] Hclose]". set_solver.
    - replace ((nclose N ∪ mgmtE) ∖ N) with mgmtE by set_solver.
      iAssert (&{κ}▷ l' ↦★: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { iApply lft_borrow_persist. eauto. }
      iVs (lft_borrow_open with "[Hb Htok]") as "[Hown Hob]". set_solver. by iFrame.
      iVs (lft_open_borrow_contravar with "[Hob]") as "Hob". set_solver.
      { iSplitR "Hob"; last done. instantiate (1:=(l' ↦★: ty_own ty tid)%I). eauto 10. }
      iIntros "!==>!>".
      iVs (lft_borrow_close with "[Hown Hob]") as "[Hb Htok]". set_solver.
        by iFrame "Hown".
      iVs (ty.(ty_share) with "[Hb Htok]") as "[#Hshr Htok]"; try done. by iFrame.
      iVs ("Hclose" with "[]") as "_"; by eauto.
    - replace ((nclose N ∪ mgmtE) ∖ N) with mgmtE by set_solver.
      iIntros "!==>!>". iVs ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid E E' l ?. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iExists l'.
    iSplit. by iApply (lft_frac_borrow_incl with "[]").
    iIntros (q') "!#Htok".
    iVs (lft_incl_trade with "Hκ Htok") as (q'') "[Htok Hclose]". set_solver.
    iApply (pvs_trans _ (E ∪ mgmtE)). iApply pvs_intro'. set_solver.
    iIntros "Hclose'". iVs ("Hvs" $! q'' with "Htok") as "Hvs'".
    iIntros "!==>!>". iVs "Hvs'" as "[Hshr Htok]". iVs "Hclose'".
    iVs ("Hclose" with "Htok"). iFrame.
    iApply (ty.(ty_shr_mono) with "Hκ"); last done. done.
  Qed.
  Next Obligation. done. Qed.

  Program Definition uniq_borrow (κ:lifetime) (ty:type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (∃ l:loc, vl = [ #l ] ★ &{κ} l ↦★: ty.(ty_own) tid)%I;
       ty_shr κ' tid E l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ★
            ∀ q' κ'', □ (κ'' ⊑ κ ★ κ'' ⊑ κ' ★ [κ'']{q'} →
               |={E ∪ mgmtE, mgmtE}▷=> ty.(ty_shr) κ'' tid E l' ★ [κ'']{q'}))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros κ ty E N κ' l tid q' ?? =>/=. iIntros "[Hshr Hq']".
    iVs (lft_borrow_open with "[Hshr Hq']") as "[Hown Hob]". set_solver. by iFrame.
    iDestruct "Hown" as (vl) "[Hmt Hvl]". iDestruct "Hvl" as (l') "(>%&Hown)". subst.
    iVs (lft_open_borrow_contravar with "[Hob]") as "Hob". set_solver.
    { iSplitR "Hob"; last done. iIntros "!>[Hmt1 Hmt2]!==>!>". iExists [ #l' ].
      rewrite heap_mapsto_vec_singleton. iSplitL "Hmt1"; first done.
      iExists _. by iSplitR "Hmt2". }
    iVs (lft_borrow_close with "[Hmt Hown Hob]") as "[Hb Htok]". set_solver.
    { rewrite heap_mapsto_vec_singleton. iSplitR "Hob"; last done.
      by iIntros "!>{$Hmt$Hown}". }
    iVs (lft_borrow_split with "Hb") as "[Hb1 Hb2]". set_solver.
    iVs (lft_borrow_fracture _ _ (λ q, l ↦{q} #l')%I with "Hb1") as "Hbf".
    rewrite lft_borrow_persist.
    iDestruct "Hb2" as (κ0 i) "(#Hord&#Hpb&Hpbown)".
    iVs (inv_alloc N _ (lft_pers_borrow_own i κ0 ∨ ty_shr ty κ' tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!==>{$Htok}". iExists l'. iFrame.
    iIntros (q'' κ'') "!#(#Hκ''κ & #Hκ''κ' & Htok)".
    iVs (inv_open with "Hinv") as "[[>Hbtok|#Hshr] Hclose]". set_solver.
    - replace ((nclose N ∪ mgmtE) ∖ N) with mgmtE by set_solver.
      iAssert (&{κ''}&{κ} l' ↦★: ty_own ty tid)%I with "[Hbtok]" as "Hb".
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
    - replace ((nclose N ∪ mgmtE) ∖ N) with mgmtE by set_solver.
      iIntros "!==>!>". iVs ("Hclose" with "[]") as "_". by eauto.
      iIntros "!==>{$Htok}". by iApply (ty.(ty_shr_mono) with "Hκ''κ'").
  Admitted.
  Next Obligation.
    intros κ0 ty κ κ' tid E E' l ?. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iExists l'.
    iSplit. by iApply (lft_frac_borrow_incl with "[]").
    iIntros (q' κ'') "!#(#Hκ0 & #Hκ' & Htok)".
    iApply (pvs_trans _ (E ∪ mgmtE)). iApply pvs_intro'. set_solver.
    iIntros "Hclose'". iVs ("Hvs" $! q' κ'' with "[Htok]") as "Hclose".
    { iFrame. iSplit. done. iApply lft_incl_trans. eauto. }
    iIntros "!==>!>". iVs "Hclose" as "[Hshr Htok]". iVs "Hclose'".
    iIntros "!==>{$Htok}". iApply (ty.(ty_shr_mono) with "[] Hshr"). done.
    iApply lft_incl_refl.
  Qed.
  Next Obligation. done. Qed.



End types.

End Types.