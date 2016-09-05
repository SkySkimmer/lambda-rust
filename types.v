From iris.program_logic Require Import thread_local.
From lrust Require Export notation.
From lrust Require Import lifetime heap.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Record type :=
    { ty_size : nat;
      ty_dup : bool;
      ty_own : thread_id → list val → iProp Σ;
      ty_shr : lifetime → thread_id → coPset → loc → iProp Σ;

      ty_shr_persistent κ tid N l : PersistentP (ty_shr κ tid N l);

      ty_size_eq tid vl : ty_own tid vl ⊢ length vl = ty_size;
      ty_dup_dup tid vl : ty_dup → ty_own tid vl ⊢ ty_own tid vl ★ ty_own tid vl;
      ty_shr_share E N κ l tid q : N ⊥ tlN → N ⊥ lftN →
        nclose N ⊆ E → nclose tlN ⊆ E → nclose lftN ⊆ E →
        lft κ ⊢ &{κ} (l ↦★: ty_own tid) ★ [κ]{q}
                ={E}=> ty_shr κ tid N l ★ [κ]{q};
      ty_shr_mono κ κ' tid E E' l : E ⊆ E' →
        κ' ⊑ κ ⊢ ty_shr κ tid E l → ty_shr κ' tid E' l;
      ty_shr_acc κ tid E E' l q :
        E ⊆ E' → nclose lftN ⊆ E' → nclose tlN ⊆ E' → ty_dup →
        ty_shr κ tid E l ⊢
          [κ]{q} ★ tl_own tid E ={E'}=> ∃ q', ▷l ↦★{q'}: ty_own tid ★
             (▷l ↦★{q'}: ty_own tid ={E'}=★ [κ]{q} ★ tl_own tid E)
    }.

  Global Existing Instance ty_shr_persistent.

  Definition ty_incl (ty1 ty2 : type) :=
    ((□ ∀ tid vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ∧
     (□ ∀ κ tid E l, ty1.(ty_shr) κ tid E l → ty2.(ty_shr) κ tid E l))%I.

  Record simple_type :=
    { st_size : nat;
      st_dup : bool;
      st_own : thread_id → list val → iProp Σ;

      st_size_eq tid vl : st_own tid vl ⊢ length vl = st_size;
      st_dup_dup tid vl : st_dup → st_own tid vl ⊢ st_own tid vl ★ st_own tid vl
    }.

  Program Coercion ty_of_st (st : simple_type) : type :=
    {| ty_size := st.(st_size);
       ty_dup := st.(st_dup);
       ty_own := st.(st_own);
       ty_shr := λ κ tid _ l, (&frac{κ} λ q, l ↦★{q}: st.(st_own) tid)%I
    |}.
  Next Obligation. apply st_size_eq. Qed.
  Next Obligation. apply st_dup_dup. Qed.
  Next Obligation.
    intros st E N κ l tid q ?????. iIntros "#Hκ !# [Hmt Hlft]".
    iVs (lft_borrow_fracture with "[Hmt]"); last by iFrame. done.
  Qed.
  Next Obligation.
    iIntros (st κ κ' tid E E' l _) "#Hord". by iApply lft_frac_borrow_incl.
  Qed.
  Next Obligation.
    intros st κ tid E E' l q ????.  iIntros "#Hshr!#[Hlft Htlown]".
    iVs (lft_frac_borrow_open with "[] Hlft"); first done; last by iFrame.
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

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* FIXME : why does not the coercion work ?  *)
  Program Definition bot : type :=
    ty_of_st {| st_size := 1;
       st_dup := true;
       st_own tid vl := False%I
    |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation. iIntros (tid vl _) "[]". Qed.

  (* FIXME : idem *)
  Program Definition unit : type :=
    ty_of_st {| st_size := 0;
       st_dup := true;
       st_own tid vl := (vl = [])%I
    |}.
  Next Obligation. iIntros (tid vl) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "%". auto. Qed.

  (* FIXME : idem  *)
  Program Definition bool : type :=
    ty_of_st {| st_size := 1;
       st_dup := true;
       st_own tid vl := (∃ z:bool, vl = [ #z ]%V)%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  (* FIXME : idem  *)
  Program Definition int : type :=
    ty_of_st {| st_size := 1;
       st_dup := true;
       st_own tid vl := (∃ z:Z, vl = [ #z ]%V)%I
    |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.
  Next Obligation. iIntros (tid vl _) "H". auto. Qed.

  


End types.

End Types.