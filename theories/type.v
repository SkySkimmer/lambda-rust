From Coq Require Import Qcanon.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Export thread_local.
From iris.program_logic Require Import hoare.
From lrust Require Export notation lifetime frac_borrow heap.

Class iris_typeG Σ := Iris_typeG {
  type_heapG :> heapG Σ;
  type_lifetimeG :> lifetimeG Σ;
  type_thread_localG :> thread_localG Σ;
  type_frac_borrowG Σ :> frac_borrowG Σ
}.

Definition mgmtE := nclose tlN ∪ lftN.
Definition lrustN := nroot .@ "lrust".

(* [perm] is defined here instead of perm.v in order to define [cont] *)
Definition perm {Σ} := thread_id → iProp Σ.

Section type.

Context `{iris_typeG Σ}.

Record type :=
  { ty_size : nat;
    ty_dup : bool;
    ty_own : thread_id → list val → iProp Σ;
    ty_shr : lifetime → thread_id → coPset → loc → iProp Σ;

    ty_dup_persistent tid vl : ty_dup → PersistentP (ty_own tid vl);
    ty_shr_persistent κ tid E l : PersistentP (ty_shr κ tid E l);

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
      lft_ctx ⊢ &{κ} (l ↦∗: ty_own tid) -∗ q.[κ] ={E}=∗ ty_shr κ tid N l ∗ q.[κ];
    ty_shr_mono κ κ' tid E E' l : E ⊆ E' →
      lft_ctx ⊢ κ' ⊑ κ -∗ ty_shr κ tid E l -∗ ty_shr κ' tid E' l;
    ty_shr_acc κ tid E F l q :
      ty_dup → mgmtE ∪ F ⊆ E →
      lft_ctx ⊢ ty_shr κ tid F l -∗
        q.[κ] ∗ tl_own tid F ={E}=∗ ∃ q', ▷l ↦∗{q'}: ty_own tid ∗
           (▷l ↦∗{q'}: ty_own tid ={E}=∗ q.[κ] ∗ tl_own tid F)
  }.
Global Existing Instances ty_shr_persistent ty_dup_persistent.

(* We are repeating the typeclass parameter here jsut to make sure
   that simple_type does depend on it. Otherwise, the coercion defined
   bellow will not be acceptable by Coq. *)
Record simple_type `{iris_typeG Σ} :=
  { st_size : nat;
    st_own : thread_id → list val → iProp Σ;

    st_size_eq tid vl : st_own tid vl ⊢ length vl = st_size;
    st_own_persistent tid vl : PersistentP (st_own tid vl) }.
Global Existing Instance st_own_persistent.

Program Coercion ty_of_st (st : simple_type) : type :=
  {| ty_size := st.(st_size); ty_dup := true;
     ty_own := st.(st_own);

     (* [st.(st_own) tid vl] needs to be outside of the fractured
        borrow, otherwise I do not know how to prove the shr part of
        [lft_incl_ty_incl_shared_borrow]. *)
     ty_shr := λ κ tid _ l,
               (∃ vl, (&frac{κ} λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) tid vl)%I
  |}.
Next Obligation. intros. apply st_size_eq. Qed.
Next Obligation.
  intros st E N κ l tid q ? ?. iIntros "#LFT Hmt Htok".
  iMod (borrow_exists with "LFT Hmt") as (vl) "Hmt". set_solver.
  iMod (borrow_split with "LFT Hmt") as "[Hmt Hown]". set_solver.
  iMod (borrow_persistent with "LFT Hown Htok") as "[Hown $]". set_solver.
  iMod (borrow_fracture with "LFT [Hmt]") as "Hfrac"; last first.
  { iExists vl. by iFrame. }
  done. set_solver.
Qed.
Next Obligation.
  intros st κ κ' tid E E' l ?. iIntros "#LFT #Hord H".
  iDestruct "H" as (vl) "[Hf Hown]".
  iExists vl. iFrame. by iApply (frac_borrow_shorten with "Hord").
Qed.
Next Obligation.
  intros st κ tid E F l q ??. iIntros "#LFT #Hshr[Hlft $]".
  iDestruct "Hshr" as (vl) "[Hf Hown]".
  iMod (frac_borrow_acc with "LFT [] Hf Hlft") as (q') "[Hmt Hclose]";
    first set_solver.
  - iIntros "!#". iIntros (q1 q2). rewrite heap_mapsto_vec_op_eq.
    iSplit; auto.
  - iModIntro. rewrite {1}heap_mapsto_vec_op_split. iExists _.
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

End type.

Hint Extern 0 (Is_true _.(ty_dup)) =>
  exact I || assumption : typeclass_instances.

Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

Module Types.
Section types.

  Context `{iris_typeG Σ}.

  (* [emp] cannot be defined using [ty_of_st], because the least we
     would be able to prove from its [ty_shr] would be [▷ False], but
     we really need [False] to prove [ty_incl_emp]. *)
  Program Definition emp :=
    {| ty_size := 0; ty_dup := true;
       ty_own tid vl := False%I; ty_shr κ tid E l := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation.
    iIntros (????????) "#LFT Hb Htok".
    iMod (borrow_exists with "LFT Hb") as (vl) "Hb". set_solver.
    iMod (borrow_split with "LFT Hb") as "[_ Hb]". set_solver.
    iMod (borrow_persistent with "LFT Hb Htok") as "[>[] _]". set_solver.
  Qed.
  Next Obligation. intros. iIntros "_ _ []". Qed.
  Next Obligation. intros. iIntros "_ []". Qed.

  Program Definition unit : type :=
    {| st_size := 0; st_own tid vl := (vl = [])%I |}.
  Next Obligation. iIntros (tid vl) "%". simpl. by subst. Qed.

  Program Definition bool : type :=
    {| st_size := 1; st_own tid vl := (∃ z:bool, vl = [ #z ])%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Program Definition int : type :=
    {| st_size := 1; st_own tid vl := (∃ z:Z, vl = [ #z ])%I |}.
  Next Obligation. iIntros (tid vl) "H". iDestruct "H" as (z) "%". by subst. Qed.

  Program Definition own (q : Qp) (ty : type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [ty_incl_own].

            Since this assertion is timeless, this should not cause
            problems. *)
         (∃ l:loc, vl = [ #l ] ∗ ▷ l ↦∗: ty.(ty_own) tid ∗ ▷ †{q}l…ty.(ty_size))%I;
       ty_shr κ tid E l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗
            ∀ q', □ (q'.[κ] ={mgmtE ∪ E, mgmtE}▷=∗ ty.(ty_shr) κ tid E l' ∗ q'.[κ]))%I
    |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    move=> q ty E N κ l tid q' ?? /=. iIntros "#LFT Hshr Htok".
    iMod (borrow_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (borrow_split with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (borrow_exists with "LFT Hb2") as (l') "Hb2". set_solver.
    iMod (borrow_split with "LFT Hb2") as "[EQ Hb2]". set_solver.
    iMod (borrow_persistent with "LFT EQ Htok") as "[>% $]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iMod (borrow_split with "LFT Hb2") as "[Hb2 _]". set_solver.
    iMod (borrow_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hbf". set_solver.
    rewrite /borrow. iDestruct "Hb2" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc N _ (idx_borrow_own 1 i ∨ ty_shr ty κ tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iExists l'. iIntros "!>{$Hbf}".  iIntros (q'') "!#Htok".
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    replace ((mgmtE ∪ N) ∖ N) with mgmtE by set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ}▷ l' ↦∗: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { rewrite /borrow. iExists i. eauto. }
      iMod (borrow_acc_strong with "LFT Hb Htok") as "[Hown Hclose']". set_solver.
      iIntros "!>". iNext.
      iMod ("Hclose'" with "*[Hown]") as "[Hb Htok]". iFrame. by iIntros "!>?$".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#Hshr Htok]"; try done.
      iMod ("Hclose" with "[]") as "_"; by eauto.
    - iIntros "!>". iNext. iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid E E' l ?. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]".
    iExists l'. iSplit. by iApply (frac_borrow_shorten with "[]").
    iIntros (q') "!#Htok".
    iApply step_fupd_mask_mono. reflexivity. apply union_preserving_l. eassumption.
    iMod (lft_incl_acc with "Hκ Htok") as (q'') "[Htok Hclose]". set_solver.
    iMod ("Hvs" $! q'' with "Htok") as "Hvs'".
    iIntros "!>". iNext. iMod "Hvs'" as "[Hshr Htok]".
    iMod ("Hclose" with "Htok"). iFrame.
    iApply (ty.(ty_shr_mono) with "LFT Hκ"); last done. done.
  Qed.
  Next Obligation. done. Qed.

  Program Definition uniq_borrow (κ:lifetime) (ty:type) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl :=
         (∃ l:loc, vl = [ #l ] ∗ &{κ} l ↦∗: ty.(ty_own) tid)%I;
       ty_shr κ' tid E l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
            ∀ q', □ (q'.[κ ⋅ κ']
               ={mgmtE ∪ E, mgmtE}▷=∗ ty.(ty_shr) (κ⋅κ') tid E l' ∗ q'.[κ⋅κ']))%I
    |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    move=> κ ty E N κ' l tid q' ??/=. iIntros "#LFT Hshr Htok".
    iMod (borrow_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (borrow_split with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (borrow_exists with "LFT Hb2") as (l') "Hb2". set_solver.
    iMod (borrow_split with "LFT Hb2") as "[EQ Hb2]". set_solver.
    iMod (borrow_persistent with "LFT EQ Htok") as "[>% $]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iMod (borrow_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hbf". set_solver.
    rewrite {1}/borrow. iDestruct "Hb2" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc N _ (idx_borrow_own 1 i ∨ ty_shr ty (κ⋅κ') tid N l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iExists l'. iIntros "!>{$Hbf}". iIntros (q'') "!#Htok".
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    replace ((mgmtE ∪ N) ∖ N) with mgmtE by set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ'}&{κ} l' ↦∗: ty_own ty tid)%I with "[Hbtok]" as "Hb".
      { rewrite /borrow. eauto. }
      iMod (borrow_unnest with "LFT Hb") as "Hb". set_solver.
      iIntros "!>". iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#Hshr Htok]"; try done.
      iMod ("Hclose" with "[]") as "_". eauto. by iFrame.
    - iIntros "!>". iNext. iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid E E' l ?. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0⋅κ' ⊑ κ0⋅κ) as "#Hκ0".
    { iApply lft_incl_lb. iSplit.
      - iApply lft_le_incl. by exists κ'.
      - iApply lft_incl_trans. iSplit; last done.
        iApply lft_le_incl. exists κ0. apply (comm _). }
    iExists l'. iSplit. by iApply (frac_borrow_shorten with "[]"). iIntros (q) "!#Htok".
    iApply step_fupd_mask_mono. reflexivity. apply union_preserving_l. eassumption.
    iMod (lft_incl_acc with "Hκ0 Htok") as (q') "[Htok Hclose]". set_solver.
    iMod ("Hvs" $! q' with "Htok") as "Hclose'".  iIntros "!>". iNext.
    iMod "Hclose'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    iApply (ty_shr_mono with "LFT Hκ0"); last done. done.
  Qed.
  Next Obligation. done. Qed.

  Program Definition shared_borrow (κ : lifetime) (ty : type) : type :=
    {| st_size := 1;
       st_own tid vl :=
         (∃ (l:loc), vl = [ #l ] ∗ ty.(ty_shr) κ tid lrustN l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Lemma split_prod_mt tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl,
       ∃ vl1 vl2, vl = vl1 ++ vl2 ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) tid ∗ shift_loc l ty1.(ty_size) ↦∗{q}: ty2.(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]". iDestruct "H1" as (vl1) "[H↦1 H1]".
      iDestruct "H2" as (vl2) "[H↦2 H2]". iExists (vl1 ++ vl2).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "H1") as %->.
      iFrame. iExists _, _. by iFrame.
  Qed.

  Program Definition product2 (ty1 ty2 : type) :=
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_dup := ty1.(ty_dup) && ty2.(ty_dup);
       ty_own tid vl := (∃ vl1 vl2,
         vl = vl1 ++ vl2 ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid E l :=
         (∃ E1 E2, ■ (E1 ⊥ E2 ∧ E1 ⊆ E ∧ E2 ⊆ E) ∗
            ty1.(ty_shr) κ tid E1 l ∗
            ty2.(ty_shr) κ tid E2 (shift_loc l ty1.(ty_size)))%I |}.
  Next Obligation. intros ty1 ty2 tid vl [Hdup1 Hdup2]%andb_True. apply _. Qed.
  Next Obligation.
    iIntros (ty1 ty2 tid vl) "H". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
    subst. rewrite app_length !ty_size_eq.
    iDestruct "H1" as %->. iDestruct "H2" as %->. done.
  Qed.
  Next Obligation.
    intros ty1 ty2 E N κ l tid q ??. iIntros "#LFT /=H Htok".
    rewrite split_prod_mt.
    iMod (borrow_split with "LFT H") as "[H1 H2]". set_solver.
    iMod (ty1.(ty_share) _ (N .@ 1) with "LFT H1 Htok") as "[? Htok]". solve_ndisj. done.
    iMod (ty2.(ty_share) _ (N .@ 2) with "LFT H2 Htok") as "[? $]". solve_ndisj. done.
    iModIntro. iExists (N .@ 1). iExists (N .@ 2). iFrame.
    iPureIntro. split. solve_ndisj. split; apply nclose_subseteq.
  Qed.
  Next Obligation.
    intros ty1 ty2 κ κ' tid E E' l ?. iIntros "#LFT /= #H⊑ H".
    iDestruct "H" as (N1 N2) "(% & H1 & H2)". iExists N1, N2.
    iSplit. iPureIntro. set_solver.
    iSplitL "H1"; by iApply (ty_shr_mono with "LFT H⊑").
  Qed.
  Next Obligation.
    intros ty1 ty2 κ tid E F l q [Hdup1 Hdup2]%andb_True ?.
    iIntros "#LFT H[[Htok1 Htok2] Htl]". iDestruct "H" as (E1 E2) "(% & H1 & H2)".
    assert (F = E1 ∪ E2 ∪ F∖(E1 ∪ E2)) as ->.
    { rewrite -union_difference_L; set_solver. }
    repeat setoid_rewrite tl_own_union; first last.
    set_solver. set_solver. set_solver. set_solver.
    iDestruct "Htl" as "[[Htl1 Htl2] $]".
    iMod (ty1.(ty_shr_acc) with "LFT H1 [$Htok1 $Htl1]") as (q1) "[H1 Hclose1]". done. set_solver.
    iMod (ty2.(ty_shr_acc) with "LFT H2 [$Htok2 $Htl2]") as (q2) "[H2 Hclose2]". done. set_solver.
    destruct (Qp_lower_bound q1 q2) as (qq & q'1 & q'2 & -> & ->). iExists qq.
    iDestruct "H1" as (vl1) "[H↦1 H1]". iDestruct "H2" as (vl2) "[H↦2 H2]".
    rewrite -!heap_mapsto_vec_op_eq !split_prod_mt.
    iAssert (▷ (length vl1 = ty1.(ty_size)))%I with "[#]" as ">%".
    { iNext. by iApply ty_size_eq. }
    iAssert (▷ (length vl2 = ty2.(ty_size)))%I with "[#]" as ">%".
    { iNext. by iApply ty_size_eq. }
    iDestruct "H↦1" as "[H↦1 H↦1f]". iDestruct "H↦2" as "[H↦2 H↦2f]".
    iIntros "!>". iSplitL "H↦1 H1 H↦2 H2".
    - iNext. iSplitL "H↦1 H1". iExists vl1. by iFrame. iExists vl2. by iFrame.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (vl1') "[H↦1 H1]". iDestruct "H2" as (vl2') "[H↦2 H2]".
      iAssert (▷ (length vl1' = ty1.(ty_size)))%I with "[#]" as ">%".
      { iNext. by iApply ty_size_eq. }
      iAssert (▷ (length vl2' = ty2.(ty_size)))%I with "[#]" as ">%".
      { iNext. by iApply ty_size_eq. }
      iCombine "H↦1" "H↦1f" as "H↦1". iCombine "H↦2" "H↦2f" as "H↦2".
      rewrite !heap_mapsto_vec_op; try by congruence.
      iDestruct "H↦1" as "[_ H↦1]". iDestruct "H↦2" as "[_ H↦2]".
      iMod ("Hclose1" with "[H1 H↦1]") as "[$$]". by iExists _; iFrame.
      iMod ("Hclose2" with "[H2 H↦2]") as "[$$]". by iExists _; iFrame. done.
  Qed.

  Definition product := fold_right product2 unit.

  Lemma split_sum_mt l tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl', vl = #i :: vl' ∗ ty_own (nth i tyl emp) tid vl')%I
    ⊣⊢ ∃ (i : nat), l ↦{q} #i ∗ shift_loc l 1 ↦∗{q}: ty_own (nth i tyl emp) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl') "[% Hown]". subst.
      iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[Hmt1 Hown]". iDestruct "Hown" as (vl) "[Hmt2 Hown]".
      iExists (#i::vl). rewrite heap_mapsto_vec_cons. iFrame. eauto.
  Qed.

  Class LstTySize (n : nat) (tyl : list type) :=
    size_eq : Forall ((= n) ∘ ty_size) tyl.
  Instance LstTySize_nil n : LstTySize n nil := List.Forall_nil _.
  Lemma LstTySize_cons n ty tyl :
    ty.(ty_size) = n → LstTySize n tyl → LstTySize n (ty :: tyl).
  Proof. intros. constructor; done. Qed.

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
         (∃ (i : nat) vl', vl = #i :: vl' ∗ (nth i tyl emp).(ty_own) tid vl')%I;
       ty_shr κ tid N l :=
         (∃ (i : nat), (&frac{κ} λ q, l ↦{q} #i) ∗
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
    intros n tyl Hn E N κ l tid q ??. iIntros "#LFT Hown Htok". rewrite split_sum_mt.
    iMod (borrow_exists with "LFT Hown") as (i) "Hown". set_solver.
    iMod (borrow_split with "LFT Hown") as "[Hmt Hown]". set_solver.
    iMod ((nth i tyl emp).(ty_share) with "LFT Hown Htok") as "[#Hshr $]"; try done.
    iMod (borrow_fracture with "LFT [-]") as "H"; last by eauto. set_solver. iFrame.
  Qed.
  Next Obligation.
    intros n tyl Hn κ κ' tid E E' l ?. iIntros "#LFT #Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i. iSplitL "Hown0".
    by iApply (frac_borrow_shorten with "Hord").
    iApply ((nth i tyl emp).(ty_shr_mono) with "LFT Hord"); last done. done.
  Qed.
  Next Obligation.
    intros n tyl Hn κ tid E F l q Hdup%Is_true_eq_true ?.
    iIntros "#LFT #H[[Htok1 Htok2] Htl]".
    setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 Hshr]".
    iMod (frac_borrow_acc with "LFT [] Hshr0 Htok1") as (q'1) "[Hown Hclose]". set_solver.
    { iIntros "!#". iIntros (q1 q2). rewrite heap_mapsto_op_eq. iSplit; eauto. }
    iMod ((nth i tyl emp).(ty_shr_acc) with "LFT Hshr [Htok2 $Htl]")
      as (q'2) "[Hownq Hclose']"; try done.
    { edestruct nth_in_or_default as [| ->]; last done.
      rewrite ->forallb_forall in Hdup. auto using Is_true_eq_left. }
    destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
    iExists q'. iModIntro.
    rewrite -{1}heap_mapsto_op_eq -{1}heap_mapsto_vec_prop_op;
      last (by intros; apply sum_size_eq, Hn).
    iDestruct "Hownq" as "[Hownq1 Hownq2]". iDestruct "Hown" as "[Hown1 Hown2]".
    iSplitL "Hown1 Hownq1".
    - iNext. iExists i. by iFrame.
    - iIntros "H". iDestruct "H" as (i') "[Hown1 Hownq1]".
      rewrite (lft_own_split _ q).
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_op.
      iDestruct "Hown" as "[>#Hi Hown]". iDestruct "Hi" as %[= ->%Z_of_nat_inj].
      iMod ("Hclose" with "Hown") as "$".
      iCombine "Hownq1" "Hownq2" as "Hownq".
      rewrite heap_mapsto_vec_prop_op; last (by intros; apply sum_size_eq, Hn).
      by iApply "Hclose'".
  Qed.

  Program Definition uninit : type :=
    {| st_size := 1; st_own tid vl := (length vl = 1%nat)%I |}.
  Next Obligation. done. Qed.

  Program Definition cont {n : nat} (ρ : vec val n → @perm Σ) :=
    {| ty_size := 1; ty_dup := false;
       ty_own tid vl := (∃ f, vl = [f] ∗
          ∀ vl, ρ vl tid -∗ tl_own tid ⊤
                 -∗ WP f (map of_val vl) {{λ _, False}})%I;
       ty_shr κ tid N l := True%I |}.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros (n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.
  Next Obligation. intros. by iIntros "_ _ $". Qed.
  Next Obligation. intros. by iIntros "_ _ _". Qed.
  Next Obligation. done. Qed.

  (* TODO : For now, functions are not Send. This means they cannot be
     called in another thread than the one that created it.  We will
     need Send functions when dealing with multithreading ([fork]
     needs a Send closure). *)
  Program Definition fn {A n} (ρ : A -> vec val n → @perm Σ) : type :=
    {| st_size := 1;
       st_own tid vl := (∃ f, vl = [f] ∗ ∀ x vl,
         {{ ρ x vl tid ∗ tl_own tid ⊤ }} f (map of_val vl) {{λ _, False}})%I |}.
  Next Obligation.
    iIntros (x n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.

End types.

End Types.

Existing Instance Types.LstTySize_nil.
Hint Extern 1 (Types.LstTySize _ (_ :: _)) =>
  apply Types.LstTySize_cons; [compute; reflexivity|] : typeclass_instances.

Import Types.

Notation "∅" := emp : lrust_type_scope.
Notation "&uniq{ κ } ty" := (uniq_borrow κ ty)
  (format "&uniq{ κ } ty", at level 20, right associativity) : lrust_type_scope.
Notation "&shr{ κ } ty" := (shared_borrow κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Arguments product : simpl never.
Notation Π := product.
(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1 (..(cons tyn nil)..))) : lrust_type_scope.
