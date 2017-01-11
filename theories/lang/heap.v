From Coq Require Import Min.
From iris.algebra Require Import cmra_big_op gmap frac agree.
From iris.algebra Require Import csum excl auth.
From iris.base_logic Require Import big_op lib.invariants lib.fractional.
From iris.proofmode Require Export tactics.
From lrust.lang Require Export lifting.
Set Default Proof Using "Type".
Import uPred.

Definition heapN : namespace := nroot .@ "heap".

Definition lock_stateR : cmraT :=
  csumR (exclR unitC) natR.

Definition heapUR : ucmraT :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR valC)).

Definition heap_freeableUR : ucmraT :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitC))).

Class heapG Σ := HeapG {
  heapG_ownP_inG :> ownPG lrust_lang Σ;
  heap_inG :> inG Σ (authR heapUR);
  heap_freeable_inG :> inG Σ (authR heap_freeableUR);
  heap_name : gname;
  heap_freeable_name : gname
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
Definition to_heap : state → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).
Definition heap_freeable_rel (σ : state) (hF : heap_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs →
  qs.2 ≠ ∅ ∧ ∀ i, is_Some (σ !! (blk, i)) ↔ is_Some (qs.2 !! i).

Section definitions.
  Context `{heapG Σ}.

  Definition heap_mapsto_st (st : lock_state)
             (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own heap_name (◯ {[ l := (q, to_lock_stateR st, to_agree v) ]}).

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    heap_mapsto_st (RSt 0) l q v.
  Definition heap_mapsto_aux : seal (@heap_mapsto_def). by eexists. Qed.
  Definition heap_mapsto := unseal heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    seal_eq heap_mapsto_aux.

  Definition heap_mapsto_vec (l : loc) (q : Qp) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_mapsto (shift_loc l i) q v)%I.

  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitC) :=
    match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: nat) : iProp Σ :=
    own heap_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}).
  Definition heap_freeable_aux : seal (@heap_freeable_def). by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.

  Definition heap_inv : iProp Σ :=
    (∃ (σ:state) hF, ownP σ ∗ own heap_name (● to_heap σ)
                            ∗ own heap_freeable_name (● hF)
                            ∗ ⌜heap_freeable_rel σ hF⌝)%I.
  Definition heap_ctx : iProp Σ := inv heapN heap_inv.

  Global Instance heap_ctx_persistent : PersistentP heap_ctx.
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto heap_freeable heap_mapsto_vec.
Instance: Params (@heap_mapsto) 4.
Instance: Params (@heap_freeable) 5.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Notation "l ↦∗{ q } vl" := (heap_mapsto_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : uPred_scope.
Notation "l ↦∗ vl" := (heap_mapsto_vec l 1 vl) (at level 20) : uPred_scope.

Notation "l ↦∗{ q }: P" := (∃ vl, l ↦∗{ q } vl ∗ P vl)%I
  (at level 20, q at level 50, format "l  ↦∗{ q }:  P") : uPred_scope.
Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : uPred_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : uPred_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  (** Allocation *)
  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l)=> [[[|n] v]|] //=. Qed.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_insert σ l x v :
    to_heap (<[l:=(x, v)]> σ)
    = <[l:=(1%Qp, to_lock_stateR x, to_agree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma to_heap_delete σ l : to_heap (delete l σ) = delete l (to_heap σ).
  Proof. by rewrite /to_heap fmap_delete. Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l↦{q}v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q.
    by rewrite heap_mapsto_eq -own_op -auth_frag_op op_singleton pair_op agree_idemp.
  Qed.
  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Global Instance heap_mapsto_vec_timeless l q vl : TimelessP (l ↦∗{q} vl).
  Proof. rewrite /heap_mapsto_vec. apply _. Qed.

  Global Instance heap_mapsto_vec_fractional l vl: Fractional (λ q, l ↦∗{q} vl)%I.
  Proof.
    intros p q. rewrite /heap_mapsto_vec -big_sepL_sepL.
    by setoid_rewrite (fractional (Φ := λ q, _ ↦{q} _)%I).
  Qed.
  Global Instance heap_mapsto_vec_as_fractional l q vl:
    AsFractional (l ↦∗{q} vl) (λ q, l ↦∗{q} vl)%I q.
  Proof. split. done. apply _. Qed.

  Global Instance heap_freeable_timeless q l n : TimelessP (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid uPred.discrete_valid.
    eapply pure_elim; [done|]=> /auth_own_valid /=.
    rewrite op_singleton pair_op singleton_valid. case.
    rewrite /= to_agree_comp_valid=>? Heq. fold_leibniz. eauto.
  Qed.

  Lemma heap_mapsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto_vec big_sepL_nil. Qed.

  Lemma heap_mapsto_vec_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ shift_loc l (length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /heap_mapsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_vec_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /heap_mapsto_vec big_sepL_singleton /= shift_loc_0. Qed.

  Lemma heap_mapsto_vec_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ shift_loc l 1 ↦∗{q} vl.
  Proof.
    by rewrite (heap_mapsto_vec_app l q [v] vl) heap_mapsto_vec_singleton.
  Qed.

  Lemma heap_mapsto_vec_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 ∗ l ↦∗{q2} vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗{q1+q2} vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_mapsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_mapsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (shift_loc l 1) with "[Hvl1 Hvl2]") as "[% $]";
        subst; first by iFrame.
      rewrite (inj_iff (:: vl2)).
      iDestruct (heap_mapsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.
    - by iIntros "[% [$ Hl2]]"; subst.
  Qed.

  Lemma heap_mapsto_pred_op l q1 q2 n (Φ : list val → iProp Σ) :
    (∀ vl, Φ vl -∗ ⌜length vl = n⌝) →
    l ↦∗{q1}: Φ ∗ l ↦∗{q2}: (λ vl, ⌜length vl = n⌝) ⊣⊢ l ↦∗{q1+q2}: Φ.
  Proof.
    intros Hlen. iSplit.
    - iIntros "[Hmt1 Hmt2]".
      iDestruct "Hmt1" as (vl) "[Hmt1 Hown]". iDestruct "Hmt2" as (vl') "[Hmt2 %]".
      iDestruct (Hlen with "Hown") as %?.
      iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op; last congruence.
      iDestruct "Hmt" as "[_ Hmt]". iExists vl. by iFrame.
    - iIntros "Hmt". iDestruct "Hmt" as (vl) "[[Hmt1 Hmt2] Hown]".
      iDestruct (Hlen with "Hown") as %?.
      iSplitL "Hmt1 Hown"; iExists _; by iFrame.
  Qed.

  Lemma heap_mapsto_pred_wand l q Φ1 Φ2 :
    l ↦∗{q}: Φ1 -∗ (∀ vl, Φ1 vl -∗ Φ2 vl) -∗ l ↦∗{q}: Φ2.
  Proof.
    iIntros "Hm Hwand". iDestruct "Hm" as (vl) "[Hm HΦ]". iExists vl.
    iFrame "Hm". iApply "Hwand". done.
  Qed.

  Lemma heap_mapsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own heap_name (◯ [⋅ list] i ↦ v ∈ vl,
      {[shift_loc l i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def /heap_mapsto_st=>?.
    by rewrite (big_opL_commute (Auth None)) big_opL_commute1 //.
  Qed.

  Global Instance heap_mapsto_pred_fractional l (P : list val → iProp Σ):
    (∀ vl, PersistentP (P vl)) → Fractional (λ q, l ↦∗{q}: P)%I.
  Proof.
    intros p q q'. iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[[Hown1 Hown2] #HP]".
      iSplitL "Hown1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (vl1) "[Hown1 #HP1]".
      iDestruct "H2" as (vl2) "[Hown2 #HP2]".
      set (ll := min (length vl1) (length vl2)).
      rewrite -[vl1](firstn_skipn ll) -[vl2](firstn_skipn ll) 2!heap_mapsto_vec_app.
      iDestruct "Hown1" as "[Hown1 _]". iDestruct "Hown2" as "[Hown2 _]".
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_vec_op; last first.
      { rewrite !firstn_length. subst ll.
        rewrite -!min_assoc min_idempotent min_comm -min_assoc min_idempotent min_comm. done. }
      iDestruct "Hown" as "[H Hown]". iDestruct "H" as %Hl. iExists (take ll vl1). iFrame.
      destruct (min_spec (length vl1) (length vl2)) as [[Hne Heq]|[Hne Heq]].
      + iClear "HP2". rewrite take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
      + iClear "HP1". rewrite Hl take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
  Qed.
  Global Instance heap_mapsto_pred_as_fractional l q (P : list val → iProp Σ):
    (∀ vl, PersistentP (P vl)) → AsFractional (l ↦∗{q}: P) (λ q, l ↦∗{q}: P)%I q.
  Proof. split. done. apply _. Qed.

  Lemma inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intros j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n as [|n IH]=>i. done. by apply insert_valid. Qed.

  Lemma heap_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ∗ †{q2}shift_loc l n…n' ⊣⊢ †{q1+q2}l…(n+n').
  Proof.
    by rewrite heap_freeable_eq /heap_freeable_def -own_op -auth_frag_op
      op_singleton pair_op inter_op.
  Qed.

  (** Properties about heap_freeable_rel and heap_freeable *)
  Lemma heap_freeable_rel_None σ l hF :
    (∀ m : Z, σ !! shift_loc l m = None) → heap_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma heap_freeable_is_Some σ hF l n i :
    heap_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    is_Some (σ !! shift_loc l i) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt inter_lookup_Some; lia.
    - rewrite is_Some_alt inter_lookup_None; lia.
  Qed.

  Lemma heap_freeable_rel_init_mem l h vl σ:
    vl ≠ [] →
    (∀ m : Z, σ !! shift_loc l m = None) →
    heap_freeable_rel σ h →
    heap_freeable_rel (init_mem l vl σ)
                      (<[l.1 := (1%Qp, inter (l.2) (length vl))]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct vl as [|v vl]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + length vl)).
      + rewrite inter_lookup_Some //.
        destruct (lookup_init_mem_Some σ l (l.1, i) vl); naive_solver.
      + rewrite inter_lookup_None; last lia. rewrite lookup_init_mem_ne /=; last lia.
        replace (l.1,i) with (shift_loc l (i - l.2))
          by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_init_mem_ne; last auto.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l :
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    heap_freeable_rel σ hF →
    heap_freeable_rel (free_mem l n σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_free_mem_ne.
  Qed.

  Lemma heap_freeable_rel_stable σ h l p :
    heap_freeable_rel σ h → is_Some (σ !! l) →
    heap_freeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs σ l vl:
    (∀ m : Z, σ !! shift_loc l m = None) →
    own heap_name (● to_heap σ)
    ==∗ own heap_name (● to_heap (init_mem l vl σ))
       ∗ own heap_name (◯ [⋅ list] i ↦ v ∈ vl,
           {[shift_loc l i := (1%Qp, Cinr 0%nat, to_agree v)]}).
  Proof.
    intros FREE. rewrite -own_op. apply own_update, auth_update_alloc.
    revert l FREE. induction vl as [|v vl IH]=> l FRESH; [done|].
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /=.
    etrans; first apply (IH (shift_loc l 1)).
    { intros. by rewrite shift_loc_assoc. }
    rewrite shift_loc_0 -insert_singleton_op; last first.
    { rewrite -equiv_None big_opL_commute equiv_None big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None -{2}(shift_loc_0 l). apply not_inj; lia. }
    rewrite to_heap_insert. setoid_rewrite shift_loc_assoc.
    apply alloc_local_update; last done. apply lookup_to_heap_None.
    rewrite lookup_init_mem_ne /=; last lia. by rewrite -(shift_loc_0 l) FRESH.
  Qed.

  Lemma wp_alloc E n:
    ↑heapN ⊆ E → 0 < n →
    {{{ heap_ctx }}} Alloc (Lit $ LitInt n) @ E
    {{{ l vl, RET LitV $ LitLoc l; ⌜n = length vl⌝ ∗ †l…(Z.to_nat n) ∗ l ↦∗ vl }}}.
  Proof.
    iIntros (???) "#Hinv HΦ". rewrite /heap_ctx /heap_inv.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iApply (wp_alloc_pst with "[$Hσ]")=> //.
    iNext. iIntros (l σ') "(% & #Hσσ' & Hσ')".
    iDestruct "Hσσ'" as %(vl & HvlLen & Hvl).
    assert (vl ≠ []) by (intros ->; simpl in *; lia).
    iMod (heap_alloc_vs with "[$Hvalσ]") as "[Hvalσ' Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split. done. apply inter_valid. }
    iMod ("Hclose" with "[Hσ' Hvalσ' HhF]") as "_".
    - iNext. iExists σ', _. subst σ'. iFrame. iPureIntro.
      rewrite HvlLen Nat2Z.id. auto using heap_freeable_rel_init_mem.
    - rewrite heap_freeable_eq /heap_freeable_def. iApply "HΦ".
      iSplit; first auto. iFrame. by rewrite heap_mapsto_vec_combine.
  Qed.

  Lemma heap_free_vs l vl σ :
    own heap_name (● to_heap σ) ∗ own heap_name (◯ [⋅ list] i ↦ v ∈ vl,
      {[shift_loc l i := (1%Qp, Cinr 0%nat, to_agree v)]})
    ==∗ own heap_name (● to_heap (free_mem l (length vl) σ)).
  Proof.
    rewrite -own_op. apply own_update, auth_update_dealloc.
    revert σ l. induction vl as [|v vl IH]=> σ l; [done|].
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= shift_loc_0.
    apply local_update_total_valid=> _ Hvalid _.
    assert (([⋅ list] k↦y ∈ vl,
      {[shift_loc l (1 + k) := (1%Qp, Cinr 0%nat, to_agree y)]}) !! l
      = @None (frac * lock_stateR * agree valC)).
    { move: (Hvalid l). rewrite lookup_op lookup_singleton.
      by move=> /(cmra_discrete_valid_iff 0) /exclusiveN_Some_l. }
    rewrite -insert_singleton_op //. etrans.
    { apply (delete_local_update _ _ l (1%Qp, Cinr 0%nat, to_agree v)).
      by rewrite lookup_insert. }
    rewrite delete_insert // -to_heap_delete delete_free_mem.
    setoid_rewrite <-shift_loc_assoc. apply IH.
  Qed.

  Lemma wp_free E (n:Z) l vl :
    ↑heapN ⊆ E → n = length vl →
    {{{ heap_ctx ∗ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
      Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
    {{{ RET LitV LitUnit; True }}}.
  Proof.
    iIntros (???Φ) "(#Hinv & >Hmt & >Hf) HΦ". rewrite /heap_ctx /heap_inv.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & REL)" "Hclose". iDestruct "REL" as %REL.
    rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_valid_discrete_2.
    move: Hl=> /singleton_included [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iApply (wp_free_pst _ σ with "[$Hσ]"). by auto.
    { intros i. subst n. eauto using heap_freeable_is_Some. }
    iNext. iIntros "Hσ". iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ".
    { rewrite heap_mapsto_vec_combine //. iFrame. }
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iMod ("Hclose" with "[-HΦ]") as "_"; last by iApply "HΦ".
    iNext. iExists _, _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  Lemma heap_mapsto_lookup l ls q v σ:
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_valid_discrete_2.
    iPureIntro. move: Hl=> /singleton_included [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    by exists O. eauto. exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_lookup_1 l ls v σ:
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜σ !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_valid_discrete_2.
    iPureIntro. move: Hl=> /singleton_included [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma wp_read_sc E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Read ScOrd (Lit $ LitLoc l) @ E
    {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (??) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup with "Hvalσ Hv") as %[n Hσl].
    iApply (wp_read_sc_pst with "[$Hσ]"); first done. iNext. iIntros "Hσ".
    iMod ("Hclose" with "[-Hv HΦ]"); last by iApply "HΦ".
    iNext. iExists σ, hF. iFrame. eauto.
  Qed.

  Lemma heap_read_vs σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    own heap_name (● to_heap σ) ∗ heap_mapsto_st (RSt n1) l q v
    ==∗ own heap_name (● to_heap (<[l:=(RSt (n2 + nf), v)]> σ))
        ∗ heap_mapsto_st (RSt n2) l q v.
  Proof.
    intros Hσv. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma wp_read_na E l q v :
    ↑heapN ⊆ E →
    {{{ heap_ctx ∗ ▷ l ↦{q} v }}} Read Na1Ord (Lit $ LitLoc l) @ E
    {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (??Φ) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iApply (wp_read_na1_pst E).
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup with "Hvalσ Hv") as %[n Hσl].
    iMod (heap_read_vs _ 0 1 with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod (fupd_intro_mask' (E∖↑heapN) ∅) as "Hclose'"; first set_solver.
    iModIntro. iExists σ, n, v. iFrame. iSplit; [done|]. iIntros "!> Hσ".
    iMod "Hclose'" as "_". iMod ("Hclose" with "[Hσ Hvalσ HhF]") as "_".
    { iNext. iExists _, _. iFrame. eauto using heap_freeable_rel_stable. }
    iModIntro. clear dependent n σ hF.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup with "Hvalσ Hv") as %[n Hσl].
    iApply (wp_read_na2_pst with "[$Hσ]"); first done. iNext. iIntros "Hσ".
    iMod (heap_read_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod ("Hclose" with "[-Hv HΦ]") as "_"; last by iApply "HΦ".
    iNext. iExists _, hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_vs σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own heap_name (● to_heap σ) ∗ heap_mapsto_st st1 l 1%Qp v
    ==∗ own heap_name (● to_heap (<[l:=(st2, v')]> σ))
        ∗ heap_mapsto_st st2 l 1%Qp v'.
  Proof.
    intros Hσv. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma wp_write_sc E l e v v' :
    ↑heapN ⊆ E → to_val e = Some v →
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Write ScOrd (Lit $ LitLoc l) e @ E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (? <-%of_to_val?) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iApply (wp_write_sc_pst with "[$Hσ]"); [done|]. iNext. iIntros "Hσ".
    iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod ("Hclose" with "[-Hv HΦ]") as "_"; last by iApply "HΦ".
    iNext. iExists _, hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma wp_write_na E l e v v' :
    ↑heapN ⊆ E → to_val e = Some v →
    {{{ heap_ctx ∗ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
    {{{ RET LitV LitUnit; l ↦ v }}}.
  Proof.
    iIntros (? <-%of_to_val?) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iApply (wp_write_na1_pst E).
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod (fupd_intro_mask' (E∖↑heapN) ∅) as "Hclose'"; first set_solver.
    iModIntro. iExists σ, v'. iSplit; [done|]. iIntros "{$Hσ} !> Hσ".
    iMod "Hclose'" as "_". iMod ("Hclose" with "[Hσ Hvalσ HhF]") as "_".
    { iNext. iExists _, _. iFrame. eauto using heap_freeable_rel_stable. }
    iModIntro. clear dependent σ hF.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iApply (wp_write_na2_pst with "[$Hσ]"); [done|]. iNext. iIntros "Hσ".
    iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod ("Hclose" with "[-Hv HΦ]"); last by iApply "HΦ".
    iNext. iExists _, hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma wp_cas_int_fail E l q z1 e2 lit2 zl :
    ↑heapN ⊆ E → to_val e2 = Some $ LitV lit2 → z1 ≠ zl →
    {{{ heap_ctx ∗ ▷ l ↦{q} (LitV $ LitInt zl) }}}
      CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
    {{{ RET LitV $ LitInt 0; l ↦{q} (LitV $ LitInt zl) }}}.
  Proof.
    iIntros (? <-%of_to_val ??) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup with "Hvalσ Hv") as %[n Hσl].
    iApply (wp_cas_pst with "[$Hσ]"); eauto.
    { right. by constructor. }
    { inversion 1. done. }
    iNext. iIntros ([|]).
    { iIntros "[Heq _]". iDestruct "Heq" as %Heq. inversion Heq. done. }
    iIntros "[_ Hσ]". iMod ("Hclose" with "[-Hv HΦ]") as "_"; last by iApply "HΦ".
    iNext. iExists _, hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma wp_cas_int_suc E l z1 e2 lit2 :
    ↑heapN ⊆ E → to_val e2 = Some $ LitV lit2 →
    {{{ heap_ctx ∗ ▷ l ↦ (LitV $ LitInt z1) }}}
      CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
    {{{ RET LitV $ LitInt 1; l ↦ LitV lit2 }}}.
  Proof.
    iIntros (? <-%of_to_val?) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iApply (wp_cas_pst with "[$Hσ]"); eauto.
    { left. by constructor. }
    iNext. iIntros ([|]); last first.
    { iIntros "[Hneq _]". iDestruct "Hneq" as %Hneq. inversion Hneq. done. }
    iIntros "[_ Hσ]". iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod ("Hclose" with "[-Hv HΦ]"); last by iApply "HΦ"; iFrame.
    iNext. iExists _, hF. iFrame. eauto using  heap_freeable_rel_stable.
  Qed.

  Lemma wp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
    ↑heapN ⊆ E → to_val e2 = Some $ LitV lit2 → l1 ≠ l' →
    {{{ heap_ctx ∗ ▷ l ↦{q} (LitV $ LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
      CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
    {{{ RET LitV $ LitInt 0;
        l ↦{q} (LitV $ LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
  Proof.
    iIntros (? <-%of_to_val ??) "(#Hinv & >Hl & >Hl' & >Hl1) HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup with "Hvalσ Hl") as %[n Hσl].
    iDestruct (heap_mapsto_lookup with "Hvalσ Hl'") as %[n' Hσl'].
    iDestruct (heap_mapsto_lookup with "Hvalσ Hl1") as %[n1 Hσl1].
    iApply (wp_cas_pst with "[$Hσ]"); eauto.
    { right. by constructor. }
    { inversion 1; subst; (by destruct (σ !! l1)) || by destruct (σ !! l'). }
    iNext. iIntros ([|]).
    { iIntros "[Heq _]". iDestruct "Heq" as %Heq. inversion Heq; subst.
      done. by destruct (σ !! l1). by destruct (σ !! l'). }
    iIntros "[_ Hσ]". iMod ("Hclose" with "[-Hl Hl' Hl1 HΦ]") as "_"; last by iApply "HΦ"; iFrame.
    iNext. iExists _, hF. by iFrame.
  Qed.

  Lemma wp_cas_loc_suc E l l1 e2 lit2 :
    ↑heapN ⊆ E → to_val e2 = Some $ LitV lit2 →
    {{{ heap_ctx ∗ ▷ l ↦ (LitV $ LitLoc l1) }}}
      CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
    {{{ RET LitV $ LitInt 1; l ↦ LitV lit2 }}}.
  Proof.
    iIntros (? <-%of_to_val?) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iApply (wp_cas_pst with "[$Hσ]"); eauto.
    { left. by constructor. }
    iNext. iIntros ([|]); last first.
    { iIntros "[Hneq _]". iDestruct "Hneq" as %Hneq. inversion Hneq. done. }
    iIntros "[_ Hσ]". iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
    iMod ("Hclose" with "[-Hv HΦ]"); last by iApply "HΦ"; iFrame.
    iNext. iExists _, hF. iFrame. eauto using  heap_freeable_rel_stable.
  Qed.

  Lemma wp_cas_loc_nondet E l l1 e2 l2 ll :
    ↑heapN ⊆ E → to_val e2 = Some $ LitV $ LitLoc l2 →
    {{{ heap_ctx ∗ ▷ l ↦ (LitV $ LitLoc ll) }}}
      CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
    {{{ b, RET LitV $ lit_of_bool b;
        if b is true then l ↦ LitV (LitLoc l2)
        else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
  Proof.
    iIntros (? <-%of_to_val?) "[#Hinv >Hv] HΦ".
    rewrite /heap_ctx /heap_inv heap_mapsto_eq /heap_mapsto_def.
    iInv heapN as (σ hF) ">(Hσ & Hvalσ & HhF & %)" "Hclose".
    iDestruct (heap_mapsto_lookup_1 with "Hvalσ Hv") as %?.
    iApply (wp_cas_pst with "[$Hσ]"); eauto.
    { destruct (decide (l1 = ll)) as [->|Hne].
      - left. by constructor.
      - right. by constructor. }
    iNext. iIntros ([|]).
    - iIntros "[_ Hσ]". iMod (heap_write_vs with "[$Hvalσ $Hv]") as "[Hvalσ Hv]"; first done.
      iMod ("Hclose" with "[-Hv HΦ]"); last by iApply "HΦ"; iFrame.
      iNext. iExists _, hF. iFrame. eauto using  heap_freeable_rel_stable.
    - iIntros "[Hneq Hσ]". iDestruct "Hneq" as %Hneq. inversion_clear Hneq.
      iMod ("Hclose" with "[-Hv HΦ]"); last by iApply ("HΦ" $! false); iFrame.
      iNext. iExists _, hF. iFrame. eauto using  heap_freeable_rel_stable.
  Qed.
End heap.
