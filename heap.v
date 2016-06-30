From lrust Require Export lifting.
From iris.algebra Require Import upred_big_op cmra_big_op frac dec_agree csum.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Import weakestpre invariants.
Import uPred.

Definition lock_stateR : cmraT := csumR (exclR unitC) natR.

Definition heapValUR : ucmraT :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (dec_agreeR val)).

Definition heapFreeUR : ucmraT :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitC))).

Class heapG Σ := HeapG {
  heapVal_inG :> authG lrust_lang Σ heapValUR;
  heapFree_inG :> authG lrust_lang Σ heapFreeUR;
  heapVal_name : gname;
  heapFree_name : gname
}.
Definition heapValGF : gFunctor := authGF heapValUR.
Definition heapFreeGF : gFunctor := authGF heapFreeUR.

Definition of_lock_state (x : lock_state) : lock_stateR :=
  match x with
  | RSt n => Cinr n
  | WSt => Cinl (Excl ())
  end.
Definition to_heapVal : state → heapValUR :=
  fmap (λ v, (1%Qp, of_lock_state (v.1), DecAgree (v.2))).
Definition heapFree_rel (σ : state) (heapFree : heapFreeUR) : Prop :=
  ∀ blk q s, heapFree !! blk = Some(q, s) →
  s ≠ ∅ ∧ ∀ i, is_Some (σ !! (blk, i)) ↔ is_Some (s !! i).

Section definitions.
  Context `{i : heapG Σ}.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iPropG lrust_lang Σ :=
    auth_own heapVal_name {[ l := (q, Cinr O, DecAgree v) ]}.
  Definition heap_mapsto_aux : { x | x = @heap_mapsto_def }. by eexists. Qed.
  Definition heap_mapsto := proj1_sig heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    proj2_sig heap_mapsto_aux.

  Definition heap_mapsto_vec (l : loc) (q : Qp) (vl : list val) :
    iPropG lrust_lang Σ :=
    ([★] imap (fun i v => heap_mapsto (shift_loc l i) q v) vl)%I.

  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitC) :=
    match n with
    | O => ∅
    | S n => <[i0 := Excl ()]>(inter (i0+1) n)
    end.
  Definition heap_freeable_def (l : loc) (q : Qp) (n: nat) : iPropG lrust_lang Σ :=
    auth_own heapFree_name {[ l.1 := (q, inter (l.2) n) ]}.
  Definition heap_freeable_aux : { x | x = @heap_freeable_def }. by eexists. Qed.
  Definition heap_freeable := proj1_sig heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    proj2_sig heap_freeable_aux.

  Definition heap_inv : iPropG lrust_lang Σ :=
    (∃ σ heapFree, ownP σ ★ own heapVal_name (● to_heapVal σ)
               ★ own heapFree_name (● heapFree) ★ ■ heapFree_rel σ heapFree)%I.
  Definition heap_ctx (N : namespace) := inv N heap_inv.

  Global Instance heap_ctx_persistent N : PersistentP (heap_ctx N).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque heap_ctx heap_mapsto heap_freeable.
Instance: Params (@heap_mapsto) 4.
Instance: Params (@heap_freeable) 5.
Instance: Params (@heap_ctx) 2.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l ↦{ q } v") : uPred_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : uPred_scope.

Notation "l ↦★{ q } vl" := (heap_mapsto_vec l q vl)
  (at level 20, q at level 50, format "l ↦★{ q }  vl") : uPred_scope.
Notation "l ↦★ vl" := (heap_mapsto_vec l 1 vl) (at level 20) : uPred_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : uPred_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : uPred_scope.

Section heap.
  Context {Σ : gFunctors}.
  Implicit Types N : namespace.
  Implicit Types P Q : iPropG lrust_lang Σ.
  Implicit Types Φ : val → iPropG lrust_lang Σ.
  Implicit Types σ : state.

  (** Allocation *)
  Lemma to_heap_valid σ : ✓ to_heapVal σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l)=>[[[|n] v]|]//=. Qed.
  Lemma heap_alloc N E σ :
    authG lrust_lang Σ heapValUR → authG lrust_lang Σ heapFreeUR →
    nclose N ⊆ E →
    ownP σ ={E}=> ∃ _ : heapG Σ, heap_ctx N.
  Proof.
    iIntros {???} "Hσ".
    iPvs (own_alloc (● to_heapVal σ)) as {vγ} "Hvγ".
    { split; last apply to_heap_valid. intro. apply ucmra_unit_leastN. }
    iPvs (own_alloc (● (∅ : heapFreeUR))) as {fγ} "Hfγ".
    { split. intro. apply ucmra_unit_leastN. apply ucmra_unit_valid. }
    set (HeapG _ _ _ vγ fγ). unfold heap_ctx. iExists _.
    iPvs (inv_alloc N E heap_inv with "[-]") as "HN"; try done.
    iNext. iExists _, _. iFrame. iPureIntro. intros ???. by rewrite lookup_empty.
  Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l↦{q}v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Global Instance heap_mapsto_vec_timeless l q vl : TimelessP (l ↦★{q} vl).
  Proof.
    unfold heap_mapsto_vec, imap. generalize O. induction vl=>/=; apply _.
  Qed.

  Lemma heap_mapsto_op_eq l q1 q2 v : l ↦{q1} v ★ l ↦{q2} v ⊣⊢ l ↦{q1+q2} v.
  Proof.
    by rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_idemp.
  Qed.

  Lemma heap_mapsto_vec_op_eq l q1 q2 vl :
    l ↦★{q1} vl ★ l ↦★{q2} vl ⊣⊢ l ↦★{q1+q2} vl.
  Proof.
    unfold heap_mapsto_vec, imap. generalize O. induction vl as [|v vl IH]=>/= n.
    - apply right_id, _.
    - rewrite -IH -heap_mapsto_op_eq equiv_spec.
      by split; iIntros "[[??][??]]"; iFrame.
  Qed.

  Lemma heap_mapsto_op l q1 q2 v1 v2 :
    l ↦{q1} v1 ★ l ↦{q2} v2 ⊣⊢ v1 = v2 ∧ l ↦{q1+q2} v1.
  Proof.
    destruct (decide (v1 = v2)) as [->|].
    { by rewrite heap_mapsto_op_eq pure_equiv // left_id. }
    rewrite heap_mapsto_eq -auth_own_op op_singleton pair_op dec_agree_ne //.
    apply (anti_symm (⊢)); last by apply pure_elim_l.
    rewrite auth_own_valid gmap_validI (forall_elim l) lookup_singleton.
    rewrite option_validI prod_validI !discrete_valid. by apply pure_elim_r.
  Qed.

  Lemma heap_mapsto_vec_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦★{q1} vl1 ★ l ↦★{q2} vl2 ⊣⊢ vl1 = vl2 ∧ l ↦★{q1+q2} vl1.
  Proof.
    unfold heap_mapsto_vec, imap. generalize O. revert vl2.
    induction vl1 as [|v1 vl1 IH]=>[][|v2 vl2]n/=; try done.
    - rewrite equiv_spec. split; iIntros; auto.
    - assert (∀ A B C D : iPropG lrust_lang Σ,
                 (A ★ B) ★ (C ★ D) ⊣⊢ (A ★ C) ★ (B ★ D)) as ->.
      { by intros; rewrite equiv_spec; split; iIntros "[[??][??]]"; iFrame. }
      intros [=?]. rewrite heap_mapsto_op IH // equiv_spec; split.
      + iIntros "[[%?][%?]]". subst. iSplit. auto. by iFrame.
      + iIntros "[#Heq[Hv Hvl]]". iDestruct "Heq" as %[=->->]. iSplitL "Hv"; auto.
  Qed.

  Lemma heap_mapsto_vec_app_op l q vl1 vl2 :
    l ↦★{q} vl1 ★ (shift_loc l (length vl1)) ↦★{q} vl2 ⊣⊢ l ↦★{q} (vl1++vl2).
  Proof.
    unfold heap_mapsto_vec, imap. generalize O. induction vl1 as [|v1 vl1 IH]=>n/=.
    - by rewrite left_id shift_loc_0.
    - rewrite -IH assoc. f_equiv. clear IH. revert n.
      induction vl2 as [|v2 vl2 IH]=>n //=.
      rewrite !shift_loc_assoc IH. apply reflexive_eq. repeat (lia||f_equal).
  Qed.

  Lemma heap_mapsto_op_split l q v : l ↦{q} v ⊣⊢ (l ↦{q/2} v ★ l ↦{q/2} v).
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  Lemma heap_mapsto_vec_op_split l q vl :
    l ↦★{q} vl ⊣⊢ (l ↦★{q/2} vl ★ l ↦★{q/2} vl).
  Proof. by rewrite heap_mapsto_vec_op_eq Qp_div_2. Qed.

  Lemma heap_mapsto_vec_auth l q vl:
    vl ≠ [] →
    l ↦★{q} vl ⊣⊢
      auth_own heapVal_name (big_op (imap
        (λ i v, {[shift_loc l i := (q, Cinr 0%nat, DecAgree v)]}) vl)).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def.
    revert l. induction vl as [|v vl IH]=>// l _. destruct (decide (vl = [])).
    - subst. simpl. by rewrite !right_id.
    - rewrite !imap_cons auth_own_op /=.
      erewrite imap_ext, (IH (shift_loc l 1)), imap_ext; [done| |done|];
        simpl; intros i v'; rewrite shift_loc_assoc; repeat f_equiv; lia.
  Qed.

  Lemma inter_lookup_Some i j (n:nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n=>/= i. lia. rewrite lookup_insert_Some.
    destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n=>/= i. by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n': inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intro j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n=>i. done. by apply insert_valid. Qed.

  Lemma heap_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ★ †{q2}(shift_loc l n)…n' ⊣⊢ †{q1+q2}(l)…(n+n').
  Proof.
    by rewrite heap_freeable_eq /heap_freeable_def -auth_own_op op_singleton
               pair_op inter_op.
  Qed.

  (** Weakest precondition *)
  Lemma init_mem_update_val σ l vl:
    (∀ m : Z, σ !! shift_loc l m = None) →
    ● to_heapVal σ ~~> ● to_heapVal (init_mem l vl σ)
      ⋅ ◯ big_op (imap
            (λ i v, {[shift_loc l i := (1%Qp, Cinr 0%nat, DecAgree v)]}) vl).
  Proof.
    revert l. induction vl as [|v vl IH]=> l FRESH.
    - simpl. rewrite right_id. reflexivity.
    - rewrite imap_cons. simpl. etrans. apply (IH (shift_loc l 1)).
      { intros. by rewrite shift_loc_assoc. }
      rewrite auth_frag_op assoc. apply cmra_update_op; last first.
      { erewrite imap_ext. reflexivity. move=>i x/=. rewrite shift_loc_assoc.
        f_equal. f_equal. lia. }
      assert (Hinit: (to_heapVal (init_mem (shift_loc l 1) vl σ)) !! l = None).
      { clear-FRESH. rewrite lookup_fmap fmap_None.
        cut (0 < 1); last lia. generalize 1. revert l FRESH.
        induction vl as [|v vl IH]=>/= l FRESH n Hn. by rewrite -(shift_loc_0 l).
        rewrite shift_loc_assoc lookup_insert_ne;
          [apply IH; auto; lia | destruct l; intros [=]; lia]. }
      rewrite -[X in X ~~> _]right_id -{1}[to_heapVal (init_mem _ _ _)]left_id
              shift_loc_0 /to_heapVal fmap_insert insert_singleton_op //.
        by apply auth_update, alloc_unit_singleton_local_update.
  Qed.

  Lemma fresh_block_heap_free σ l heapFree:
    (∀ m : Z, σ !! shift_loc l m = None) → heapFree_rel σ heapFree →
    heapFree !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some; intros [[q s] [=[Hsne REL']%REL]].
    destruct (map_choose s) as [i Hi%REL']; first done.
    specialize (FRESH (i-l.2)). rewrite /shift_loc Zplus_minus in FRESH.
    rewrite FRESH in Hi. by eapply is_Some_None.
  Qed.

  Lemma init_mem_update_free (l:loc) n heapFree σ:
    (∀ m : Z, σ !! shift_loc l m = None) → heapFree_rel σ heapFree →
    ● heapFree ~~>
      ● ({[l.1 := (1%Qp, inter (l.2) n)]} ⋅ heapFree) ⋅
      ◯ {[l.1 := (1%Qp, inter (l.2) n)]}.
  Proof.
    intros FRESH REL.
    etrans; last apply auth_update, alloc_unit_singleton_local_update.
    - rewrite right_id left_id. reflexivity.
    - simpl. eauto using fresh_block_heap_free.
    - split. done. apply inter_valid.
  Qed.

  Lemma init_mem_rel_free (l:loc) n heapFree vl σ:
    0 < n → heapFree_rel σ heapFree →
    (∀ m : Z, σ !! shift_loc l m = None) →
    n = Datatypes.length vl →
    heapFree_rel (init_mem l vl σ)
                 ({[l.1 := (1%Qp, inter (l.2) (Z.to_nat n))]} ⋅ heapFree).
  Proof.
    intros Hn REL FRESH Hlen blk q s. destruct (decide (l.1 = blk)) as [EQ|NEQ].
    - subst blk. rewrite lookup_op lookup_insert (fresh_block_heap_free σ)=>//.
      intros [=]. subst. rewrite Nat2Z.id. split.
      + destruct (List.length vl). lia. intros EQ%(f_equal (lookup (l.2))).
        by rewrite lookup_insert lookup_empty in EQ.
      + revert l FRESH. clear. induction vl as [|v vl IH]=>/=l FRESH i.
        * specialize (FRESH (i-l.2)). rewrite /shift_loc Zplus_minus in FRESH.
          rewrite lookup_empty FRESH. by split; intros []%is_Some_None.
        * rewrite !lookup_insert_is_Some IH /=;
                  last by intros; rewrite shift_loc_assoc.
          destruct l. simpl. split; intros [|[]]; naive_solver congruence.
    - rewrite lookup_op lookup_insert_ne // lookup_empty.
      specialize (REL blk). revert REL. case: (heapFree !! blk); last done.
      move=>? REL /REL [Hse Hs]. split. done. intros i. rewrite -Hs.
      clear -NEQ. revert l NEQ. induction vl as [|v vl IH]=>//= l NEQ.
      rewrite lookup_insert_is_Some IH //. naive_solver.
  Qed.

  Lemma wp_alloc N E (n:Z) Φ :
    nclose N ⊆ E → 0 < n →
    heap_ctx N ★
    ▷ (∀ l vl, l ↦★ vl ★ n = length vl ★ †l…(Z.to_nat n) -★ Φ (LitV $ LitLoc l))
    ⊢ WP Alloc (Lit $ LitInt n) @ E {{ Φ }}.
  Proof.
    iIntros {??} "[#Hinv HΦ]". rewrite /heap_ctx /heap_inv.
    iInv> N as "INV". iDestruct "INV" as {σ heapFree} "(Hσ&Hvalσ&Hfree&%)".
    iApply wp_pvs. iApply wp_alloc_pst =>//. iNext. iFrame "Hσ".
    iIntros {l σ'} "(%&#Hσσ'&Hσ')". iDestruct "Hσσ'" as %(vl&HvlLen&Hvl).
    iPvs (own_update _ (● to_heapVal σ) with "Hvalσ") as "[Hvalσ' Hmapsto]";
      first apply (init_mem_update_val _ l vl); auto.
    iPvs (own_update _ (● heapFree) with "Hfree") as "[Hfree' Hfreeable]";
      first apply (init_mem_update_free l (Z.to_nat n) heapFree σ); auto.
    iPvsIntro. iSplitL "Hσ' Hvalσ' Hfree'".
    - iExists σ', _. subst σ'. iFrame. iPureIntro. by apply init_mem_rel_free.
    - rewrite heap_freeable_eq /heap_freeable_def /auth_own. iApply "HΦ".
      iFrame. iSplit; last auto. rewrite heap_mapsto_vec_auth /auth_own //.
      destruct vl; simpl in *. lia. done.
  Qed.

End heap.
