From lrust Require Export lifting.
From iris.algebra Require Import upred_big_op cmra_big_op frac dec_agree csum.
From iris.program_logic Require Export invariants ghost_ownership.
From iris.program_logic Require Import ownership auth.
From iris.proofmode Require Export weakestpre invariants.
Import uPred.

Definition lock_stateR : cmraT := csumR (exclR unitC) natR.

Definition heapValUR : ucmraT :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (dec_agreeR val)).

Definition heapFreeableUR : ucmraT :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitC))).

Class heapG Σ := HeapG {
  heapVal_inG :> authG lrust_lang Σ heapValUR;
  heapFreeable_inG :> authG lrust_lang Σ heapFreeableUR;
  heapVal_name : gname;
  heapFreeable_name : gname
}.
Definition heapValGF : gFunctor := authGF heapValUR.
Definition heapFreeableGF : gFunctor := authGF heapFreeableUR.

Definition of_lock_state (x : lock_state) : lock_stateR :=
  match x with
  | RSt n => Cinr n
  | WSt => Cinl (Excl ())
  end.
Definition to_heapVal : state → heapValUR :=
  fmap (λ v, (1%Qp, of_lock_state (v.1), DecAgree (v.2))).
Definition heapFreeable_rel (σ : state) (hF : heapFreeableUR) : Prop :=
  ∀ blk qs, hF !! blk ≡ Some qs →
  qs.2 ≠ ∅ ∧ ∀ i, is_Some (σ !! (blk, i)) ↔ is_Some (qs.2 !! i).

Instance heapFreeable_rel_proper σ : Proper ((≡) ==> (↔)) (heapFreeable_rel σ).
Proof.
  intros x y Hxy. unfold heapFreeable_rel. split; intros H blk qs.
  rewrite -Hxy. apply H. rewrite Hxy. apply H.
Qed.

Section definitions.
  Context `{i : heapG Σ}.

  Definition heap_mapsto_st (st : lock_state)
             (l : loc) (q : Qp) (v: val) : iPropG lrust_lang Σ :=
    auth_own heapVal_name {[ l := (q, of_lock_state st, DecAgree v) ]}.
  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iPropG lrust_lang Σ :=
    heap_mapsto_st (RSt 0) l q v.
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
    auth_own heapFreeable_name {[ l.1 := (q, inter (l.2) n) ]}.
  Definition heap_freeable_aux : { x | x = @heap_freeable_def }. by eexists. Qed.
  Definition heap_freeable := proj1_sig heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    proj2_sig heap_freeable_aux.

  Definition heap_inv : iPropG lrust_lang Σ :=
    (∃ (σ:state) hF, ownP σ ★ own heapVal_name (● to_heapVal σ)
                            ★ own heapFreeable_name (● hF)
                            ★ ■ heapFreeable_rel σ hF)%I.
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
    authG lrust_lang Σ heapValUR → authG lrust_lang Σ heapFreeableUR →
    nclose N ⊆ E →
    ownP σ ={E}=> ∃ _ : heapG Σ, heap_ctx N.
  Proof.
    iIntros (???) "Hσ".
    iPvs (own_alloc (● to_heapVal σ)) as (vγ) "Hvγ".
    { split; last apply to_heap_valid. intro. apply ucmra_unit_leastN. }
    iPvs (own_alloc (● (∅ : heapFreeableUR))) as (fγ) "Hfγ".
    { split. intro. apply ucmra_unit_leastN. apply ucmra_unit_valid. }
    set (HeapG _ _ _ vγ fγ). unfold heap_ctx. iExists _.
    iPvs (inv_alloc N E heap_inv with "[-]") as "HN"; try done.
    iNext. iExists _, _. iFrame. iPureIntro. intros ??. rewrite lookup_empty.
    inversion 1.
  Qed.

  Context `{heapG Σ}.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l q v : TimelessP (l↦{q}v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Global Instance heap_mapsto_vec_timeless l q vl : TimelessP (l ↦★{q} vl).
  Proof.
    unfold heap_mapsto_vec, imap. generalize O. induction vl=>/=; apply _.
  Qed.

  Global Instance heap_freeable_timeless q l n : TimelessP (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

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

  Lemma heap_mapsto_vec_singleton l q v :
    l ↦★{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /heap_mapsto_vec /= right_id shift_loc_0. Qed.

  Lemma heap_mapsto_vec_cons_op l q v vl:
    l ↦{q} v ★ (shift_loc l 1) ↦★{q} vl ⊣⊢ l ↦★{q} (v::vl).
  Proof.
    by rewrite -(heap_mapsto_vec_app_op l q [v] vl) heap_mapsto_vec_singleton.
  Qed.

  Lemma heap_mapsto_op_split l q v : l ↦{q} v ⊣⊢ (l ↦{q/2} v ★ l ↦{q/2} v).
  Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

  Lemma heap_mapsto_vec_op_split l q vl :
    l ↦★{q} vl ⊣⊢ (l ↦★{q/2} vl ★ l ↦★{q/2} vl).
  Proof. by rewrite heap_mapsto_vec_op_eq Qp_div_2. Qed.

  Lemma heap_mapsto_vec_combine l q vl:
    l ↦★{q} vl ⊣⊢
      vl = [] ∨
      auth_own heapVal_name (big_op (imap
        (λ i v, {[shift_loc l i := (q, Cinr 0%nat, DecAgree v)]}) vl)).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def.
    revert l. induction vl as [|v vl IH]=>l.
    { apply equiv_spec. simpl. split; iIntros; auto. }
    assert (v :: vl = [] ⊣⊢ (False:iPropG lrust_lang Σ)) as ->.
    { apply equiv_spec; split; iIntros "%"; done. }
    rewrite left_id !imap_cons /=. destruct (decide (vl = [])).
    { subst. by rewrite !right_id. }
    erewrite auth_own_op, imap_ext, (IH (shift_loc l 1)), imap_ext.
    - assert (vl = [] ⊣⊢ (False:iPropG lrust_lang Σ)) as ->.
      { apply equiv_spec; split; iIntros "%"; done. }
        by rewrite left_id.
    - intros. rewrite shift_loc_assoc /=. repeat f_equiv; lia.
    - intros. simpl. rewrite shift_loc_assoc. repeat f_equal; lia.
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

  (** Properties about heapFreeable_rel and heapFreeable *)
  Lemma fresh_heapFreeable_None σ l h:
    (∀ m : Z, σ !! shift_loc l m = None) → heapFreeable_rel σ h →
    h !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] Hqs].
    apply (reflexive_eq (R:=equiv)), REL in Hqs. destruct Hqs as [Hsne REL'].
    destruct (map_choose s) as [i Hi%REL']; first done.
    specialize (FRESH (i-l.2)). rewrite /shift_loc Zplus_minus in FRESH.
    rewrite FRESH in Hi. by eapply is_Some_None.
  Qed.

  Lemma valid_heapFreeable_None blk s (h : heapFreeableUR):
    ✓ ({[blk := (1%Qp, s)]} ⋅ h) → h !! blk = None.
  Proof.
    intros Hv. specialize (Hv blk). revert Hv.
    rewrite lookup_op lookup_insert cmra_valid_validN.
    intros Hv. specialize (Hv O). apply exclusiveN_Some_l in Hv. done. apply _.
  Qed.

  Lemma valid_heapFreeable_is_Some σ l n h:
    heapFreeable_rel σ ({[l.1 := (1%Qp, inter (l.2) n)]} ⋅ h) →
    ✓ ({[l.1 := (1%Qp, inter (l.2) n)]} ⋅ h) →
    ∀ m : Z, is_Some (σ !! shift_loc l m) ↔ 0 ≤ m ∧ m < n.
  Proof.
    intros REL FREED%valid_heapFreeable_None m. unfold shift_loc.
    edestruct (REL (l.1)) as [_ ->].
      by rewrite -insert_singleton_op // lookup_insert.
    destruct (decide (0 ≤ m ∧ m < n)).
    - rewrite inter_lookup_Some; last lia. naive_solver.
    - rewrite inter_lookup_None; last lia.
      split. intros []%is_Some_None. naive_solver.
  Qed.

  Lemma heapFreeable_rel_stable σ h l p :
    heapFreeable_rel σ h → is_Some (σ !! l) →
    heapFreeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split. done. intro i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.

  (** Weakest precondition *)
  Lemma init_mem_update_val σ l vl:
    (∀ m : Z, σ !! shift_loc l m = None) →
    ● to_heapVal σ ~~>
    ● to_heapVal (init_mem l vl σ)
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

  Lemma heapFreeable_init_mem_update l n h σ:
    (∀ m : Z, σ !! shift_loc l m = None) → heapFreeable_rel σ h →
    ● h ~~>
    ● ({[l.1 := (1%Qp, inter (l.2) n)]}⋅h)⋅◯ {[l.1 := (1%Qp, inter (l.2) n)]}.
  Proof.
    intros FRESH REL.
    etrans; last apply auth_update, alloc_unit_singleton_local_update.
    - rewrite right_id left_id. reflexivity.
    - simpl. eauto using fresh_heapFreeable_None.
    - split. done. apply inter_valid.
  Qed.

  Lemma heapFreeable_rel_init_mem l h vl σ:
    vl ≠ [] → (∀ m : Z, σ !! shift_loc l m = None) →
    heapFreeable_rel σ h →
    heapFreeable_rel (init_mem l vl σ)
                     ({[l.1 := (1%Qp, inter (l.2) (length vl))]} ⋅ h).
  Proof.
    intros Hvlnil FRESH REL blk qs. destruct (decide (l.1 = blk)) as [|NEQ].
    - subst.
      rewrite lookup_op lookup_insert (fresh_heapFreeable_None σ) //.
      inversion 1. subst. split.
      + destruct vl. done.
        intros EQ%(f_equal (lookup (l.2)))%(reflexive_eq (R:=equiv)).
        setoid_subst. rewrite lookup_insert lookup_empty in EQ. inversion EQ.
      + setoid_subst. clear -FRESH. revert l FRESH. induction vl as [|v vl IH]=>/=l FRESH i.
        * specialize (FRESH (i-l.2)). rewrite /shift_loc Zplus_minus in FRESH.
          rewrite lookup_empty FRESH. by split; intros []%is_Some_None.
        * rewrite !lookup_insert_is_Some IH /=;
                  last by intros; rewrite shift_loc_assoc.
          destruct l. simpl. split; intros [|[]]; naive_solver congruence.
    - rewrite lookup_op lookup_insert_ne // lookup_empty.
      specialize (REL blk). revert REL. case: (h !! blk); last inversion 2.
      move=>? REL /REL [Hse Hs]. split. done. intros i. rewrite -Hs.
      clear -NEQ. revert l NEQ. induction vl as [|v vl IH]=>//= l NEQ.
      rewrite lookup_insert_is_Some IH //. naive_solver.
  Qed.

  Lemma wp_alloc N E n Φ :
    nclose N ⊆ E → 0 < n →
    heap_ctx N ★
    ▷ (∀ l vl, n = length vl ★ †l…(Z.to_nat n) ★ l ↦★ vl ={E}=★ Φ (LitV $ LitLoc l))
    ⊢ WP Alloc (Lit $ LitInt n) @ E {{ Φ }}.
  Proof.
    iIntros (??) "[#Hinv HΦ]". rewrite /heap_ctx /heap_inv. iApply wp_pvs.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)". iApply wp_alloc_pst =>//. iFrame "Hσ".
    iNext. iIntros (l σ') "(%&#Hσσ'&Hσ')". iDestruct "Hσσ'" as %(vl&HvlLen&Hvl).
    iPvs (own_update _ (● to_heapVal σ) with "Hvalσ") as "[Hvalσ' Hmapsto]";
      first apply (init_mem_update_val _ l vl); auto.
    iPvs (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]";
      first apply (heapFreeable_init_mem_update l (Z.to_nat n) hF σ); auto.
    iPvsIntro. iSplitL "Hσ' Hvalσ' HhF".
    - iExists σ', _. subst σ'. iFrame. iPureIntro.
      subst. rewrite Nat2Z.id. apply heapFreeable_rel_init_mem; try done.
        by destruct vl.
    - rewrite heap_freeable_eq /heap_freeable_def /auth_own. iApply "HΦ".
      iSplit; first auto. iFrame. rewrite heap_mapsto_vec_combine /auth_own. auto.
  Qed.

  Lemma heapFreeable_rel_free_mem σ n h l s:
    ✓ ({[l.1 := (1%Qp, s)]} ⋅ h) →
    heapFreeable_rel σ ({[l.1 := (1%Qp, s)]} ⋅ h) →
    heapFreeable_rel (free_mem l n σ) h.
  Proof.
    intros FREED%valid_heapFreeable_None REL blk qs'.
    destruct (decide (blk = l.1)) as [|NEQ].
    - subst. rewrite FREED. inversion 1.
    - intros Hqs'. specialize (REL blk qs').
      revert REL. rewrite -insert_singleton_op // lookup_insert_ne=>//REL.
      destruct (REL Hqs') as [? REL']. split. done. intro i. rewrite -REL'.
      clear- NEQ. revert l NEQ. induction n as [|n IH]=>//= l NEQ.
      rewrite lookup_delete_is_Some IH //. naive_solver.
  Qed.

  Lemma free_mem_heapVal_pvs l vl σ E :
    vl ≠ [] →
    l ↦★ vl ★ own heapVal_name (● to_heapVal σ)
    ⊢ |={E}=> own heapVal_name (● to_heapVal (free_mem l (length vl) σ)).
  Proof.
    iIntros (Hvlnil) "[Hvl Hσ]". rewrite heap_mapsto_vec_combine /auth_own.
    iDestruct "Hvl" as "[%|Hvl]"; first done. iCombine "Hvl" "Hσ" as "Hσ".
    iApply (own_update _ _ (● to_heapVal _) with "Hσ"). clear. revert l.
    induction vl as [|v vl IH]=>l. by rewrite left_id.
    rewrite imap_cons /= auth_frag_op -assoc. etrans.
    - apply cmra_update_op. reflexivity. erewrite imap_ext. apply (IH (shift_loc l 1)).
      move=> i x /=. rewrite shift_loc_assoc. repeat f_equiv. lia.
    - clear IH. unfold to_heapVal. rewrite fmap_delete.
      apply cmra_update_valid0. intros [[f Hf%timeless] Hv]; last apply _.
      revert Hf Hv. rewrite shift_loc_0 right_id =>/= Hf. rewrite {1 2}Hf=>Hv.

      (* FIXME : make "rewrite Hf" work. *)
      eapply cmra_update_proper. reflexivity.
      apply Auth_proper, reflexivity. apply Some_proper, Excl_proper.
      rewrite Hf. reflexivity.

      rewrite comm. etrans. eapply auth_update, (delete_local_update _ l).
      2:rewrite lookup_insert //. apply _.

      assert (f !! l = None). {
        specialize (Hv l). rewrite lookup_op lookup_singleton in Hv.
        revert Hv. case: (f !! l) => //= ? /(exclusiveN_l _ (_, _, _)) //.
      }
      by rewrite -insert_singleton_op // delete_singleton delete_insert // right_id left_id.
  Qed.

  Lemma wp_free N E (n:Z) l vl Φ :
    nclose N ⊆ E →
    n = length vl →
    heap_ctx N ★ l ↦★ vl ★ †l…(length vl) ★
    ▷ (|={E}=> Φ (LitV LitUnit))
    ⊢ WP Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E {{ Φ }}.
  Proof.
    iIntros (??) "(#Hinv&Hmt&Hf&HΦ)". rewrite /heap_ctx /heap_inv. iApply wp_pvs.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&REL)". iDestruct "REL" as %REL.
    rewrite heap_freeable_eq /heap_freeable_def /auth_own.
    iCombine "Hf" "HhF" as "HhF". iDestruct (own_valid _ with "#HhF") as "Hfvalid".
    rewrite auth_validI /=. iDestruct "Hfvalid" as "[Hfle Hfvalid]".
    iDestruct "Hfle" as (frameF) "Hfle". rewrite right_id. iDestruct "Hfle" as "%".
    setoid_subst. iDestruct "Hfvalid" as %Hfvalid.
    assert (vl ≠ []).
    { destruct (REL (l.1) (1%Qp, inter(l.2) (length vl))) as [EQnil ?].
      rewrite -insert_singleton_op // ?lookup_insert //.
      eauto using valid_heapFreeable_None. intro. subst. done. }
    iApply (wp_free_pst _ σ). by destruct vl. by eapply valid_heapFreeable_is_Some.
    iFrame. iIntros "> Hσ'". iFrame. iExists _, frameF. iFrame.
    rewrite Nat2Z.id. iSplitL "Hvalσ Hmt"; last iSplitR "".
    - iApply free_mem_heapVal_pvs. done. iFrame. done.
    - iApply (own_update _ _ (● frameF) with "HhF"). rewrite comm.
      etrans. eapply auth_update, (delete_local_update _ (l.1)).
      2:rewrite lookup_insert//. apply _.
      by rewrite delete_insert ?right_id ?left_id ?lookup_empty.
    - iPureIntro. eauto using heapFreeable_rel_free_mem.
  Qed.

  Lemma mapsto_heapVal_lookup l ls q v σ:
    let globst n' :=
        match ls with
        | RSt n => RSt (n+n')
        | WSt => WSt
        end
    in
    auth_own heapVal_name {[ l := (q, of_lock_state ls, DecAgree v) ]} ★
    own heapVal_name (● to_heapVal σ)
    ⊢ ■ ∃ (n':nat), σ !! l = Some (globst n', v) ∧ (q = 1%Qp → n' = O).
  Proof.
    iIntros (globst) "(Hv&Hσ)". rewrite /auth_own /globst.
    iCombine "Hv" "Hσ" as "Hσ".
    iDestruct (own_valid (A:=authR heapValUR) with "Hσ") as "#Hσ".
    iDestruct "Hσ" as %Hσ. iPureIntro. case: Hσ=>[Hσ _]. specialize (Hσ O).
    destruct Hσ as [f Hσ]. specialize (Hσ l). revert Hσ. simpl.
    rewrite right_id !lookup_op lookup_fmap lookup_singleton.
    case:(σ !! l)=>[[ls' v']|]; case:(f !! l)=>[[[q' ls''] v'']|]; try by inversion 1.
    - inversion 1 as [?? EQ|]. subst. destruct EQ as [[EQ1 EQ2] EQ3].
      destruct v'' as [v''|]; last by inversion EQ3. simpl in EQ3.
      destruct (decide (v = v'')) as [|NE]; last by rewrite dec_agree_ne in EQ3.
      subst. rewrite dec_agree_idemp in EQ3. inversion EQ3. subst.
      destruct ls as [|n], ls' as [|n'], ls'' as [|n''|];
        try by inversion EQ2. by eauto.
      inversion EQ2. exists n''. split. by repeat f_equal.
      intros ?. subst. destruct (exclusive_l 1%Qp q'). simpl in EQ1.
      rewrite -EQ1. done.
    - inversion 1 as [?? EQ|]. subst. destruct EQ as [[EQ1 EQ2] EQ3].
      inversion EQ3. destruct ls as [|n], ls' as [|n']; inversion EQ2. by eauto.
      exists O. rewrite -plus_n_O. split. by repeat f_equal. done.
  Qed.

  Lemma wp_read_sc N E l q v Φ :
    nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Read ScOrd (Lit $ LitLoc l) @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv&Hv&HΦ)". iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) q v σ with "[#]") as %(n&Hσl&_).
      by iFrame.
    iApply wp_read_sc_pst. by apply Hσl. iFrame. iIntros ">Hσ".
    iSplitR "Hv HΦ"; last by iApply "HΦ".
    iExists σ, hF. iFrame. iPureIntro. rewrite -(insert_id σ l (RSt n, v)) //.
    apply heapFreeable_rel_stable; try done. eauto.
  Qed.

  Lemma read_pvs E σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    own heapVal_name (● to_heapVal σ) ★ heap_mapsto_st (RSt n1) l q v
    ⊢ |={E}=> own heapVal_name (● to_heapVal (<[l:=(RSt (n2 + nf), v)]> σ))
              ★ heap_mapsto_st (RSt n2) l q v.
  Proof.
    rewrite -!own_op. intros Hσv.
    apply own_update, cmra_update_valid0. intros [[f EQf]_].
    revert EQf. rewrite left_id /= => EQf. apply timeless in EQf; last apply _.
    assert (EQfi: to_heapVal (<[l:=(RSt (n2 + nf), v)]>σ)
                             ≡ {[l := (q, Cinr n2%nat, DecAgree v)]} ⋅ f).
    { intros l'. specialize (EQf l'). revert EQf. rewrite !lookup_op !lookup_fmap.
      destruct (decide (l = l')); last by rewrite !lookup_insert_ne.
      subst. rewrite Hσv !lookup_singleton lookup_insert /=.
      case: (f !! l') =>[[[q' ls] v']|]; inversion 1 as [?? EQ|]; subst;
        repeat constructor; try apply EQ; apply proj1, proj2 in EQ;
        [destruct ls as [|n'|]|]; inversion EQ as [|?? EQ'|]; subst;
      (* FIXME : constructor and apply do not work. *)
      refine (Cinlr_equiv _ _ _).
        by apply Nat.add_cancel_l in EQ'; subst.
        destruct nf. by rewrite Nat.add_0_r. inversion EQ'; lia. }
    rewrite EQf EQfi. apply auth_update, singleton_local_update.
    repeat apply prod_local_update=> //=. apply csum_local_update_r.
    intros. apply nat_local_update.
  Qed.

  Lemma wp_read_na2 N E l q v Φ :
    nclose N ⊆ E →
    heap_ctx N ★ heap_mapsto_st (RSt 1) l q v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Read Na2Ord (Lit $ LitLoc l) @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv&Hv&HΦ)". iApply wp_pvs.
    rewrite /heap_ctx /heap_inv /auth_own. iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 1) q v σ with "[#]") as %(n&Hσl&_).
      by iFrame.
    iApply wp_read_na2_pst. by apply Hσl. iFrame. iIntros ">Hσ".
    iPvs (read_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". by apply Hσl. by iFrame.
    iSplitR "Hv HΦ"; last by rewrite heap_mapsto_eq; iApply "HΦ".
    iExists _, hF. iFrame. iPureIntro.
    apply heapFreeable_rel_stable; try done. eauto.
  Qed.

  Lemma wp_read_na N E l q v Φ :
    nclose N ⊆ E →
    heap_ctx N ★ ▷ l ↦{q} v ★ ▷ (l ↦{q} v ={E}=★ Φ v)
    ⊢ WP Read Na1Ord (Lit $ LitLoc l) @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hinv&Hv&HΦ)". iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own.
    iDestruct (inv_open E N _ with "Hinv") as (E') "[% Hinvpvs]"; first done.
    iApply (wp_read_na1_pst E E'). by set_solver.
    iPvs "Hinvpvs" as "[INV Hclose]". by set_solver. iTimeless "INV".
    iDestruct "INV" as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) q v σ with "[#]") as %(n&Hσl&_).
      by rewrite heap_mapsto_eq; iFrame.
    iPvs (read_pvs _ _ 0 1 with "[Hvalσ Hv]") as "[Hvalσ Hv]". by apply Hσl.
      by rewrite heap_mapsto_eq; iFrame.
    iPvsIntro. iExists σ, n, v. iSplit. done. iFrame. iIntros ">Hσ".
    iPvs ("Hclose" with "[Hσ Hvalσ HhF]"); [|set_solver|].
    - iNext. iExists _, _. iFrame. iPureIntro. eauto using heapFreeable_rel_stable.
    - iPvsIntro. iApply (wp_read_na2 N). set_solver. iSplit.
      unfold heap_ctx, heap_inv. iApply "Hinv". iFrame. iIntros ">Hlv". by iApply "HΦ".
  Qed.

  Lemma write_pvs E σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own heapVal_name (● to_heapVal σ) ★ heap_mapsto_st st1 l 1%Qp v
    ⊢ |={E}=> own heapVal_name (● to_heapVal (<[l:=(st2, v')]> σ))
              ★ heap_mapsto_st st2 l 1%Qp v'.
  Proof.
    rewrite -!own_op. intros Hσv.
    apply own_update, cmra_update_valid0. intros [[f EQf]_].
    revert EQf. rewrite left_id /= => EQf. apply timeless in EQf; last apply _.
    assert (EQfi: to_heapVal (<[l:=(st2, v')]>σ)
                             ≡ {[l := (1%Qp, of_lock_state st2, DecAgree v')]} ⋅ f).
    { intros l'. specialize (EQf l'). revert EQf. rewrite !lookup_op !lookup_fmap.
      destruct (decide (l = l')); last by rewrite !lookup_insert_ne.
      subst. rewrite Hσv !lookup_singleton lookup_insert /=.
      case: (f !! l') =>[[[q' ls] v'']|]; inversion 1 as [?? EQ|]; subst; last done.
      destruct (exclusive_l (1%Qp, of_lock_state st1, DecAgree v) (q', ls, v'')).
      rewrite - EQ. destruct st1; done. }
    rewrite EQf EQfi.
    apply auth_update, singleton_local_update, exclusive_local_update.
    destruct st2; done.
  Qed.

  Lemma wp_write_sc N E l e v v' Φ :
    nclose N ⊆ E → to_val e = Some v →
    heap_ctx N ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Write ScOrd (Lit $ LitLoc l) e @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val) "(#Hinv&Hv&HΦ)". iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) 1 v' σ with "[#]") as %(n&Hσl&EQ).
      by iFrame.
    specialize (EQ (reflexivity _)). subst.
    iApply wp_write_sc_pst; try done. iFrame. iIntros ">Hσ".
    iPvs (write_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". done. by iFrame.
    iSplitR "Hv HΦ"; last by iApply "HΦ". iExists _, hF. iFrame. iPureIntro.
    apply heapFreeable_rel_stable; try done. eauto.
  Qed.

  Lemma wp_write_na2 N E l e v v' Φ :
    nclose N ⊆ E → to_val e = Some v →
    heap_ctx N ★ heap_mapsto_st WSt l 1%Qp v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Write Na2Ord (Lit $ LitLoc l) e @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val) "(#Hinv&Hv&HΦ)". iApply wp_pvs.
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l WSt 1 v' σ with "[#]") as %(n&Hσl&EQ).
      by iFrame.
    specialize (EQ (reflexivity _)). subst.
    iApply wp_write_na2_pst. done. iFrame. iIntros ">Hσ".
    iPvs (write_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". done. by iFrame.
    iSplitR "Hv HΦ"; last by iApply "HΦ". iExists _, hF. iFrame. iPureIntro.
    apply heapFreeable_rel_stable; try done. eauto.
  Qed.

  Lemma wp_write_na N E l e v v' Φ :
    nclose N ⊆ E → to_val e = Some v →
    heap_ctx N ★ ▷ l ↦ v' ★ ▷ (l ↦ v ={E}=★ Φ (LitV LitUnit))
    ⊢ WP Write Na1Ord (Lit $ LitLoc l) e @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val) "(#Hinv&Hv&HΦ)". iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own.
    iDestruct (inv_open E N _ with "Hinv") as (E') "[% Hinvpvs]"; first done.
    iApply (wp_write_na1_pst E E'). by set_solver.
    iPvs "Hinvpvs" as "[INV Hclose]". by set_solver. iTimeless "INV".
    iDestruct "INV" as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) 1 v' σ with "[#]") as %(n&Hσl&EQ).
      by rewrite heap_mapsto_eq; iFrame.
    specialize (EQ (reflexivity _)). subst.
    iPvs (write_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". done.
      by rewrite heap_mapsto_eq; iFrame.
    iPvsIntro. iExists σ, v'. iSplit. done. iFrame. iIntros ">Hσ".
    iPvs ("Hclose" with "[Hσ Hvalσ HhF]"); [|set_solver|].
    - iNext. iExists _, _. iFrame. iPureIntro. eauto using heapFreeable_rel_stable.
    - iPvsIntro. iApply (wp_write_na2 N). set_solver. apply to_of_val. iFrame.
      iSplit. unfold heap_ctx, heap_inv. iApply "Hinv". iIntros ">Hlv". by iApply "HΦ".
  Qed.

  Lemma wp_cas_int_fail N E l q z1 e2 v2 zl Φ :
    nclose N ⊆ E → to_val e2 = Some v2 → z1 ≠ zl →
    heap_ctx N ★ ▷ l ↦{q} (LitV $ LitInt zl)
               ★ ▷ (l ↦{q} (LitV $ LitInt zl) ={E}=★ Φ (LitV $ LitInt 0))
    ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val ?) "(#Hinv&Hv&HΦ)". iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) q with "[#]") as %(n&Hσl&_). by iFrame.
    iApply wp_cas_fail_pst; eauto. by rewrite /= bool_decide_false.
    iFrame. iIntros ">Hσ". iSplitR "Hv HΦ"; last by iApply "HΦ".
    iExists _, hF. by iFrame.
  Qed.

  Lemma wp_cas_loc_fail N E l q q' q1 l1 v1' e2 v2 l' vl' Φ :
    nclose N ⊆ E → to_val e2 = Some v2 → l1 ≠ l' →
    heap_ctx N ★ ▷ l ↦{q} (LitV $ LitLoc l') ★ ▷ l' ↦{q'} vl' ★ ▷ l1 ↦{q1} v1'
               ★ ▷ (l ↦{q} (LitV $ LitLoc l') ★ l' ↦{q'} vl' ★ l1 ↦{q1} v1'
                    ={E}=★ Φ (LitV $ LitInt 0))
    ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val ?) "(#Hinv&Hl&Hl'&Hl1&HΦ)". subst. iApply wp_pvs.
    iTimeless "Hl". iTimeless "Hl'". iTimeless "Hl1".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) q with "[#]") as %(n&Hσl&_). by iFrame.
    iDestruct (mapsto_heapVal_lookup l' (RSt 0) q' with "[#]") as %(n'&Hσl'&_). by iFrame.
    iDestruct (mapsto_heapVal_lookup l1 (RSt 0) q1 with "[#]") as %(n1&Hσl1&_). by iFrame.
    iApply wp_cas_fail_pst; eauto. by rewrite /= bool_decide_false // Hσl1 Hσl'.
    iFrame. iIntros ">Hσ". iSplitR "Hl Hl' Hl1 HΦ"; last by iApply "HΦ"; iFrame.
    iExists _, hF. by iFrame.
  Qed.

  Lemma wp_cas_int_suc N E l z1 e2 v2 Φ :
    nclose N ⊆ E → to_val e2 = Some v2 →
    heap_ctx N ★ ▷ l ↦ (LitV $ LitInt z1)
               ★ ▷ (l ↦ v2 ={E}=★ Φ (LitV $ LitInt 1))
    ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val) "(#Hinv&Hv&HΦ)". subst. iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) 1 with "[#]") as %(n&Hσl&EQ).
      by iFrame. rewrite EQ // in Hσl.
    iApply wp_cas_suc_pst; eauto. by rewrite /= bool_decide_true.
    iFrame. iIntros ">Hσ".
    iPvs (write_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". done. by iFrame.
    iSplitR "Hv HΦ"; last by iApply "HΦ". iExists _, hF. iFrame.
    iPureIntro. eauto using  heapFreeable_rel_stable.
  Qed.

  Lemma wp_cas_loc_suc N E l l1 e2 v2 Φ :
    nclose N ⊆ E → to_val e2 = Some v2 →
    heap_ctx N ★ ▷ l ↦ (LitV $ LitLoc l1)
               ★ ▷ (l ↦ v2 ={E}=★ Φ (LitV $ LitInt 1))
    ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E {{ Φ }}.
  Proof.
    iIntros (? <-%of_to_val) "(#Hinv&Hv&HΦ)". subst. iApply wp_pvs. iTimeless "Hv".
    rewrite /heap_ctx /heap_inv /auth_own heap_mapsto_eq /heap_mapsto_def.
    iInv> N as (σ hF) "(Hσ&Hvalσ&HhF&%)".
    iDestruct (mapsto_heapVal_lookup l (RSt 0) 1 with "[#]") as %(n&Hσl&EQ).
      by iFrame. rewrite EQ // in Hσl.
    iApply wp_cas_suc_pst; eauto. by rewrite /= bool_decide_true.
    iFrame. iIntros ">Hσ".
    iPvs (write_pvs with "[Hvalσ Hv]") as "[Hvalσ Hv]". done. by iFrame.
    iSplitR "Hv HΦ"; last by iApply "HΦ". iExists _, hF. iFrame.
    iPureIntro. eauto using  heapFreeable_rel_stable.
  Qed.

End heap.
