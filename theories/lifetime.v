From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.prelude Require Import gmultiset.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import boxes.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
Import uPred.

Definition lftN : namespace := nroot .@ "lft".
Definition borN : namespace := lftN .@ "bor".
Definition inhN : namespace := lftN .@ "inh".
Definition mgmtN : namespace := lftN .@ "mgmt".

Definition atomic_lft := positive.
Notation lft := (gmultiset positive).
Definition static : lft := ∅.

Inductive bor_state :=
  | Bor_in
  | Bor_open (q : frac)
  | Bor_rebor (κ : lft).
Instance bor_state_eq_dec : EqDecision bor_state.
Proof. solve_decision. Defined.

Definition bor_filled (s : bor_state) : bool :=
  match s with Bor_in => true | _ => false end.

Definition lft_stateR := csumR fracR unitR.
Definition to_lft_stateR (b : bool) : lft_stateR :=
  if b then Cinl 1%Qp else Cinr ().

Record lft_names := LftNames {
  bor_name : gname;
  cnt_name : gname;
  inh_name : gname
}.
Instance lft_names_eq_dec : EqDecision lft_names.
Proof. solve_decision. Defined.

Class lftG Σ := LftG {
  lft_box :> boxG Σ;
  lft_atomic_inG :> inG Σ (authR (gmapUR atomic_lft lft_stateR));
  lft_atomic_name : gname;
  lft_inter_inG :> inG Σ (authR (gmapUR lft (dec_agreeR lft_names)));
  lft_inter_name : gname;
  lft_bor_box :>
    inG Σ (authR (gmapUR slice_name (prodR fracR (dec_agreeR bor_state))));
  lft_cnt_inG :> inG Σ (authR natUR);
  lft_inh_box :> inG Σ (authR (gset_disjUR slice_name));
}.

Section defs.
  Context `{invG Σ, lftG Σ}.

  Definition lft_own (q : Qp) (κ : lft) : iProp Σ :=
    ([∗ mset] Λ ∈ κ, own lft_atomic_name (◯ {[ Λ := Cinl q ]}))%I.

  Definition lft_dead_own (κ : lft) : iProp Σ :=
    (∃ Λ, ⌜Λ ∈ κ⌝ ∗ own lft_atomic_name (◯ {[ Λ := Cinr () ]}))%I.

  Definition own_alft_auth (A : gmap atomic_lft bool) : iProp Σ :=
    own lft_atomic_name (● (to_lft_stateR <$> A)).
  Definition own_ilft_auth (I : gmap lft lft_names) : iProp Σ :=
    own lft_inter_name (● (DecAgree <$> I)).

  Definition own_bor (κ : lft)
      (x : auth (gmap slice_name (frac * dec_agree bor_state))) : iProp Σ :=
    (∃ γs,
      own lft_inter_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (bor_name γs) x)%I.

  Definition own_cnt (κ : lft) (x : auth nat) : iProp Σ :=
    (∃ γs,
      own lft_inter_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (cnt_name γs) x)%I.

  Definition own_inh (κ : lft) (x : auth (gset_disj slice_name)) : iProp Σ :=
    (∃ γs,
      own lft_inter_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (inh_name γs) x)%I.

  Definition bor_cnt (κ : lft) (s : bor_state) : iProp Σ :=
    match s with
    | Bor_in => True
    | Bor_open q => lft_own q κ
    | Bor_rebor κ' => ⌜κ ⊂ κ'⌝ ∗ own_cnt κ' (◯ 1)
    end%I.

  Definition lft_bor_alive (κ : lft) (P : iProp Σ) : iProp Σ :=
    (∃ B : gmap slice_name bor_state,
      box borN (bor_filled <$> B) P ∗
      own_bor κ (● ((1%Qp,) ∘ DecAgree <$> B)) ∗
      [∗ map] s ∈ B, bor_cnt κ s)%I.

  Definition lft_bor_dead (κ : lft) : iProp Σ :=
     (∃ (B: gset slice_name) (P : iProp Σ),
       own_bor κ (● to_gmap (1%Qp, DecAgree Bor_in) B) ∗
       box borN (to_gmap false B) P)%I.

   Definition lft_inh (κ : lft) (s : bool) (P : iProp Σ) : iProp Σ :=
     (∃ E : gset slice_name,
       own_inh κ (● GSet E) ∗
       box inhN (to_gmap s E) P)%I.

   Definition lft_vs_inv_go (κ : lft) (lft_alive : ∀ κ', κ' ⊂ κ → iProp Σ)
       (I : gmap lft lft_names) : iProp Σ :=
     (lft_bor_dead κ ∗
       own_ilft_auth I ∗
       [∗ set] κ' ∈ dom _ I, ∀ Hκ : κ' ⊂ κ, lft_alive κ' Hκ)%I.

   Definition lft_vs_go (κ : lft) (lft_alive : ∀ κ', κ' ⊂ κ → iProp Σ)
       (P Q : iProp Σ) : iProp Σ :=
     (∃ n : nat,
       own_cnt κ (● n) ∗
       ∀ I : gmap lft lft_names,
         lft_vs_inv_go κ lft_alive I -∗ ▷ P -∗ lft_dead_own κ
           ={⊤∖↑mgmtN}=∗
         lft_vs_inv_go κ lft_alive I ∗ ▷ Q ∗ own_cnt κ (◯ n))%I.

  Definition lft_alive_go (κ : lft) (lft_alive : ∀ κ', κ' ⊂ κ → iProp Σ) : iProp Σ :=
    (∃ P Q,
      lft_bor_alive κ P ∗
      lft_vs_go κ lft_alive P Q ∗
      lft_inh κ false Q)%I.

  Definition lft_alive (κ : lft) : iProp Σ :=
    Fix_F _ lft_alive_go (gmultiset_wf κ).
  Definition lft_vs_inv (κ : lft) (I : gmap lft lft_names) : iProp Σ :=
    lft_vs_inv_go κ (λ κ' _, lft_alive κ') I.
  Definition lft_vs (κ : lft) (P Q : iProp Σ) : iProp Σ :=
    lft_vs_go κ (λ κ' _, lft_alive κ') P Q.

  Definition lft_dead (κ : lft) : iProp Σ :=
    (∃ P,
      lft_bor_dead κ ∗
      own_cnt κ (● 0) ∗
      lft_inh κ true P)%I.

  Definition lft_alive_in (A : gmap atomic_lft bool) (κ : lft) : Prop :=
    ∀ Λ, Λ ∈ κ → A !! Λ = Some true.
  Definition lft_dead_in (A : gmap atomic_lft bool) (κ : lft) : Prop :=
    ∃ Λ, Λ ∈ κ ∧ A !! Λ = Some false.

  Definition lft_inv (A : gmap atomic_lft bool) (κ : lft) : iProp Σ :=
    (lft_alive κ ∗ ⌜lft_alive_in A κ⌝ ∨ lft_dead κ ∗ ⌜lft_dead_in A κ⌝)%I.

  Definition lfts_inv : iProp Σ :=
    (∃ (A : gmap atomic_lft bool) (I : gmap lft lft_names),
      own_alft_auth A ∗
      own_ilft_auth I ∗
      [∗ set] κ ∈ dom _ I, lft_inv A κ)%I.

  Definition lft_ctx : iProp Σ := inv mgmtN lfts_inv.

  Definition lft_incl (κ κ' : lft) : iProp Σ :=
    (□ ((∀ q, lft_own q κ ={↑lftN}=∗ ∃ q',
                 lft_own q' κ' ∗ (lft_own q' κ' ={↑lftN}=∗ lft_own q κ)) ∗
        (lft_dead_own κ' ={↑lftN}=∗ lft_dead_own κ)))%I.

  Definition bor_idx := (lft * slice_name)%type.

  Definition idx_bor_own (q : frac) (i : bor_idx) : iProp Σ :=
    own_bor (i.1) (◯ {[ i.2 := (q,DecAgree Bor_in) ]}).
  Definition idx_bor (κ : lft) (i : bor_idx) (P : iProp Σ) : iProp Σ :=
    (lft_incl κ (i.1) ∗ slice borN (i.2) P)%I.
  Definition raw_bor (i : bor_idx) (P : iProp Σ) : iProp Σ :=
    (idx_bor_own 1 i ∗ slice borN (i.2) P)%I.
  Definition bor (κ : lft) (P : iProp Σ) : iProp Σ :=
    (∃ i, lft_incl κ (i.1) ∗ raw_bor i P)%I.
End defs.

Instance: Params (@lft_bor_alive) 4.
Instance: Params (@lft_inh) 5.
Instance: Params (@lft_vs) 4.
Instance: Params (@idx_bor) 5.
Instance: Params (@raw_bor) 4.
Instance: Params (@bor) 4.

Notation "q .[ κ ]" := (lft_own q κ)
    (format "q .[ κ ]", at level 0) : uPred_scope.
Notation "[† κ ]" := (lft_dead_own κ) (format "[† κ ]"): uPred_scope.

Notation "&{ κ } P" := (bor κ P)
  (format "&{ κ }  P", at level 20, right associativity) : uPred_scope.
Notation "&{ κ , i } P" := (idx_bor κ i P)
  (format "&{ κ , i }  P", at level 20, right associativity) : uPred_scope.

Infix "⊑" := lft_incl (at level 70) : uPred_scope.

Typeclasses Opaque lft_own lft_dead_own bor_cnt lft_bor_alive lft_bor_dead
  lft_inh lft_alive lft_vs_inv lft_vs lft_dead lft_inv lft_incl idx_bor_own
  idx_bor raw_bor bor.

Section theorems.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(* Unfolding lemmas *)
Lemma lft_vs_inv_go_ne κ (f f' : ∀ κ', κ' ⊂ κ → iProp Σ) I n :
  (∀ κ' (Hκ : κ' ⊂ κ), f κ' Hκ ≡{n}≡ f' κ' Hκ) →
  lft_vs_inv_go κ f I ≡{n}≡ lft_vs_inv_go κ f' I.
Proof.
  intros Hf. apply sep_ne, sep_ne, big_opS_ne=> // κ'.
  by apply forall_ne=> Hκ.
Qed.

Lemma lft_vs_go_ne κ (f f' : ∀ κ', κ' ⊂ κ → iProp Σ) P P' Q Q' n :
  (∀ κ' (Hκ : κ' ⊂ κ), f κ' Hκ ≡{n}≡ f' κ' Hκ) →
  P ≡{n}≡ P' → Q ≡{n}≡ Q' →
  lft_vs_go κ f P Q ≡{n}≡ lft_vs_go κ f' P' Q'.
Proof.
  intros Hf HP HQ. apply exist_ne=> n'.
  apply sep_ne, forall_ne=> // I. rewrite lft_vs_inv_go_ne //. solve_proper.
Qed.

Lemma lft_alive_go_ne κ (f f' : ∀ κ', κ' ⊂ κ → iProp Σ) n :
  (∀ κ' (Hκ : κ' ⊂ κ), f κ' Hκ ≡{n}≡ f' κ' Hκ) →
  lft_alive_go κ f ≡{n}≡ lft_alive_go κ f'.
Proof.
  intros Hf. apply exist_ne=> P; apply exist_ne=> Q. by rewrite lft_vs_go_ne.
Qed.

Lemma lft_alive_unfold κ :
  lft_alive κ ⊣⊢ ∃ P Q, lft_bor_alive κ P ∗ lft_vs κ P Q ∗ lft_inh κ false Q.
Proof.
  apply equiv_dist=> n. rewrite /lft_alive -Fix_F_eq.
  apply lft_alive_go_ne=> κ' Hκ.
  apply (Fix_F_proper _ (λ _, dist n)); auto using lft_alive_go_ne.
Qed.
Lemma lft_vs_inv_unfold κ (I : gmap lft lft_names) :
  lft_vs_inv κ I ⊣⊢ lft_bor_dead κ ∗
    own_ilft_auth I ∗
    [∗ set] κ' ∈ dom _ I, ⌜κ' ⊂ κ⌝ → lft_alive κ'.
Proof.
  rewrite /lft_vs_inv /lft_vs_inv_go. by setoid_rewrite pure_impl_forall.
Qed.
Lemma lft_vs_unfold κ P Q :
  lft_vs κ P Q ⊣⊢ ∃ n : nat,
    own_cnt κ (● n) ∗
    ∀ I : gmap lft lft_names,
      lft_vs_inv κ I -∗ ▷ P -∗ lft_dead_own κ ={⊤∖↑mgmtN}=∗
      lft_vs_inv κ I ∗ ▷ Q ∗ own_cnt κ (◯ n).
Proof. done. Qed.

Global Instance lft_bor_alive_ne κ n : Proper (dist n ==> dist n) (lft_bor_alive κ).
Proof. solve_proper. Qed.
Global Instance lft_bor_alive_proper κ : Proper ((≡) ==> (≡)) (lft_bor_alive κ).
Proof. apply (ne_proper _). Qed.

Global Instance lft_inh_ne κ s n : Proper (dist n ==> dist n) (lft_inh κ s).
Proof. solve_proper. Qed.
Global Instance lft_inh_proper κ s : Proper ((≡) ==> (≡)) (lft_inh κ s).
Proof. apply (ne_proper _). Qed.

Global Instance lft_vs_ne κ n :
  Proper (dist n ==> dist n ==> dist n) (lft_vs κ).
Proof. intros P P' HP Q Q' HQ. by apply lft_vs_go_ne. Qed.
Global Instance lft_vs_proper κ : Proper ((≡) ==> (≡) ==> (≡)) (lft_vs κ).
Proof. apply (ne_proper_2 _). Qed.

Global Instance idx_bor_ne κ i n : Proper (dist n ==> dist n) (idx_bor κ i).
Proof. solve_proper. Qed.
Global Instance idx_bor_proper κ i : Proper ((≡) ==> (≡)) (idx_bor κ i).
Proof. apply (ne_proper _). Qed.

Global Instance raw_bor_ne i n : Proper (dist n ==> dist n) (raw_bor i).
Proof. solve_proper. Qed.
Global Instance raw_bor_proper i : Proper ((≡) ==> (≡)) (raw_bor i).
Proof. apply (ne_proper _). Qed.

Global Instance bor_ne κ n : Proper (dist n ==> dist n) (bor κ).
Proof. solve_proper. Qed.
Global Instance bor_proper κ : Proper ((≡) ==> (≡)) (bor κ).
Proof. apply (ne_proper _). Qed.

(*** PersistentP and TimelessP instances  *)
Global Instance lft_own_timeless q κ : TimelessP q.[κ].
Proof. rewrite /lft_own. apply _. Qed.
Global Instance lft_dead_own_persistent κ : PersistentP [†κ].
Proof. rewrite /lft_dead_own. apply _. Qed.
Global Instance lft_dead_own_timeless κ : PersistentP [†κ].
Proof. rewrite /lft_own. apply _. Qed.

Global Instance lft_incl_persistent κ κ' : PersistentP (κ ⊑ κ').
Proof. rewrite /lft_incl. apply _. Qed.

Global Instance idx_bor_persistent κ i P : PersistentP (&{κ,i} P).
Proof. rewrite /idx_bor. apply _. Qed.
Global Instance idx_borrow_own_timeless q i : TimelessP (idx_bor_own q i).
Proof. rewrite /idx_bor_own. apply _. Qed.

Global Instance lft_ctx_persistent : PersistentP lft_ctx.
Proof. rewrite /lft_ctx. apply _. Qed.

(** Alive and dead *)
Global Instance lft_alive_in_dec A κ : Decision (lft_alive_in A κ).
Proof.
  refine (cast_if (decide (set_Forall (λ Λ, A !! Λ = Some true)
                  (dom (gset atomic_lft) κ))));
    rewrite /lft_alive_in; by setoid_rewrite <-gmultiset_elem_of_dom.
Qed.
Global Instance lft_dead_in_dec A κ : Decision (lft_dead_in A κ).
Proof.
  refine (cast_if (decide (set_Exists (λ Λ, A !! Λ = Some false)
                  (dom (gset atomic_lft) κ))));
      rewrite /lft_dead_in; by setoid_rewrite <-gmultiset_elem_of_dom.
Qed.

Lemma lft_alive_or_dead_in A κ :
  (∃ Λ, Λ ∈ κ ∧ A !! Λ = None) ∨ (lft_alive_in A κ ∨ lft_dead_in A κ).
Proof.
  rewrite /lft_alive_in /lft_dead_in.
  destruct (decide (set_Exists (λ Λ, A !! Λ = None) (dom (gset _) κ)))
    as [(Λ & ?%gmultiset_elem_of_dom & HAΛ)|HA%(not_set_Exists_Forall _)]; first eauto.
  destruct (decide (set_Exists (λ Λ, A !! Λ = Some false) (dom (gset _) κ)))
    as [(Λ & HΛ%gmultiset_elem_of_dom & ?)|HA'%(not_set_Exists_Forall _)]; first eauto.
  right; left. intros Λ HΛ%gmultiset_elem_of_dom.
  move: (HA _ HΛ) (HA' _ HΛ)=> /=. case: (A !! Λ)=>[[]|]; naive_solver.
Qed.
Lemma lft_alive_and_dead_in A κ : lft_alive_in A κ → lft_dead_in A κ → False.
Proof. intros Halive (Λ&HΛ&?). generalize (Halive _ HΛ). naive_solver. Qed.

Lemma lft_alive_in_subseteq A κ κ' :
  lft_alive_in A κ → κ' ⊆ κ → lft_alive_in A κ'.
Proof. intros Halive ? Λ ?. by eapply Halive, gmultiset_elem_of_subseteq. Qed.

Lemma lft_alive_in_insert A κ Λ b :
  A !! Λ = None → lft_alive_in A κ → lft_alive_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ Halive Λ' HΛ'.
  assert (Λ ≠ Λ') by (intros ->; move:(Halive _ HΛ'); by rewrite HΛ).
  rewrite lookup_insert_ne; eauto.
Qed.
Lemma lft_alive_in_insert_false A κ Λ b :
  Λ ∉ κ → lft_alive_in A κ → lft_alive_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ Halive Λ' HΛ'.
  rewrite lookup_insert_ne; last (by intros ->); auto.
Qed.

Lemma lft_dead_in_insert A κ Λ b :
  A !! Λ = None → lft_dead_in A κ → lft_dead_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ (Λ'&?&HΛ').
  assert (Λ ≠ Λ') by (intros ->; move:HΛ'; by rewrite HΛ).
  exists Λ'. by rewrite lookup_insert_ne.
Qed.
Lemma lft_dead_in_insert_false A κ Λ :
  lft_dead_in A κ → lft_dead_in (<[Λ:=false]> A) κ.
Proof.
  intros (Λ'&?&HΛ'). destruct (decide (Λ = Λ')) as [<-|].
  - exists Λ. by rewrite lookup_insert.
  - exists Λ'. by rewrite lookup_insert_ne.
Qed.
Lemma lft_dead_in_insert_false' A κ Λ : Λ ∈ κ → lft_dead_in (<[Λ:=false]> A) κ.
Proof. exists Λ. by rewrite lookup_insert. Qed.

(** Silly stuff *)
Lemma own_ilft_auth_agree (I : gmap lft lft_names) κ γs :
  own_ilft_auth I ⊢
    own lft_inter_name (◯ {[κ := DecAgree γs]}) -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI Hκ". iDestruct (own_valid_2 with "HI Hκ")
    as %[[? [??]]%singleton_included _]%auth_valid_discrete_2.
  simplify_map_eq; simplify_option_eq; eauto.
Qed.

Lemma own_bor_auth I κ x : own_ilft_auth I ⊢ own_bor κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.
Lemma own_bor_op κ x y : own_bor κ (x ⋅ y) ⊣⊢ own_bor κ x ∗ own_bor κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs%auth_own_valid.
  move: Hγs; rewrite /= op_singleton singleton_valid=> /dec_agree_op_inv [<-].
  iExists γs. iSplit. done. rewrite own_op; iFrame.
Qed.
Lemma own_bor_valid κ x : own_bor κ x ⊢ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_bor_valid_2 κ x y : own_bor κ x ⊢ own_bor κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_bor_op. apply own_bor_valid. Qed.
Lemma own_bor_update κ x y : x ~~> y → own_bor κ x ==∗ own_bor κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.

Lemma own_cnt_auth I κ x : own_ilft_auth I ⊢ own_cnt κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.
Lemma own_cnt_op κ x y : own_cnt κ (x ⋅ y) ⊣⊢ own_cnt κ x ∗ own_cnt κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs%auth_own_valid.
  move: Hγs; rewrite /= op_singleton singleton_valid=> /dec_agree_op_inv [<-].
  iExists γs. iSplit; first done. rewrite own_op; iFrame.
Qed.
Lemma own_cnt_valid κ x : own_cnt κ x ⊢ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_cnt_valid_2 κ x y : own_cnt κ x ⊢ own_cnt κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_cnt_op. apply own_cnt_valid. Qed.
Lemma own_cnt_update κ x y : x ~~> y → own_cnt κ x ==∗ own_cnt κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.
Lemma own_cnt_update_2 κ x1 x2 y :
  x1 ⋅ x2 ~~> y → own_cnt κ x1 ⊢ own_cnt κ x2 ==∗ own_cnt κ y.
Proof.
  intros. apply wand_intro_r. rewrite -own_cnt_op. by apply own_cnt_update.
Qed.

Lemma own_inh_auth I κ x : own_ilft_auth I ⊢ own_inh κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.
Lemma own_inh_op κ x y : own_inh κ (x ⋅ y) ⊣⊢ own_inh κ x ∗ own_inh κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs%auth_own_valid.
  move: Hγs; rewrite /= op_singleton singleton_valid=> /dec_agree_op_inv [<-].
  iExists γs. iSplit. done. rewrite own_op; iFrame.
Qed.
Lemma own_inh_valid κ x : own_inh κ x ⊢ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_inh_valid_2 κ x y : own_inh κ x ⊢ own_inh κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_inh_op. apply own_inh_valid. Qed.
Lemma own_inh_update κ x y : x ~~> y → own_inh κ x ==∗ own_inh κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.

Lemma lft_alive_twice κ : lft_alive κ ⊢ lft_alive κ -∗ False.
Proof.
  rewrite lft_alive_unfold /lft_inh.
  iDestruct 1 as (P Q) "(_&_&Hinh)"; iDestruct 1 as (P' Q') "(_&_&Hinh')".
  iDestruct "Hinh" as (E) "[HE _]"; iDestruct "Hinh'" as (E') "[HE' _]".
  by iDestruct (own_inh_valid_2 with "HE HE'") as %?.
Qed.

(** Basic rules about lifetimes  *)
Lemma lft_own_op q κ1 κ2 : q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ∪ κ2].
Proof. by rewrite /lft_own -big_sepMS_union. Qed.

Lemma lft_dead_own_or κ1 κ2 : [†κ1] ∨ [†κ2] ⊣⊢ [† κ1 ∪ κ2].
Proof.
  rewrite /lft_dead_own -or_exist. apply exist_proper=> Λ.
  rewrite -sep_or_r -pure_or. do 2 f_equiv. set_solver.
Qed.

Lemma lft_own_frac_op κ q q' : (q + q').[κ] ⊣⊢ q.[κ] ∗ q'.[κ].
Proof.
  rewrite /lft_own -big_sepMS_sepMS. apply big_sepMS_proper=> Λ _.
  by rewrite -own_op -auth_frag_op op_singleton.
Qed.

Lemma lft_own_split κ q : q.[κ] ⊣⊢ (q/2).[κ] ∗ (q/2).[κ].
Proof. by rewrite -lft_own_frac_op Qp_div_2. Qed.

Lemma lft_own_dead_own q κ : q.[κ] ⊢ [† κ] -∗ False.
Proof.
  rewrite /lft_own /lft_dead_own. iIntros "H"; iDestruct 1 as (Λ') "[% H']".
  iDestruct (big_sepMS_elem_of _ _ Λ' with "H") as "H"=> //.
  iDestruct (own_valid_2 with "H H'") as %Hvalid.
  move: Hvalid=> /auth_own_valid /=; by rewrite op_singleton singleton_valid.
Qed.

Lemma lft_own_static q : True ⊢ q.[static].
Proof. by rewrite /lft_own big_sepMS_empty. Qed.

Lemma lft_dead_own_static : [† static] ⊢ False.
Proof. rewrite /lft_dead_own. iDestruct 1 as (Λ) "[% H']". set_solver. Qed.

(* Lifetime creation *)
Lemma lft_inh_kill E κ Q :
  ↑inhN ⊆ E →
  lft_inh κ false Q ∗ ▷ Q ={E}=∗ lft_inh κ true Q.
Proof.
  rewrite /lft_inh. iIntros (?) "[Hinh HQ]".
  iDestruct "Hinh" as (E') "[Hinh Hbox]".
  iMod (box_fill_all with "[$Hbox $HQ]") as "?"=>//.
  rewrite fmap_to_gmap. iModIntro. iExists E'. by iFrame.
Qed.

Lemma lft_vs_inv_frame (KI K : gset lft) κ :
  (∀ κ', κ' ∈ KI → κ' ⊂ κ → κ' ∈ K) →
  ([∗ set] κ' ∈ K, lft_alive κ') ⊢
    ([∗ set] κ' ∈ KI, ⌜κ' ⊂ κ⌝ → lft_alive κ') ∗
    (([∗ set] κ' ∈ KI, ⌜κ' ⊂ κ⌝ → lft_alive κ') -∗
      ([∗ set] κ' ∈ K, lft_alive κ')).
Proof.
  intros ?.
  destruct (proj1 (subseteq_disjoint_union_L (filter (⊂ κ) KI) K)) as (K'&->&?).
  { intros κ'. rewrite elem_of_filter. set_solver. }
  rewrite big_sepS_union // big_sepS_filter. iIntros "[$ $]"; auto.
Qed.

Lemma ilft_create A I κ :
  own_ilft_auth I ⊢ own_alft_auth A -∗ ▷ ([∗ set] κ ∈ dom _ I, lft_inv A κ)
      ==∗ ∃ A' I', ⌜is_Some (I' !! κ)⌝ ∗
    own_ilft_auth I' ∗ own_alft_auth A' ∗ ▷ ([∗ set] κ ∈ dom _ I', lft_inv A' κ).
Proof.
  iIntros "HI HA HA'".
  destruct (decide (is_Some (I !! κ))) as [?|HIκ%eq_None_not_Some].
  { iModIntro. iExists A, I. by iFrame. }
  iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γcnt) "[Hcnt Hcnt']"; first done.
  iMod (own_alloc ((● ∅ ⋅ ◯ ∅) :auth (gmap slice_name
      (frac * dec_agree bor_state)))) as (γbor) "[Hbor Hbor']";
    first by apply auth_valid_discrete_2.
  iMod (own_alloc ((● ∅ ⋅ ◯ ∅) :auth (gset_disj slice_name)))
    as (γinh) "[Hinh Hinh']"; first by apply auth_valid_discrete_2.
  set (γs := LftNames γbor γcnt γinh).
  iMod (own_update with "HI") as "[HI Hγs]".
  { apply auth_update_alloc,
      (alloc_singleton_local_update _ κ (DecAgree γs)); last done.
    by rewrite lookup_fmap HIκ. }
  iDestruct "Hγs" as "#Hγs".
  iAssert (lft_dead κ ∧ lft_alive κ)%I with "[-HA HA' HI]" as "Hdeadandalive".
  { iSplit.
    - rewrite /lft_dead. iExists True%I. iSplitL "Hbor".
      { rewrite /lft_bor_dead. iExists ∅, True%I. rewrite !to_gmap_empty.
        iSplitL "Hbor". iExists γs. by iFrame. iApply box_alloc. }
      iSplitL "Hcnt".
      { rewrite /own_cnt. iExists γs. by iFrame. }
      rewrite /lft_inh. iExists ∅. rewrite to_gmap_empty.
      iSplitL; [|iApply box_alloc]. rewrite /own_inh. iExists γs. by iSplit.
    - rewrite lft_alive_unfold. iExists True%I, True%I. iSplitL "Hbor".
      { rewrite /lft_bor_alive. iExists ∅. rewrite !fmap_empty big_sepM_empty.
        iSplitR; [iApply box_alloc|]. iSplit=>//.
        rewrite /own_bor. iExists γs. by iFrame. }
      rewrite lft_vs_unfold. iSplitR "Hinh".
      { iExists 0. iSplitL "Hcnt".
        { rewrite /own_cnt. iExists γs. by iFrame. }
        iIntros (I') "$ $ _ !>". rewrite /own_cnt. iExists γs. by iFrame. }
      rewrite /lft_inh. iExists ∅. rewrite to_gmap_empty.
      iSplitL; [|iApply box_alloc]. rewrite /own_inh. iExists γs. by iFrame. }
  destruct (lft_alive_or_dead_in A κ) as [(Λ&?&HAΛ)|Haliveordead].
  - iMod (own_update with "HA") as "[HA _]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ Λ (Cinr ())); last done.
      by rewrite lookup_fmap HAΛ. }
    iModIntro. iExists (<[Λ:=false]>A), (<[κ:=γs]> I).
    iSplit; first rewrite lookup_insert; eauto.
    rewrite /own_ilft_auth /own_alft_auth !fmap_insert. iFrame "HA HI".
    rewrite dom_insert_L big_sepS_insert ?not_elem_of_dom //.
    iSplitR "HA'".
    { rewrite /lft_inv. iNext. iRight. iSplit.
      { by iDestruct "Hdeadandalive" as "[? _]". }
      iPureIntro. exists Λ. rewrite lookup_insert; auto. }
    iNext. iApply (big_sepS_impl _ _ (dom (gset lft) I) with "[$HA']").
    rewrite /lft_inv. iIntros "!#"; iIntros (κ' ?%elem_of_dom)
      "[[HA HA']|[HA HA']]"; iDestruct "HA'" as %HA.
    + iLeft. iFrame "HA". iPureIntro. by apply lft_alive_in_insert.
    + iRight. iFrame "HA". iPureIntro. by apply lft_dead_in_insert.
  - iModIntro. iExists A, (<[κ:=γs]> I).
    iSplit; first rewrite lookup_insert; eauto.
    iSplitL "HI"; first by rewrite /own_ilft_auth fmap_insert.
    rewrite dom_insert_L big_sepS_insert ?not_elem_of_dom //.
    iFrame "HA HA'". iNext. rewrite /lft_inv. destruct Haliveordead.
    + iLeft. by iDestruct "Hdeadandalive" as "[_ $]".
    + iRight. by iDestruct "Hdeadandalive" as "[$ _]".
Qed.

Lemma lft_kill (I : gmap lft lft_names) (K K' : gset lft) (κ : lft) :
  let Iinv := (
    own_ilft_auth I ∗
    ([∗ set] κ' ∈ K, lft_alive κ') ∗
    ([∗ set] κ' ∈ K', lft_dead κ'))%I in
  (∀ κ', is_Some (I !! κ') → κ' ⊂ κ → κ' ∈ K) →
  (∀ κ', is_Some (I !! κ') → κ ⊂ κ' → κ' ∈ K') →
  Iinv ⊢ lft_alive κ -∗ [†κ] ={⊤∖↑mgmtN}=∗ Iinv ∗ lft_dead κ.
Proof.
  iIntros (Iinv HK HK') "(HI & Halive & Hdead) Hlalive Hκ".
  rewrite lft_alive_unfold; iDestruct "Hlalive" as (P Q) "(Hbor & Hvs & Hinh)".
  rewrite /lft_bor_alive; iDestruct "Hbor" as (B) "(Hbox & Hbor & HB)".
  iAssert ⌜∀ i s, B !! i = Some s → s = Bor_in⌝%I with "[#]" as %HB.
  { iIntros (i s HBI).
    iDestruct (big_sepM_lookup _ B with "HB") as "HB"=> //.
    destruct s as [|q|κ']; rewrite /bor_cnt //.
    { iDestruct (lft_own_dead_own with "HB Hκ") as "[]". }
    iDestruct "HB" as "[% Hcnt]".
    iDestruct (own_cnt_auth with "HI Hcnt") as %?.
    iDestruct (big_sepS_elem_of _ K' with "Hdead") as "Hdead"; first by eauto.
    rewrite /lft_dead; iDestruct "Hdead" as (R) "(_ & Hcnt' & _)".
    iDestruct (own_cnt_valid_2 with "Hcnt' Hcnt")
      as %[?%nat_included _]%auth_valid_discrete_2; omega. }
  iMod (box_empty_all with "Hbox") as "[HP Hbox]"=>//; first solve_ndisj.
  { intros i s. by rewrite lookup_fmap fmap_Some=> -[? [/HB -> ->]]. }
  rewrite lft_vs_unfold; iDestruct "Hvs" as (n) "[Hcnt Hvs]".
  iDestruct (lft_vs_inv_frame (dom _ I) _ κ with "Halive") as "[Halive Halive']".
  { intros κ'. rewrite elem_of_dom. eauto. }
  iMod ("Hvs" $! I with "[HI Halive Hbox Hbor] HP Hκ") as "(Hinv & HQ & Hcnt')".
  { rewrite lft_vs_inv_unfold. iFrame. rewrite /lft_bor_dead.
    iExists (dom _ B), P. rewrite !to_gmap_dom -map_fmap_compose.
    rewrite (map_fmap_ext _ ((1%Qp,) ∘ DecAgree) B); last naive_solver.
    iFrame. }
  rewrite lft_vs_inv_unfold; iDestruct "Hinv" as "(?&HI&Halive)".
  iSpecialize ("Halive'" with "Halive").
  iMod (own_cnt_update_2 with "Hcnt Hcnt'") as "?".
  { apply auth_update_dealloc, (nat_local_update _ _ 0 0); omega. }
  rewrite /Iinv. iFrame "Hdead Halive' HI".
  iMod (lft_inh_kill with "[$Hinh $HQ]"); first solve_ndisj.
  iModIntro. rewrite /lft_dead. iExists Q. by iFrame.
Qed.

Lemma lfts_kill A (I : gmap lft lft_names) (K K' : gset lft) :
  let Iinv K' := (own_ilft_auth I ∗ [∗ set] κ' ∈ K', lft_alive κ')%I in
  (∀ κ κ', κ ∈ K → is_Some (I !! κ') → κ ⊆ κ' → κ' ∈ K) →
  (∀ κ κ', κ ∈ K → lft_alive_in A κ → is_Some (I !! κ') →
    κ' ∉ K → κ' ⊂ κ → κ' ∈ K') →
  Iinv K' ⊢ ([∗ set] κ ∈ K, lft_inv A κ ∗ [†κ])
    ={⊤∖↑mgmtN}=∗ Iinv K' ∗ [∗ set] κ ∈ K, lft_dead κ.
Proof.
  intros Iinv. revert K'.
  induction (collection_wf K) as [K _ IH]=> K' HK HK'.
  iIntros "[HI Halive] HK".
  pose (Kalive := filter (lft_alive_in A) K).
  destruct (decide (Kalive = ∅)) as [HKalive|].
  { iModIntro. rewrite /Iinv. iFrame.
    iApply (big_sepS_impl _ _ K with "[$HK]"); iAlways.
    rewrite /lft_inv. iIntros (κ Hκ) "[[[_ %]|[$ _]] _]". set_solver. }
  destruct (minimal_exists_L (⊂) Kalive)
    as (κ & [Hκalive HκK]%elem_of_filter & Hκmin); first done.
  iDestruct (big_sepS_delete _ K κ with "HK") as "[[Hκinv Hκ] HK]"; first done.
  rewrite {1}/lft_inv. iDestruct "Hκinv" as "[[Hκalive _]|[_ %]]"; last first.
  { by destruct (lft_alive_and_dead_in A κ). } 
  iAssert ⌜κ ∉ K'⌝%I with "[#]" as %HκK'.
  { iIntros (Hκ). iApply (lft_alive_twice κ with "Hκalive").
    by iApply (big_sepS_elem_of _ K' κ with "Halive"). }
  specialize (IH (K ∖ {[ κ ]})). feed specialize IH; [set_solver +HκK|].
  iMod (IH ({[ κ ]} ∪ K') with "[HI Halive Hκalive] HK") as "[[HI Halive] Hdead]".
  { intros κ' κ''.
    rewrite !elem_of_difference !elem_of_singleton=> -[? Hneq] ??.
    split; [by eauto|]; intros ->.
    eapply (minimal_strict_1 _ _ κ' Hκmin), strict_spec_alt; eauto.
    apply elem_of_filter; eauto using lft_alive_in_subseteq. }
  { intros κ' κ'' Hκ' ? [γs'' ?].
    destruct (decide (κ'' = κ)) as [->|]; [set_solver +|].
    move: Hκ'; rewrite not_elem_of_difference elem_of_difference
       elem_of_union not_elem_of_singleton elem_of_singleton.
    intros [??] [?|?]; eauto. }
  { rewrite /Iinv big_sepS_insert //. iFrame. }
  iDestruct (big_sepS_insert _ K' with "Halive") as "[Hκalive Halive]"; first done.
  iMod (lft_kill with "[$HI $Halive $Hdead] Hκalive Hκ")
    as "[(HI&Halive&Hdead) Hκdead]".
  { intros κ' ??. eapply (HK' κ); eauto.
    intros ?. eapply (minimal_strict_1 _ _ _ Hκmin); eauto.
    apply elem_of_filter; split; last done.
    eapply lft_alive_in_subseteq, gmultiset_subset_subseteq; eauto. }
  { intros κ' ? [??]%strict_spec_alt.
    rewrite elem_of_difference elem_of_singleton; eauto. }
  iModIntro. rewrite /Iinv (big_sepS_delete _ K) //. iFrame.
Qed.

Definition kill_set (I : gmap lft lft_names) (Λ : atomic_lft) : gset lft :=
  filter (Λ ∈) (dom (gset lft) I).

Lemma elem_of_kill_set I Λ κ : κ ∈ kill_set I Λ ↔ Λ ∈ κ ∧ is_Some (I !! κ).
Proof. by rewrite /kill_set elem_of_filter elem_of_dom. Qed.
Lemma kill_set_subseteq I Λ : kill_set I Λ ⊆ dom (gset lft) I.
Proof. intros κ [??]%elem_of_kill_set. by apply elem_of_dom. Qed.

Definition down_close (A : gmap atomic_lft bool)
    (I : gmap lft lft_names) (K : gset lft) : gset lft :=
  filter (λ κ, κ ∉ K ∧
    set_Exists (λ κ', κ ⊂ κ' ∧ lft_alive_in A κ') K) (dom (gset lft) I).
Lemma elem_of_down_close A I K κ :
  κ ∈ down_close A I K ↔
    is_Some (I !! κ) ∧ κ ∉ K ∧ ∃ κ', κ' ∈ K ∧ κ ⊂ κ' ∧ lft_alive_in A κ'.
Proof. rewrite /down_close elem_of_filter elem_of_dom /set_Exists. tauto. Qed.

Lemma down_close_lft_alive_in A I K κ : κ ∈ down_close A I K → lft_alive_in A κ.
Proof.
  rewrite elem_of_down_close; intros (?&?&?&?&?&?).
  eapply lft_alive_in_subseteq, gmultiset_subset_subseteq; eauto.
Qed.
Lemma down_close_disjoint A I K : K ⊥ down_close A I K.
Proof. intros κ. rewrite elem_of_down_close. naive_solver. Qed.
Lemma down_close_subseteq A I K :
  down_close A I K ⊆ dom (gset lft) I.
Proof. intros κ [??]%elem_of_down_close. by apply elem_of_dom. Qed.

Lemma lft_create E :
  ↑lftN ⊆ E →
  lft_ctx ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={⊤,⊤∖↑lftN}▷=∗ [†κ]).
Proof.
  iIntros (?) "#Hmgmt".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  destruct (exist_fresh (dom (gset _) A)) as [Λ HΛ%not_elem_of_dom].
  iMod (own_update with "HA") as "[HA HΛ]".
  { apply auth_update_alloc, (alloc_singleton_local_update _ Λ (Cinl 1%Qp))=>//.
    by rewrite lookup_fmap HΛ. }
  iMod ("Hclose" with "[HA HI Hinv]") as "_".
  { iNext. rewrite /lfts_inv /own_alft_auth.
    iExists (<[Λ:=true]>A), I; rewrite fmap_insert; iFrame.
    iApply (big_sepS_impl _ _ (dom (gset lft) I) with "[$Hinv]").
    iAlways. rewrite /lft_inv. iIntros (κ ?) "[[Hκ %]|[Hκ %]]".
    - iLeft. iFrame "Hκ". iPureIntro. by apply lft_alive_in_insert.
    - iRight. iFrame "Hκ". iPureIntro. by apply lft_dead_in_insert. }
  iModIntro; iExists {[ Λ ]}.
  rewrite {1}/lft_own big_sepMS_singleton. iFrame "HΛ".
  clear I A HΛ. iIntros "!# HΛ".
  iApply (step_fupd_mask_mono ⊤ _ _ (⊤∖↑mgmtN)); [solve_ndisj..|].
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  rewrite /lft_own big_sepMS_singleton.
  iDestruct (own_valid_2 with "HA HΛ")
    as %[[s [?%leibniz_equiv ?]]%singleton_included _]%auth_valid_discrete_2.
  iMod (own_update_2 with "HA HΛ") as "[HA HΛ]".
  { by eapply auth_update, singleton_local_update,
      (exclusive_local_update _ (Cinr ())). }
  iDestruct "HΛ" as "#HΛ". iModIntro; iNext.
  pose (K := kill_set I Λ); pose (K' := down_close A I K).
  assert (K ⊥ K') by (by apply down_close_disjoint).
  destruct (proj1 (subseteq_disjoint_union_L (K ∪ K')
    (dom (gset lft) I))) as (K''&HI&?).
  { apply union_least. apply kill_set_subseteq. apply down_close_subseteq. }
  rewrite HI !big_sepS_union //. iDestruct "Hinv" as "[[HinvK HinvD] Hinv]".
  iAssert ([∗ set] κ ∈ K', lft_alive κ)%I with "[HinvD]" as "HinvD".
  { iApply (big_sepS_impl _ _ K' with "[$HinvD]"); iIntros "!#".
    rewrite /lft_inv. iIntros (κ Hκ) "[[$ _]|[_ %]]".
    destruct (lft_alive_and_dead_in A κ); eauto using down_close_lft_alive_in. }
  iAssert ([∗ set] κ ∈ K, lft_inv A κ ∗ [† κ])%I with "[HinvK]" as "HinvK". 
  { iApply (big_sepS_impl _ _ K with "[$HinvK]"); iIntros "!#".
    iIntros (κ [? _]%elem_of_kill_set) "$". rewrite /lft_dead_own. eauto. }
  iMod (lfts_kill A I K K' with "[$HI $HinvD] HinvK") as "[[HI HinvD] HinvK]".
  { intros κ κ' [??]%elem_of_kill_set ??. apply elem_of_kill_set.
    split; last done. by eapply gmultiset_elem_of_subseteq. }
  { intros κ κ' ?????. apply elem_of_down_close; eauto 10. }
  iMod ("Hclose" with "[-]") as "_"; last first.
  { iModIntro. rewrite /lft_dead_own. iExists Λ.
    rewrite elem_of_singleton. auto. }
  iNext. iExists (<[Λ:=false]>A), I.
  rewrite /own_alft_auth fmap_insert. iFrame "HA HI".
  rewrite HI !big_sepS_union //.
  iSplitL "HinvK HinvD"; first iSplitL "HinvK".
  - iApply (big_sepS_impl _ _ K with "[$HinvK]"); iIntros "!#".
    iIntros (κ [? _]%elem_of_kill_set) "Hdead". rewrite /lft_inv.
    iRight. iFrame. iPureIntro. by apply lft_dead_in_insert_false'.
  - iApply (big_sepS_impl _ _ K' with "[$HinvD]"); iIntros "!#".
    iIntros (κ Hκ) "Halive". rewrite /lft_inv.
    iLeft. iFrame "Halive". iPureIntro.
    assert (lft_alive_in A κ) as Halive by (by eapply down_close_lft_alive_in).
    apply lft_alive_in_insert_false; last done.
    apply elem_of_down_close in Hκ as (?&HFOO&_).
    move: HFOO. by rewrite elem_of_kill_set not_and_l=> -[?|[] //].
  - iApply (big_sepS_impl _ _ K'' with "[$Hinv]"); iIntros "!#".
    rewrite /lft_inv. iIntros (κ Hκ) "[[? %]|[? %]]".
    + iLeft. iFrame. iPureIntro.
      apply lft_alive_in_insert_false; last done.
      assert (κ ∉ K). intros ?. eapply H5. 2: eauto. rewrite elem_of_union. eauto.
      move: H7. rewrite elem_of_kill_set not_and_l. intros [?|?]. done.
contradict H7. apply elem_of_dom. set_solver +HI Hκ.
    + iRight. iFrame. iPureIntro. by apply lft_dead_in_insert_false.
Qed.

(*
(** Basic borrows  *)
Lemma bor_create E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
Proof. Admitted.
Lemma bor_fake E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ [†κ] ={E}=∗ &{κ}P.
Proof.
  iIntros (?) "#?". iDestruct 1 as (Λ) "[% ?]".
Admitted.
Lemma bor_sep E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
Proof.
  iIntros (?) "#? Hbor".
Admitted.
Lemma bor_combine E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).
Proof. Admitted.
Lemma bor_acc_strong E q κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ Q ∗ ▷([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ} Q ∗ q.[κ].
Proof. Admitted.
Lemma bor_acc_atomic_strong E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P ={E,E∖lftN}=∗
    (▷ P ∗ ∀ Q, ▷ Q ∗ ▷ ([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E∖lftN,E}=∗ &{κ} Q) ∨
    [†κ] ∗ |={E∖lftN,E}=> True.
Proof. Admitted.
Lemma bor_reborrow' E κ κ' P :
  ↑lftN ⊆ E → κ ⊆ κ' →
  lft_ctx ⊢ &{κ} P ={E}=∗ &{κ'} P ∗ ([†κ'] ={E}=∗ &{κ} P).
Proof. Admitted.
Lemma bor_unnest E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ'} &{κ} P ={E}▷=∗ &{κ ∪ κ'} P.
Proof. Admitted.

(** Indexed borrow *)
Lemma idx_bor_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ idx_bor κ i P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
            ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
Proof. Admitted.

Lemma idx_bor_atomic_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ idx_bor κ i P -∗ idx_bor_own q i ={E,E∖lftN}=∗
              ▷ P ∗ (▷ P ={E∖lftN,E}=∗ idx_bor_own q i) ∨
              [†κ] ∗ (|={E∖lftN,E}=> idx_bor_own q i).
Proof. Admitted.

Lemma idx_bor_shorten κ κ' i P :
  κ ⊑ κ' ⊢ idx_bor κ' i P -∗ idx_bor κ i P.
Proof. Admitted.

  (*** Derived lemmas  *)

  Lemma borrow_acc E q κ P : ↑lftN ⊆ E →
      lft_ctx ⊢ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT HP Htok".
    iMod (borrow_acc_strong with "LFT HP Htok") as "[HP Hclose]". done.
    iIntros "!> {$HP} HP". iApply "Hclose". by iIntros "{$HP}!>_$".
  Qed.

  Lemma borrow_exists {A} `(↑lftN ⊆ E) κ (Φ : A → iProp Σ) {_:Inhabited A}:
    lft_ctx ⊢ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
  Proof.
    iIntros "#LFT Hb".
    iMod (borrow_acc_atomic_strong with "LFT Hb") as "[[HΦ Hclose]|[H† Hclose]]". done.
    - iDestruct "HΦ" as (x) "HΦ". iExists x. iApply "Hclose". iIntros "{$HΦ}!>_?". eauto.
    - iMod "Hclose" as "_". iExists inhabitant. by iApply (borrow_fake with "LFT").
  Qed.

  Lemma borrow_or `(↑lftN ⊆ E) κ P Q:
    lft_ctx ⊢ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
  Proof.
    iIntros "#LFT H". rewrite uPred.or_alt.
    iMod (borrow_exists with "LFT H") as ([]) "H"; auto.
  Qed.

  Lemma borrow_persistent `(↑lftN ⊆ E) `{PersistentP _ P} κ q:
    lft_ctx ⊢ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
  Proof.
    iIntros "#LFT Hb Htok".
    iMod (borrow_acc with "LFT Hb Htok") as "[#HP Hob]". done.
    by iMod ("Hob" with "HP") as "[_$]".
  Qed.

  Lemma lft_incl_acc `(↑lftN ⊆ E) κ κ' q:
    κ ⊑ κ' ⊢ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
  Proof.
    iIntros "#[H _] Hq". iApply fupd_mask_mono. eassumption.
    iMod ("H" with "*Hq") as (q') "[Hq' Hclose]". iExists q'.
    iIntros "{$Hq'}!>Hq". iApply fupd_mask_mono. eassumption. by iApply "Hclose".
  Qed.

  Lemma lft_incl_dead `(↑lftN ⊆ E) κ κ': κ ⊑ κ' ⊢ [†κ'] ={E}=∗ [†κ].
  Proof.
    iIntros "#[_ H] Hq". iApply fupd_mask_mono. eassumption. by iApply "H".
  Qed.

  Lemma lft_le_incl κ κ': κ' ≼ κ → True ⊢ κ ⊑ κ'.
  Proof.
    iIntros ([κ0 ->%leibniz_equiv]) "!#". iSplitR.
    - iIntros (q) "[Hκ' Hκ0]". iExists q. iIntros "!>{$Hκ'}Hκ'!>". by iSplitR "Hκ0".
    - iIntros "? !>". iApply lft_dead_or. auto.
  Qed.

  Lemma lft_incl_refl κ : True ⊢ κ ⊑ κ.
  Proof. by apply lft_le_incl. Qed.

  Lemma lft_incl_trans κ κ' κ'': κ ⊑ κ' ∗ κ' ⊑ κ'' ⊢ κ ⊑ κ''.
  Proof.
    unfold lft_incl. iIntros "[#[H1 H1†] #[H2 H2†]]!#". iSplitR.
    - iIntros (q) "Hκ".
      iMod ("H1" with "*Hκ") as (q') "[Hκ' Hclose]".
      iMod ("H2" with "*Hκ'") as (q'') "[Hκ'' Hclose']".
      iExists q''. iIntros "{$Hκ''}!>Hκ''". iMod ("Hclose'" with "Hκ''") as "Hκ'".
        by iApply "Hclose".
    - iIntros "H†". iMod ("H2†" with "H†"). by iApply "H1†".
  Qed.



  Lemma borrow_shorten κ κ' P: κ ⊑ κ' ⊢ &{κ'}P -∗ &{κ}P.
  Proof.
    iIntros "H⊑ H". unfold borrow. iDestruct "H" as (i) "[??]".
    iExists i. iFrame. by iApply (idx_borrow_shorten with "H⊑").
  Qed.

  Lemma lft_incl_lb κ κ' κ'' : κ ⊑ κ' ∗ κ ⊑ κ'' ⊢ κ ⊑ κ' ⋅ κ''.
  Proof.
    iIntros "[#[H1 H1†] #[H2 H2†]]!#". iSplitR.
    - iIntros (q) "[Hκ'1 Hκ'2]".
      iMod ("H1" with "*Hκ'1") as (q') "[Hκ' Hclose']".
      iMod ("H2" with "*Hκ'2") as (q'') "[Hκ'' Hclose'']".
      destruct (Qp_lower_bound q' q'') as (qq & q'0 & q''0 & -> & ->).
      iExists qq. rewrite -lft_own_op !lft_own_frac_op.
      iDestruct "Hκ'" as "[$ Hκ']". iDestruct "Hκ''" as "[$ Hκ'']".
      iIntros "!>[Hκ'0 Hκ''0]".
      iMod ("Hclose'" with "[$Hκ' $Hκ'0]") as "$".
      by iMod ("Hclose''" with "[$Hκ'' $Hκ''0]") as "$".
    - rewrite -lft_dead_or. iIntros "[H†|H†]". by iApply "H1†". by iApply "H2†".
  Qed.

  Lemma lft_incl_static κ : True ⊢ κ ⊑ static.
  Proof.
    iIntros "!#". iSplitR.
    - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_own_static. auto.
    - iIntros "?". by iDestruct (lft_not_dead_static with "[-]") as "[]".
  Qed.

  Lemma reborrow `(↑lftN ⊆ E) P κ κ':
    lft_ctx ⊢ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗  &{κ}P).
  Proof.
    iIntros "#LFT #H⊑ HP". iMod (borrow_reborrow' with "LFT HP") as "[Hκ' H∋]".
      done. by exists κ'.
    iDestruct (borrow_shorten with "[H⊑] Hκ'") as "$".
    { iApply lft_incl_lb. iSplit. done. iApply lft_incl_refl. }
    iIntros "!>Hκ'". iApply ("H∋" with "[Hκ']"). iApply lft_dead_or. auto.
  Qed.

End incl.

Typeclasses Opaque lft_incl.
*)
