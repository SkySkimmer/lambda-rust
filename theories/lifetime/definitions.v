From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.prelude Require Export gmultiset strings.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import boxes.
From iris.base_logic Require Import big_op.

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

Instance to_lft_stateR_inj : Inj eq eq to_lft_stateR.
Proof. by intros [] []. Qed.

Record lft_names := LftNames {
  bor_name : gname;
  cnt_name : gname;
  inh_name : gname
}.
Instance lft_names_eq_dec : EqDecision lft_names.
Proof. solve_decision. Defined.

Class lftG Σ := LftG {
  lft_box :> boxG Σ;
  alft_inG :> inG Σ (authR (gmapUR atomic_lft lft_stateR));
  alft_name : gname;
  ilft_inG :> inG Σ (authR (gmapUR lft (dec_agreeR lft_names)));
  ilft_name : gname;
  lft_bor_box :>
    inG Σ (authR (gmapUR slice_name (prodR fracR (dec_agreeR bor_state))));
  lft_cnt_inG :> inG Σ (authR natUR);
  lft_inh_box :> inG Σ (authR (gset_disjUR slice_name));
}.

Section defs.
  Context `{invG Σ, lftG Σ}.

  Definition lft_tok (q : Qp) (κ : lft) : iProp Σ :=
    ([∗ mset] Λ ∈ κ, own alft_name (◯ {[ Λ := Cinl q ]}))%I.

  Definition lft_dead (κ : lft) : iProp Σ :=
    (∃ Λ, ⌜Λ ∈ κ⌝ ∗ own alft_name (◯ {[ Λ := Cinr () ]}))%I.

  Definition own_alft_auth (A : gmap atomic_lft bool) : iProp Σ :=
    own alft_name (● (to_lft_stateR <$> A)).
  Definition own_ilft_auth (I : gmap lft lft_names) : iProp Σ :=
    own ilft_name (● (DecAgree <$> I)).

  Definition own_bor (κ : lft)
      (x : auth (gmap slice_name (frac * dec_agree bor_state))) : iProp Σ :=
    (∃ γs,
      own ilft_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (bor_name γs) x)%I.

  Definition own_cnt (κ : lft) (x : auth nat) : iProp Σ :=
    (∃ γs,
      own ilft_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (cnt_name γs) x)%I.

  Definition own_inh (κ : lft) (x : auth (gset_disj slice_name)) : iProp Σ :=
    (∃ γs,
      own ilft_name (◯ {[ κ := DecAgree γs ]}) ∗
      own (inh_name γs) x)%I.

  Definition bor_cnt (κ : lft) (s : bor_state) : iProp Σ :=
    match s with
    | Bor_in => True
    | Bor_open q => lft_tok q κ
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

   Definition lft_vs_inv_go (κ : lft) (lft_inv_alive : ∀ κ', κ' ⊂ κ → iProp Σ)
       (I : gmap lft lft_names) : iProp Σ :=
     (lft_bor_dead κ ∗
       own_ilft_auth I ∗
       [∗ set] κ' ∈ dom _ I, ∀ Hκ : κ' ⊂ κ, lft_inv_alive κ' Hκ)%I.

   Definition lft_vs_go (κ : lft) (lft_inv_alive : ∀ κ', κ' ⊂ κ → iProp Σ)
       (P Q : iProp Σ) : iProp Σ :=
     (∃ n : nat,
       own_cnt κ (● n) ∗
       ∀ I : gmap lft lft_names,
         lft_vs_inv_go κ lft_inv_alive I -∗ ▷ P -∗ lft_dead κ
           ={⊤∖↑mgmtN}=∗
         lft_vs_inv_go κ lft_inv_alive I ∗ ▷ Q ∗ own_cnt κ (◯ n))%I.

  Definition lft_inv_alive_go (κ : lft)
      (lft_inv_alive : ∀ κ', κ' ⊂ κ → iProp Σ) : iProp Σ :=
    (∃ P Q,
      lft_bor_alive κ P ∗
      lft_vs_go κ lft_inv_alive P Q ∗
      lft_inh κ false Q)%I.

  Definition lft_inv_alive (κ : lft) : iProp Σ :=
    Fix_F _ lft_inv_alive_go (gmultiset_wf κ).
  Definition lft_vs_inv (κ : lft) (I : gmap lft lft_names) : iProp Σ :=
    lft_vs_inv_go κ (λ κ' _, lft_inv_alive κ') I.
  Definition lft_vs (κ : lft) (P Q : iProp Σ) : iProp Σ :=
    lft_vs_go κ (λ κ' _, lft_inv_alive κ') P Q.

  Definition lft_inv_dead (κ : lft) : iProp Σ :=
    (∃ P,
      lft_bor_dead κ ∗
      own_cnt κ (● 0) ∗
      lft_inh κ true P)%I.

  Definition lft_alive_in (A : gmap atomic_lft bool) (κ : lft) : Prop :=
    ∀ Λ:atomic_lft, Λ ∈ κ → A !! Λ = Some true.
  Definition lft_dead_in (A : gmap atomic_lft bool) (κ : lft) : Prop :=
    ∃ Λ:atomic_lft, Λ ∈ κ ∧ A !! Λ = Some false.

  Definition lft_inv (A : gmap atomic_lft bool) (κ : lft) : iProp Σ :=
    (lft_inv_alive κ ∗ ⌜lft_alive_in A κ⌝ ∨
     lft_inv_dead κ ∗ ⌜lft_dead_in A κ⌝)%I.

  Definition lfts_inv : iProp Σ :=
    (∃ (A : gmap atomic_lft bool) (I : gmap lft lft_names),
      own_alft_auth A ∗
      own_ilft_auth I ∗
      [∗ set] κ ∈ dom _ I, lft_inv A κ)%I.

  Definition lft_ctx : iProp Σ := inv mgmtN lfts_inv.

  Definition lft_incl (κ κ' : lft) : iProp Σ :=
    (□ ((∀ q, lft_tok q κ ={↑lftN}=∗ ∃ q',
                 lft_tok q' κ' ∗ (lft_tok q' κ' ={↑lftN}=∗ lft_tok q κ)) ∗
        (lft_dead κ' ={↑lftN}=∗ lft_dead κ)))%I.

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

Notation "q .[ κ ]" := (lft_tok q κ)
    (format "q .[ κ ]", at level 0) : uPred_scope.
Notation "[† κ ]" := (lft_dead κ) (format "[† κ ]"): uPred_scope.

Notation "&{ κ } P" := (bor κ P)
  (format "&{ κ }  P", at level 20, right associativity) : uPred_scope.
Notation "&{ κ , i } P" := (idx_bor κ i P)
  (format "&{ κ , i }  P", at level 20, right associativity) : uPred_scope.

Infix "⊑" := lft_incl (at level 70) : uPred_scope.

Typeclasses Opaque lft_tok lft_dead bor_cnt lft_bor_alive lft_bor_dead
  lft_inh lft_inv_alive lft_vs_inv lft_vs lft_inv_dead lft_inv lft_incl
  idx_bor_own idx_bor raw_bor bor.
