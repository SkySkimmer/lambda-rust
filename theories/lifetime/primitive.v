From lrust.lifetime Require Export definitions.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
Import uPred.

Section primitive.
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

Lemma lft_inv_alive_go_ne κ (f f' : ∀ κ', κ' ⊂ κ → iProp Σ) n :
  (∀ κ' (Hκ : κ' ⊂ κ), f κ' Hκ ≡{n}≡ f' κ' Hκ) →
  lft_inv_alive_go κ f ≡{n}≡ lft_inv_alive_go κ f'.
Proof.
  intros Hf. apply exist_ne=> P; apply exist_ne=> Q. by rewrite lft_vs_go_ne.
Qed.

Lemma lft_inv_alive_unfold κ :
  lft_inv_alive κ ⊣⊢ ∃ P Q, lft_bor_alive κ P ∗ lft_vs κ P Q ∗ lft_inh κ false Q.
Proof.
  apply equiv_dist=> n. rewrite /lft_inv_alive -Fix_F_eq.
  apply lft_inv_alive_go_ne=> κ' Hκ.
  apply (Fix_F_proper _ (λ _, dist n)); auto using lft_inv_alive_go_ne.
Qed.
Lemma lft_vs_inv_unfold κ (I : gmap lft lft_names) :
  lft_vs_inv κ I ⊣⊢ lft_bor_dead κ ∗
    own_ilft_auth I ∗
    [∗ set] κ' ∈ dom _ I, ⌜κ' ⊂ κ⌝ → lft_inv_alive κ'.
Proof.
  rewrite /lft_vs_inv /lft_vs_inv_go. by setoid_rewrite pure_impl_forall.
Qed.
Lemma lft_vs_unfold κ P Q :
  lft_vs κ P Q ⊣⊢ ∃ n : nat,
    own_cnt κ (● n) ∗
    ∀ I : gmap lft lft_names,
      lft_vs_inv κ I -∗ ▷ P -∗ lft_dead κ ={⊤∖↑mgmtN}=∗
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
Global Instance lft_tok_timeless q κ : TimelessP q.[κ].
Proof. rewrite /lft_tok. apply _. Qed.
Global Instance lft_dead_persistent κ : PersistentP [†κ].
Proof. rewrite /lft_dead. apply _. Qed.
Global Instance lft_dead_timeless κ : PersistentP [†κ].
Proof. rewrite /lft_tok. apply _. Qed.

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
    own ilft_name (◯ {[κ := DecAgree γs]}) -∗ ⌜is_Some (I !! κ)⌝.
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

Lemma lft_inv_alive_twice κ : lft_inv_alive κ ⊢ lft_inv_alive κ -∗ False.
Proof.
  rewrite lft_inv_alive_unfold /lft_inh.
  iDestruct 1 as (P Q) "(_&_&Hinh)"; iDestruct 1 as (P' Q') "(_&_&Hinh')".
  iDestruct "Hinh" as (E) "[HE _]"; iDestruct "Hinh'" as (E') "[HE' _]".
  by iDestruct (own_inh_valid_2 with "HE HE'") as %?.
Qed.

(** Basic rules about lifetimes  *)
Lemma lft_tok_op q κ1 κ2 : q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ∪ κ2].
Proof. by rewrite /lft_tok -big_sepMS_union. Qed.

Lemma lft_dead_or κ1 κ2 : [†κ1] ∨ [†κ2] ⊣⊢ [† κ1 ∪ κ2].
Proof.
  rewrite /lft_dead -or_exist. apply exist_proper=> Λ.
  rewrite -sep_or_r -pure_or. do 2 f_equiv. set_solver.
Qed.

Lemma lft_tok_frac_op κ q q' : (q + q').[κ] ⊣⊢ q.[κ] ∗ q'.[κ].
Proof.
  rewrite /lft_tok -big_sepMS_sepMS. apply big_sepMS_proper=> Λ _.
  by rewrite -own_op -auth_frag_op op_singleton.
Qed.

Lemma lft_tok_split κ q : q.[κ] ⊣⊢ (q/2).[κ] ∗ (q/2).[κ].
Proof. by rewrite -lft_tok_frac_op Qp_div_2. Qed.

Lemma lft_tok_dead_own q κ : q.[κ] ⊢ [† κ] -∗ False.
Proof.
  rewrite /lft_tok /lft_dead. iIntros "H"; iDestruct 1 as (Λ') "[% H']".
  iDestruct (big_sepMS_elem_of _ _ Λ' with "H") as "H"=> //.
  iDestruct (own_valid_2 with "H H'") as %Hvalid.
  move: Hvalid=> /auth_own_valid /=; by rewrite op_singleton singleton_valid.
Qed.

Lemma lft_tok_static q : True ⊢ q.[static].
Proof. by rewrite /lft_tok big_sepMS_empty. Qed.

Lemma lft_dead_static : [† static] ⊢ False.
Proof. rewrite /lft_dead. iDestruct 1 as (Λ) "[% H']". set_solver. Qed.
End primitive.
