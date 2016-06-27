From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ownership ectx_lifting. (* for ownP *)
From lrust Require Export lang.
From lrust Require Import tactics.
From iris.proofmode Require Import weakestpre.
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.

Section lifting.
Context {Σ : iFunctor}.
Implicit Types P Q : iProp lrust_lang Σ.
Implicit Types Φ : val → iProp lrust_lang Σ.
Implicit Types ef : option (expr []).

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} ⊢
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Base axioms for core primitives of the language: Stateful reductions. *)
Lemma wp_alloc_pst E σ n Φ :
  0 < n →
  (▷ ownP σ ★
   ▷ (∀ l σ', (∀ i, σ !! (l.1, i) = None) ∧ ■ init_mem_spec l n σ σ' ∧ ownP σ'
            -★ Φ (LitV $ LitLoc l)))
  ⊢ WP Alloc (Lit $ LitInt n) @ E {{ Φ }}.
Proof.
  iIntros {?}  "[HP HΦ]".
  set (φ (e' : expr []) σ' ef := ∃ l,
          ef = None ∧ e' = Lit (LitLoc l) ∧ init_mem_spec l n σ σ' ∧
          (∀ i, σ !! (l.1, i) = None)).
  iApply (wp_lift_atomic_head_step _ φ σ);
    try (by simpl; eauto).
  { intros; subst φ; inv_head_step; eauto 8 using init_mem_sound. }
  iFrame "HP". iNext. iIntros {v2 σ2 ef} "[Hφ HP]".
  iDestruct "Hφ" as %(l & -> & [= <-]%of_to_val_flip & ? & ?); simpl.
  iSplit; last done. iApply "HΦ". repeat iSplit; auto.
Qed.

Lemma wp_free_pst E σ l n Φ :
  0 < n →
  (∀ i, is_Some (σ !! (l.1, i)) ↔ (l.2 ≤ i ∧ i < l.2 + n)) →
  (▷ ownP σ ★
   ▷ (∀ l σ', ■ free_mem_spec l n σ σ' ∧ ownP σ'
              -★ Φ (LitV $ LitUnit)))
  ⊢ WP Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  iIntros {??}  "[HP HΦ]".
  set (φ (e' : expr []) σ' ef :=
          ef = None ∧ e' = Lit LitUnit ∧ free_mem_spec l n σ σ').
  iApply (wp_lift_atomic_head_step _ φ σ); try (by simpl; eauto).
  { intros; subst φ; inv_head_step; eauto 8 using free_mem_sound. }
  iFrame "HP". iNext. iIntros {v2 σ2 ef} "[Hφ HP]".
  iDestruct "Hφ" as %(-> & [= <-]%of_to_val_flip & ?); simpl.
  iSplit; last done. iApply "HΦ". repeat iSplit; auto.
Qed.

Lemma wp_read_sc_pst E σ l v Φ :
  σ !! l = Some (RSt 0, v) →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ v)) ⊢ WP Read ScOrd (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_atomic_det_head_step σ v σ None) ?right_id //.
  intros; inv_head_step; eauto using to_of_val.
Qed.

Lemma wp_read_in_pst E σ l n v Φ :
  σ !! l = Some(RSt $ S n, v) →
  (▷ ownP σ ★ ▷ (ownP (<[l:=(RSt n, v)]>σ) -★ Φ v))
  ⊢ WP Read InOrd (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  intros.
  rewrite -(wp_lift_atomic_det_head_step σ v (<[l:=(RSt n, v)]>σ) None)
          ?right_id //.
  intros; inv_head_step; eauto using to_of_val.
Qed.

Lemma wp_read_na_pst E1 E2 σ l n v Φ :
  E2 ⊆ E1 →
  σ !! l = Some(RSt $ n, v) →
  (|={E1,E2}=> ▷ ownP σ ★
               ▷ (ownP (<[l:=(RSt $ S n, v)]>σ) ={E2,E1}=★
                  WP Read InOrd (Lit $ LitLoc l) @ E1 {{ Φ }}))
  ⊢ WP Read NaOrd (Lit $ LitLoc l) @ E1 {{ Φ }}.
Proof.
  iIntros {??} "HΦP".
  set (φ (e' : expr []) σ' ef :=
         ef = None ∧ e' = Read InOrd (Lit $ LitLoc l) ∧ σ' = <[l:=(RSt $ S n, v)]>σ).
  iApply (wp_lift_head_step E1 E2 φ _ _ σ); auto.
  { intros. subst φ. inv_head_step. auto. }
  subst φ. iPvs "HΦP"; first set_solver. iPvsIntro. iNext.
  iDestruct "HΦP" as "[HΦ HP]". iFrame "HΦ". iIntros {e2 σ2 ef} "[#Hφ HΦ]".
  iDestruct "Hφ" as %(->&->&->). iPvs ("HP" with "HΦ"); first set_solver.
  by rewrite right_id.
Qed.

Lemma wp_write_sc_pst E σ l e v v' Φ :
  to_val e = Some v →
  σ !! l = Some (RSt 0, v') →
  (▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, v)]>σ) -★ Φ (LitV LitUnit)))
  ⊢ WP Write ScOrd (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  intros.
  rewrite-(wp_lift_atomic_det_head_step σ (LitV LitUnit)
             (<[l:=(RSt 0, v)]>σ) None) ?right_id //=. eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_write_in_pst E σ l e v v' Φ :
  to_val e = Some v →
  σ !! l = Some(WSt, v') →
  (▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, v)]>σ) -★ Φ (LitV LitUnit)))
  ⊢ WP Write InOrd (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  intros.
  rewrite-(wp_lift_atomic_det_head_step σ (LitV LitUnit)
             (<[l:=(RSt 0, v)]>σ) None) ?right_id //=. eauto.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_write_na_pst E1 E2 σ l e v v' Φ :
  to_val e = Some v →
  E2 ⊆ E1 →
  σ !! l = Some(RSt 0, v') →
  (|={E1,E2}=> ▷ ownP σ ★
               ▷ (ownP (<[l:=(WSt, v')]>σ) ={E2,E1}=★
                  WP Write InOrd (Lit $ LitLoc l) e @ E1 {{ Φ }}))
  ⊢ WP Write NaOrd (Lit $ LitLoc l) e @ E1 {{ Φ }}.
Proof.
  iIntros {???} "HΦP".
  set (φ (e' : expr []) σ' ef :=
         ef = None ∧ e' = Write InOrd (Lit $ LitLoc l) e ∧ σ' = <[l:=(WSt, v')]>σ).
  iApply (wp_lift_head_step E1 E2 φ _ _ σ); auto.
  { intros. subst φ. inv_head_step. auto. }
  subst φ. iPvs "HΦP"; first set_solver. iPvsIntro. iNext.
  iDestruct "HΦP" as "[HΦ HP]". iFrame "HΦ".
  iIntros {e2 σ2 ef} "[#Hφ HΦ]". iDestruct "Hφ" as %(->&->&->).
  iPvs ("HP" with "HΦ"); first set_solver. by rewrite right_id.
Qed.

Lemma wp_cas_fail_pst E σ l z1 z2 z' Φ :
  σ !! l = Some (RSt 0, LitV $ LitInt z') → z' ≠ z1 →
  (▷ ownP σ ★ ▷ (ownP σ -★ Φ (LitV $ LitInt 0)))
  ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  intros.
  rewrite-(wp_lift_atomic_det_head_step σ (LitV $ LitInt 0) σ None) ?right_id //.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_cas_suc_pst E σ l z1 z2 Φ :
  σ !! l = Some (RSt 0, LitV $ LitInt z1) →
  (▷ ownP σ ★ ▷ (ownP (<[l:=(RSt 0, LitV $ LitInt z2)]>σ) -★ Φ (LitV $ LitInt 1)))
  ⊢ WP CAS (Lit $ LitLoc l) (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  intros.
  rewrite -(wp_lift_atomic_det_head_step σ (LitV $ LitInt 1)
              (<[l:=(RSt 0, LitV $ LitInt z2 )]>σ) None) ?right_id //.
  intros; inv_head_step; eauto.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e Φ :
  (▷ Φ (LitV LitUnit) ★ ▷ WP e {{ _, True }}) ⊢ WP Fork e @ E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) (Lit LitUnit) (Some e)) //=.
  rewrite later_sep -(wp_value _ _ (Lit _)) //.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_rec E f xl erec erec' e el Φ :
  e = Rec f xl erec →
  List.Forall (λ ei, is_Some (to_val ei)) el →
  subst_l xl el erec = Some erec' →
  ▷ WP subst f e erec' @ E {{ Φ }}
  ⊢ WP App e el @ E {{ Φ }}.
Proof.
  intros -> ??.
  rewrite-(wp_lift_pure_det_head_step (App _ _) (subst f (Rec f xl erec) erec') None)
          ?right_id //=.
  intros; inv_head_step; eauto.
Qed.

Lemma wp_bin_op E op l1 l2 l' Φ :
  bin_op_eval op l1 l2 = Some l' →
  ▷ Φ (LitV l') ⊢ WP BinOp op (Lit l1) (Lit l2) @ E {{ Φ }}.
Proof.
  intros Heval. rewrite -(wp_lift_pure_det_head_step (BinOp op _ _) (Lit l') None)
    ?right_id -?wp_value //; intros; inv_head_step; eauto.
Qed.

Lemma wp_case E i e el Φ :
  0 ≤ i →
  List.nth_error el (Z.to_nat i) = Some e →
  ▷ WP e @ E {{ Φ }} ⊢ WP Case (Lit $ LitInt i) el @ E {{ Φ }}.
Proof.
  intros. rewrite -(wp_lift_pure_det_head_step (Case _ _) e None) ?right_id //.
  intros; inv_head_step; auto.
Qed.
End lifting.
