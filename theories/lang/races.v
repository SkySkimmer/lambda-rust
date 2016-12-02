From iris.prelude Require Import gmap.
From iris.program_logic Require Export hoare.
From iris.program_logic Require Import adequacy.
From lrust.lang Require Import tactics.

Inductive access_kind : Type := ReadAcc | WriteAcc | FreeAcc.

Inductive next_access_head : expr → state → access_kind * order → loc → Prop :=
| Access_read ord l σ :
    next_access_head (Read ord (Lit $ LitLoc l)) σ (ReadAcc, ord) l
| Access_write ord l e σ :
    is_Some (to_val e) →
    next_access_head (Write ord (Lit $ LitLoc l) e) σ (WriteAcc, ord) l
| Access_cas_fail l st e1 v1 e2 vl σ :
    to_val e1 = Some v1 → is_Some (to_val e2) →  v1 ≠ vl →
    σ !! l = Some (st, vl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (ReadAcc, ScOrd) l
| Access_cas_suc l st e1 v1 e2 v2 σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    σ !! l = Some (st, v1) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (WriteAcc, ScOrd) l
| Access_free n l σ i :
    0 ≤ i < n →
    next_access_head (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                     σ (FreeAcc, Na2Ord) (shift_loc l i).

Definition next_access_thread (e: expr) (σ : state)
           (a : access_kind * order) (l : loc) : Prop :=
  ∃ K e', next_access_head e' σ a l ∧ e = fill K e'.

Definition next_accesses_threadpool (el: list expr) (σ : state)
           (a1 a2 : access_kind * order) (l : loc): Prop :=
  ∃ t1 e1 t2 e2 t3, el = t1 ++ e1 :: t2 ++ e2 :: t3 ∧
                    next_access_thread e1 σ a1 l ∧ next_access_thread e2 σ a2 l.

Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) σ : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l →
             nonracing_accesses a1 a2.

Lemma next_access_head_head K e σ a l:
  next_access_head (fill_item K e) σ a l → is_Some (to_val e).
Proof.
  destruct K; inversion 1; eauto.
Qed.

Lemma next_access_head_reductible_ctx e σ σ' a l K :
  next_access_head e σ' a l → reducible (fill K e) σ → head_reducible e σ.
Proof.
  intros Ha (e'&σ''&ef&Hstep). assert (to_val e = None). by destruct Ha.
  change fill with ectx_language.fill in Hstep.
  apply fill_step_inv in Hstep; last done. destruct Hstep as (e2'&_&Hstep).
  clear K. destruct Hstep as [K e1' e2'' ?? Hstep]. subst. destruct K as [|K0 K].
    by unfold head_reducible; eauto.
  exfalso. simpl in Ha. apply next_access_head_head in Ha.
  change to_val with ectxi_language.to_val in Ha.
  rewrite fill_not_val in Ha. by eapply is_Some_None. by eapply val_stuck.
Qed.

Lemma next_access_head_reducible_state e σ a l :
  next_access_head e σ a l → head_reducible e σ →
  match a with
  | (ReadAcc, ScOrd | Na1Ord) => ∃ v n, σ !! l = Some (RSt n, v)
  | (ReadAcc, Na2Ord) => ∃ v n, σ !! l = Some (RSt (S n), v)
  | (WriteAcc, ScOrd | Na1Ord) => ∃ v, σ !! l = Some (RSt 0, v)
  | (WriteAcc, Na2Ord) => ∃ v, σ !! l = Some (WSt, v)
  | (FreeAcc, _) => ∃ v ls, σ !! l = Some (ls, v)
  end.
Proof.
  assert (Hrefl : ∀ v, value_eq σ v v ≠ Some false).
  by destruct v as [[]|]=>//=; rewrite bool_decide_true.
  intros Ha (e'&σ'&ef&Hstep). destruct Ha; inv_head_step; eauto.
  by edestruct Hrefl.
  match goal with H : ∀ m, _ |- _ => destruct (H i) as [_ [[]?]] end; eauto.
Qed.

Lemma next_access_head_Na1Ord_step e1 e2 ef σ1 σ2 a l :
  next_access_head e1 σ1 (a, Na1Ord) l →
  head_step e1 σ1 e2 σ2 ef →
  next_access_head e2 σ2 (a, Na2Ord) l.
Proof.
  intros Ha Hstep. inversion Ha; subst; clear Ha; inv_head_step; constructor.
  by rewrite to_of_val.
Qed.

Lemma next_access_head_Na1Ord_concurent_step e1 e1' e2 e'f σ σ' a1 a2 l :
  next_access_head e1 σ (a1, Na1Ord) l →
  head_step e1 σ e1' σ' e'f →
  next_access_head e2 σ a2 l →
  next_access_head e2 σ' a2 l.
Proof.
  intros Ha1 Hstep Ha2. inversion Ha1; subst; clear Ha1; inv_head_step;
  destruct Ha2; simplify_eq; econstructor; eauto; apply lookup_insert.
Qed.

Lemma next_access_head_Free_concurent_step e1 e1' e2 e'f σ σ' o1 a2 l :
  next_access_head e1 σ (FreeAcc, o1) l → head_step e1 σ e1' σ' e'f →
  next_access_head e2 σ a2 l → head_reducible e2 σ' →
  False.
Proof.
  intros Ha1 Hstep Ha2 Hred2.
  assert (FREE : ∀ l n i, 0 ≤ i ∧ i < n → free_mem l (Z.to_nat n) σ !! shift_loc l i = None).
  { clear. intros l n i Hi.
    replace n with (Z.of_nat (Z.to_nat n)) in Hi by (apply Z2Nat.id; lia).
    revert l i Hi. induction (Z.to_nat n) as [|? IH]=>/=l i Hi. lia.
    destruct (decide (i = 0)).
    - subst. by rewrite /shift_loc Z.add_0_r -surjective_pairing lookup_delete.
    - replace i with (1+(i-1)) by lia.
      rewrite lookup_delete_ne -shift_loc_assoc ?IH //. lia.
      destruct l; intros [=?]. lia. }
  assert (FREE' : σ' !! l = None).
  { inversion Ha1; clear Ha1; inv_head_step. auto. }
  destruct Hred2 as (e2'&σ''&ef&?).
  inversion Ha2; clear Ha2; inv_head_step.
  eapply (@is_Some_None (lock_state * val)). rewrite -FREE'. naive_solver.
Qed.

Theorem safe_nonracing el σ :
  (∀ el' σ' e', rtc step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  nonracing_threadpool el σ.
Proof.
  change to_val with ectxi_language.to_val.
  intros Hsafe l a1 a2 (t1&?&t2&?&t3&->&(K1&e1&Ha1&->)&(K2&e2&Ha2&->)).

  assert (to_val e1 = None). by destruct Ha1.
  assert (Hrede1:head_reducible e1 σ).
  { eapply (next_access_head_reductible_ctx e1 σ σ a1 l K1), Hsafe, fill_not_val=>//.
    set_solver. }
  assert (Hσe1:=next_access_head_reducible_state _ _ _ _ Ha1 Hrede1).
  destruct Hrede1 as (e1'&σ1'&ef1&Hstep1).
  assert (Ha1' : a1.2 = Na1Ord → next_access_head e1' σ1' (a1.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep1.
    by destruct a1; simpl in *; subst. }
  assert (Hrtc_step1:
    rtc step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1' :: t2 ++ fill K2 e2 :: t3 ++ ef1, σ1')).
  { eapply rtc_l, rtc_refl. eapply step_atomic, Ectx_step, Hstep1; try  done.
    by rewrite -assoc. }
  assert (Hrede1: a1.2 = Na1Ord → head_reducible e1' σ1').
  { destruct a1 as [a1 []]=>// _.
    eapply (next_access_head_reductible_ctx e1' σ1' σ1' (a1, Na2Ord) l K1), Hsafe,
           fill_not_val=>//.
    by auto. set_solver. by destruct Hstep1; inversion Ha1. }

  assert (to_val e2 = None). by destruct Ha2.
  assert (Hrede2:head_reducible e2 σ).
  { eapply (next_access_head_reductible_ctx e2 σ σ a2 l K2), Hsafe, fill_not_val=>//.
    set_solver. }
  assert (Hσe2:=next_access_head_reducible_state _ _ _ _ Ha2 Hrede2).
  destruct Hrede2 as (e2'&σ2'&ef2&Hstep2).
  assert (Ha2' : a2.2 = Na1Ord → next_access_head e2' σ2' (a2.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep2.
    by destruct a2; simpl in *; subst. }
  assert (Hrtc_step2:
    rtc step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2' :: t3 ++ ef2, σ2')).
  { eapply rtc_l, rtc_refl. rewrite app_comm_cons assoc.
    eapply step_atomic, Ectx_step, Hstep2; try done. by rewrite -assoc. }
  assert (Hrede2: a2.2 = Na1Ord → head_reducible e2' σ2').
  { destruct a2 as [a2 []]=>// _.
    eapply (next_access_head_reductible_ctx e2' σ2' σ2' (a2, Na2Ord) l K2), Hsafe,
           fill_not_val=>//.
    by auto. set_solver. by destruct Hstep2; inversion Ha2. }


  assert (Ha1'2 : a1.2 = Na1Ord → next_access_head e2 σ1' a2 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede1_2: head_reducible e2 σ1').
  { intros. eapply (next_access_head_reductible_ctx e2 σ1' σ  a2 l K2), Hsafe, fill_not_val=>//.
    set_solver. }
  assert (Hσe1'1:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha1' Hord) (Hrede1 Hord)).
  assert (Hσe1'2:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha1'2 Hord) Hrede1_2).

  assert (Ha2'1 : a2.2 = Na1Ord → next_access_head e1 σ2' a1 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede2_1: head_reducible e1 σ2').
  { intros. eapply (next_access_head_reductible_ctx e1 σ2' σ a1 l K1), Hsafe, fill_not_val=>//.
    set_solver. }
  assert (Hσe2'1:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha2'1 Hord) Hrede2_1).
  assert (Hσe2'2:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha2' Hord) (Hrede2 Hord)).

  assert (a1.1 = FreeAcc → False).
  { destruct a1 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }
  assert (a2.1 = FreeAcc → False).
  { destruct a2 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }

  destruct Ha1 as [[]|[]| | |], Ha2 as [[]|[]| | |]=>//=; simpl in *;
    repeat match goal with
    | H : _ = Na1Ord → _ |- _ => specialize (H (eq_refl Na1Ord)) || clear H
    | H : False |- _ => destruct H
    | H : ∃ _, _ |- _ => destruct H
    end;
    try congruence.

  clear e2' Hstep2 σ2' Hrtc_step2 Hrede2_1. destruct Hrede1_2 as (e2'&σ'&ef&?).
  inv_head_step.
  match goal with
  | H : <[l:=_]> σ !! l = _ |- _ => by rewrite lookup_insert in H
  end.
Qed.

Corollary adequate_nonracing e1 t2 σ1 σ2 φ :
  adequate e1 σ1 φ →
  rtc step ([e1], σ1) (t2, σ2) →
  nonracing_threadpool t2 σ2.
Proof.
  intros [_ Had] Hrtc. apply safe_nonracing. intros el' σ' e' ?? He'.
  edestruct (Had el' σ' e') as [He''|]; try done. etrans; eassumption.
  rewrite /language.to_val /= He' in He''. by edestruct @is_Some_None.
Qed.
