From iris.program_logic Require Import thread_local.
From iris.proofmode Require Import tactics.
From lrust Require Export type proofmode.

Delimit Scope perm_scope with P.
Bind Scope perm_scope with perm.

Module Perm.

Section perm.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Fixpoint eval_expr (ν : expr) : option val :=
    match ν with
    | BinOp ProjOp e (Lit (LitInt n)) =>
      match eval_expr e with
      | Some (#(LitLoc l)) => Some (#(shift_loc l n))
      | _ => None
      end
    | e => to_val e
    end.

  Definition has_type (ν : expr) (ty : type) : perm := λ tid,
    from_option (λ v, ty.(ty_own) tid [v]) False%I (eval_expr ν).

  Definition extract (κ : lifetime) (ρ : perm) : perm :=
    λ tid, (κ ∋ ρ tid)%I.

  Definition tok (κ : lifetime) (q : Qp) : perm :=
    λ _, ([κ]{q} ★ lft κ)%I.

  Definition incl (κ κ' : lifetime) : perm :=
    λ _, (κ ⊑ κ')%I.

  Definition exist {A : Type} (P : A -> perm) : @perm Σ :=
    λ tid, (∃ x, P x tid)%I.

  Definition sep (ρ1 ρ2 : perm) : @perm Σ :=
    λ tid, (ρ1 tid ★ ρ2 tid)%I.

  Global Instance top : Top (@perm Σ) :=
    λ _, True%I.

End perm.

End Perm.

Import Perm.

Notation "v ◁ ty" := (has_type v ty)
  (at level 75, right associativity) : perm_scope.

Notation "κ ∋ ρ" := (extract κ ρ)
  (at level 75, right associativity) : perm_scope.

Notation "[ κ ]{ q }" := (tok κ q) (format "[ κ ]{ q }") : perm_scope.

Infix "⊑" := incl (at level 70) : perm_scope.

Notation "∃ x .. y , P" :=
  (exist (λ x, .. (exist (λ y, P)) ..)) : perm_scope.

Infix "★" := sep (at level 80, right associativity) : perm_scope.

Section duplicable.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Class Duplicable (ρ : @perm Σ) :=
    duplicable_persistent tid : PersistentP (ρ tid).
  Global Existing Instance duplicable_persistent.

  Global Instance has_type_dup v ty : ty.(ty_dup) → Duplicable (v ◁ ty).
  Proof. intros Hdup tid. apply _. Qed.

  Global Instance lft_incl_dup κ κ' : Duplicable (κ ⊑ κ').
  Proof. intros tid. apply _. Qed.

  Global Instance sep_dup P Q :
    Duplicable P → Duplicable Q → Duplicable (P ★ Q).
  Proof. intros HP HQ tid. apply _. Qed.

  Global Instance top_dup : Duplicable ⊤.
  Proof. intros tid. apply _. Qed.

End duplicable.

Section has_type.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Lemma has_type_value (v : val) ty tid :
    (v ◁ ty)%P tid ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    destruct v as [|f xl e ?]. done.
    unfold has_type, eval_expr, of_val.
    assert (Rec f xl e = RecV f xl e) as -> by done. by rewrite to_of_val.
  Qed.

  Lemma has_type_wp E (ν : expr) ty tid (Φ : val -> iProp _) :
    (ν ◁ ty)%P tid ★ (∀ (v : val), eval_expr ν = Some v ★ (v ◁ ty)%P tid -★ Φ v)
    ⊢ WP ν @ E {{ Φ }}.
  Proof.
    iIntros "[H◁ HΦ]". setoid_rewrite has_type_value. unfold has_type.
    destruct (eval_expr ν) eqn:EQν; last by iDestruct "H◁" as "[]". simpl.
    iSpecialize ("HΦ" $! v with "[$H◁]"). done.
    iInduction ν as [| | |[] e ? [|[]| | | | | | | | | |] _| | | | | | | |] "IH"
      forall (Φ v EQν); try done.
    - inversion EQν. subst. wp_value. auto.
    - wp_value. auto.
    - wp_bind e. simpl in EQν. destruct (eval_expr e) as [[[|l|]|]|]; try done.
      iApply ("IH" with "[] [HΦ]"). done. simpl. wp_op. inversion EQν. eauto.
  Qed.

End has_type.