From iris.program_logic Require Import thread_local.
From iris.proofmode Require Import invariants.
From lrust Require Export type.

Delimit Scope perm_scope with P.
Bind Scope perm_scope with perm.

Module Perm.

Section perm.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Definition has_type (v : val) (ty : type) : perm :=
    λ tid, ty.(ty_own) tid [v].

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
