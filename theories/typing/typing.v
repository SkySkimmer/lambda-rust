From iris.program_logic Require Import hoare.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context cont_context.
From lrust.lang Require Import proofmode.
From lrust.lifetime Require Import frac_borrow reborrow borrow creation.

(* TODO: This is all still using the outdated type system. *)

Section typing.
  Context `{typeG Σ}.

  (* TODO : good notations for [typed_step] and [typed_step_ty] ? *)
  Definition typed_step (ρ : perm) e (θ : val → perm) :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ na_own tid ⊤ }} e
           {{ v, θ v tid ∗ na_own tid ⊤ }}.

  Definition typed_step_ty (ρ : perm) e ty :=
    typed_step ρ e (λ ν, ν ◁ ty)%P.

End typing.
