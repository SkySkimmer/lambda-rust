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

  Definition typed_program (ρ : perm) e :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ na_own tid ⊤ }} e {{ _, False }}.

  Lemma typed_newlft ρ:
    typed_step ρ Newlft (λ _, ∃ α, 1.[α] ∗ α ∋ top)%P.
  Proof.
    iIntros (tid) "!#(_&#LFT&_&$)". wp_value.
    iMod (lft_create with "LFT") as (α) "[?#?]". done.
    iExists α. iFrame. iIntros "!>_!>". done.
  Qed.

  Lemma typed_endlft κ ρ:
    typed_step (κ ∋ ρ ∗ 1.[κ] ∗ †κ) Endlft (λ _, ρ)%P.
  Proof.
    rewrite /killable /extract. iIntros (tid) "!#(_&_&(Hextr&Htok&Hend)&$)".
    iDestruct ("Hend" with "Htok") as "Hend".
    iApply (wp_fupd_step with "Hend"); try done. wp_seq.
    iIntros "!>H†". by iApply fupd_mask_mono; last iApply "Hextr".
  Qed.

  Definition consumes (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, lftE ∪ ↑lrustN ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗ na_own tid ⊤ -∗
      (∀ (l:loc) vl q,
        (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗{q} vl ∗
         |={E}▷=> (ty.(ty_own) tid vl ∗ (l ↦∗{q} vl ={E}=∗ ρ2 ν tid ∗ na_own tid ⊤)))
       -∗ Φ #l)
      -∗ WP ν @ E {{ Φ }}.

  Definition update (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, lftE ∪ (↑lrustN) ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗
      (∀ (l:loc) vl,
         (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗ vl ∗
           ∀ vl', l ↦∗ vl' ∗ ▷ (ty.(ty_own) tid vl') ={E}=∗ ρ2 ν tid) -∗ Φ #l) -∗
      WP ν @ E {{ Φ }}.

End typing.
