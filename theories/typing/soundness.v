From iris.algebra Require Import frac.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import tactics.
From lrust.lang Require Import races adequacy proofmode notation.
From lrust.lifetime Require Import lifetime frac_borrow.
From lrust.typing Require Import typing.

Set Default Proof Using "Type".

Class typePreG Σ := PreTypeG {
  type_heapG :> lrustPreG Σ;
  type_lftG :> lftPreG Σ;
  type_preG_na_invG :> na_invG Σ;
  type_frac_borrowG :> frac_borG Σ
}.

Definition typeΣ : gFunctors :=
  #[lrustΣ; lftΣ; na_invΣ; GFunctor (constRF fracR)].
Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Section type_soundness.
  Definition exit_cont : val := λ: [<>], #().

  Definition main_type `{typeG Σ} :=
    fn (λ _, []) (λ _, [# ]) (λ _:(), box unit).

  Theorem type_soundness `{typePreG Σ} (main : val) σ t :
    (∀ `{typeG Σ}, typed_instruction_ty [] [] [] main main_type) →
    rtc step ([main [exit_cont]%E], ∅) (t, σ) →
    nonracing_threadpool t σ ∧
    (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
  Proof.
    intros Hmain Hrtc.
    cut (adequate (main [exit_cont]%E) ∅ (λ _, True)).
    { split. by eapply adequate_nonracing.
      intros. by eapply (adequate_safe (main [exit_cont]%E)). }
    apply: lrust_adequacy=>?.
    iMod lft_init as (?) "#LFT". done.
    iMod na_alloc as (tid) "Htl". set (Htype := TypeG _ _ _ _ _).
    wp_bind (of_val main). iApply (wp_wand with "[Htl]").
    iApply (Hmain _ $! tid 1%Qp with "LFT Htl [] [] []").
    { by rewrite /elctx_interp big_sepL_nil. }
    { by rewrite /llctx_interp big_sepL_nil. }
    { by rewrite tctx_interp_nil. }
    clear Hrtc Hmain main. iIntros (main) "(Htl & HE & HL & Hmain)".
    rewrite tctx_interp_singleton. iDestruct "Hmain" as (?) "[EQ Hmain]".
    rewrite eval_path_of_val. iDestruct "EQ" as %[= <-].
    iDestruct "Hmain" as (f k x e ?) "(EQ & % & Hmain)". iDestruct "EQ" as %[= ->].
    destruct x; try done.
    iApply (wp_rec _ _ _ _ _ _ [exit_cont]%E); [done| |by simpl_subst|iNext].
    { repeat econstructor. apply to_of_val. }
    iApply ("Hmain" $! () exit_cont [#] tid 1%Qp with "LFT Htl HE HL []");
      last by rewrite tctx_interp_nil.
    iIntros "_". rewrite cctx_interp_singleton. simpl. iIntros (args) "_ _".
    inv_vec args. iIntros (x) "_ /=". by wp_lam.
  Qed.
End type_soundness.

(* Soundness theorem when no other CMRA is needed. *)

Theorem type_soundness_closed (main : val) σ t :
  (∀ `{typeG typeΣ}, typed_instruction_ty [] [] [] main main_type) →
  rtc step ([main [exit_cont]%E], ∅) (t, σ) →
  nonracing_threadpool t σ ∧
  (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
Proof.
  intros. eapply @type_soundness; try done. apply _.
Qed.
