From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing util option mutex.
Set Default Proof Using "Type".

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mguard.
  Context `{!typeG Σ, !lockG Σ}.

  (*
    pub struct MutexGuard<'a, T: ?Sized + 'a> {
      // funny underscores due to how Deref/DerefMut currently work (they
      // disregard field privacy).
      __lock: &'a Mutex<T>,
      __poison: poison::Guard,
    }
  *)

  Program Definition mutex_guard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ γ β, locked γ ∗ α ⊑ β ∗
             &shr{α, mutexN} (lock_proto γ l (&{β} shift_loc l 1 ↦∗: ty.(ty_own) tid)) ∗
             &{β} (shift_loc l 1 ↦∗: ty.(ty_own) tid)
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l':loc), &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α⊓κ]
                ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (α⊓κ) tid (shift_loc l' 1) ∗ q.[α⊓κ]
    |}%I.
  Next Obligation. by iIntros (? ty tid [|[[]|][]]) "H". Qed.
  (* This is to a large extend copy-pasted from RWLock's write guard. *)
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hlcked H]"; first done.
    iMod (bor_sep with "LFT H") as "[Hαβ H]"; first done.
    iMod (bor_sep with "LFT H") as "[_ H]"; first done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ $]"; first done.
    iExists _. iFrame "H↦". iApply delay_sharing_nested; try done.
    (* FIXME: "iApply lft_intersect_mono" only preserves the later on the last
       goal, as does "iApply (lft_intersect_mono with ">")". *)
    iNext. iApply lft_intersect_mono. done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (l') "[#Hf #H]".
    iExists _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. iApply lft_incl_refl. done.
  Qed.
End mguard.
