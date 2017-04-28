From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import util typing.
From lrust.typing.lib.rwlock Require Import rwlock.
Set Default Proof Using "Type".

Section rwlockwriteguard.
  Context `{typeG Σ, rwlockG Σ}.

  (* Original Rust type (we ignore poisoning):
      pub struct RwLockWriteGuard<'a, T: ?Sized + 'a> {
          __lock: &'a RwLock<T>,
          __poison: poison::Guard,
      }
  *)

  Program Definition rwlockwriteguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ γ β, &{β}(shift_loc l 1 ↦∗: ty.(ty_own) tid) ∗
             α ⊑ β ∗ &shr{β,rwlockN}(rwlock_inv tid l γ β ty) ∗
             own γ (◯ writing_st)
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (l' : loc),
           &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α ⊓ κ] ={F, F∖↑shrN∖↑lftN}▷=∗
               ty.(ty_shr) (α ⊓ κ) tid (shift_loc l' 1) ∗ q.[α ⊓ κ] |}%I.
  Next Obligation. by iIntros (???[|[[]|][]]) "?". Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hαβ _]". done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ $]". done.
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

  Global Instance rwlockwriteguard_wf α ty `{!TyWf ty} : TyWf (rwlockwriteguard α ty) :=
    { ty_lfts := [α]; ty_wf_E := ty.(ty_wf_E) ++ ty.(ty_outlives_E) α }.

  Global Instance rwlockwriteguard_type_contractive α : TypeContractive (rwlockwriteguard α).
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || (eapply rwlock_inv_type_ne; try reflexivity) ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.
  Global Instance rwlockwriteguard_ne α : NonExpansive (rwlockwriteguard α).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance rwlockwriteguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) rwlockwriteguard.
  Proof.
    intros α1 α2 Hα ty1 ty2 Hty. generalize Hty. rewrite eqtype_unfold. iIntros (Hty' q) "HL".
    iDestruct (Hty' with "HL") as "#Hty". iDestruct (Hα with "HL") as "#Hα".
    iDestruct (rwlock_inv_proper with "HL") as "#Hty1ty2"; first done.
    iDestruct (rwlock_inv_proper with "HL") as "#Hty2ty1"; first by symmetry.
    iIntros "!# #HE". iDestruct ("Hα" with "HE") as "Hα1α2".
    iDestruct ("Hty" with "HE") as "(%&#Ho&#Hs)". iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][]]) "H"; try done.
      iDestruct "H" as (γ β) "(Hb & #H⊑ & #Hinv & Hown)".
      iExists γ, β. iFrame "∗#". iSplit; last iSplit.
      + iApply bor_iff; last done.
        iSplit; iIntros "!>!# H"; iDestruct "H" as (vl) "[??]";
        iExists vl; iFrame; by iApply "Ho".
      + by iApply lft_incl_trans.
      + iApply shr_bor_iff; try done.
        iIntros "!>!#"; iSplit; iIntros "H". by iApply "Hty1ty2". by iApply "Hty2ty1".
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "H". iExists l'.
      iDestruct "H" as "[$ #H]". iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. done. iApply lft_incl_refl. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. done. iApply lft_incl_refl.
      by iApply "Hs".
  Qed.
  Global Instance rwlockwriteguard_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) rwlockwriteguard.
  Proof. intros ??????. by apply rwlockwriteguard_mono. Qed.
  Lemma rwlockwriteguard_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (rwlockwriteguard α1 ty1) (rwlockwriteguard α2 ty2) .
  Proof. intros. by eapply rwlockwriteguard_mono. Qed.
  Global Instance rwlockwriteguard_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E  L) rwlockwriteguard.
  Proof. intros ??[]???. split; by apply rwlockwriteguard_mono'. Qed.
  Lemma rwlockwriteguard_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (rwlockwriteguard α1 ty1) (rwlockwriteguard α2 ty2).
  Proof. intros. by eapply rwlockwriteguard_proper. Qed.

  (* Rust requires the type to also be Send.  Not sure why. *)
  Global Instance rwlockwriteguard_sync α ty :
    Sync ty → Sync (rwlockwriteguard α ty).
  Proof.
    move=>?????/=. apply uPred.exist_mono=>?. do 6 f_equiv.
    by rewrite sync_change_tid.
  Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for RwLockWriteGuard. We could
     prove this. *)
End rwlockwriteguard.

Hint Resolve rwlockwriteguard_mono' rwlockwriteguard_proper' : lrust_typing.
