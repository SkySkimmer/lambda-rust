From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.rwlock Require Import rwlock.
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
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α ∪ κ] ={F, F∖↑shrN∖↑lftN}▷=∗
               ty.(ty_shr) (α ∪ κ) tid (shift_loc l' 1) ∗ q.[α ∪ κ] |}%I.
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
    iExists _. iFrame "H↦". rewrite {1}bor_unfold_idx.
    iDestruct "Hb" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (α ∪ κ) tid (shift_loc l' 1))%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". clear HE.
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT [Hb] Htok") as "[#Hshr $]". solve_ndisj.
      { iApply (bor_shorten with "[] Hb"). iApply lft_glb_mono. done.
        iApply lft_incl_refl. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (l') "[#Hf #H]".
    iExists _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance rwlockwriteguard_contractive α : Contractive (rwlockwriteguard α).
  Proof.
    intros n ?? EQ. unfold rwlockwriteguard. constructor=>//=.
    - intros tid vl. destruct n as [|n]=>//=.
      do 9 f_equiv. solve_contractive. by repeat f_equiv.
    - intros κ tid l. repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance rwlockwriteguard_ne α : NonExpansive (rwlockwriteguard α).
  Proof. apply contractive_ne, _. Qed.

  Global Instance rwlockwriteguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) rwlockwriteguard.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty) "#HE #HL".
    pose proof Hty as Hty'%eqtype_unfold.
    iDestruct (Hty' with "HE HL") as "(%&#Ho&#Hs)".
    iDestruct (Hα with "HE HL") as "Hα1α2".
    iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][]]) "H"; try done.
      iDestruct "H" as (γ β) "(Hb & #H⊑ & #Hinv & Hown)".
      iExists γ, β. iFrame "∗#". iSplit; last iSplit.
      + iApply bor_iff; last done.
        iSplit; iIntros "!>!# H"; iDestruct "H" as (vl) "[??]";
        iExists vl; iFrame; by iApply "Ho".
      + by iApply lft_incl_trans.
      + iApply shr_bor_iff; try done.
        iIntros "!>!#"; iSplit; iIntros "H"; by iApply rwlock_inv_proper.
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "H". iExists l'.
      iDestruct "H" as "[$ #H]". iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. done. iApply lft_incl_refl. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. done. iApply lft_incl_refl.
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
End rwlockwriteguard.

Hint Resolve rwlockwriteguard_mono' rwlockwriteguard_proper' : lrust_typing.
