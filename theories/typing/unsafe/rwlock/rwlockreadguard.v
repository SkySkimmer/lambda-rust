From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.rwlock Require Import rwlock.
Set Default Proof Using "Type".

Section rwlockreadguard.
  Context `{typeG Σ, rwlockG Σ}.

  (* Original Rust type:
    pub struct RwLockReadGuard<'a, T: ?Sized + 'a> {
        __lock: &'a RwLock<T>,
    }
  *)

  Program Definition rwlockreadguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ ν q γ β, ty.(ty_shr) (α ∪ ν) tid (shift_loc l 1) ∗
             α ⊑ β ∗ &shr{β,rwlockN}(rwlock_inv tid l γ β ty) ∗
             q.[ν] ∗ own γ (◯ reading_st q ν) ∗
             (1.[ν] ={↑lftN,∅}▷=∗ [†ν])
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (l' : loc),
           &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
           ▷ ty.(ty_shr) (α ∪ κ) tid (shift_loc l' 1) |}%I.
  Next Obligation. intros α ty tid [|[[]|] []]; auto. Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb". done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[Hshr Hb]". done.
    iMod (bor_persistent_tok with "LFT Hshr Htok") as "[#Hshr Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ Hb]". done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]". done.
    iMod (bor_persistent_tok with "LFT Hinv Htok") as "[#Hinv $]". done.
    iMod (bor_sep with "LFT Hb") as "[Hκν _]". done.
    iDestruct (frac_bor_lft_incl with "LFT >[Hκν]") as "#Hκν".
    { iApply bor_fracture; try done. by rewrite Qp_mult_1_r. }
    iExists _. iFrame "#". iApply ty_shr_mono; last done.
    iApply lft_glb_mono; last done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (α ty κ κ' tid l) "#Hκ'κ H". iDestruct "H" as (l') "[#Hf #Hshr]".
    iExists l'. iSplit; first by iApply frac_bor_shorten.
    iApply ty_shr_mono; last done. iApply lft_glb_mono; last done.
    iApply lft_incl_refl.
  Qed.

  Global Instance rwlockreadguard_contractive α : Contractive (rwlockreadguard α).
  Proof.
    intros n ?? EQ. unfold rwlockreadguard. constructor=>//=.
    - intros tid vl. destruct n as [|n]=>//=. by repeat f_equiv.
    - intros κ tid l. repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance rwlockreadguard_ne n α : Proper (dist n ==> dist n) (rwlockreadguard α).
  Proof. apply contractive_ne, _. Qed.

  (* The rust type is not covariant, although it probably could (cf. refcell).
     This would require changing the definition of the type, though. *)
  Global Instance rwlockreadguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) rwlockreadguard.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty) "#HE #HL".
    iDestruct (proj1 Hty with "HE HL") as "(%&#Ho&#Hs)".
    iDestruct (Hα with "HE HL") as "Hα1α2".
    iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][]]) "H"; try done.
      iDestruct "H" as (ν q γ β) "(#Hshr & #H⊑ & #Hinv & Htok & Hown)".
      iExists ν, q, γ, β. iFrame "∗#". iSplit; last iSplit.
      + iApply ty_shr_mono; last by iApply "Hs".
        iApply lft_glb_mono. done. iApply lft_incl_refl.
      + by iApply lft_incl_trans.
      + iApply (shr_bor_iff with "[] Hinv").
        iIntros "!>!#"; iSplit; iIntros "H"; by iApply rwlock_inv_proper.
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "[Hf Hshr]". iExists l'.
      iFrame. iApply ty_shr_mono; last by iApply "Hs".
      iApply lft_glb_mono. done. iApply lft_incl_refl.
  Qed.
  Global Instance rwlockreadguard_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L))
           rwlockreadguard.
  Proof. intros ??????. by apply rwlockreadguard_mono. Qed.
  Lemma rwlockreadguard_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_mono. Qed.
  Global Instance rwlockreadguard_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) rwlockreadguard.
  Proof. intros ??[]?? EQ. split; apply rwlockreadguard_mono'; try done; apply EQ. Qed.
  Lemma rwlockreadguard_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_proper. Qed.
End rwlockreadguard.

Hint Resolve rwlockreadguard_mono' rwlockreadguard_proper' : lrust_typing.
