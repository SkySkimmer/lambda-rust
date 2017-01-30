From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.refcell Require Import refcell.
Set Default Proof Using "Type".

Section refmut.
  Context `{typeG Σ, refcellG Σ}.
  Local Hint Extern 1000 (_ ⊆ _) => set_solver : ndisj.

  Program Definition refmut (α : lft) (ty : type) :=
    {| ty_size := 2;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc lv);  #(LitLoc lrc) ] =>
           ∃ ν γ β ty', &{α ∪ ν}(lv ↦∗: ty.(ty_own) tid) ∗
             α ⊑ β ∗ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             1.[ν] ∗ own γ (◯ writing_st ν)
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (lv lrc : loc),
           &frac{κ} (λ q, l↦∗{q} [ #lv; #lrc]) ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α ∪ κ]
             ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (α ∪ κ) tid lv ∗ q.[α ∪ κ] |}%I.
  Next Obligation.
    iIntros (???[|[[]|][|[[]|][]]]); try iIntros "[]". by iIntros "_".
  Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (ty') "Hb". done.
    rewrite (assoc _ _ (α ⊑ β)%I). iMod (bor_sep with "LFT Hb") as "[Hb H]". done.
    rewrite (comm _ (1).[ν])%I. rewrite (assoc _ _ _ (1).[ν])%I.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_fracture (λ q, (1 * q).[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mult_1_l. }
    iDestruct (frac_bor_lft_incl _ _ 1 with "LFT H") as "#Hκν". iClear "H".
    iMod (bor_sep with "LFT Hb") as "[Hb Hαβ]". done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ $]". done.
    iExists _, _. iFrame "H↦". rewrite {1}bor_unfold_idx.
    iDestruct "Hb" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (α ∪ κ) tid lv)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". clear HE.
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT [Hb] Htok") as "[#Hshr $]". solve_ndisj.
      { iApply bor_shorten; last done. rewrite -assoc.
        iApply lft_glb_mono; first by iApply lft_incl_refl.
        iApply lft_incl_glb; first done. iApply lft_incl_refl. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    iIntros (??????) "#? #? H". iDestruct "H" as (lv lrc) "[#Hf #H]".
    iExists _, _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance refmut_contractive α : Contractive (refmut α).
  Proof.
    intros n ?? EQ. unfold refmut. split; [split|]=>//=.
    - f_contractive=>tid vl. repeat (f_contractive || f_equiv). apply EQ.
    - intros κ tid l. repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance refmut_ne n α : Proper (dist n ==> dist n) (refmut α).
  Proof. apply contractive_ne, _. Qed.

  Global Instance refmut_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) refmut.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty) "#LFT #HE #HL".
    pose proof Hty as Hty'%eqtype_unfold.
    iDestruct (Hty' with "LFT HE HL") as "(%&#Ho&#Hs)".
    iDestruct (Hα with "HE HL") as "Hα1α2".
    iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][|[[]|][]]]); try iIntros "[]". iIntros "H".
      iDestruct "H" as (ν γ β ty') "(Hb & #H⊑ & #Hinv & Hν & Hown)".
      iExists ν, γ, β, ty'. iFrame "∗#". iSplit.
      + iApply bor_shorten; last iApply bor_iff; last done.
        * iApply lft_glb_mono; first done. iApply lft_incl_refl.
        * iSplit; iIntros "!>!# H"; iDestruct "H" as (vl) "[??]";
          iExists vl; iFrame; by iApply "Ho".
      + by iApply lft_incl_trans.
    - iIntros (κ tid l) "H". iDestruct "H" as (lv lrc) "H". iExists lv, lrc.
      iDestruct "H" as "[$ #H]". iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. done. iApply lft_incl_refl. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. done. iApply lft_incl_refl.
      by iApply "Hs".
  Qed.
  Global Instance refmut_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) refmut.
  Proof. intros ??????. by apply refmut_mono. Qed.
  Lemma refmut_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (refmut α1 ty1) (refmut α2 ty2) .
  Proof. intros. by eapply refmut_mono. Qed.
  Global Instance refmut_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E  L) refmut.
  Proof. intros ??[]???. split; by apply refmut_mono'. Qed.
  Lemma refmut_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (refmut α1 ty1) (refmut α2 ty2).
  Proof. intros. by eapply refmut_proper. Qed.
End refmut.

Hint Resolve refmut_mono' refmut_proper' : lrust_typing.
