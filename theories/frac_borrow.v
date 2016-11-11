From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.
From lrust Require Export lifetime shr_borrow.

Class frac_borrowG Σ := frac_borrowG_inG :> inG Σ fracR.

Definition frac_borrow `{invG Σ, lifetimeG Σ, frac_borrowG Σ} κ (Φ : Qp → iProp Σ) :=
  (∃ γ κ', κ ⊑ κ' ∗ &shr{κ'} ∃ q, Φ q ∗ own γ q ∗
                       (q = 1%Qp ∨ ∃ q', (q + q')%Qp = 1%Qp ∗ q'.[κ']))%I.
Notation "&frac{ κ } P" := (frac_borrow κ P)
  (format "&frac{ κ } P", at level 20, right associativity) : uPred_scope.

Section frac_borrow.

  Context `{invG Σ, lifetimeG Σ, frac_borrowG Σ}.

  Global Instance frac_borrow_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (frac_borrow κ).
  Proof. solve_proper. Qed.
  Global Instance frac_borrow_persistent : PersistentP (&frac{κ}φ) := _.

  Lemma borrow_fracture φ `(nclose lftN ⊆ E) κ:
    lft_ctx ⊢ &{κ}(φ 1%Qp) ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros "#LFT Hφ". iMod (own_alloc 1%Qp) as (γ) "?". done.
    iMod (borrow_acc_atomic_strong with "LFT Hφ") as "[[Hφ Hclose]|[H† Hclose]]". done.
    - iMod ("Hclose" with "*[-]") as "Hφ"; last first.
      { iExists γ, κ. iSplitR; last by iApply (borrow_share with "Hφ").
        iApply lft_incl_refl. }
      iSplitL. by iExists 1%Qp; iFrame; auto.
      iIntros "!>H† Hφ!>". iNext. iDestruct "Hφ" as (q') "(Hφ & _ & [%|Hκ])". by subst.
      iDestruct "Hκ" as (q'') "[_ Hκ]".
      iDestruct (lft_own_dead with "Hκ H†") as "[]".
    - iMod ("Hclose" with "*") as "Hφ"; last first.
      iExists γ, κ. iSplitR. by iApply lft_incl_refl.
      iMod (borrow_fake with "LFT H†"). done. by iApply borrow_share.
  Qed.

  Lemma frac_borrow_atomic_acc `(nclose lftN ⊆ E) κ φ:
    lft_ctx ⊢ &frac{κ}φ ={E,E∖lftN}=∗ (∃ q, ▷ φ q ∗ (▷ φ q ={E∖lftN,E}=∗ True))
                                      ∨ [†κ] ∗ |={E∖lftN,E}=> True.
  Proof.
    iIntros "#LFT #Hφ". iDestruct "Hφ" as (γ κ') "[Hκκ' Hshr]".
    iMod (shr_borrow_acc with "LFT Hshr") as "[[Hφ Hclose]|[H† Hclose]]". done.
    - iLeft. iDestruct "Hφ" as (q) "(Hφ & Hγ & H)". iExists q. iFrame.
      iIntros "!>Hφ". iApply "Hclose". iExists q. iFrame.
    - iRight. iMod "Hclose" as "_". iMod (lft_incl_dead with "Hκκ' H†") as "$". done.
      iApply fupd_intro_mask. set_solver. done.
  Qed.

  Lemma frac_borrow_acc `(nclose lftN ⊆ E) q κ φ:
    lft_ctx ⊢ □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) -∗
    &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros "#LFT #Hφ Hfrac Hκ". unfold frac_borrow.
    iDestruct "Hfrac" as (γ κ') "#[#Hκκ' Hshr]".
    iMod (lft_incl_acc with "Hκκ' Hκ") as (qκ') "[[Hκ1 Hκ2] Hclose]". done.
    iMod (shr_borrow_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & Hq)".
    destruct (Qp_lower_bound (qκ'/2) (qφ/2)) as (qq & qκ'0 & qφ0 & Hqκ' & Hqφ).
    iExists qq.
    iAssert (▷ φ qq ∗ ▷ φ (qφ0 + qφ / 2))%Qp%I with "[Hφqφ]" as "[$ Hqφ]".
    { iNext. rewrite -{1}(Qp_div_2 qφ) {1}Hqφ. iApply "Hφ". by rewrite assoc. }
    rewrite -{1}(Qp_div_2 qφ) {1}Hqφ -assoc {1}Hqκ'.
    iDestruct "Hκ2" as "[Hκq Hκqκ0]". iDestruct "Hown" as "[Hownq Hown]".
    iMod ("Hclose'" with "[Hqφ Hq Hown Hκq]") as "Hκ1".
    { iNext. iExists _. iFrame. iRight. iDestruct "Hq" as "[%|Hq]".
      - subst. iExists qq. iIntros "{$Hκq}!%".
        by rewrite (comm _ qφ0) -assoc (comm _ qφ0) -Hqφ Qp_div_2.
      - iDestruct "Hq" as (q') "[% Hq'κ]". iExists (qq + q')%Qp.
        rewrite lft_own_frac_op. iIntros "{$Hκq $Hq'κ}!%".
        by rewrite assoc (comm _ _ qq) assoc -Hqφ Qp_div_2. }
    clear Hqφ qφ qφ0. iIntros "!>Hqφ".
    iMod (shr_borrow_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & >[%|Hq])".
    { subst. iCombine "Hown" "Hownq" as "Hown".
      by iDestruct (own_valid with "Hown") as %Hval%Qp_not_plus_q_ge_1. }
    iDestruct "Hq" as (q') "[Hqφq' Hq'κ]". iCombine "Hown" "Hownq" as "Hown".
    iDestruct (own_valid with "Hown") as %Hval. iDestruct "Hqφq'" as %Hqφq'.
    assert (0 < q'-qq ∨ qq = q')%Qc as [Hq'q|<-].
    { change (qφ + qq ≤ 1)%Qc in Hval. apply Qp_eq in Hqφq'. simpl in Hval, Hqφq'.
      rewrite <-Hqφq', <-Qcplus_le_mono_l in Hval. apply Qcle_lt_or_eq in Hval.
      destruct Hval as [Hval|Hval].
      by left; apply ->Qclt_minus_iff. by right; apply Qp_eq, Qc_is_canon. }
    - assert (q' = mk_Qp _ Hq'q + qq)%Qp as ->. { apply Qp_eq. simpl. ring. }
      iDestruct "Hq'κ" as "[Hq'qκ Hqκ]".
      iMod ("Hclose'" with "[Hqφ Hφqφ Hown Hq'qκ]") as "Hqκ2".
      { iNext. iExists (qφ + qq)%Qp. iFrame. iSplitR "Hq'qκ". by iApply "Hφ"; iFrame.
        iRight. iExists _. iIntros "{$Hq'qκ}!%".
        revert Hqφq'. rewrite !Qp_eq. move=>/=<-. ring. }
      iApply "Hclose". iFrame. rewrite Hqκ' !lft_own_frac_op. by iFrame.
    - iMod ("Hclose'" with "[Hqφ Hφqφ Hown]") as "Hqκ2".
      { iNext. iExists (qφ ⋅ qq)%Qp. iFrame. iSplitL. by iApply "Hφ"; iFrame. auto. }
      iApply "Hclose". rewrite -{2}(Qp_div_2 qκ') {2}Hqκ' !lft_own_frac_op. by iFrame.
  Qed.

  Lemma frac_borrow_shorten κ κ' φ: κ ⊑ κ' ⊢ &frac{κ'}φ -∗ &frac{κ}φ.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (γ κ0) "[H⊑?]". iExists γ, κ0. iFrame.
    iApply lft_incl_trans. iFrame.
  Qed.

  Lemma frac_borrow_incl κ κ' q:
    lft_ctx ⊢ &frac{κ}(λ q', (q * q').[κ']) -∗ κ ⊑ κ'.
  Proof.
    iIntros "#LFT#Hbor!#". iSplitR.
    - iIntros (q') "Hκ'".
      iMod (frac_borrow_acc with "LFT [] Hbor Hκ'") as (q'') "[>? Hclose]". done.
      + iIntros "/=!#*". rewrite Qp_mult_plus_distr_r lft_own_frac_op. iSplit; auto.
      + iExists _. iFrame. iIntros "!>Hκ'". iApply "Hclose". auto.
    - iIntros "H†'".
      iMod (frac_borrow_atomic_acc with "LFT Hbor") as "[H|[$ $]]". done.
      iDestruct "H" as (q') "[>Hκ' _]".
      iDestruct (lft_own_dead with "Hκ' H†'") as "[]".
  Qed.

End frac_borrow.

Typeclasses Opaque frac_borrow.
