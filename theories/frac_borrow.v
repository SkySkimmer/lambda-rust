From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics fractional.
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
  Global Instance frac_borrow_persistent : PersistentP (&frac{κ}Φ) := _.

  Lemma borrow_fracture Φ `(nclose lftN ⊆ E) κ:
    lft_ctx ⊢ &{κ}(Φ 1%Qp) ={E}=∗ &frac{κ}Φ.
  Proof.
    iIntros "#LFT HΦ". iMod (own_alloc 1%Qp) as (γ) "?". done.
    iMod (borrow_acc_atomic_strong with "LFT HΦ") as "[[HΦ Hclose]|[H† Hclose]]". done.
    - iMod ("Hclose" with "*[-]") as "HΦ"; last first.
      { iExists γ, κ. iSplitR; last by iApply (borrow_share with "HΦ").
        iApply lft_incl_refl. }
      iSplitL. by iExists 1%Qp; iFrame; auto.
      iIntros "!>H† HΦ!>". iNext. iDestruct "HΦ" as (q') "(HΦ & _ & [%|Hκ])". by subst.
      iDestruct "Hκ" as (q'') "[_ Hκ]".
      iDestruct (lft_own_dead with "Hκ H†") as "[]".
    - iMod ("Hclose" with "*") as "HΦ"; last first.
      iExists γ, κ. iSplitR. by iApply lft_incl_refl.
      iMod (borrow_fake with "LFT H†"). done. by iApply borrow_share.
  Qed.

  Lemma frac_borrow_atomic_acc `(nclose lftN ⊆ E) κ Φ:
    lft_ctx ⊢ &frac{κ}Φ ={E,E∖lftN}=∗ (∃ q, ▷ Φ q ∗ (▷ Φ q ={E∖lftN,E}=∗ True))
                                      ∨ [†κ] ∗ |={E∖lftN,E}=> True.
  Proof.
    iIntros "#LFT #HΦ". iDestruct "HΦ" as (γ κ') "[Hκκ' Hshr]".
    iMod (shr_borrow_acc with "LFT Hshr") as "[[HΦ Hclose]|[H† Hclose]]". done.
    - iLeft. iDestruct "HΦ" as (q) "(HΦ & Hγ & H)". iExists q. iFrame.
      iIntros "!>HΦ". iApply "Hclose". iExists q. iFrame.
    - iRight. iMod "Hclose" as "_". iMod (lft_incl_dead with "Hκκ' H†") as "$". done.
      iApply fupd_intro_mask. set_solver. done.
  Qed.

  Lemma frac_borrow_acc_strong `(nclose lftN ⊆ E) q κ Φ:
    lft_ctx ⊢ □ (∀ q1 q2, Φ (q1+q2)%Qp ↔ Φ q1 ∗ Φ q2) -∗
    &frac{κ}Φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ Φ q' ∗ (▷ Φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros "#LFT #HΦ Hfrac Hκ". unfold frac_borrow.
    iDestruct "Hfrac" as (γ κ') "#[#Hκκ' Hshr]".
    iMod (lft_incl_acc with "Hκκ' Hκ") as (qκ') "[[Hκ1 Hκ2] Hclose]". done.
    iMod (shr_borrow_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qΦ) "(HΦqΦ & >Hown & Hq)".
    destruct (Qp_lower_bound (qκ'/2) (qΦ/2)) as (qq & qκ'0 & qΦ0 & Hqκ' & HqΦ).
    iExists qq.
    iAssert (▷ Φ qq ∗ ▷ Φ (qΦ0 + qΦ / 2))%Qp%I with "[HΦqΦ]" as "[$ HqΦ]".
    { iNext. rewrite -{1}(Qp_div_2 qΦ) {1}HqΦ. iApply "HΦ". by rewrite assoc. }
    rewrite -{1}(Qp_div_2 qΦ) {1}HqΦ -assoc {1}Hqκ'.
    iDestruct "Hκ2" as "[Hκq Hκqκ0]". iDestruct "Hown" as "[Hownq Hown]".
    iMod ("Hclose'" with "[HqΦ Hq Hown Hκq]") as "Hκ1".
    { iNext. iExists _. iFrame. iRight. iDestruct "Hq" as "[%|Hq]".
      - subst. iExists qq. iIntros "{$Hκq}!%".
        by rewrite (comm _ qΦ0) -assoc (comm _ qΦ0) -HqΦ Qp_div_2.
      - iDestruct "Hq" as (q') "[% Hq'κ]". iExists (qq + q')%Qp.
        iIntros "{$Hκq $Hq'κ}!%". by rewrite assoc (comm _ _ qq) assoc -HqΦ Qp_div_2. }
    clear HqΦ qΦ qΦ0. iIntros "!>HqΦ".
    iMod (shr_borrow_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qΦ) "(HΦqΦ & >Hown & >[%|Hq])".
    { subst. iCombine "Hown" "Hownq" as "Hown".
      by iDestruct (own_valid with "Hown") as %Hval%Qp_not_plus_q_ge_1. }
    iDestruct "Hq" as (q') "[HqΦq' Hq'κ]". iCombine "Hown" "Hownq" as "Hown".
    iDestruct (own_valid with "Hown") as %Hval. iDestruct "HqΦq'" as %HqΦq'.
    assert (0 < q'-qq ∨ qq = q')%Qc as [Hq'q|<-].
    { change (qΦ + qq ≤ 1)%Qc in Hval. apply Qp_eq in HqΦq'. simpl in Hval, HqΦq'.
      rewrite <-HqΦq', <-Qcplus_le_mono_l in Hval. apply Qcle_lt_or_eq in Hval.
      destruct Hval as [Hval|Hval].
      by left; apply ->Qclt_minus_iff. by right; apply Qp_eq, Qc_is_canon. }
    - assert (q' = mk_Qp _ Hq'q + qq)%Qp as ->. { apply Qp_eq. simpl. ring. }
      iDestruct "Hq'κ" as "[Hq'qκ Hqκ]".
      iMod ("Hclose'" with "[HqΦ HΦqΦ Hown Hq'qκ]") as "Hqκ2".
      { iNext. iExists (qΦ + qq)%Qp. iFrame. iSplitR "Hq'qκ". by iApply "HΦ"; iFrame.
        iRight. iExists _. iIntros "{$Hq'qκ}!%".
        revert HqΦq'. rewrite !Qp_eq. move=>/=<-. ring. }
      iApply "Hclose". iFrame. rewrite Hqκ'. by iFrame.
    - iMod ("Hclose'" with "[HqΦ HΦqΦ Hown]") as "Hqκ2".
      { iNext. iExists (qΦ ⋅ qq)%Qp. iFrame. iSplitL. by iApply "HΦ"; iFrame. auto. }
      iApply "Hclose". iFrame. rewrite Hqκ'. by iFrame.
  Qed.

  Lemma frac_borrow_acc `(nclose lftN ⊆ E) q κ Φ:
    Fractional Φ →
    lft_ctx ⊢ &frac{κ}Φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ Φ q' ∗ (▷ Φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "LFT". iApply (frac_borrow_acc_strong with "LFT"). done.
    iIntros "!#*". rewrite fractional. iSplit; auto.
  Qed.

  Lemma frac_borrow_shorten κ κ' Φ: κ ⊑ κ' ⊢ &frac{κ'}Φ -∗ &frac{κ}Φ.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (γ κ0) "[H⊑?]". iExists γ, κ0. iFrame.
    iApply lft_incl_trans. iFrame.
  Qed.

  Lemma frac_borrow_incl κ κ' q:
    lft_ctx ⊢ &frac{κ}(λ q', (q * q').[κ']) -∗ κ ⊑ κ'.
  Proof.
    iIntros "#LFT#Hbor!#". iSplitR.
    - iIntros (q') "Hκ'".
      iMod (frac_borrow_acc with "LFT Hbor Hκ'") as (q'') "[>? Hclose]". done.
      iExists _. iFrame. iIntros "!>Hκ'". iApply "Hclose". auto.
    - iIntros "H†'".
      iMod (frac_borrow_atomic_acc with "LFT Hbor") as "[H|[$ $]]". done.
      iDestruct "H" as (q') "[>Hκ' _]".
      iDestruct (lft_own_dead with "Hκ' H†'") as "[]".
  Qed.

End frac_borrow.

Typeclasses Opaque frac_borrow.
