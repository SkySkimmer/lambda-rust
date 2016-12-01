From lrust.lifetime Require Export borrow derived.
From lrust.lifetime Require Import raw_reborrow.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.

Section reborrow.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma rebor E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx -∗ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗ &{κ}P).
Proof.
  iIntros (?) "#LFT #H⊑". rewrite {1}/bor; iDestruct 1 as (κ'') "[#H⊑' Hκ'']".
  iMod (raw_rebor _ _ (κ' ∪ κ'') with "LFT Hκ''") as "[Hκ'' Hclose]"; first done.
  { apply gmultiset_union_subseteq_r. }
  iModIntro. iSplitL "Hκ''".
  - rewrite /bor. iExists (κ' ∪ κ''). iFrame "Hκ''".
    iApply (lft_incl_glb with "[]"); first iApply lft_incl_refl.
    by iApply (lft_incl_trans with "H⊑").
  - iIntros "Hκ†". iMod ("Hclose" with "[Hκ†]") as "Hκ''".
    { iApply lft_dead_or; auto. }
    iModIntro. rewrite /bor. eauto. 
Qed.

Lemma bor_unnest E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ'} &{κ} P ={E, E∖↑lftN}▷=∗ &{κ ∪ κ'} P.
Proof.
  iIntros (?) "#LFT Hκ". rewrite {2}/bor.
  iMod (bor_exists with "LFT Hκ") as (κ0) "Hκ"; first done.
  rewrite {1}/bor; iDestruct "Hκ" as (κ0') "[#H⊑ Hκ]".
  set (κ'' := κ0 ∪ κ0').
  iMod (raw_rebor _ _ κ'' with "LFT Hκ") as "[Hκ _]"; first done.
  { apply gmultiset_union_subseteq_r. }
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ'' with "HA HI Hinv") as (A' I') "(% & HA & HI & Hinv)".
  clear A I; rename A' into A; rename I' into I.
  iDestruct (big_sepS_delete _ _ κ'' with "Hinv") as "[Hinv' Hinv]";
    first by apply elem_of_dom.
  rewrite {1}/lft_inv; iDestruct "Hinv'" as "[[Hinv' >%]|[Hdead >%]]"; last first.
  { rewrite /lft_inv_dead;
      iDestruct "Hdead" as (Pi) "(Hdead & Hcnt & Hinh)".
    iMod (raw_bor_fake _ true _ P with "Hdead")
      as "[Hdead Hbor]"; first solve_ndisj.
    iMod ("Hclose" with "[- Hbor]") as "_".
    { rewrite /lfts_inv. iExists A, I. iFrame "HA HI".
      iApply (big_sepS_delete _ _ κ''); first by apply elem_of_dom.
      iNext; iFrame "Hinv". rewrite /lft_inv. iRight. iSplit; last auto.
      rewrite /lft_inv_dead. iExists Pi. iFrame. }
    iApply (step_fupd_mask_mono E _ _ E); try solve_ndisj.
    rewrite /bor. do 3 iModIntro. 
    iExists κ''. iFrame "Hbor". rewrite /κ''.
    (* Why is this going to work out *)
    admit. }
  rewrite {1}/raw_bor /idx_bor_own /=; iDestruct "Hκ" as (i) "[Hi #Hislice]".
  rewrite lft_inv_alive_unfold;
    iDestruct "Hinv'" as (Pb Pi) "(Halive & Hvs & Hinh)".
  rewrite /lft_bor_alive; iDestruct "Halive" as (B) "(Hbox & >HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi")
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (own_bor_update_2 with "HB● Hi") as "[HB● Hi]".
Admitted.
End reborrow.
