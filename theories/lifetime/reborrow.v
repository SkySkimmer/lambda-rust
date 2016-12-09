From lrust.lifetime Require Export borrow derived.
From lrust.lifetime Require Import raw_reborrow accessors.
From iris.algebra Require Import csum auth frac gmap agree gset.
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
  iMod (bor_sep with "LFT Hκ") as "[Hκ⊑ Hκ]"; first done.
  rewrite {2}/bor; iDestruct "Hκ" as (κ0') "[#Hκ'⊑ Hκ]".
  iMod (bor_acc_atomic with "LFT Hκ⊑") as "[[#Hκ⊑ Hclose]|[#H† Hclose]]"; first done; last first.
  { iModIntro. iNext. iMod "Hclose" as "_". iApply (bor_fake with "LFT"); first done.
    iApply lft_dead_or. iRight. done. }
  iMod ("Hclose" with "Hκ⊑") as "_".
  set (κ'' := κ0 ∪ κ0').
  iMod (raw_rebor _ _ κ'' with "LFT Hκ") as "[Hκ _]"; first done.
  { apply gmultiset_union_subseteq_r. }
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ'' with "HA HI Hinv") as (A' I') "(% & HA & HI & Hinv)".
  clear A I; rename A' into A; rename I' into I.
  iDestruct (big_sepS_delete _ _ κ'' with "Hinv") as "[Hκ'' Hinv]";
    first by apply elem_of_dom.
  rewrite {1}/lft_inv; iDestruct "Hκ''" as "[[Hinv' >%]|[Hdead >Hdeadin]]"; last first.
  { iDestruct "Hdeadin" as %Hdeadin. iMod (lft_dead_in_tok with "HA") as "[HA #H†]"; first done.
    iMod ("Hclose" with "[-]") as "_".
    { rewrite /lfts_inv. iExists A, I. iFrame "HA HI".
      iApply (big_sepS_delete _ _ κ''); first by apply elem_of_dom.
      iNext; iFrame "Hinv". rewrite /lft_inv. iRight. iSplit; auto. }
    iMod (fupd_intro_mask') as "Hclose"; last iModIntro; first solve_ndisj.
    iNext. iMod "Hclose" as "_".
    iApply (bor_fake with "LFT >"); first done.
    iApply (lft_incl_dead with "[] H†"); first done.
    by iApply (lft_incl_mono with "Hκ⊑"). }
  rewrite {1}/raw_bor /idx_bor_own /=; iDestruct "Hκ" as (i) "[Hi #Hislice]".
  rewrite lft_inv_alive_unfold;
    iDestruct "Hinv'" as (Pb Pi) "(Halive & Hvs & Hinh)".
  rewrite /lft_bor_alive; iDestruct "Halive" as (B) "(Hbox & >HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi")
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (slice_delete_full _ _ true with "Hislice Hbox") as (Pb') "(HP & #EQ & Hbox)"; first solve_ndisj.
  {  by rewrite lookup_fmap HB. }
  iMod (own_bor_update_2 with "HB● Hi") as "HB●".
  { apply auth_update_dealloc, delete_singleton_local_update. apply _. }
  iMod (fupd_intro_mask') as "Hclose'"; last iModIntro; first solve_ndisj.
  iNext. iMod "Hclose'" as "_".
  iAssert (lft_bor_alive κ'' Pb') with "[Hbox HB● HB]" as "Halive".
  { rewrite /lft_bor_alive. iExists (delete i B).
    rewrite fmap_delete. iFrame "Hbox". iSplitL "HB●".
    - rewrite /to_borUR fmap_delete. done.
    - rewrite big_sepM_delete; last done. iDestruct "HB" as "[_ $]". }
  iMod (raw_bor_unnest' _ false with "[$HI $Hinv] HP Halive [Hvs]") as (Pb'') "([HI Hinv] & HP & Halive & Hvs)";
    [solve_ndisj|exact: gmultiset_union_subseteq_l|done| |].
  { (* TODO: Use iRewrite supporting contractive rewriting. *)
    iApply (lft_vs_cons with "[]"); last done.
     iIntros "[$ Hbor]". iModIntro. iNext. by iRewrite "EQ". }
  iMod ("Hclose" with "[-HP]") as "_".
  { iNext. simpl. rewrite /lfts_inv. iExists A, I. iFrame.
    rewrite (big_sepS_delete _ (dom _ I) κ''); last by apply elem_of_dom.
    iFrame. rewrite /lft_inv lft_inv_alive_unfold. iLeft.
    iFrame "%". iExists Pb'', Pi. iFrame. }
  iModIntro. rewrite /bor. iExists κ''. iFrame. subst κ''.
  by iApply (lft_incl_mono with "Hκ⊑").
Qed.

End reborrow.
