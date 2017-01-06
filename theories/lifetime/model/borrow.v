From lrust.lifetime Require Export primitive.
From lrust.lifetime Require Export faking raw_reborrow.
From iris.algebra Require Import csum auth frac gmap agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section borrow.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma bor_create E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
Proof.
  iIntros (HE) "#LFT HP". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ with "HA HI Hinv") as (A' I') "(Hκ & HA & HI & Hinv)".
  iDestruct "Hκ" as %Hκ. iDestruct (@big_sepS_later with "Hinv") as "Hinv".
  iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hinv Hclose']".
  { by apply elem_of_dom. }
  rewrite {1}/lft_inv. iDestruct "Hinv" as "[[Hinv >%]|[Hinv >%]]".
  - rewrite {1}lft_inv_alive_unfold;
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    rewrite /lft_bor_alive; iDestruct "Halive" as (B) "(HboxB & >HownB & HB)".
    iMod (lft_inh_extend _ _ P with "Hinh")
      as "(Hinh & HIlookup & Hinh_close)"; first solve_ndisj.
    iMod (slice_insert_full _ _ true with "HP HboxB")
      as (γB) "(HBlookup & HsliceB & HboxB)"; first by solve_ndisj.
    rewrite lookup_fmap. iDestruct "HBlookup" as %HBlookup.
    rewrite -(fmap_insert bor_filled _ _ Bor_in).
    iMod (own_bor_update with "HownB") as "[HB● HB◯]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ γB (1%Qp, to_agree Bor_in)); last done.
      rewrite lookup_fmap. case:(B !! γB) HBlookup; done. }
    rewrite -fmap_insert.
    iSpecialize ("Hclose'" with "[Hvs Hinh HboxB HB● HB]").
    { iNext. rewrite /lft_inv. iLeft. iFrame "%".
      rewrite lft_inv_alive_unfold. iExists (P ∗ Pb)%I, (P ∗ Pi)%I.
      iFrame "Hinh". iSplitL "HboxB HB● HB"; last by iApply lft_vs_frame.
      rewrite /lft_bor_alive. iExists _. iFrame "HboxB HB●".
      iApply @big_sepM_insert; first by destruct (B !! γB).
      simpl. iFrame. }
    iMod ("Hclose" with "[HA HI Hclose']") as "_"; [by iExists _, _; iFrame|].
    iSplitL "HB◯ HsliceB".
    + rewrite /bor /raw_bor /idx_bor_own. iExists κ; simpl.
      iModIntro. iSplit; first by iApply lft_incl_refl. iExists γB. by iFrame.
    + clear -HE. iIntros "!> H†".
      iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
      iDestruct ("HIlookup" with "* HI") as %Hκ.
      iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hinv Hclose']".
      { by apply elem_of_dom. }
      rewrite /lft_dead; iDestruct "H†" as (Λ) "[% #H†]".
      iDestruct (own_alft_auth_agree A Λ false with "HA H†") as %EQAΛ.
      rewrite {1}/lft_inv; iDestruct "Hinv" as "[[_ >%]|[Hinv >%]]".
      { unfold lft_alive_in in *. naive_solver. }
      rewrite /lft_inv_dead; iDestruct "Hinv" as (Pinh) "(Hdead & >Hcnt & Hinh)".
      iMod ("Hinh_close" $! Pinh with "Hinh") as (Pinh') "(? & $ & ?)".
      iApply "Hclose". iExists A, I. iFrame. iNext. iApply "Hclose'".
      rewrite /lft_inv. iRight. iFrame "%".
      rewrite /lft_inv_dead. iExists Pinh'. iFrame.
  - iFrame "HP". iApply fupd_frame_r. iSplitR ""; last by auto.
    rewrite /lft_inv_dead. iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)" .
    iMod (raw_bor_fake _ true with "Hdead") as "[Hdead Hbor]"; first solve_ndisj.
    unfold bor. iExists κ. iFrame. rewrite -lft_incl_refl -big_sepS_later.
    iApply "Hclose". iExists _, _. iFrame. iApply "Hclose'". iNext.
    rewrite /lft_inv. iRight. rewrite /lft_inv_dead. iFrame. eauto.
Qed.

Lemma bor_sep E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
Proof.
  iIntros (HE) "#LFT Hbor". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  rewrite {1}/bor. iDestruct "Hbor" as (κ') "[#Hκκ' Hbor]".
  rewrite /raw_bor /idx_bor_own. iDestruct "Hbor" as (s) "[Hbor Hslice]".
  iDestruct (own_bor_auth with "HI Hbor") as %Hκ'.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in. simpl.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose']".
  - rewrite lft_inv_alive_unfold /lft_bor_alive.
    iDestruct "Hinv" as (Pb Pi) "(H & Hvs & Hinh)".
    iDestruct "H" as (B) "(Hbox & >Hown & HB)".
    iDestruct (own_bor_valid_2 with "Hown Hbor")
        as %[EQB%to_borUR_included _]%auth_valid_discrete_2.
    iMod (slice_split _ _ true with "Hslice Hbox")
      as (γ1 γ2) "(% & % & % & Hs1 & Hs2 & Hbox)"; first solve_ndisj.
    { by rewrite lookup_fmap EQB. }
    iMod (own_bor_update_2 with "Hown Hbor") as "Hbor".
    { etrans; last etrans.
      - apply auth_update_dealloc. by apply delete_singleton_local_update, _.
      - apply auth_update_alloc,
           (alloc_singleton_local_update _ γ1 (1%Qp, to_agree Bor_in)); last done.
        rewrite /to_borUR -fmap_delete lookup_fmap fmap_None
                -fmap_None -lookup_fmap fmap_delete //.
      - apply cmra_update_op; last done.
        apply auth_update_alloc,
          (alloc_singleton_local_update _ γ2 (1%Qp, to_agree Bor_in)); last done.
        rewrite lookup_insert_ne // /to_borUR -fmap_delete lookup_fmap fmap_None
                -fmap_None -lookup_fmap fmap_delete //. }
    rewrite !own_bor_op. iDestruct "Hbor" as "[[H● H◯2] H◯1]".
    iAssert (&{κ}P)%I with "[H◯1 Hs1]" as "$".
    { rewrite /bor /raw_bor /idx_bor_own. iExists κ'. iFrame "#". iExists γ1. iFrame. }
    iAssert (&{κ}Q)%I with "[H◯2 Hs2]" as "$".
    { rewrite /bor /raw_bor /idx_bor_own. iExists κ'. iFrame "#". iExists γ2. iFrame. }
    iApply "Hclose". iExists A, I. iFrame. rewrite big_sepS_later.
    iApply "Hclose'". iLeft. iFrame "%". iExists Pb, Pi. iFrame. iExists _.
    rewrite /to_borUR -!fmap_delete -!fmap_insert. iFrame "Hbox H●".
    rewrite !big_sepM_insert /=.
    + by rewrite left_id -(big_sepM_delete _ _ _ _ EQB).
    + by rewrite -fmap_None -lookup_fmap fmap_delete.
    + by rewrite lookup_insert_ne // -fmap_None -lookup_fmap fmap_delete.
  - iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)".
    iMod (raw_bor_fake _ true with "Hdead") as "[Hdead Hbor1]"; first solve_ndisj.
    iMod (raw_bor_fake _ true with "Hdead") as "[Hdead Hbor2]"; first solve_ndisj.
    iMod ("Hclose" with "[-Hbor1 Hbor2]") as "_".
    { iExists A, I. iFrame. rewrite big_sepS_later. iApply "Hclose'".
      iRight. iSplit; last by auto. iExists _. iFrame. }
    unfold bor. iSplitL "Hbor1"; iExists _; eauto.
Qed.

Lemma bor_combine E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).
Proof.
  iIntros (?) "#LFT HP HQ". rewrite {1 2}/bor.
  iDestruct "HP" as (κ1) "[#Hκ1 Hbor1]". iDestruct "HQ" as (κ2) "[#Hκ2 Hbor2]".
  iMod (raw_rebor _ _ (κ1 ∪ κ2) with "LFT Hbor1") as "[Hbor1 _]".
    done. by apply gmultiset_union_subseteq_l.
  iMod (raw_rebor _ _ (κ1 ∪ κ2) with "LFT Hbor2") as "[Hbor2 _]".
    done. by apply gmultiset_union_subseteq_r.
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose". unfold raw_bor, idx_bor_own.
  iDestruct "Hbor1" as (j1) "[Hbor1 Hslice1]". iDestruct "Hbor2" as (j2) "[Hbor2 Hslice2]".
  iDestruct (own_bor_auth with "HI Hbor1") as %Hκ'.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in. simpl.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose']".
  - rewrite lft_inv_alive_unfold /lft_bor_alive.
    iDestruct "Hinv" as (Pb Pi) "(H & Hvs & Hinh)".
    iDestruct "H" as (B) "(Hbox & >Hown & HB)".
    iDestruct (own_bor_valid_2 with "Hown Hbor1")
        as %[EQB1%to_borUR_included _]%auth_valid_discrete_2.
    iDestruct (own_bor_valid_2 with "Hown Hbor2")
        as %[EQB2%to_borUR_included _]%auth_valid_discrete_2.
    iAssert ⌜j1 ≠ j2⌝%I with "[#]" as %Hj1j2.
    { iIntros (->).
      iDestruct (own_bor_valid_2 with "Hbor1 Hbor2") as %Hj1j2%auth_valid_discrete.
      exfalso. revert Hj1j2. rewrite /= op_singleton singleton_valid.
      by intros [[]]. }
    iMod (slice_combine _ _ true with "Hslice1 Hslice2 Hbox")
      as (γ) "(% & Hslice & Hbox)"; first solve_ndisj.
    { done. }
    { by rewrite lookup_fmap EQB1. }
    { by rewrite lookup_fmap EQB2. }
    iCombine "Hown" "Hbor1" as "Hbor1". iCombine "Hbor1" "Hbor2" as "Hbor".
    rewrite -!own_bor_op. iMod (own_bor_update with "Hbor") as "Hbor".
    { etrans; last etrans.
      - apply cmra_update_op; last done.
        apply auth_update_dealloc. by apply delete_singleton_local_update, _.
      - apply auth_update_dealloc. by apply delete_singleton_local_update, _.
      - apply auth_update_alloc,
           (alloc_singleton_local_update _ γ (1%Qp, to_agree Bor_in)); last done.
        rewrite /to_borUR -!fmap_delete lookup_fmap fmap_None
                -fmap_None -lookup_fmap !fmap_delete //. }
    rewrite own_bor_op. iDestruct "Hbor" as "[H● H◯]".
    iAssert (&{κ}(P ∗ Q))%I with "[H◯ Hslice]" as "$".
    { rewrite /bor /raw_bor /idx_bor_own. iExists (κ1 ∪ κ2).
      iSplit; first by iApply (lft_incl_glb with "Hκ1 Hκ2").
      iExists γ. iFrame. }
    iApply "Hclose". iExists A, I. iFrame. rewrite big_sepS_later.
    iApply "Hclose'". iLeft. iFrame "%". iExists Pb, Pi. iFrame. iExists _.
    rewrite /to_borUR -!fmap_delete -!fmap_insert. iFrame "Hbox H●".
    rewrite !big_sepM_insert /=.
    + rewrite (big_sepM_delete _ _ _ _ EQB1) /=. iNext. simpl.
      rewrite [([∗ map] _ ∈ delete _ _, _)%I](big_sepM_delete _ _ j2 Bor_in) /=.
      by iDestruct "HB" as "[_ $]". rewrite lookup_delete_ne //.
    + rewrite -fmap_None -lookup_fmap !fmap_delete //.
  - iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)".
    iMod (raw_bor_fake _ true with "Hdead") as "[Hdead Hbor]"; first solve_ndisj.
    iMod ("Hclose" with "[-Hbor]") as "_".
    { iExists A, I. iFrame. rewrite big_sepS_later. iApply "Hclose'".
      iRight. iSplit; last by auto. iExists _. iFrame. }
    unfold bor. iExists _. iFrame. iApply (lft_incl_glb with "Hκ1 Hκ2").
Qed.

End borrow.
