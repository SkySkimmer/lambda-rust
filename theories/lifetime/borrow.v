From lrust.lifetime Require Export primitive creation.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.

Section borrow.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma bor_fake_internal E κ P :
  ↑borN ⊆ E →
  ▷ lft_bor_dead κ ={E}=∗ ▷ lft_bor_dead κ ∗ &{κ}P.
Proof.
  iIntros (?) "Hdead". rewrite /lft_bor_dead.
  iDestruct "Hdead" as (B Pinh) "[>Hown Hbox]".
  iMod (box_insert_empty _ _ _ _ P with "Hbox") as (γ) "(% & Hslice & Hbox)".
  iMod (own_bor_update with "Hown") as "Hown".
  { apply auth_update_alloc.
    apply: (alloc_local_update _ _ _ (1%Qp, DecAgree Bor_in)); last done.
    do 2 eapply lookup_to_gmap_None. by eauto. }
  rewrite own_bor_op insert_empty /bor /raw_bor /idx_bor_own.
  iDestruct "Hown" as "[H● H◯]". iSplitL "H● Hbox".
  - iExists _, _. rewrite -!to_gmap_union_singleton. by iFrame.
  - iExists (_, _). iSplitL "". iApply lft_incl_refl. by iFrame.
Qed.

Lemma bor_fake E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ [†κ] ={E}=∗ &{κ}P.
Proof.
  iIntros (?) "#Hmgmt H†". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ with "HI HA Hinv") as (A' I') "(Hκ & HI & HA & Hinv)".
  iDestruct "Hκ" as %Hκ. rewrite /lft_dead. iDestruct "H†" as (Λ) "[% #H†]".
  iDestruct (own_alft_auth_agree A' Λ false with "HA H†") as %EQAΛ.
  rewrite big_sepS_later big_sepS_elem_of_acc
          ?elem_of_dom // /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in.
  iDestruct "Hinv" as "[[[_ >%]|[Hinv >%]]Hclose']". naive_solver.
  iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)".
  iMod (bor_fake_internal with "Hdead") as "[Hdead $]". solve_ndisj.
  iSpecialize ("Hclose'" with "[Hdead Hcnt Hinh]").
  { iNext. iRight. iFrame "∗%". eauto. }
  iApply "Hclose". iExists _, _. iFrame.
Qed.

Lemma bor_create E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
Proof.
  iIntros (HE) "#Hmgmt HP". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ with "HI HA Hinv") as (A' I') "(Hκ & HI & HA & Hinv)".
  iDestruct "Hκ" as %Hκ. rewrite big_sepS_later.
  rewrite big_sepS_elem_of_acc
          ?elem_of_dom // /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]]Hclose']".
  - rewrite lft_inv_alive_unfold /lft_bor_alive /lft_inh.
    iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iDestruct "Halive" as (B) "(HboxB & >HownB & HB)".
    iDestruct "Hinh" as (PE) "[>HownE HboxE]".
    iMod (box_insert_full _ _ _ _ P with "[$HboxB $HP]")
      as (γB) "(HBlookup & HsliceB & HboxB)". by solve_ndisj.
    rewrite lookup_fmap. iDestruct "HBlookup" as %HBlookup.
    iMod (box_insert_empty _ _ _ _ P with "HboxE") as (γE) "(% & HsliceE & HboxE)".
    rewrite -(fmap_insert bor_filled _ _ Bor_in) -to_gmap_union_singleton.
    iMod (own_bor_update with "HownB") as "HownB".
    { apply auth_update_alloc.
      apply: (alloc_local_update _ _ γB (1%Qp, DecAgree Bor_in)); last done.
      rewrite lookup_fmap. by destruct (B!!γB). }
    iMod (own_inh_update with "HownE") as "HownE".
    { by eapply auth_update_alloc, (gset_disj_alloc_empty_local_update _ {[γE]}),
                disjoint_singleton_l, lookup_to_gmap_None. }
    rewrite -fmap_insert own_bor_op own_inh_op insert_empty.
    iDestruct "HownB" as "[HB● HB◯]". iDestruct "HownE" as "[HE● HE◯]".
    iSpecialize ("Hclose'" with "[Hvs HboxE HboxB HB● HE● HB]").
    { iNext. iLeft. iFrame "%". iExists _, (P ∗ Pi)%I.
      iSplitL "HboxB HB● HB"; last iSplitL "Hvs".
      - iExists _. iFrame "HboxB HB●". rewrite big_sepM_insert /=.
          by iFrame. by destruct (B !! γB).
      - rewrite !lft_vs_unfold. iDestruct "Hvs" as (n) "[Hcnt Hvs]".
        iExists n. iFrame "Hcnt". iIntros (I'') "Hvsinv [$ HPb] H†".
        iApply ("Hvs" $! I'' with "Hvsinv HPb H†").
      - iExists _. iFrame. }
    iMod ("Hclose" with "[HA HI Hclose']") as "_"; [by iExists _, _; iFrame|].
    iSplitL "HB◯ HsliceB".
    + unfold bor, raw_bor, idx_bor_own. iExists (κ, γB).
      iSplitL "". by iApply lft_incl_refl. by iFrame.
    + clear -HE. iIntros "!>H†".
      iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
      iDestruct (own_inh_auth with "HI HE◯") as %Hκ.
      rewrite big_sepS_elem_of_acc ?elem_of_dom //
              /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in /lft_dead /lft_inh.
      iDestruct "H†" as (Λ) "[% #H†]".
      iDestruct (own_alft_auth_agree A Λ false with "HA H†") as %EQAΛ.
      iDestruct "Hinv" as "[[[_ >%]|[Hinv >%]]Hclose']". naive_solver.
      iDestruct "Hinv" as (Pinh) "(Hdead & >Hcnt & Hinh)".
      iDestruct "Hinh" as (ESlices) "[>Hinh Hbox]".
      iDestruct (own_inh_valid_2 with "Hinh HE◯")
        as %[Hle%gset_disj_included _]%auth_valid_discrete_2.
      rewrite <-elem_of_subseteq_singleton in Hle.
      iMod (own_inh_update with "[HE◯ Hinh]") as "HE●"; [|iApply own_inh_op; by iFrame|].
      { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
      iMod (box_delete_full with "[$HsliceE $Hbox]") as "[$ Hbox]".
        solve_ndisj. by rewrite lookup_to_gmap_Some.
      iDestruct "Hbox" as (Pinh') "[_ Hbox]". iApply "Hclose".
      iExists _, _. iFrame. iNext. iApply "Hclose'". iRight. iFrame "%".
      iExists _. iFrame. iExists _. iFrame.
      rewrite {1}(union_difference_L {[γE]} ESlices); last set_solver.
      rewrite to_gmap_union_singleton delete_insert // lookup_to_gmap_None. set_solver.
  - iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)".
    iMod (bor_fake_internal with "Hdead") as "[Hdead $]". solve_ndisj.
    iSpecialize ("Hclose'" with "[Hdead Hcnt Hinh]").
    { iNext. iRight. iFrame "∗%". eauto. }
    iFrame. iMod ("Hclose" with "[-]") as "_"; last by auto. iExists _, _. by iFrame.
Qed.

End borrow.