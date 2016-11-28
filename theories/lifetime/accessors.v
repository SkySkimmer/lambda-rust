From iris.proofmode Require Import tactics.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From lrust.lifetime Require Export primitive rebor.

Section accessors.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(* Helper internal lemmas *)

Lemma bor_open_internal E P i Pb q :
  ↑borN ⊆ E →
  slice borN (i.2) P -∗ ▷ lft_bor_alive (i.1) Pb -∗
  idx_bor_own 1%Qp i -∗ (q).[i.1] ={E}=∗
    ▷ lft_bor_alive (i.1) Pb ∗
    own_bor (i.1) (◯ {[i.2 := (1%Qp, DecAgree (Bor_open q))]}) ∗ ▷ P.
Proof.
  iIntros (?) "Hslice Halive Hbor Htok". unfold lft_bor_alive, idx_bor_own.
  iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
  iDestruct (own_bor_valid_2 with "Hown Hbor")
    as %[EQB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (box_empty with "Hslice Hbox") as "[$ Hbox]".
    solve_ndisj. by rewrite lookup_fmap EQB.
  rewrite -(fmap_insert bor_filled _ _ (Bor_open q)).
  iMod (own_bor_update_2 with "Hown Hbor") as "Hbor". apply auth_update.
  { eapply singleton_local_update. by rewrite lookup_fmap EQB.
    by apply (exclusive_local_update _ (1%Qp, DecAgree (Bor_open q))). }
  rewrite own_bor_op -fmap_insert. iDestruct "Hbor" as "[Hown $]".
  iExists _. iFrame "∗".
  rewrite -insert_delete big_sepM_insert ?lookup_delete // big_sepM_delete /=; last done.
  iDestruct "HB" as "[_ $]". auto.
Qed.

Lemma bor_close_internal E P i Pb q :
  ↑borN ⊆ E →
  slice borN (i.2) P -∗ ▷ lft_bor_alive (i.1) Pb -∗
  own_bor (i.1) (◯ {[i.2 := (1%Qp, DecAgree (Bor_open q))]}) -∗ ▷ P ={E}=∗
    ▷ lft_bor_alive (i.1) Pb ∗ idx_bor_own 1%Qp i ∗ (q).[i.1].
Proof.
  iIntros (?) "Hslice Halive Hbor HP". unfold lft_bor_alive, idx_bor_own.
  iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
  iDestruct (own_bor_valid_2 with "Hown Hbor")
    as %[EQB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (box_fill with "Hslice HP Hbox") as "Hbox".
    solve_ndisj. by rewrite lookup_fmap EQB.
  rewrite -(fmap_insert bor_filled _ _ Bor_in).
  iMod (own_bor_update_2 with "Hown Hbor") as "Hbor". apply auth_update.
  { eapply singleton_local_update. by rewrite lookup_fmap EQB.
    by apply (exclusive_local_update _ (1%Qp, DecAgree Bor_in)). }
  rewrite own_bor_op -fmap_insert. iDestruct "Hbor" as "[Hown $]".
  rewrite big_sepM_delete //. simpl. iDestruct "HB" as "[>$ HB]".
  iExists _. iFrame "Hbox Hown".
  rewrite -insert_delete big_sepM_insert ?lookup_delete //. simpl. by iFrame.
Qed.

Lemma bor_acc_internal E P i Pb q :
  ↑borN ⊆ E →
  slice borN (i.2) P -∗ ▷ lft_bor_alive (i.1) Pb -∗ idx_bor_own q%Qp i ={E}=∗
    ▷ P ∗ (▷ P ={E}=∗ ▷ lft_bor_alive (i.1) Pb ∗ idx_bor_own q%Qp i).
Proof.
  iIntros (?) "#Hslice Halive Hbor". unfold lft_bor_alive, idx_bor_own.
  iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
  iDestruct (own_bor_valid_2 with "Hown Hbor")
    as %[EQB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (box_empty with "Hslice Hbox") as "[$ Hbox]".
    solve_ndisj. by rewrite lookup_fmap EQB.
  iIntros "!>HP{$Hbor}". iMod (box_fill with "Hslice HP Hbox") as "Hbox".
    done. by rewrite lookup_insert.
  iExists _. iFrame. rewrite insert_insert insert_id // lookup_fmap EQB //.
Qed.

Lemma create_dead A κ:
  lft_dead_in A κ →
  own_alft_auth A ==∗ own_alft_auth A ∗ [†κ].
Proof.
  iIntros ((Λ & HΛκ & EQΛ)) "HA". unfold own_alft_auth, lft_dead.
  iMod (own_update _ ((● to_alftUR A)) with "HA") as "HA".
  { eapply (auth_update_alloc _ _ ({[Λ := Cinr ()]}⋅∅)), op_local_update_discrete=>HA Λ'.
    specialize (HA Λ'). revert HA.
    rewrite lookup_op lookup_fmap. destruct (decide (Λ = Λ')) as [<-|].
    - by rewrite lookup_singleton EQΛ.
    - rewrite lookup_singleton_ne //. by destruct (to_lft_stateR <$> A !! Λ'). }
  rewrite right_id. iDestruct "HA" as "[HA HΛ]". iSplitL "HA"; last (iExists _; by iFrame).
  assert ({[Λ := Cinr ()]} ⋅ to_alftUR A ≡ to_alftUR A) as ->; last done.
  intros Λ'. rewrite lookup_op. destruct (decide (Λ = Λ')) as [<-|].
  - by rewrite lookup_singleton lookup_fmap EQΛ.
  - rewrite lookup_singleton_ne //. by case: (to_alftUR A !! Λ').
Qed.

Lemma add_vs Pb Pb' P Q Pi κ :
  ▷ ▷ (Pb ≡ (P ∗ Pb')) -∗ ▷ lft_vs κ Pb Pi -∗ ▷ (▷ Q -∗ [†κ] ={⊤∖↑lftN}=∗ ▷ P) -∗
  ▷ lft_vs κ (Q ∗ Pb') Pi.
Proof.
  iIntros "#HEQ Hvs HvsQ". iNext. rewrite !lft_vs_unfold.
  iDestruct "Hvs" as (n) "[Hcnt Hvs]". iExists n.
  iIntros "{$Hcnt}*Hinv[HQ HPb] #H†". iApply fupd_trans.
  iApply fupd_mask_mono; last iMod ("HvsQ" with "HQ H†") as "HP". solve_ndisj.
  iModIntro. iAssert (▷ Pb)%I with "[HPb HP]" as "HPb".
  { iNext. iRewrite "HEQ". iFrame. }
  iApply ("Hvs" with "* Hinv HPb H†").
Qed.

(** Indexed borrow *)

Lemma idx_bor_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ,i}P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
            ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
Proof.
  unfold idx_bor. iIntros (HE) "#LFT [#Hle #Hs] Hbor Htok".
  iMod (lft_incl_acc with "Hle Htok") as (q') "[Htok Hclose]". solve_ndisj.
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iMod (bor_open_internal with "Hs Halive Hbor Htok") as "(Halive & Hf & $)".
      solve_ndisj.
    iMod ("Hclose'" with "[-Hf Hclose]") as "_".
    { iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame. }
    iIntros "!>HP". clear -HE.
    iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
    iDestruct (own_bor_auth with "HI Hf") as %Hκ'.
    rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
            /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in /lft_bor_dead.
    iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >Hdead_in]] Hclose'']".
    + rewrite lft_inv_alive_unfold.
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
      iMod (bor_close_internal with "Hs Halive Hf HP") as "(Halive & $ & Htok)".
        solve_ndisj.
      iMod ("Hclose'" with "[-Htok Hclose]") as "_"; last by iApply "Hclose".
      iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame.
    + iDestruct "Hinv" as (?) "[Hinv _]". iDestruct "Hinv" as (B ?) "[>Hinv _]".
      iDestruct (own_bor_valid_2 with "Hinv Hf")
        as %[(_ & <- & INCL%option_included)%singleton_included _]%auth_valid_discrete_2.
      by destruct INCL as [[=]|(? & ? & [=<-] &
        [[_<-]%lookup_to_gmap_Some [[_[=]]|[]%(exclusive_included _)]])].
  - iMod (create_dead with "HA") as "[_ H†]". done.
    iDestruct (lft_tok_dead with "Htok H†") as "[]".
Qed.

Lemma idx_bor_atomic_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ,i}P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
              ▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i) ∨
              ([†κ] ∗ |={E∖↑lftN,E}=> idx_bor_own q i).
Proof.
  unfold idx_bor. iIntros (HE) "#LFT [#Hle #Hs] Hbor".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iLeft. iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iMod (bor_acc_internal with "Hs Halive Hbor") as "($ & Hf)". solve_ndisj.
    iMod fupd_intro_mask' as "Hclose"; last iIntros "!>HP". solve_ndisj.
    iMod "Hclose" as "_". iMod ("Hf" with "HP") as "[Hinv $]". iApply "Hclose'".
    iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''". iLeft.
    iFrame "%". iExists _, _. iFrame.
  - iRight. iMod (create_dead with "HA") as "[HA #H†]". done.
    iMod ("Hclose'" with "[-Hbor]") as "_".
    + iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''". eauto.
    + iMod (lft_incl_dead with "Hle H†"). done. iFrame.
      iApply fupd_intro_mask'. solve_ndisj.
Qed.

(** Basic borrows  *)

Lemma bor_acc_strong E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ Q -∗ ▷(▷ Q -∗ [†κ] ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ} Q ∗ q.[κ].
Proof.
  unfold bor, raw_bor. iIntros (HE) "#LFT Hbor Htok".
  iDestruct "Hbor" as (i) "(#Hle & Hbor & #Hs)".
  iMod (lft_incl_acc with "Hle Htok") as (q') "[Htok Hclose]". solve_ndisj.
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iMod (bor_open_internal with "Hs Halive Hbor Htok") as "(Halive & Hbor & $)".
      solve_ndisj.
    iMod ("Hclose'" with "[-Hbor Hclose]") as "_".
    { iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame. }
    iIntros "!>*HQ HvsQ". clear -HE.
    iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
    iDestruct (own_bor_auth with "HI Hbor") as %Hκ'.
    rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
            /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in /lft_bor_dead.
    iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >Hdead_in]] Hclose'']".
    + rewrite lft_inv_alive_unfold /lft_bor_alive.
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
      iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
      iDestruct (own_bor_valid_2 with "Hown Hbor")
        as %[EQB%to_borUR_included _]%auth_valid_discrete_2.
      iMod (box_delete_empty with "Hs Hbox") as (Pb') "[EQ Hbox]".
        solve_ndisj. by rewrite lookup_fmap EQB.
      iDestruct (add_vs with "EQ Hvs [HvsQ]") as "Hvs".
      { iNext. iIntros "HQ H†". iApply ("HvsQ" with "HQ"). admit. }
      iMod (box_insert_empty with "Hbox") as (γ) "(% & Hs' & Hbox)".
      admit.
    + iDestruct "Hinv" as (?) "[Hinv _]". iDestruct "Hinv" as (B ?) "[>Hinv _]".
      iDestruct (own_bor_valid_2 with "Hinv Hbor")
        as %[(_ & <- & INCL%option_included)%singleton_included _]%auth_valid_discrete_2.
      by destruct INCL as [[=]|(? & ? & [=<-] &
        [[_<-]%lookup_to_gmap_Some [[_[=]]|[]%(exclusive_included _)]])].
  - iMod (create_dead with "HA") as "[_ H†]". done.
    iDestruct (lft_tok_dead with "Htok H†") as "[]".
Admitted.

Lemma bor_acc_atomic_strong E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
    (▷ P ∗ ∀ Q, ▷ Q -∗ ▷ (▷ Q -∗ [†κ] ={⊤∖↑lftN}=∗ ▷ P) ={E∖↑lftN,E}=∗ &{κ} Q) ∨
    [†κ] ∗ |={E∖↑lftN,E}=> True.
Proof. Admitted.

Lemma bor_acc E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_strong with "LFT HP Htok") as "[HP Hclose]"; first done.
  iIntros "!> {$HP} HP". iApply ("Hclose" with "HP"). by iIntros "!>$_".
Qed.

End accessors.