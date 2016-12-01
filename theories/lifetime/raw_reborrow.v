From lrust.lifetime Require Export primitive.
From lrust.lifetime Require Import faking.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.

Section rebor.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(* Notice that taking lft_inv for both κ and κ' already implies
   κ ≠ κ'.  Still, it is probably more instructing to require
   κ ⊂ κ' in this lemma (as opposed to just κ ⊆ κ'), and it
   should not increase the burden on the user. *)
Lemma raw_bor_unnest E A I Pb Pi P κ i κ' :
  ↑borN ⊆ E →
  let Iinv := (own_ilft_auth I ∗ ▷ lft_inv A κ)%I in
  κ ⊂ κ' →
  lft_alive_in A κ' →
  Iinv -∗ idx_bor_own 1 (κ, i) -∗ slice borN i P -∗ ▷ lft_bor_alive κ' Pb -∗
  ▷ lft_vs κ' (idx_bor_own 1 (κ, i) ∗ Pb) Pi ={E}=∗ ∃ Pb',
    Iinv ∗ raw_bor κ' P ∗ ▷ lft_bor_alive κ' Pb' ∗ ▷ lft_vs κ' Pb' Pi.
Proof.
  iIntros (? Iinv Hκκ' Haliveκ') "(HI & Hκ) Hi #Hislice Hκalive' Hvs".
  rewrite lft_vs_unfold. iDestruct "Hvs" as (n) "[>Hn● Hvs]".
  iMod (own_cnt_update with "Hn●") as "[Hn● H◯]".
  { apply auth_update_alloc, (nat_local_update _ 0 (S n) 1); omega. }
  rewrite {1}/raw_bor /idx_bor_own /=.
  iDestruct (own_bor_auth with "HI Hi") as %?.
  assert (κ ⊆ κ') by (by apply strict_include).
  iDestruct (lft_inv_alive_in with "Hκ") as "Hκ";
    first by eauto using lft_alive_in_subseteq.
  rewrite lft_inv_alive_unfold;
    iDestruct "Hκ" as (Pb' Pi') "(Hκalive&Hvs'&Hinh')".
  rewrite {2}/lft_bor_alive; iDestruct "Hκalive" as (B) "(Hbox & >HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi")
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (slice_empty _ _ true with "Hislice Hbox") as "[HP Hbox]"; first done.
  { by rewrite lookup_fmap HB. }
  iMod (own_bor_update_2 with "HB● Hi") as "[HB● Hi]".
  { eapply auth_update, singleton_local_update,
     (exclusive_local_update _ (1%Qp, DecAgree (Bor_rebor κ'))); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  iAssert (▷ lft_inv A κ)%I with "[H◯ HB● HB Hvs' Hinh' Hbox]" as "Hκ".
  { iNext. rewrite /lft_inv. iLeft.
    iSplit; last by eauto using lft_alive_in_subseteq.
    rewrite lft_inv_alive_unfold. iExists Pb', Pi'. iFrame "Hvs' Hinh'".
    rewrite /lft_bor_alive. iExists (<[i:=Bor_rebor κ']>B).
    rewrite /to_borUR !fmap_insert. iFrame "Hbox HB●".
    iDestruct (@big_sepM_delete with "HB") as "[_ HB]"; first done.
    rewrite (big_sepM_delete _ (<[_:=_]>_) i); last by rewrite lookup_insert.
    rewrite -insert_delete delete_insert ?lookup_delete //=. iFrame; auto. }
  clear B HB Pb' Pi'.
  rewrite {1}/lft_bor_alive. iDestruct "Hκalive'" as (B) "(Hbox & >HB● & HB)".
  iMod (slice_insert_full _ _ true with "HP Hbox")
    as (j) "(HBj & #Hjslice & Hbox)"; first done.
  iDestruct "HBj" as %HBj; move: HBj; rewrite lookup_fmap fmap_None=> HBj.
  iMod (own_bor_update with "HB●") as "[HB● Hj]".
  { apply auth_update_alloc,
     (alloc_singleton_local_update _ j (1%Qp, DecAgree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HBj. }
  iModIntro. iExists (P ∗ Pb)%I. rewrite /Iinv. iFrame "HI". iFrame.
  iSplitL "Hj".
  { rewrite /raw_bor /idx_bor_own. iExists j. by iFrame. }
  iSplitL "Hbox HB● HB".
  { rewrite /lft_bor_alive. iNext. iExists (<[j:=Bor_in]> B).
    rewrite /to_borUR !fmap_insert big_sepM_insert //. iFrame.
    by rewrite /bor_cnt. }
  clear dependent Iinv I.
  iNext. rewrite lft_vs_unfold. iExists (S n). iFrame "Hn●".
  iIntros (I) "Hinv [HP HPb] #Hκ†".
  rewrite {1}lft_vs_inv_unfold; iDestruct "Hinv" as "(Hκdead' & HI & Hinv)".
  iDestruct (own_bor_auth with "HI Hi") as %?%elem_of_dom.
  iDestruct (@big_sepS_delete with "Hinv") as "[Hκalive Hinv]"; first done.
  rewrite lft_inv_alive_unfold.
  iDestruct ("Hκalive" with "[%]") as (Pb' Pi') "(Hκalive&Hvs'&Hinh)"; first done.
  rewrite /lft_bor_alive; iDestruct "Hκalive" as (B') "(Hbox & HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi") 
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (own_bor_update_2 with "HB● Hi") as "[HB● Hi]".
  { eapply auth_update, singleton_local_update,
     (exclusive_local_update _ (1%Qp, DecAgree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  iMod (slice_fill _ _ false with "Hislice HP Hbox")
     as "Hbox"; first by solve_ndisj.
  { by rewrite lookup_fmap HB. }
  iDestruct (@big_sepM_delete with "HB") as "[Hcnt HB]"; first done.
  rewrite /=; iDestruct "Hcnt" as "[% H1◯]".
  iMod ("Hvs" $! I with "[Hκdead' HI Hinv Hvs' Hinh HB● Hbox HB]
                         [$HPb Hi] Hκ†") as "($ & $ & Hcnt')".
  { rewrite lft_vs_inv_unfold. iFrame "Hκdead' HI".
    iApply (big_sepS_delete _ (dom (gset lft) I) with "[- $Hinv]"); first done.
    iIntros (_). rewrite lft_inv_alive_unfold.
    iExists Pb', Pi'. iFrame "Hvs' Hinh". rewrite /lft_bor_alive.
    iExists (<[i:=Bor_in]>B'). rewrite /to_borUR !fmap_insert. iFrame.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //=. by iFrame. }
  { rewrite /raw_bor /idx_bor_own /=. auto. }
  iModIntro. rewrite -[S n]Nat.add_1_l -nat_op_plus auth_frag_op own_cnt_op.
  by iFrame.
Qed.

Lemma raw_rebor E κ κ' P :
  ↑lftN ⊆ E → κ ⊆ κ' →
  lft_ctx -∗ raw_bor κ P ={E}=∗
    raw_bor κ' P ∗ ([†κ'] ={E}=∗ raw_bor κ P).
Proof.
  rewrite /lft_ctx. iIntros (??) "#LFT Hκ".
  destruct (decide (κ = κ')) as [<-|Hκneq].
  { iFrame. iIntros "!> #Hκ†". by iApply (raw_bor_fake' with "LFT Hκ†"). }
  assert (κ ⊂ κ') by (by apply strict_spec_alt).
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ' with "HA HI Hinv") as (A' I') "(% & HA & HI & Hinv)".
  clear A I; rename A' into A; rename I' into I.
  iDestruct (big_sepS_delete _ _ κ' with "Hinv") as "[Hκinv' Hinv]";
    first by apply elem_of_dom.
  rewrite {1}/lft_inv; iDestruct "Hκinv'" as "[[? >%]|[Hdead >%]]"; last first.
  { rewrite /lft_inv_dead; iDestruct "Hdead" as (Pi) "(Hdead & >H● & Hinh)".
    iMod (raw_bor_fake _ true _ P with "Hdead") as "[Hdead $]"; first solve_ndisj.
    iMod ("Hclose" with "[-Hκ]") as "_"; last auto.
    iNext. rewrite {2}/lfts_inv. iExists A, I. iFrame "HA HI".
    iApply (big_sepS_delete _ _ κ'); first by apply elem_of_dom.
    iFrame "Hinv". rewrite /lft_inv /lft_inv_dead. iRight.
    iSplit; last done. iExists Pi. by iFrame. }
  rewrite lft_inv_alive_unfold; iDestruct "Hκinv'" as (Pb Pi) "(Hbor & Hvs & Hinh)".
  rewrite {1}/raw_bor. iDestruct "Hκ" as (i) "[Hi #Hislice]".
  iMod (lft_inh_extend _ _ (idx_bor_own 1 (κ, i)) with "Hinh")
    as "(Hinh & HIlookup & Hinh_close)"; first solve_ndisj.
  iDestruct (own_bor_auth with "HI [Hi]") as %?.
  { by rewrite /idx_bor_own. }
  iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hκ Hκclose]".
  { by rewrite elem_of_difference elem_of_dom not_elem_of_singleton. }
  iMod (raw_bor_unnest _ _ _ _ (idx_bor_own 1 (κ, i) ∗ Pi)%I
    with "[$HI $Hκ] Hi Hislice Hbor [Hvs]")
    as (Pb') "([HI Hκ] & $ & Halive & Hvs)"; [solve_ndisj|done|done|..].
  { iNext. by iApply lft_vs_frame. }
  iDestruct ("Hκclose" with "Hκ") as "Hinv".
  iMod ("Hclose" with "[HA HI Hinv Halive Hinh Hvs]") as "_".
  { iNext. rewrite {2}/lfts_inv. iExists A, I. iFrame "HA HI".
    iApply (big_sepS_delete _ _ κ'); first by apply elem_of_dom. iFrame "Hinv".
    rewrite /lft_inv. iLeft. iSplit; last done.
    rewrite lft_inv_alive_unfold. iExists Pb', (idx_bor_own 1 (κ, i) ∗ Pi)%I.
    iFrame. }
  clear dependent A I Pb Pb' Pi. iModIntro. iIntros "H†".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iDestruct ("HIlookup" with "* HI") as %Hκ'.
  iDestruct (big_sepS_delete _ _ κ' with "Hinv") as "[Hκinv' Hinv]";
    first by apply elem_of_dom.
  rewrite {1}/lft_inv; iDestruct "Hκinv'" as "[[Halive >%]|[Hdead >%]]".
  - (* the same proof is in bor_fake and bor_create *)
    rewrite /lft_dead; iDestruct "H†" as (Λ) "[% #H†]".
    iDestruct (own_alft_auth_agree A Λ false with "HA H†") as %EQAΛ.
    unfold lft_alive_in in *. naive_solver.
  - rewrite /lft_inv_dead; iDestruct "Hdead" as (Pi) "(Hdead & Hcnt & Hinh)".
    iMod ("Hinh_close" $! Pi with "Hinh") as (Pi') "(Heq & >Hbor & Hinh)".
    iMod ("Hclose" with "[HA HI Hinv Hdead Hinh Hcnt]") as "_".
    { iNext. rewrite /lfts_inv. iExists A, I. iFrame "HA HI".
      iApply (big_sepS_delete _ _ κ'); first by apply elem_of_dom. iFrame "Hinv".
      rewrite /lft_inv /lft_inv_dead. iRight. iSplit; last done.
      iExists Pi'. iFrame. }
    iModIntro. rewrite /raw_bor. iExists i. by iFrame.
Qed.
End rebor.
