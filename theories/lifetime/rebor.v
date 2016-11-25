From lrust.lifetime Require Export primitive (* borrow *).
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.

Global Instance into_wand_bupd {M} (R P Q : uPred M) :
  IntoWand R P Q → IntoWand R (▷ P) (▷ Q) | 100.
Proof. rewrite /IntoWand=>->. Admitted.

Section rebor.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma raw_bor_unnest A I Pb Pi P κ κ' i :
  let Iinv := (
    own_ilft_auth I ∗
    ▷ ([∗ set] κ ∈ dom _ I ∖ {[ κ' ]}, lft_inv A κ))%I in
  κ ⊆ κ' →
  lft_alive_in A κ' →
  Iinv -∗ raw_bor (κ,i) P -∗ ▷ lft_bor_alive κ' Pb -∗
  ▷ lft_vs κ' (Pb ∗ raw_bor (κ,i) P) Pi ={↑borN}=∗ ∃ Pb' j,
    Iinv ∗ raw_bor (κ',j) P ∗ ▷ lft_bor_alive κ' Pb' ∗ ▷ lft_vs κ' Pb' Pi.
Proof.
  iIntros (Iinv Hκκ' Haliveκ') "(HI & HA) Hraw Hκalive' Hvs".
  destruct (decide (κ = κ')) as [<-|Hκneq].
  { iModIntro. iExists Pb, i. rewrite /Iinv. iFrame "HI HA Hκalive' Hraw".
    iNext. rewrite !lft_vs_unfold. iDestruct "Hvs" as (n) "[Hn Hvs]".
    iExists n. iFrame "Hn". clear Iinv I.
    iIntros (I) "Hinv HPb Hdead". admit. }
  assert (κ ⊂ κ') by (by apply strict_spec_alt).
  rewrite lft_vs_unfold. iDestruct "Hvs" as (n) "[>Hcnt Hvs]".
  iMod (own_cnt_update with "Hcnt") as "Hcnt".
  { apply auth_update_alloc, (nat_local_update _ 0 (S n) 1); omega. }
  rewrite own_cnt_op; iDestruct "Hcnt" as "[Hcnt Hcnt1]".
  rewrite {1}/raw_bor /idx_bor_own /=. iDestruct "Hraw" as "[Hbor #Hislice]".
  iDestruct (own_bor_auth with "HI Hbor") as %?.
  rewrite big_sepS_later.
  iDestruct (big_sepS_elem_of_acc _ (dom (gset lft) I ∖ _) κ
    with "HA") as "[HAκ HA]".
  { by rewrite elem_of_difference elem_of_dom not_elem_of_singleton. }
  iDestruct (lft_inv_alive_in with "HAκ") as "Hκalive";
    first by eauto using lft_alive_in_subseteq.
  rewrite lft_inv_alive_unfold;
    iDestruct "Hκalive" as (Pb' Pi') "(Hbor'&Hvs'&Hinh')".
  rewrite {2}/lft_bor_alive; iDestruct "Hbor'" as (B) "(Hbox & >HκB & HB)".
  iDestruct (own_bor_valid_2 with "HκB Hbor")
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (box_empty with "Hislice Hbox") as "[HP Hbox]"; first done.
  { by rewrite lookup_fmap HB. }
  iMod (own_bor_update_2 with "HκB Hbor") as "HFOO".
  { eapply auth_update, singleton_local_update,
     (exclusive_local_update _ (1%Qp, DecAgree (Bor_rebor κ'))); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  rewrite own_bor_op. iDestruct "HFOO" as "[HκB Hrebor]".
  iSpecialize ("HA" with "[Hcnt1 HB Hvs' Hinh' Hbox HκB]").
  { iNext. rewrite /lft_inv. iLeft.
    iSplit; last by eauto using lft_alive_in_subseteq.
    rewrite lft_inv_alive_unfold. iExists Pb', Pi'. iFrame "Hvs' Hinh'".
    rewrite /lft_bor_alive. iExists (<[i:=Bor_rebor κ']>B).
    rewrite /to_borUR !fmap_insert. iFrame "Hbox HκB".
    iDestruct (@big_sepM_delete with "HB") as "[_ HB]"; first done.
    rewrite (big_sepM_delete _ (<[_:=_]>_) i); last by rewrite lookup_insert.
    rewrite -insert_delete delete_insert ?lookup_delete //.
    iFrame; simpl; auto. }
  clear B HB Pb' Pi'.
  rewrite {1}/lft_bor_alive. iDestruct "Hκalive'" as (B) "(Hbox & >Hbor & HB)".
  iMod (box_insert_full with "HP Hbox") as (j) "(HBj & #Hjslice & Hbox)"; first done.
  iDestruct "HBj" as %HBj. move: HBj; rewrite lookup_fmap fmap_None=> HBj.
  iMod (own_bor_update with "Hbor") as "HFOO".
  { apply auth_update_alloc,
     (alloc_singleton_local_update _ j (1%Qp, DecAgree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HBj. }
  rewrite own_bor_op. iDestruct "HFOO" as "[HκB Hj]".
  iModIntro. iExists (P ∗ Pb)%I, j. rewrite /Iinv. iFrame "HI HA".
  iSplitL "Hj".
  { rewrite /raw_bor /idx_bor_own. by iFrame. }
  iSplitL "HB HκB Hbox".
  { rewrite /lft_bor_alive. iNext. iExists (<[j:=Bor_in]> B).
    rewrite /to_borUR !fmap_insert big_sepM_insert //. iFrame.
    by rewrite /bor_cnt. }
  clear dependent Iinv I.
  iNext. rewrite lft_vs_unfold. iExists (S n). iFrame "Hcnt".
  iIntros (I) "Hinv [HP HPb] Hκ'".
  rewrite {1}lft_vs_inv_unfold; iDestruct "Hinv" as "(Hdead&HI&Hκs)".
  iDestruct (own_bor_auth with "HI Hrebor") as %?%elem_of_dom.
  iDestruct (@big_sepS_delete with "Hκs") as "[Hκ Hκs]"; first done.
  rewrite lft_inv_alive_unfold.
  iDestruct ("Hκ" with "[%]") as (Pb' Pi') "(Halive&Hvs'&Hinh)"; first done.
  rewrite /lft_bor_alive; iDestruct "Halive" as (B') "(Hbox & Hbor & HB)".
  iDestruct (own_bor_valid_2 with "Hbor Hrebor") 
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  iMod (own_bor_update_2 with "Hbor Hrebor") as "HFOO".
  { eapply auth_update, singleton_local_update,
     (exclusive_local_update _ (1%Qp, DecAgree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  rewrite own_bor_op. iDestruct "HFOO" as "[Hbor Hrebor]".
  iMod (box_fill with "Hislice HP [Hbox]") as "Hbox". 3: by iNext. solve_ndisj.
  by rewrite lookup_fmap HB.
iAssert (box borN (<[i:=true]> (bor_filled <$> B')) Pb') with "[Hbox]" as "Hbox".
admit.
  iDestruct (@big_sepM_delete with "HB") as "[Hκ HB]"; first done.
  rewrite /=; iDestruct "Hκ" as "[% Hcnt]".
  iMod ("Hvs" $! I with "[Hdead HI Hκs Hbox Hvs' Hinh Hbor HB]
                         [$HPb Hrebor] Hκ'") as "($&$&Hcnt')".
  { rewrite lft_vs_inv_unfold. iFrame "Hdead HI".
    iApply (big_sepS_delete _ (dom (gset lft) I) with "[- $Hκs]"); first done.
    iIntros (_). rewrite lft_inv_alive_unfold.
    iExists Pb', Pi'. iFrame "Hvs' Hinh". rewrite /lft_bor_alive.
    iExists (<[i:=Bor_in]>B'). rewrite /to_borUR !fmap_insert. iFrame.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //=. by iFrame. }
  { rewrite /raw_bor /idx_bor_own /=. iFrame; auto. }
    iModIntro. rewrite -[S n]Nat.add_1_l -nat_op_plus.
(* auth_frag_op. *)

Admitted.

Lemma bor_rebor' E κ κ' P :
  ↑lftN ⊆ E → κ ⊆ κ' →
  lft_ctx -∗ &{κ} P ={E}=∗ &{κ'} P ∗ ([†κ'] ={E}=∗ &{κ} P).
Proof. Admitted.
Lemma bor_unnest E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ'} &{κ} P ={E}▷=∗ &{κ ∪ κ'} P.
Proof. Admitted.
End rebor.
