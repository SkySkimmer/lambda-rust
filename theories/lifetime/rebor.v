From lrust.lifetime Require Export primitive.
From iris.algebra Require Import csum auth frac gmap dec_agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.

Section rebor.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma bor_fake E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ [†κ] ={E}=∗ &{κ}P.
Proof.
Admitted.

Lemma raw_bor_unnest A I Pb Pi P κ κ' i :
  let Iinv := (
    own_ilft_auth I ∗
    ▷ ([∗ set] κ ∈ dom _ I ∖ {[ κ' ]}, lft_inv A κ) ∗
    ▷ lft_bor_alive κ' Pb)%I in
  κ ⊆ κ' →
  lft_alive_in A κ' →
  Iinv -∗ raw_bor (κ,i) P -∗ ▷ lft_vs κ' (Pb ∗ raw_bor (κ,i) P) Pi ={↑borN}=∗
    ∃ Pb' j, Iinv ∗ raw_bor (κ',j) P ∗ ▷ lft_vs κ' Pb' Pi.
Proof.
  iIntros (Iinv Hκκ' Haliveκ') "(HI & HA & Hbor) Hraw Hvs".
  destruct (decide (κ = κ')) as [<-|Hκneq].
  { admit. }
  assert (κ ⊂ κ') by (by apply strict_spec_alt).
  rewrite lft_vs_unfold. iDestruct "Hvs" as (n) "[>Hcnt Hvs]".
  iMod (own_cnt_update with "Hcnt") as "Hcnt".
  { apply auth_update_alloc, (nat_local_update _ 0 (S n) 1); omega. }
  rewrite own_cnt_op; iDestruct "Hcnt" as "[Hcnt Hcnt1]".
  rewrite {1}/raw_bor /idx_bor_own /=. iDestruct "Hraw" as "[Hraw Hslice]".
  iDestruct (own_bor_auth with "HI Hraw") as %?.
  rewrite big_sepS_later.
  iDestruct (big_sepS_elem_of_acc _ (dom (gset lft) I ∖ _) κ
    with "HA") as "[HAκ HA]".
  { by rewrite elem_of_difference elem_of_dom not_elem_of_singleton. }
  rewrite {1}/lft_inv. iDestruct "HAκ" as "[[HAκ >%]|[_ >%]]"; last first.
  { destruct (lft_alive_and_dead_in A κ); eauto using lft_alive_in_subseteq. }
  rewrite lft_inv_alive_unfold;
    iDestruct "HAκ" as (Pb' Pi') "(Hbor'&Hvs'&Hinh')".
  rewrite {2}/lft_bor_alive; iDestruct "Hbor'" as (B) "(Hbox & >HκB & HB)".
  iDestruct (own_bor_valid_2 with "HκB Hraw")
    as %[HB%to_borUR_included _]%auth_valid_discrete_2.
  

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