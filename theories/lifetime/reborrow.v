From lrust.lifetime Require Export derived.
From lrust.lifetime Require Export raw_reborrow.
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
  iIntros (?) "#LFT Hκ'". rewrite {2}/bor.
  iMod (bor_exists with "LFT Hκ'") as (κ'') "Hκ'"; first done.
  rewrite {1}/bor; iDestruct "Hκ'" as (κ''') "[#H⊑' Hκ''']".
(*
  iMod (raw_rebor _ _ (κ'' ∪ κ''') with "LFT Hκ'''") as "[Hκ Hclose]"; first done.
  { apply gmultiset_union_subseteq_r. }
Check   
Qed. *)
Admitted.
End reborrow.
