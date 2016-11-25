From lrust.lifetime Require Export primitive borrow todo.
From iris.proofmode Require Import tactics.

Section derived.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(*** Derived lemmas  *)
Lemma bor_acc E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
Proof.
  iIntros (?) "#LFT HP Htok".
  iMod (bor_acc_strong with "LFT HP Htok") as "[HP Hclose]"; first done.
  iIntros "!> {$HP} HP". iApply "Hclose". by iIntros "{$HP}!>_$".
Qed.

Lemma bor_exists {A} (Φ : A → iProp Σ) `{!Inhabited A} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_strong with "LFT Hb") as "[[HΦ Hclose]|[H† Hclose]]"; first done.
  - iDestruct "HΦ" as (x) "HΦ". iExists x.
    iApply "Hclose". iIntros "{$HΦ} !> _ ?"; eauto.
  - iMod "Hclose" as "_". iExists inhabitant. by iApply (bor_fake with "LFT").
Qed.

Lemma bor_or E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
Proof.
  iIntros (?) "#LFT H". rewrite uPred.or_alt.
  iMod (bor_exists with "LFT H") as ([]) "H"; auto.
Qed.

Lemma bor_persistent `{!PersistentP P} E κ q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc with "LFT Hb Htok") as "[#HP Hob]"; first done.
  by iMod ("Hob" with "HP") as "[_$]".
Qed.

Lemma lft_incl_acc E κ κ' q :
  ↑lftN ⊆ E →
  κ ⊑ κ' -∗ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
Proof.
  rewrite /lft_incl.
  iIntros (?) "#[H _] Hq". iApply fupd_mask_mono; first done.
  iMod ("H" with "* Hq") as (q') "[Hq' Hclose]". iExists q'.
  iIntros "{$Hq'} !> Hq". iApply fupd_mask_mono; first done. by iApply "Hclose".
Qed.

Lemma lft_incl_dead E κ κ' : ↑lftN ⊆ E → κ ⊑ κ' -∗ [†κ'] ={E}=∗ [†κ].
Proof.
  rewrite /lft_incl.
  iIntros (?) "#[_ H] Hq". iApply fupd_mask_mono; first done. by iApply "H".
Qed.

Lemma lft_incl_static κ : (κ ⊑ static)%I.
Proof.
  iIntros "!#". iSplitR.
  - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_tok_static. auto.
  - iIntros "Hst". by iDestruct (lft_dead_static with "Hst") as "[]".
Qed.

End derived.
