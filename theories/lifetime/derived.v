From lrust.lifetime Require Export primitive accessors faking.
From lrust.lifetime Require Export raw_reborrow.
From iris.proofmode Require Import tactics.
(* TODO: the name derived makes no sense: reborrow/bor_unnest, which is proven
in the model, depends on this file. *)

Section derived.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma bor_exists {A} (Φ : A → iProp Σ) `{!Inhabited A} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[H|[H† >_]]"; first done.
  - iDestruct "H" as "[HΦ Hclose]". iDestruct "HΦ" as (x) "HΦ".
    iExists x. iApply ("Hclose" with "HΦ"). iIntros "!> ?"; eauto.
  - iExists inhabitant. by iApply (bor_fake with "LFT").
Qed.

Lemma bor_or E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
Proof.
  iIntros (?) "#LFT H". rewrite uPred.or_alt.
  iMod (bor_exists with "LFT H") as ([]) "H"; auto.
Qed.

Lemma bor_later E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) ={E,E∖↑lftN}▷=∗ &{κ}P.
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[H|[H† Hclose]]"; first done.
  - iDestruct "H" as "[HP  Hclose]". iModIntro. iNext.
    iApply ("Hclose" with "* HP"). by iIntros "!> $".
  - iIntros "!> !>". iMod "Hclose" as "_". by iApply (bor_fake with "LFT").
Qed.

Lemma bor_later_tok E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}(▷ P) -∗ q.[κ] ={E}▷=∗ &{κ}P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose]"; first done.
  iModIntro. iNext. iApply ("Hclose" with "* HP []"). by iIntros "!> $".
Qed.

Lemma bor_iff (P Q : iProp Σ) E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ □ (P ↔ Q) -∗ &{κ}P ={E}=∗ &{κ}Q.
Proof.
  iIntros (?) "#LFT #Heq Hb".
  iMod (bor_acc_atomic_cons with "LFT Hb") as "[[HP Hclose]|[H† Hclose]]". done.
  - iApply ("Hclose" with "[HP] []").
      by iApply "Heq". by iIntros "!>HQ!>"; iApply "Heq".
  - iMod "Hclose". by iApply (bor_fake with "LFT").
Qed.

Lemma bor_persistent P `{!PersistentP P} E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P ={E}=∗ ▷ P ∨ [†κ].
Proof.
  iIntros (?) "#LFT Hb".
  iMod (bor_acc_atomic with "LFT Hb") as "[[#HP Hob]|[#H† Hclose]]"; first done.
  - iMod ("Hob" with "HP") as "_". auto.
  - iMod "Hclose" as "_". auto.
Qed.

Lemma bor_persistent_tok P `{!PersistentP P} E κ q :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
Proof.
  iIntros (?) "#LFT Hb Htok".
  iMod (bor_acc with "LFT Hb Htok") as "[#HP Hob]"; first done.
  by iMod ("Hob" with "HP") as "[_ $]".
Qed.

Lemma lft_incl_static κ : (κ ⊑ static)%I.
Proof.
  iIntros "!#". iSplitR.
  - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_tok_static. auto.
  - iIntros "Hst". by iDestruct (lft_dead_static with "Hst") as "[]".
Qed.
End derived.
