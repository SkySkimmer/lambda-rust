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

Lemma lft_incl_lb κ κ' κ'' : κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ κ' ∪ κ''.
Proof. (*
  iIntros "[#[H1 H1†] #[H2 H2†]]!#". iSplitR.
  - iIntros (q) "[Hκ'1 Hκ'2]".
    iMod ("H1" with "*Hκ'1") as (q') "[Hκ' Hclose']".
    iMod ("H2" with "*Hκ'2") as (q'') "[Hκ'' Hclose'']".
    destruct (Qp_lower_bound q' q'') as (qq & q'0 & q''0 & -> & ->).
    iExists qq. rewrite -lft_tok_op !lft_tok_frac_op.
    iDestruct "Hκ'" as "[$ Hκ']". iDestruct "Hκ''" as "[$ Hκ'']".
    iIntros "!>[Hκ'0 Hκ''0]".
    iMod ("Hclose'" with "[$Hκ' $Hκ'0]") as "$".
    by iMod ("Hclose''" with "[$Hκ'' $Hκ''0]") as "$".
  - rewrite -lft_dead_or. iIntros "[H†|H†]". by iApply "H1†". by iApply "H2†".
Qed. *) Admitted.

Lemma lft_incl_static κ : (κ ⊑ static)%I.
Proof.
  iIntros "!#". iSplitR.
  - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_tok_static. auto.
  - iIntros "Hst". by iDestruct (lft_dead_static with "Hst") as "[]".
Qed.

Lemma reborrow E P κ κ' :
  ↑lftN ⊆ E →
  lft_ctx -∗ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗  &{κ}P).
Proof.
  iIntros (?) "#LFT #H⊑ HP". (* iMod (bor_rebor' with "LFT HP") as "[Hκ' H∋]".
    done. by exists κ'.
  iDestruct (borrow_shorten with "[H⊑] Hκ'") as "$".
  { iApply lft_incl_lb. iSplit. done. iApply lft_incl_refl. }
  iIntros "!>Hκ'". iApply ("H∋" with "[Hκ']"). iApply lft_dead_or. auto.
Qed.
*)
Admitted.
End derived.
