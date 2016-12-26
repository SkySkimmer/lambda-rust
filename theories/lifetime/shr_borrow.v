From iris.algebra Require Import gmap auth frac.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Export derived.

(** Shared bors  *)
Definition shr_bor `{invG Σ, lftG Σ} κ (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗ inv lftN (∃ q, idx_bor_own q i))%I.
Notation "&shr{ κ } P" := (shr_bor κ P)
  (format "&shr{ κ } P", at level 20, right associativity) : uPred_scope.

Section shared_bors.
  Context `{invG Σ, lftG Σ} (P : iProp Σ).

  Global Instance shr_bor_ne κ n : Proper (dist n ==> dist n) (shr_bor κ).
  Proof. solve_proper. Qed.
  Global Instance shr_bor_contractive κ : Contractive (shr_bor κ).
  Proof. solve_contractive. Qed.
  Global Instance shr_bor_proper : Proper ((⊣⊢) ==> (⊣⊢)) (shr_bor κ).
  Proof. solve_proper. Qed.
  Global Instance shr_bor_persistent : PersistentP (&shr{κ} P) := _.

  Lemma bor_share E κ : ↑lftN ⊆ E → &{κ}P ={E}=∗ &shr{κ}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "(#?&Hown)".
    iExists i. iFrame "#". iApply inv_alloc. auto.
  Qed.

  Lemma shr_bor_acc E κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ &shr{κ}P ={E,E∖↑lftN}=∗ ▷P ∗ (▷P ={E∖↑lftN,E}=∗ True) ∨
               [†κ] ∗ |={E∖↑lftN,E}=> True.
  Proof.
    iIntros (?) "#LFT #HP". iDestruct "HP" as (i) "(#Hidx&#Hinv)".
    iInv lftN as (q') ">[Hq'0 Hq'1]" "Hclose".
    iMod ("Hclose" with "[Hq'1]") as "_". by eauto.
    iMod (idx_bor_atomic_acc with "LFT Hidx Hq'0") as "[[HP Hclose]|[H† Hclose]]". done.
    - iLeft. iFrame. iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iRight. iFrame. iIntros "!>". by iMod "Hclose".
  Qed.

  Lemma shr_bor_acc_tok E q κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ &shr{κ}P -∗ q.[κ] ={E,E∖↑lftN}=∗ ▷P ∗ (▷P ={E∖↑lftN,E}=∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT #Hshr Hκ".
    iMod (shr_bor_acc with "LFT Hshr") as "[[$ Hclose]|[H† _]]". done.
    - iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iDestruct (lft_tok_dead with "Hκ H†") as "[]".
  Qed.

  Lemma shr_bor_shorten κ κ': κ ⊑ κ' -∗ &shr{κ'}P -∗ &shr{κ}P.
  Proof.
    iIntros "#H⊑ H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
      by iApply (idx_bor_shorten with "H⊑").
  Qed.

  Lemma shr_bor_fake E κ: ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &shr{κ}P.
  Proof.
    iIntros (?) "#LFT#H†". iApply (bor_share with ">"). done.
    by iApply (bor_fake with "LFT H†").
  Qed.
End shared_bors.

Typeclasses Opaque shr_bor.
