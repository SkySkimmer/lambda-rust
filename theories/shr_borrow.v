From iris.algebra Require Import gmap auth frac.
From iris.proofmode Require Import tactics.
From lrust Require Export lifetime.

(** Shared borrows  *)
Definition shr_borrow `{invG Σ, lifetimeG Σ} κ (P : iProp Σ) :=
  (∃ i, idx_borrow κ i P ∗ inv lftN (∃ q, idx_borrow_own q i))%I.
Notation "&shr{ κ } P" := (shr_borrow κ P)
  (format "&shr{ κ } P", at level 20, right associativity) : uPred_scope.

Section shared_borrows.
  Context `{invG Σ, lifetimeG Σ} (P : iProp Σ).

  Global Instance shr_borrow_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (shr_borrow κ).
  Proof. solve_proper. Qed.
  Global Instance shr_borrow_persistent : PersistentP (&shr{κ} P) := _.

  Lemma borrow_share `(nclose lftN ⊆ E) κ : &{κ}P ={E}=∗ &shr{κ}P.
  Proof.
    iIntros "HP". unfold borrow. iDestruct "HP" as (i) "(#?&Hown)".
    iExists i. iFrame "#". iApply inv_alloc. auto.
  Qed.

  Lemma shr_borrow_acc `(nclose lftN ⊆ E) κ :
    lft_ctx ⊢ &shr{κ}P ={E,E∖lftN}=∗ ▷P ∗ (▷P ={E∖lftN,E}=∗ True) ∨
                          [†κ] ∗ |={E∖lftN,E}=> True.
  Proof.
    iIntros "#LFT #HP". iDestruct "HP" as (i) "(#Hidx&#Hinv)".
    iInv lftN as (q') ">Hq'" "Hclose".
    rewrite -(Qp_div_2 q') /idx_borrow_own -op_singleton auth_frag_op own_op.
    iDestruct "Hq'" as "[Hq'0 Hq'1]". iMod ("Hclose" with "[Hq'1]") as "_". by eauto.
    iMod (idx_borrow_atomic_acc with "LFT Hidx Hq'0") as "[[HP Hclose]|[H† Hclose]]". done.
    - iLeft. iFrame. iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iRight. iFrame. iIntros "!>". by iMod "Hclose".
  Qed.

  Lemma shr_borrow_acc_tok `(nclose lftN ⊆ E) q κ :
    lft_ctx ⊢ &shr{κ}P -∗ q.[κ] ={E,E∖lftN}=∗ ▷P ∗ (▷P ={E∖lftN,E}=∗ q.[κ]).
  Proof.
    iIntros "#LFT #Hshr Hκ".
    iMod (shr_borrow_acc with "LFT Hshr") as "[[$ Hclose]|[H† _]]". done.
    - iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iDestruct (lft_own_dead with "Hκ H†") as "[]".
  Qed.

  Lemma shr_borrow_shorten κ κ': κ ⊑ κ' ⊢ &shr{κ'}P -∗ &shr{κ}P.
  Proof.
    iIntros "#H⊑ H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
      by iApply (idx_borrow_shorten with "H⊑").
  Qed.

End shared_borrows.

Typeclasses Opaque shr_borrow.
