From lrust Require Export lifetime.
From iris.base_logic.lib Require Export thread_local.
From iris.proofmode Require Import tactics.

Definition tl_borrow `{invG Σ, lifetimeG Σ, thread_localG Σ}
           (κ : lifetime) (tid : thread_id) (N : namespace) (P : iProp Σ) :=
  (∃ i, idx_borrow κ i P ∗ tl_inv tid N (idx_borrow_own 1 i))%I.

Notation "&tl{ κ , tid , N } P" := (tl_borrow κ tid N P)
  (format "&tl{ κ , tid , N } P", at level 20, right associativity) : uPred_scope.

Section tl_borrow.
  Context `{invG Σ, lifetimeG Σ, thread_localG Σ}
          (tid : thread_id) (N : namespace) (P : iProp Σ).

  Global Instance tl_borrow_persistent κ : PersistentP (&tl{κ,tid,N} P) := _.
  Global Instance tl_borrow_proper κ :
    Proper ((⊣⊢) ==> (⊣⊢)) (tl_borrow κ tid N).
  Proof.
    intros P1 P2 EQ. apply uPred.exist_proper. intros i. by rewrite EQ.
  Qed.

  Lemma borrow_tl κ E : ↑lftN ⊆ E → &{κ}P ={E}=∗ &tl{κ,tid,N}P.
  Proof.
    iIntros (?) "HP". unfold borrow. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (tl_inv_alloc tid E N with "[Hown]"). auto.
  Qed.

  Lemma tl_borrow_acc q κ E F :
    ↑lftN ⊆ E → ↑tlN ⊆ E → ↑N ⊆ F →
    lft_ctx -∗ &tl{κ,tid,N}P -∗ q.[κ] -∗ tl_own tid F ={E}=∗
            ▷P ∗ tl_own tid (F ∖ ↑N) ∗
            (▷P -∗ tl_own tid (F ∖ ↑N) ={E}=∗ q.[κ] ∗ tl_own tid F).
  Proof.
    iIntros (???) "#LFT#HP Hκ Htlown".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (tl_inv_open with "Hinv Htlown") as "(>Hown&Htlown&Hclose)"; try done.
    iMod (idx_borrow_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']". done.
    iIntros "{$HP $Htlown}!>HP Htlown".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma tl_borrow_shorten κ κ': κ ⊑ κ' -∗ &tl{κ'|tid|N}P -∗ &tl{κ,tid,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
    iApply (idx_borrow_shorten with "Hκκ' H").
  Qed.

End tl_borrow.

Typeclasses Opaque tl_borrow.
