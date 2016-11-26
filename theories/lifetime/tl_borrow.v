From lrust.lifetime Require Export derived.
From iris.base_logic.lib Require Export thread_local.
From iris.proofmode Require Import tactics.

Definition tl_bor `{invG Σ, lftG Σ, thread_localG Σ}
           (κ : lft) (tid : thread_id) (N : namespace) (P : iProp Σ) :=
  (∃ i, idx_bor κ i P ∗ tl_inv tid N (idx_bor_own 1 i))%I.

Notation "&tl{ κ , tid , N } P" := (tl_bor κ tid N P)
  (format "&tl{ κ , tid , N } P", at level 20, right associativity) : uPred_scope.

Section tl_bor.
  Context `{invG Σ, lftG Σ, thread_localG Σ}
          (tid : thread_id) (N : namespace) (P : iProp Σ).

  Global Instance tl_bor_persistent κ : PersistentP (&tl{κ,tid,N} P) := _.
  Global Instance tl_bor_proper κ :
    Proper ((⊣⊢) ==> (⊣⊢)) (tl_bor κ tid N).
  Proof.
    intros P1 P2 EQ. apply uPred.exist_proper. intros i. by rewrite EQ.
  Qed.

  Lemma bor_tl κ E : ↑lftN ⊆ E → &{κ}P ={E}=∗ &tl{κ,tid,N}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (tl_inv_alloc tid E N with "[Hown]"). auto.
  Qed.

  Lemma tl_bor_acc q κ E F :
    ↑lftN ⊆ E → ↑tlN ⊆ E → ↑N ⊆ F →
    lft_ctx -∗ &tl{κ,tid,N}P -∗ q.[κ] -∗ tl_own tid F ={E}=∗
            ▷P ∗ tl_own tid (F ∖ ↑N) ∗
            (▷P -∗ tl_own tid (F ∖ ↑N) ={E}=∗ q.[κ] ∗ tl_own tid F).
  Proof.
    iIntros (???) "#LFT#HP Hκ Htlown".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (tl_inv_open with "Hinv Htlown") as "(>Hown&Htlown&Hclose)"; try done.
    iMod (idx_bor_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']". done.
    iIntros "{$HP $Htlown}!>HP Htlown".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma tl_bor_shorten κ κ': κ ⊑ κ' -∗ &tl{κ',tid,N}P -∗ &tl{κ,tid,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
    iApply (idx_bor_shorten with "Hκκ' H").
  Qed.

End tl_bor.

Typeclasses Opaque tl_bor.
