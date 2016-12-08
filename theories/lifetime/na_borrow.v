From lrust.lifetime Require Export derived.
From iris.base_logic.lib Require Export na_invariants.
From iris.proofmode Require Import tactics.

Definition na_bor `{invG Σ, lftG Σ, na_invG Σ}
           (κ : lft) (tid : na_inv_pool_name) (N : namespace) (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗ na_inv tid N (idx_bor_own 1 i))%I.

Notation "&na{ κ , tid , N } P" := (na_bor κ tid N P)
  (format "&na{ κ , tid , N } P", at level 20, right associativity) : uPred_scope.

Section na_bor.
  Context `{invG Σ, lftG Σ, na_invG Σ}
          (tid : na_inv_pool_name) (N : namespace) (P : iProp Σ).

  Global Instance na_bor_persistent κ : PersistentP (&na{κ,tid,N} P) := _.
  Global Instance na_bor_proper κ :
    Proper ((⊣⊢) ==> (⊣⊢)) (na_bor κ tid N).
  Proof.
    intros P1 P2 EQ. apply uPred.exist_proper. intros i. by rewrite EQ.
  Qed.

  Lemma bor_na κ E : ↑lftN ⊆ E → &{κ}P ={E}=∗ &na{κ,tid,N}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (na_inv_alloc tid E N with "[Hown]"). auto.
  Qed.

  Lemma na_bor_acc q κ E :
    ↑lftN ⊆ E → ↑N ⊆ E →
    lft_ctx -∗ &na{κ,tid,N}P -∗ q.[κ] -∗ na_own tid E ={E}=∗
            ▷P ∗ na_own tid (E ∖ ↑N) ∗
            (▷P -∗ na_own tid (E ∖ ↑N) ={E}=∗ q.[κ] ∗ na_own tid E).
  Proof.
    iIntros (??) "#LFT#HP Hκ Hnaown".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (na_inv_open with "Hinv Hnaown") as "(>Hown&Hnaown&Hclose)"; try done.
    iMod (idx_bor_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']". done.
    iIntros "{$HP $Hnaown}!>HP Hnaown".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma na_bor_shorten κ κ': κ ⊑ κ' -∗ &na{κ',tid,N}P -∗ &na{κ,tid,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
    iApply (idx_bor_shorten with "Hκκ' H").
  Qed.

End na_bor.

Typeclasses Opaque na_bor.
