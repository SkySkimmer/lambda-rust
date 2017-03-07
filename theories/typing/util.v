From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section util.
  Context `{!typeG Σ}.

  (* Delayed sharing is used by various types; in particular own and uniq.
     It comes in two flavors: Borrows of "later something" and borrows of
     "borrowed something".
     TODO: Figure out a nice way to generalize that; the two proofs below are too
     similar. *)


  Lemma delay_sharing_later N κ l ty tid :
    lftE ⊆ N →
    lft_ctx -∗ &{κ} ▷ l ↦∗: ty_own ty tid ={N}=∗
       □ ∀ (F : coPset) (q : Qp),
       ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ (q).[κ] ={F,F ∖ ↑shrN ∖ ↑lftN}▷=∗ ty.(ty_shr) κ tid l ∗ (q).[κ].
  Proof.
    iIntros (?) "#LFT Hbor". rewrite bor_unfold_idx.
    iDestruct "Hbor" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ tid l)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]"; first set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later with "LFT [Hbtok]") as "Hb"; first solve_ndisj.
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#$ $]"; first solve_ndisj.
      iApply "Hclose". auto.
    - iMod fupd_intro_mask' as "Hclose'"; last iModIntro. set_solver.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.

  Lemma delay_sharing_nested N κ κ' κ'' l ty tid :
    lftE ⊆ N →
    lft_ctx -∗ ▷ (κ'' ⊑ κ ⊓ κ') -∗ &{κ'} &{κ} l ↦∗: ty_own ty tid ={N}=∗
       □ ∀ (F : coPset) (q : Qp),
       ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ (q).[κ''] ={F,F ∖ ↑shrN ∖ ↑lftN}▷=∗ ty.(ty_shr) (κ'') tid l ∗ (q).[κ''].
  Proof.
    iIntros (?) "#LFT #Hincl Hbor". rewrite bor_unfold_idx.
    iDestruct "Hbor" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (κ'') tid l)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]"; first set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT [Hb] Htok") as "[#Hshr $]". solve_ndisj.
      { iApply bor_shorten; done. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod fupd_intro_mask' as "Hclose'"; last iModIntro. set_solver.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
End util.
