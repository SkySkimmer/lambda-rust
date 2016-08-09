From iris.program_logic Require Export weakestpre adequacy.
From lrust Require Export heap.
From iris.program_logic Require Import auth ownership.
From lrust Require Import proofmode notation.
From iris.proofmode Require Import tactics weakestpre.
From iris.prelude Require Import fin_maps.

Definition heapΣ : gFunctors := #[authΣ heapValUR; authΣ heapFreeableUR; irisΣ lrust_lang].

Definition heap_adequacy Σ `{irisPreG lrust_lang Σ, authG Σ heapValUR, authG Σ heapFreeableUR} e σ φ :
  (∀ `{heapG Σ}, heap_ctx ⊢ WP e {{ v, ■ φ v }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ); iIntros (?) "Hσ".
  iVs (own_alloc (● to_heapVal σ)) as (vγ) "Hvγ".
  { split; last apply to_heap_valid. intro. simpl. refine (ucmra_unit_leastN _ _). }
  iVs (own_alloc (● (∅ : heapFreeableUR))) as (fγ) "Hfγ".
  { split. intro. refine (ucmra_unit_leastN _ _). exact ucmra_unit_valid. }
  set (h:=HeapG _ _ _ _ vγ fγ).
  iVs (inv_alloc heapN _ heap_inv with "[-]") as "HN";
    last by iApply (Hwp h); rewrite /heap_ctx.
  iNext. iExists _, _. iFrame. iPureIntro. intros ??. rewrite lookup_empty.
  inversion 1.
Qed.
