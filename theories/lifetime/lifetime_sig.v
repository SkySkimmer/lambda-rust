From iris.algebra Require Import frac.
From stdpp Require Export gmultiset strings.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import boxes fractional.
Set Default Proof Using "Type".

Definition lftN : namespace := nroot .@ "lft".

Module Type lifetime_sig.
  (** CMRAs needed by the lifetime logic  *)
  (* We can't instantie the module parameters with inductive types, so we
     have aliases here. *)
  Parameter lftG' : gFunctors → Set.
  Global Notation lftG := lftG'.
  Existing Class lftG'.
  Parameter lftPreG' : gFunctors → Set.
  Global Notation lftPreG := lftPreG'.
  Existing Class lftPreG'.

  (** Definitions *)
  Parameter lft : Type.
  Parameter static : lft.
  Parameter lft_intersect : lft → lft → lft.

  Parameter lft_ctx : ∀ `{invG, lftG Σ}, iProp Σ.

  Parameter lft_tok : ∀ `{lftG Σ} (q : Qp) (κ : lft), iProp Σ.
  Parameter lft_dead : ∀ `{lftG Σ} (κ : lft), iProp Σ.

  Parameter lft_incl : ∀ `{invG, lftG Σ} (κ κ' : lft), iProp Σ.
  Parameter bor : ∀ `{invG, lftG Σ} (κ : lft) (P : iProp Σ), iProp Σ.

  Parameter bor_idx : Type.
  Parameter idx_bor_own : ∀ `{lftG Σ} (q : frac) (i : bor_idx), iProp Σ.
  Parameter idx_bor : ∀ `{invG, lftG Σ} (κ : lft) (i : bor_idx) (P : iProp Σ), iProp Σ.

  (** Notation *)
  Notation "q .[ κ ]" := (lft_tok q κ)
      (format "q .[ κ ]", at level 0) : uPred_scope.
  Notation "[† κ ]" := (lft_dead κ) (format "[† κ ]"): uPred_scope.

  Notation "&{ κ }" := (bor κ)
    (format "&{ κ }", at level 20, right associativity) : uPred_scope.
  Notation "&{ κ , i }" := (idx_bor κ i)
    (format "&{ κ , i }", at level 20, right associativity) : uPred_scope.

  Infix "⊑" := lft_incl (at level 70) : uPred_scope.
  Infix "⊓" := lft_intersect (at level 40) : C_scope.

  Section properties.
  Context `{invG, lftG Σ}.

  (** Instances *)
  Global Declare Instance lft_inhabited : Inhabited lft.
  Global Declare Instance bor_idx_inhabited : Inhabited bor_idx.

  Global Declare Instance lft_intersect_comm : Comm eq lft_intersect.
  Global Declare Instance lft_intersect_assoc : Assoc eq lft_intersect.
  Global Declare Instance lft_intersect_inj_1 κ : Inj eq eq (lft_intersect κ).
  Global Declare Instance lft_intersect_inj_2 κ : Inj eq eq (λ κ', lft_intersect κ' κ).
  Global Declare Instance lft_intersect_left_id : LeftId eq static lft_intersect.
  Global Declare Instance lft_intersect_right_id : RightId eq static lft_intersect.

  Global Declare Instance lft_ctx_persistent : PersistentP lft_ctx.
  Global Declare Instance lft_dead_persistent κ : PersistentP ([†κ]).
  Global Declare Instance lft_incl_persistent κ κ' : PersistentP (κ ⊑ κ').
  Global Declare Instance idx_bor_persistent κ i P : PersistentP (&{κ,i} P).

  Global Declare Instance lft_tok_timeless q κ : TimelessP (q.[κ]).
  Global Declare Instance lft_dead_timeless κ : TimelessP ([†κ]).
  Global Declare Instance idx_bor_own_timeless q i : TimelessP (idx_bor_own q i).

  Global Instance idx_bor_params : Params (@idx_bor) 5.
  Global Instance bor_params : Params (@bor) 4.

  Global Declare Instance bor_ne κ n : Proper (dist n ==> dist n) (bor κ).
  Global Declare Instance bor_contractive κ : Contractive (bor κ).
  Global Declare Instance bor_proper κ : Proper ((≡) ==> (≡)) (bor κ).
  Global Declare Instance idx_bor_ne κ i n : Proper (dist n ==> dist n) (idx_bor κ i).
  Global Declare Instance idx_bor_contractive κ i : Contractive (idx_bor κ i).
  Global Declare Instance idx_bor_proper κ i : Proper ((≡) ==> (≡)) (idx_bor κ i).

  Global Declare Instance lft_tok_fractional κ : Fractional (λ q, q.[κ])%I.
  Global Declare Instance lft_tok_as_fractional κ q :
    AsFractional q.[κ] (λ q, q.[κ])%I q.
  Global Declare Instance idx_bor_own_fractional i : Fractional (λ q, idx_bor_own q i)%I.
  Global Declare Instance idx_bor_own_as_fractional i q :
    AsFractional (idx_bor_own q i) (λ q, idx_bor_own q i)%I q.

  (** Laws *)
  Parameter lft_tok_sep : ∀ q κ1 κ2, q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ⊓ κ2].
  Parameter lft_dead_or : ∀ κ1 κ2, [†κ1] ∨ [†κ2] ⊣⊢ [† κ1 ⊓ κ2].
  Parameter lft_tok_dead : ∀ q κ, q.[κ] -∗ [† κ] -∗ False.
  Parameter lft_tok_static : ∀ q, q.[static]%I.
  Parameter lft_dead_static : [† static] -∗ False.

  Parameter lft_create : ∀ E, ↑lftN ⊆ E →
    lft_ctx ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={↑lftN,∅}▷=∗ [†κ]).
  Parameter bor_create : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
  Parameter bor_fake : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &{κ}P.

  Parameter bor_iff : ∀ κ P P', ▷ □ (P ↔ P') -∗ &{κ}P -∗ &{κ}P'.
  Parameter bor_shorten : ∀ κ κ' P, κ ⊑ κ' -∗ &{κ'}P -∗ &{κ}P.

  Parameter bor_sep : ∀ E κ P Q,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
  Parameter bor_combine : ∀ E κ P Q,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).

  Parameter bor_unfold_idx : ∀ κ P, &{κ}P ⊣⊢ ∃ i, &{κ,i}P ∗ idx_bor_own 1 i.

  Parameter idx_bor_shorten : ∀ κ κ' i P, κ ⊑ κ' -∗ &{κ',i} P -∗ &{κ,i} P.
  Parameter idx_bor_iff : ∀ κ i P P', ▷ □ (P ↔ P') -∗ &{κ,i}P -∗ &{κ,i}P'.

  Parameter idx_bor_unnest : ∀ E κ κ' i P,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ,i} P -∗ &{κ'}(idx_bor_own 1 i) ={E}=∗ &{κ ⊓ κ'} P.

  Parameter idx_bor_acc : ∀ E q κ i P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ,i}P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
      ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
  Parameter idx_bor_atomic_acc : ∀ E q κ i P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ,i}P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
      (▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i)) ∨
                ([†κ] ∗ |={E∖↑lftN,E}=> idx_bor_own q i).
  Parameter bor_acc_strong : ∀ E q κ P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ∃ κ', κ ⊑ κ' ∗ ▷ P ∗
      ∀ Q, ▷ (▷ Q -∗ [†κ'] ={∅}=∗ ▷ P) -∗ ▷ Q ={E}=∗ &{κ'} Q ∗ q.[κ].
  Parameter bor_acc_atomic_strong : ∀ E κ P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
      (∃ κ', κ ⊑ κ' ∗ ▷ P ∗
         ∀ Q, ▷ (▷ Q -∗ [†κ'] ={∅}=∗ ▷ P) -∗ ▷ Q ={E∖↑lftN,E}=∗ &{κ'} Q) ∨
           ([†κ] ∗ |={E∖↑lftN,E}=> True).

  (* Because Coq's module system is horrible, we have to repeat properties of lft_incl here
     unless we want to prove them twice (both here and in model.primitive) *)
  Parameter lft_intersect_acc : ∀ κ κ' q q', q.[κ] -∗ q'.[κ'] -∗
    ∃ q'', q''.[κ ⊓ κ'] ∗ (q''.[κ ⊓ κ'] -∗ q.[κ] ∗ q'.[κ']).
  Parameter lft_intersect_incl_l : ∀ κ κ', (κ ⊓ κ' ⊑ κ)%I.
  Parameter lft_intersect_incl_r : ∀ κ κ', (κ ⊓ κ' ⊑ κ')%I.
  Parameter lft_incl_refl : ∀ κ, (κ ⊑ κ)%I.
  Parameter lft_incl_trans : ∀ κ κ' κ'', κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
  Parameter lft_incl_glb : ∀ κ κ' κ'', κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ κ' ⊓ κ''.
  Parameter lft_intersect_mono : ∀ κ1 κ1' κ2 κ2',
    κ1 ⊑ κ1' -∗ κ2 ⊑ κ2' -∗ κ1 ⊓ κ2 ⊑ κ1' ⊓ κ2'.
  Parameter lft_incl_acc : ∀ E κ κ' q,
    ↑lftN ⊆ E → κ ⊑ κ' -∗ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
  Parameter lft_incl_dead : ∀ E κ κ', ↑lftN ⊆ E → κ ⊑ κ' -∗ [†κ'] ={E}=∗ [†κ].
  Parameter lft_incl_intro : ∀ κ κ',
    □ ((∀ q, q.[κ] ={↑lftN}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={↑lftN}=∗ q.[κ])) ∗
        ([†κ'] ={↑lftN}=∗ [†κ])) -∗ κ ⊑ κ'.

  End properties.

  Parameter lftΣ : gFunctors.
  Global Declare Instance subG_lftPreG Σ : subG lftΣ Σ → lftPreG Σ.

  Parameter lft_init : ∀ `{invG Σ, !lftPreG Σ} E, ↑lftN ⊆ E →
    True ={E}=∗ ∃ _ : lftG Σ, lft_ctx.
End lifetime_sig.
