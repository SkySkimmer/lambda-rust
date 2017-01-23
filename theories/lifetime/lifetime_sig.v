From iris.algebra Require Import frac.
From iris.prelude Require Export gmultiset strings.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic.lib Require Import boxes fractional.
Set Default Proof Using "Type".

Definition lftN : namespace := nroot .@ "lft".
Definition borN : namespace := lftN .@ "bor".
Definition inhN : namespace := lftN .@ "inh".
Definition mgmtN : namespace := lftN .@ "mgmt".

Definition atomic_lft := positive.
Notation lft := (gmultiset positive).
Definition static : lft := ∅.

Module Type lifetime_sig.
  (** CMRAs needed by the lifetime logic  *)
  (* We can't instantie the module parameters with inductive types, so we have aliases here. *)
  Parameter lftG' : gFunctors → Set.
  Global Notation lftG := lftG'.
  Existing Class lftG'.
  Parameter lftPreG' : gFunctors → Set.
  Global Notation lftPreG := lftPreG'.
  Existing Class lftPreG'.

  (** Definitions *)
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

  Notation "&{ κ } P" := (bor κ P)
    (format "&{ κ }  P", at level 20, right associativity) : uPred_scope.
  Notation "&{ κ , i } P" := (idx_bor κ i P)
    (format "&{ κ , i }  P", at level 20, right associativity) : uPred_scope.

  Infix "⊑" := lft_incl (at level 70) : uPred_scope.

  Section properties.
  Context `{invG, lftG Σ}.

  (** Instances *)
  Global Declare Instance lft_ctx_persistent : PersistentP lft_ctx.
  Global Declare Instance lft_dead_persistent κ : PersistentP (lft_dead κ).
  Global Declare Instance lft_incl_persistent κ κ' : PersistentP (κ ⊑ κ').
  Global Declare Instance idx_bor_persistent κ i P : PersistentP (idx_bor κ i P).

  Global Declare Instance lft_tok_timeless q κ : TimelessP (lft_tok q κ).
  Global Declare Instance lft_dead_timeless κ : TimelessP (lft_dead κ).
  Global Declare Instance idx_bor_own_timeless q i : TimelessP (idx_bor_own q i).

  Global Instance idx_bor_params : Params (@idx_bor) 5.
  Global Instance bor_params : Params (@bor) 4.

  Global Declare Instance bor_ne κ n : Proper (dist n ==> dist n) (bor κ).
  Global Declare Instance bor_contractive κ : Contractive (bor κ).
  Global Declare Instance bor_proper κ : Proper ((≡) ==> (≡)) (bor κ).
  Parameter bor_iff_proper : ∀ κ P P', ▷ □ (P ↔ P') -∗ &{κ}P -∗ &{κ}P'.
  Global Declare Instance idx_bor_ne κ i n : Proper (dist n ==> dist n) (idx_bor κ i).
  Global Declare Instance idx_bor_contractive κ i : Contractive (idx_bor κ i).
  Global Declare Instance idx_bor_proper κ i : Proper ((≡) ==> (≡)) (idx_bor κ i).
  Parameter idx_bor_iff_proper : ∀ κ i P P', ▷ □ (P ↔ P') -∗ &{κ,i}P -∗ &{κ,i}P'.

  Global Declare Instance lft_tok_fractional κ : Fractional (λ q, q.[κ])%I.
  Global Declare Instance lft_tok_as_fractional κ q :
    AsFractional q.[κ] (λ q, q.[κ])%I q.
  Global Declare Instance idx_bor_own_fractional i : Fractional (λ q, idx_bor_own q i)%I.
  Global Declare Instance idx_bor_own_as_fractional i q :
    AsFractional (idx_bor_own q i) (λ q, idx_bor_own q i)%I q.

  (** Laws *)
  Parameter lft_tok_sep : ∀ q κ1 κ2, q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ∪ κ2].
  Parameter lft_dead_or : ∀ κ1 κ2, [†κ1] ∨ [†κ2] ⊣⊢ [† κ1 ∪ κ2].
  Parameter lft_tok_dead : ∀ q κ, q.[κ] -∗ [† κ] -∗ False.
  Parameter lft_tok_static : ∀ q, q.[static]%I.
  Parameter lft_dead_static : [† static] -∗ False.

  Parameter lft_create : ∀ E, ↑lftN ⊆ E →
    lft_ctx ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={⊤,⊤∖↑lftN}▷=∗ [†κ]).
  Parameter bor_create : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
  Parameter bor_fake : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &{κ}P.

  Parameter bor_sep : ∀ E κ P Q,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
  Parameter bor_combine : ∀ E κ P Q,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).

  Parameter bor_unfold_idx : ∀ κ P, &{κ}P ⊣⊢ ∃ i, &{κ,i}P ∗ idx_bor_own 1 i.
  Parameter bor_shorten : ∀ κ κ' P, κ ⊑ κ' -∗ &{κ'}P -∗ &{κ}P.
  Parameter idx_bor_shorten : ∀ κ κ' i P, κ ⊑ κ' -∗ &{κ',i} P -∗ &{κ,i} P.

  Parameter rebor : ∀ E κ κ' P,
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗ &{κ}P).
  Parameter bor_unnest : ∀ E κ κ' P,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ'} &{κ} P ={E, E∖↑lftN}▷=∗ &{κ ∪ κ'} P.

  Parameter idx_bor_acc : ∀ E q κ i P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ,i}P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
      ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
  Parameter idx_bor_atomic_acc : ∀ E q κ i P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ,i}P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
      (▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i)) ∨
                ([†κ] ∗ |={E∖↑lftN,E}=> idx_bor_own q i).
  Parameter bor_acc_strong : ∀ E q κ P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ∃ κ', κ ⊑ κ' ∗ ▷ P ∗
      ∀ Q, ▷ Q -∗ ▷(▷ Q -∗ [†κ'] ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ'} Q ∗ q.[κ].
  Parameter bor_acc_atomic_strong : ∀ E κ P, ↑lftN ⊆ E →
    lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
      (∃ κ', κ ⊑ κ' ∗ ▷ P ∗
         ∀ Q, ▷ Q -∗ ▷ (▷ Q -∗ [†κ'] ={⊤∖↑lftN}=∗ ▷ P) ={E∖↑lftN,E}=∗ &{κ'} Q) ∨
           ([†κ] ∗ |={E∖↑lftN,E}=> True).

  (* Because Coq's module system is horrible, we have to repeat properties of lft_incl here
     unless we want to prove them twice (both here and in model.primitive) *)
  Parameter lft_le_incl : ∀ κ κ', κ' ⊆ κ → (κ ⊑ κ')%I.
  Parameter lft_incl_refl : ∀ κ, (κ ⊑ κ)%I.
  Parameter lft_incl_trans : ∀ κ κ' κ'', κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
  Parameter lft_incl_glb : ∀ κ κ' κ'', κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ κ' ∪ κ''.
  Parameter lft_glb_mono : ∀ κ1 κ1' κ2 κ2',
    κ1 ⊑ κ1' -∗ κ2 ⊑ κ2' -∗ κ1 ∪ κ2 ⊑ κ1' ∪ κ2'.
  Parameter lft_incl_acc : ∀ E κ κ' q,
    ↑lftN ⊆ E → κ ⊑ κ' -∗ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
  Parameter lft_incl_dead : ∀ E κ κ', ↑lftN ⊆ E → κ ⊑ κ' -∗ [†κ'] ={E}=∗ [†κ].
  Parameter lft_incl_intro : ∀ κ κ',
    □ ((∀ q, lft_tok q κ ={↑lftN}=∗ ∃ q',
                 lft_tok q' κ' ∗ (lft_tok q' κ' ={↑lftN}=∗ lft_tok q κ)) ∗
        (lft_dead κ' ={↑lftN}=∗ lft_dead κ)) -∗ κ ⊑ κ'.
  (* Same for some of the derived lemmas. *)
  Parameter bor_exists : ∀ {A} (Φ : A → iProp Σ) `{!Inhabited A} E κ,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
  Parameter bor_acc_atomic_cons : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
      (▷ P ∗ ∀ Q, ▷ Q -∗ ▷ (▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E∖↑lftN,E}=∗ &{κ} Q) ∨
      ([†κ] ∗ |={E∖↑lftN,E}=> True).
  Parameter bor_acc_atomic : ∀ E κ P,
    ↑lftN ⊆ E → lft_ctx -∗ &{κ}P ={E,E∖↑lftN}=∗
       (▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ &{κ}P)) ∨ ([†κ] ∗ |={E∖↑lftN,E}=> True).

  End properties.

  Parameter lftΣ : gFunctors.
  Global Declare Instance subG_lftPreG Σ : subG lftΣ Σ → lftPreG Σ.

  Parameter lft_init : ∀ `{invG Σ, !lftPreG Σ} E, ↑lftN ⊆ E →
    True ={E}=∗ ∃ _ : lftG Σ, lft_ctx.
End lifetime_sig.
