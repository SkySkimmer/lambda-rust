From lrust.lifetime Require Export definitions.

Section todo.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(** Basic borrows  *)
Lemma bor_sep E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} (P ∗ Q) ={E}=∗ &{κ} P ∗ &{κ} Q.
Proof.
Admitted.
Lemma bor_combine E κ P Q :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P -∗ &{κ} Q ={E}=∗ &{κ} (P ∗ Q).
Proof. Admitted.
Lemma bor_acc_strong E q κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ Q ∗ ▷([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ} Q ∗ q.[κ].
Proof. Admitted.
Lemma bor_acc_atomic_strong E κ P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ} P ={E,E∖↑lftN}=∗
    (▷ P ∗ ∀ Q, ▷ Q ∗ ▷ ([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E∖↑lftN,E}=∗ &{κ} Q) ∨
    [†κ] ∗ |={E∖↑lftN,E}=> True.
Proof. Admitted.
Lemma bor_reborrow' E κ κ' P :
  ↑lftN ⊆ E → κ ⊆ κ' →
  lft_ctx ⊢ &{κ} P ={E}=∗ &{κ'} P ∗ ([†κ'] ={E}=∗ &{κ} P).
Proof. Admitted.
Lemma bor_unnest E κ κ' P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ &{κ'} &{κ} P ={E}▷=∗ &{κ ∪ κ'} P.
Proof. Admitted.

(** Indexed borrow *)
Lemma idx_bor_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ idx_bor κ i P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
            ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
Proof. Admitted.

Lemma idx_bor_atomic_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx ⊢ idx_bor κ i P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
              ▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i) ∨
              [†κ] ∗ (|={E∖↑lftN,E}=> idx_bor_own q i).
Proof. Admitted.

Lemma idx_bor_shorten κ κ' i P :
  κ ⊑ κ' ⊢ idx_bor κ' i P -∗ idx_bor κ i P.
Proof. Admitted.
End todo.