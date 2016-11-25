From lrust.lifetime Require Export definitions.

Section todo.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

(** Basic borrows  *)
Lemma bor_acc_strong E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ▷ P ∗
    ∀ Q, ▷ Q ∗ ▷([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E}=∗ &{κ} Q ∗ q.[κ].
Proof. Admitted.
Lemma bor_acc_atomic_strong E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
    (▷ P ∗ ∀ Q, ▷ Q ∗ ▷ ([†κ] -∗ ▷ Q ={⊤∖↑lftN}=∗ ▷ P) ={E∖↑lftN,E}=∗ &{κ} Q) ∨
    [†κ] ∗ |={E∖↑lftN,E}=> True.
Proof. Admitted.

(** Indexed borrow *)
Lemma idx_bor_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ idx_bor κ i P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
            ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
Proof. Admitted.

Lemma idx_bor_atomic_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ idx_bor κ i P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
              ▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i) ∨
              [†κ] ∗ (|={E∖↑lftN,E}=> idx_bor_own q i).
Proof. Admitted.

End todo.