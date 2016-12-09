From iris.base_logic Require Import big_op.
From iris.program_logic Require Import hoare.
From lrust.typing Require Export type perm.
From lrust.lifetime Require Import frac_borrow borrow.

Section ty_incl.
  Context `{typeG Σ}.

  Definition ty_incl (ρ : perm) (ty1 ty2 : type) :=
    ∀ tid, lft_ctx -∗ ρ tid ={⊤}=∗
      (□ ∀ vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ∗
      (□ ∀ κ E l, ty1.(ty_shr) κ tid E l →
       (* [ty_incl] needs to prove something about the length of the
          object when it is shared. We place this property under the
          hypothesis that [ty2.(ty_shr)] holds, so that the [!] type
          is still included in any other. *)
                  ty2.(ty_shr) κ tid E l ∗ ⌜ty1.(ty_size) = ty2.(ty_size)⌝).

  Lemma ty_incl_trans ρ θ ty1 ty2 ty3 :
    ty_incl ρ ty1 ty2 → ty_incl θ ty2 ty3 → ty_incl (ρ ∗ θ) ty1 ty3.
  Proof.
    iIntros (H12 H23 tid) "#LFT [H1 H2]".
    iMod (H12 with "LFT H1") as "[#H12 #H12']".
    iMod (H23 with "LFT H2") as "[#H23 #H23']".
    iModIntro; iSplit; iIntros "!#*H1".
    - by iApply "H23"; iApply "H12".
    - iDestruct ("H12'" $! _ _ _ with "H1") as "[H2 %]".
      iDestruct ("H23'" $! _ _ _ with "H2") as "[$ %]".
      iPureIntro. congruence.
  Qed.

  Lemma ty_incl_weaken ρ θ ty1 ty2 :
    ρ ⇒ θ → ty_incl θ ty1 ty2 → ty_incl ρ ty1 ty2.
  Proof.
    iIntros (Hρθ Hρ' tid) "#LFT H". iApply (Hρ' with "LFT>"). iApply (Hρθ with "LFT H").
  Qed.

  Global Instance ty_incl_preorder ρ: Duplicable ρ → PreOrder (ty_incl ρ).
  Proof.
    split.
    - iIntros (ty tid) "_ _!>". iSplit; iIntros "!#"; eauto.
    - eauto using ty_incl_weaken, ty_incl_trans, perm_incl_duplicable.
  Qed.

  Lemma ty_incl_perm_incl ρ ty1 ty2 ν :
    ty_incl ρ ty1 ty2 → ρ ∗ ν ◁ ty1 ⇒ ν ◁ ty2.
  Proof.
    iIntros (Hincl tid) "#LFT [Hρ Hty1]". iMod (Hincl with "LFT Hρ") as "[#Hownincl _]".
    unfold has_type. destruct (eval_expr ν); last done. by iApply "Hownincl".
  Qed.
End ty_incl.