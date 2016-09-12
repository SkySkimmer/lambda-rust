From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm.

Import Types.

Section ty_incl.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Definition ty_incl (ρ : perm) (ty1 ty2 : type) :=
    ∀ tid,
      ρ tid ⊢
      (□ ∀ tid vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ∧
      (□ ∀ κ tid E l, ty1.(ty_shr) κ tid E l →
                      ty2.(ty_shr) κ tid E l
       (* [ty_incl] needs to prove something about the length of the
          object when it is shared. We place this property under the
          hypothesis that [ty2.(ty_shr)] holds, so that the [!]  type
          is still included in any other. *)
                    ★ ty1.(ty_size) = ty2.(ty_size)).

  Lemma ty_incl_refl ρ ty : ty_incl ρ ty ty.
  Proof. iIntros (tid0) "_". iSplit; iIntros "!#"; eauto. Qed.

  Lemma ty_incl_trans ρ ty1 ty2 ty3 :
    ty_incl ρ ty1 ty2 → ty_incl ρ ty2 ty3 → ty_incl ρ ty1 ty3.
  Proof.
    iIntros (H12 H23 tid0) "H".
    iDestruct (H12 with "H") as "[#H12 #H12']".
    iDestruct (H23 with "H") as "[#H23 #H23']".
    iSplit; iIntros "{H}!#*H1".
    - by iApply "H23"; iApply "H12".
    - iDestruct ("H12'" $! _ _ _ _ with "H1") as "[H2 %]".
      iDestruct ("H23'" $! _ _ _ _ with "H2") as "[$ %]".
      iPureIntro. congruence.
  Qed.

  Lemma ty_weaken ρ θ ty1 ty2 :
    perm_incl ρ θ → ty_incl θ ty1 ty2 → ty_incl ρ ty1 ty2.
  Proof. iIntros (Hρθ Hθ tid) "H". iApply Hθ. by iApply Hρθ. Qed.

  Lemma ty_incl_bot ρ ty : ty_incl ρ ! ty.
  Proof. iIntros (tid0) "_". iSplit; iIntros "!#*/=[]". Qed.

  Lemma ty_incl_own ρ ty1 ty2 q :
    ty_incl ρ ty1 ty2 → ty_incl ρ (own q ty1) (own q ty2).
  Proof.
    iIntros (Hincl tid0) "H/=". iDestruct (Hincl with "H") as "[#Howni #Hshri]".
    iClear "H". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(%&H†&Hmt)". subst. iExists _. iSplit. done.
      iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct (ty_size_eq with "Hown") as %<-.
      iDestruct ("Howni" $! _ _ with "Hown") as "Hown".
      iDestruct (ty_size_eq with "Hown") as %<-. iFrame.
      iExists _. by iFrame.
    - iDestruct "H" as (l') "[Hfb #Hvs]". iSplit; last done. iExists l'. iFrame.
      iIntros (q') "!#Hκ".
      iVs ("Hvs" $! _ with "Hκ") as "Hvs'". iIntros "!==>!>".
      iVs "Hvs'" as "[Hshr $]". iVsIntro.
      by iDestruct ("Hshri" $! _ _ _ _ with "Hshr") as "[$ _]".
  Qed.

  Lemma lft_incl_ty_incl_uniq_borrow ρ ty κ1 κ2 :
    perm_incl ρ (κ1 ⊑ κ2) → ty_incl ρ (&uniq{κ2}ty) (&uniq{κ1}ty).
  Proof.
    iIntros (Hκκ' tid0) "H". iDestruct (Hκκ' with "H") as "#Hκκ'". iClear "H".
    iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (lft_borrow_incl with "Hκκ'").
    - admit. (* TODO : fix the definition before *)
  Admitted.

  Lemma lft_incl_ty_incl_shared_borrow ρ ty κ1 κ2 :
    perm_incl ρ (κ1 ⊑ κ2) → ty_incl ρ (&shr{κ2}ty) (&shr{κ1}ty).
  Proof.
    iIntros (Hκκ' tid0) "H". iDestruct (Hκκ' with "H") as "#Hκκ'". iClear "H".
    iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (ty.(ty_shr_mono) with "Hκκ'").
    - iDestruct "H" as (vl) "#[Hfrac Hty]". iSplit; last done.
      iExists vl. iFrame "#". iNext.
      iDestruct "Hty" as (l0) "[% Hty]". subst. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "Hκκ' Hty").
  Qed.

  Lemma ty_incl_prod ρ tyl1 tyl2 :
    Forall2 (ty_incl ρ) tyl1 tyl2 → ty_incl ρ (product tyl1) (product tyl2).
  Proof.
    rewrite {2}/ty_incl /product /=. iIntros (HFA tid0) "Hρ". iSplit.
    - assert (Himpl : ρ tid0 ⊢
         □ (∀ tid vll, length tyl1 = length vll →
               ([★ list] tyvl ∈ combine tyl1 vll, ty_own (tyvl.1) tid (tyvl.2))
             → ([★ list] tyvl ∈ combine tyl2 vll, ty_own (tyvl.1) tid (tyvl.2)))).
      { induction HFA as [|ty1 ty2 tyl1 tyl2 Hincl HFA IH].
        - iIntros "_!#* _ _". by rewrite big_sepL_nil.
        - iIntros "Hρ". iDestruct (IH with "Hρ") as "#Hqimpl".
          iDestruct (Hincl with "Hρ") as "[#Hhimpl _]". iIntros "!#*%".
          destruct vll as [|vlh vllq]. discriminate. rewrite !big_sepL_cons.
          iIntros "[Hh Hq]". iSplitL "Hh". by iApply "Hhimpl".
          iApply ("Hqimpl" with "[] Hq"). iPureIntro. simpl in *. congruence. }
      iDestruct (Himpl with "Hρ") as "#Himpl". iIntros "{Hρ}!#*H".
      iDestruct "H" as (vll) "(%&%&H)". iExists _. iSplit. done. iSplit.
      by rewrite -(Forall2_length _ _ _ HFA). by iApply ("Himpl" with "[] H").
    - iRevert "Hρ". generalize O.
      change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat). generalize O.
      induction HFA as [|ty1 ty2 tyl1 tyl2 Hincl HFA IH].
      + iIntros (i offs) "_!#* _". rewrite big_sepL_nil. eauto.
      + iIntros (i offs) "Hρ". iDestruct (IH with "[] Hρ") as "#Hqimpl". done.
        iDestruct (Hincl with "Hρ") as "[_ #Hhimpl]". iIntros "!#*".
        rewrite !big_sepL_cons. iIntros "[Hh Hq]".
        setoid_rewrite <-Nat.add_succ_comm.
        iDestruct ("Hhimpl" $! _ _ _ _ with "Hh") as "[$ %]".
        replace ty2.(ty_size) with ty1.(ty_size) by done.
        iDestruct ("Hqimpl" $! _ _ _ _ with "Hq") as "[$ %]".
        iIntros "!%/=". congruence.
  Qed.

End ty_incl.