From iris.base_logic Require Import big_op.
From iris.program_logic Require Import hoare.
From lrust.typing Require Export type perm_incl.
From lrust.lifetime Require Import frac_borrow borrow.

Import Types.

Section ty_incl.

  Context `{iris_typeG Σ}.

  Definition ty_incl (ρ : perm) (ty1 ty2 : type) :=
    ∀ tid, lft_ctx -∗ ρ tid ={⊤}=∗
      (□ ∀ vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ∗
      (□ ∀ κ E l, ty1.(ty_shr) κ tid E l →
       (* [ty_incl] needs to prove something about the length of the
          object when it is shared. We place this property under the
          hypothesis that [ty2.(ty_shr)] holds, so that the [!] type
          is still included in any other. *)
                  ty2.(ty_shr) κ tid E l ∗ ⌜ty1.(ty_size) = ty2.(ty_size)⌝).

  Global Instance ty_incl_refl ρ : Reflexive (ty_incl ρ).
  Proof. iIntros (ty tid) "_ _!>". iSplit; iIntros "!#"; eauto. Qed.

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
    split. apply _.
    eauto using ty_incl_weaken, ty_incl_trans, perm_incl_duplicable.
  Qed.

  Lemma ty_incl_emp ρ ty : ty_incl ρ ∅ ty.
  Proof. iIntros (tid) "_ _!>". iSplit; iIntros "!#*/=[]". Qed.

  Lemma ty_incl_own ρ ty1 ty2 q :
    ty_incl ρ ty1 ty2 → ty_incl ρ (own q ty1) (own q ty2).
  Proof.
    iIntros (Hincl tid) "#LFT H/=". iMod (Hincl with "LFT H") as "[#Howni #Hshri]".
    iModIntro. iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(%&Hmt&H†)". subst. iExists _. iSplit. done.
      iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct (ty_size_eq with "Hown") as %<-.
      iDestruct ("Howni" $! _ with "Hown") as "Hown".
      iDestruct (ty_size_eq with "Hown") as %<-. iFrame.
      iExists _. by iFrame.
    - iDestruct "H" as (l') "[Hfb #Hvs]". iSplit; last done. iExists l'. iFrame.
      iIntros "!#". iIntros (q' F) "% Hκ".
      iMod ("Hvs" with "* [%] Hκ") as "Hvs'". done. iModIntro. iNext.
      iMod "Hvs'" as "[Hshr $]". by iDestruct ("Hshri" with "* Hshr") as "[$ _]".
  Qed.

  Lemma lft_incl_ty_incl_uniq_bor ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&uniq{κ2}ty) (&uniq{κ1}ty).
  Proof.
    iIntros (tid) "#LFT #Hincl!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (bor_shorten with "Hincl").
    - iAssert (κ1 ∪ κ ⊑ κ2 ∪ κ)%I as "#Hincl'".
      { iApply (lft_incl_glb with "[] []").
        - iApply (lft_incl_trans with "[] Hincl"). iApply lft_le_incl.
            apply gmultiset_union_subseteq_l.
        - iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
      iSplitL; last done. iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'.
      iFrame. iIntros "!#". iIntros (q' F) "% Htok".
      iMod (lft_incl_acc with "Hincl' Htok") as (q'') "[Htok Hclose]". set_solver.
      iMod ("Hupd" with "* [%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H Htok]". iMod ("Hclose" with "Htok") as "$".
      by iApply (ty_shr_mono with "LFT Hincl' H").
  Qed.

  Lemma lft_incl_ty_incl_shared_bor ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&shr{κ2}ty) (&shr{κ1}ty).
  Proof.
    iIntros (tid) "#LFT #Hincl!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(% & H)". subst. iExists _.
      iSplit. done. by iApply (ty.(ty_shr_mono) with "LFT Hincl").
    - iDestruct "H" as (vl) "#[Hfrac Hty]". iSplit; last done.
      iExists vl. iFrame "#". iNext.
      iDestruct "Hty" as (l0) "(% & Hty)". subst. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "LFT Hincl Hty").
  Qed.

  (* We have the additional hypothesis that ρ should be duplicable.
     The only way I can see to circumvent this limitation is to deeply
     embed permissions (and their inclusion). Not sure this is worth it. *)
  Lemma ty_incl_prod2 ρ ty11 ty12 ty21 ty22 :
    Duplicable ρ → ty_incl ρ ty11 ty12 → ty_incl ρ ty21 ty22 →
    ty_incl ρ (product2 ty11 ty21) (product2 ty12 ty22).
  Proof.
    iIntros (Hρ Hincl1 Hincl2 tid) "#LFT #Hρ".
    iMod (Hincl1 with "LFT Hρ") as "[#Ho1#Hs1]".
    iMod (Hincl2 with "LFT Hρ") as "[#Ho2#Hs2]".
    iSplitL; iIntros "!>!#*H/=".
    - iDestruct "H" as (vl1 vl2) "(% & H1 & H2)". iExists _, _. iSplit. done.
      iSplitL "H1". iApply ("Ho1" with "H1"). iApply ("Ho2" with "H2").
    - iDestruct "H" as (E1 E2) "(% & H1 & H2)".
      iDestruct ("Hs1" with "*H1") as "[H1 EQ]". iDestruct ("Hs2" with "*H2") as "[H2 %]".
      iDestruct "EQ" as %->. iSplit; last by iPureIntro; f_equal.
      iExists _, _. by iFrame.
  Qed.

  Lemma ty_incl_prod ρ tyl1 tyl2 :
    Duplicable ρ → Forall2 (ty_incl ρ) tyl1 tyl2 → ty_incl ρ (Π tyl1) (Π tyl2).
  Proof. intros Hρ HFA. induction HFA. done. by apply ty_incl_prod2. Qed.

  Lemma ty_incl_prod2_assoc1 ρ ty1 ty2 ty3 :
    ty_incl ρ (product2 ty1 (product2 ty2 ty3)) (product2 (product2 ty1 ty2) ty3).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#/=*H".
    - iDestruct "H" as (vl1 vl') "(% & Ho1 & H)".
      iDestruct "H" as (vl2 vl3) "(% & Ho2 & Ho3)". subst.
      iExists _, _. iSplit. by rewrite assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as (E1 E2') "(% & Hs1 & H)".
      iDestruct "H" as (E2 E3) "(% & Hs2 & Hs3)". rewrite shift_loc_assoc_nat.
      iSplit; last by rewrite assoc.
      iExists (E1 ∪ E2), E3. iSplit. by iPureIntro; set_solver. iFrame.
      iExists E1, E2. iSplit. by iPureIntro; set_solver. by iFrame.
  Qed.

  Lemma ty_incl_prod2_assoc2 ρ ty1 ty2 ty3 :
    ty_incl ρ (product2 (product2 ty1 ty2) ty3) (product2 ty1 (product2 ty2 ty3)).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#/=*H".
    - iDestruct "H" as (vl1 vl') "(% & H & Ho3)".
      iDestruct "H" as (vl2 vl3) "(% & Ho1 & Ho2)". subst.
      iExists _, _. iSplit. by rewrite -assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as (E1' E3) "(% & H & Hs3)".
      iDestruct "H" as (E1 E2) "(% & Hs1 & Hs2)". rewrite shift_loc_assoc_nat.
      iSplit; last by rewrite assoc.
      iExists E1, (E2 ∪ E3). iSplit. by iPureIntro; set_solver. iFrame.
      iExists E2, E3. iSplit. by iPureIntro; set_solver. by iFrame.
  Qed.

  Lemma ty_incl_prod_flatten ρ tyl1 tyl2 tyl3 :
    ty_incl ρ (Π(tyl1 ++ Π tyl2 :: tyl3))
              (Π(tyl1 ++ tyl2 ++ tyl3)).
  Proof.
    apply (ty_incl_weaken _ ⊤). apply perm_incl_top.
    induction tyl1; last by apply (ty_incl_prod2 _ _ _ _ _ _).
    induction tyl2 as [|ty tyl2 IH]; simpl.
    - iIntros (tid) "#LFT _". iSplitL; iIntros "/=!>!#*H".
      + iDestruct "H" as (vl1 vl2) "(% & % & Ho)". subst. done.
      + iDestruct "H" as (E1 E2) "(% & H1 & Ho)". iSplit; last done.
        rewrite shift_loc_0. iApply (ty_shr_mono with "LFT [] Ho"). set_solver.
        iApply lft_incl_refl.
    - etransitivity. apply ty_incl_prod2_assoc2.
      eapply (ty_incl_prod2 _ _ _ _ _ _). done. apply IH.
  Qed.

  Lemma ty_incl_prod_unflatten ρ tyl1 tyl2 tyl3 :
    ty_incl ρ (Π(tyl1 ++ tyl2 ++ tyl3))
              (Π(tyl1 ++ Π tyl2 :: tyl3)).
  Proof.
    apply (ty_incl_weaken _ ⊤). apply perm_incl_top.
    induction tyl1; last by apply (ty_incl_prod2 _ _ _ _ _ _).
    induction tyl2 as [|ty tyl2 IH]; simpl.
    - iIntros (tid) "#LFT _". iMod (bor_create with "LFT []") as "[Hbor _]".
      done. instantiate (1:=True%I). by auto. instantiate (1:=static).
      iMod (bor_fracture (λ _, True%I) with "LFT Hbor") as "#Hbor". done.
      iSplitL; iIntros "/=!>!#*H".
      + iExists [], vl. iFrame. auto.
      + iSplit; last done. iExists ∅, E. iSplit. iPureIntro; set_solver.
        rewrite shift_loc_0. iFrame. iExists []. iSplit; last auto.
        setoid_rewrite heap_mapsto_vec_nil.
        iApply (frac_bor_shorten with "[] Hbor"). iApply lft_incl_static.
    - etransitivity; last apply ty_incl_prod2_assoc1.
      eapply (ty_incl_prod2 _ _ _ _ _ _). done. apply IH.
  Qed.

  Lemma ty_incl_sum ρ n tyl1 tyl2 (_ : LstTySize n tyl1) (_ : LstTySize n tyl2) :
    Duplicable ρ → Forall2 (ty_incl ρ) tyl1 tyl2 →
    ty_incl ρ (sum tyl1) (sum tyl2).
  Proof.
    iIntros (DUP FA tid) "#LFT #Hρ". rewrite /sum /=. iSplitR "".
    - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗
         (□ ∀ i vl, (nth i tyl1 ∅%T).(ty_own) tid vl
                  → (nth i tyl2 ∅%T).(ty_own) tid vl)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "_ _!>*!#". eauto.
        - iIntros "#LFT #Hρ". iMod (IH with "LFT Hρ") as "#IH".
          iMod (Hincl with "LFT Hρ") as "[#Hh _]".
          iIntros "!>*!#*Hown". destruct i as [|i]. by iApply "Hh". by iApply "IH". }
      iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H".
      iDestruct "H" as (i vl') "[% Hown]". subst. iExists _, _. iSplit. done.
        by iApply "Hincl".
    - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗
         (□ ∀ i κ E l, (nth i tyl1 ∅%T).(ty_shr) κ tid E l
                     → (nth i tyl2 ∅%T).(ty_shr) κ tid E l)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "#LFT _!>*!#". eauto.
        - iIntros "#LFT #Hρ".
          iMod (IH with "LFT Hρ") as "#IH". iMod (Hincl with "LFT Hρ") as "[_ #Hh]".
          iIntros "!>*!#*Hown". destruct i as [|i]; last by iApply "IH".
          by iDestruct ("Hh" $! _ _ _ with "Hown") as "[$ _]". }
      iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H". iSplit; last done.
      iDestruct "H" as (i) "[??]". iExists _. iSplit. done. by iApply "Hincl".
  Qed.

  Lemma ty_incl_cont {n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ vl : vec val n, ρ ∗ ρ2 vl ⇒ ρ1 vl) →
    ty_incl ρ (cont ρ1) (cont ρ2).
  Proof.
    iIntros (? Hρ1ρ2 tid) "#LFT #Hρ!>". iSplit; iIntros "!#*H"; last by auto.
    iDestruct "H" as (f) "[% Hwp]". subst. iExists _. iSplit. done.
    iIntros (vl) "Hρ2 Htl". iApply ("Hwp" with ">[-Htl] Htl").
    iApply (Hρ1ρ2 with "LFT"). by iFrame.
  Qed.

  Lemma ty_incl_fn {A n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ (x : A) (vl : vec val n), ρ ∗ ρ2 x vl ⇒ ρ1 x vl) →
    ty_incl ρ (fn ρ1) (fn ρ2).
  Proof.
    iIntros (? Hρ1ρ2 tid) "#LFT #Hρ!>". iSplit; iIntros "!#*#H".
    - iDestruct "H" as (f) "[% Hwp]". subst. iExists _. iSplit. done.
      iIntros (x vl) "!#[Hρ2 Htl]". iApply ("Hwp" with ">").
      iFrame. iApply (Hρ1ρ2 with "LFT"). by iFrame.
    - iSplit; last done. simpl. iDestruct "H" as (vl0) "[? Hvl]".
      iExists vl0. iFrame "#". iNext. iDestruct "Hvl" as (f) "[% Hwp]".
      iExists f. iSplit. done. iIntros (x vl) "!#[Hρ2 Htl]".
      iApply ("Hwp" with ">"). iFrame. iApply (Hρ1ρ2 with "LFT >"). by iFrame.
  Qed.

  Lemma ty_incl_fn_cont {A n} ρ ρf (x : A) :
    ty_incl ρ (fn ρf) (cont (n:=n) (ρf x)).
  Proof.
    iIntros (tid) "#LFT _!>". iSplit; iIntros "!#*H"; last by iSplit.
    iDestruct "H" as (f) "[%#H]". subst. iExists _. iSplit. done.
    iIntros (vl) "Hρf Htl". iApply "H". by iFrame.
  Qed.

  Lemma ty_incl_fn_specialize {A B n} (f : A → B) ρ ρfn :
    ty_incl ρ (fn (n:=n) ρfn) (fn (ρfn ∘ f)).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (fv) "[%#H]". subst. iExists _. iSplit. done.
      iIntros (x vl). by iApply "H".
    - iSplit; last done.
      iDestruct "H" as (fvl) "[?Hown]". iExists _. iFrame. iNext.
      iDestruct "Hown" as (fv) "[%H]". subst. iExists _. iSplit. done.
      iIntros (x vl). by iApply "H".
  Qed.

  Lemma ty_incl_perm_incl ρ ty1 ty2 ν :
    ty_incl ρ ty1 ty2 → ρ ∗ ν ◁ ty1 ⇒ ν ◁ ty2.
  Proof.
    iIntros (Hincl tid) "#LFT [Hρ Hty1]". iMod (Hincl with "LFT Hρ") as "[#Hownincl _]".
    unfold Perm.has_type. destruct (Perm.eval_expr ν); last done. by iApply "Hownincl".
  Qed.

End ty_incl.