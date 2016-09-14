From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm_incl.

Import Types.

Section ty_incl.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Definition ty_incl (ρ : perm) (ty1 ty2 : type) :=
    ∀ tid, ρ tid ={⊤}=>
      (□ ∀ vl, ty1.(ty_own) tid vl → ty2.(ty_own) tid vl) ★
      (□ ∀ κ E l, ty1.(ty_shr) κ tid E l →
       (* [ty_incl] needs to prove something about the length of the
          object when it is shared. We place this property under the
          hypothesis that [ty2.(ty_shr)] holds, so that the [!] type
          is still included in any other. *)
                  ty2.(ty_shr) κ tid E l ★ ty1.(ty_size) = ty2.(ty_size)).

  Global Instance ty_incl_refl ρ : Reflexive (ty_incl ρ).
  Proof. iIntros (ty tid) "_!==>". iSplit; iIntros "!#"; eauto. Qed.

  Lemma ty_incl_trans ρ θ ty1 ty2 ty3 :
    ty_incl ρ ty1 ty2 → ty_incl θ ty2 ty3 → ty_incl (ρ ★ θ) ty1 ty3.
  Proof.
    iIntros (H12 H23 tid) "[H1 H2]".
    iVs (H12 with "H1") as "[#H12 #H12']".
    iVs (H23 with "H2") as "[#H23 #H23']".
    iVsIntro; iSplit; iIntros "!#*H1".
    - by iApply "H23"; iApply "H12".
    - iDestruct ("H12'" $! _ _ _ with "H1") as "[H2 %]".
      iDestruct ("H23'" $! _ _ _ with "H2") as "[$ %]".
      iPureIntro. congruence.
  Qed.

  Lemma ty_incl_weaken ρ θ ty1 ty2 :
    ρ ⇒ θ → ty_incl θ ty1 ty2 → ty_incl ρ ty1 ty2.
  Proof. iIntros (Hρθ Hρ' tid) "H". iVs (Hρθ with "H"). by iApply Hρ'. Qed.

  Global Instance ty_incl_preorder ρ: Duplicable ρ → PreOrder (ty_incl ρ).
  Proof.
    split.
    - apply _.
    - intros ?????. eauto using ty_incl_weaken, ty_incl_trans.
  Qed.

  Lemma ty_incl_bot ρ ty : ty_incl ρ ! ty.
  Proof. iIntros (tid) "_!==>". iSplit; iIntros "!#*/=[]". Qed.

  Lemma ty_incl_own ρ ty1 ty2 q :
    ty_incl ρ ty1 ty2 → ty_incl ρ (own q ty1) (own q ty2).
  Proof.
    iIntros (Hincl tid) "H/=". iVs (Hincl with "H") as "[#Howni #Hshri]".
    iVsIntro. iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(%&H†&Hmt)". subst. iExists _. iSplit. done.
      iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct (ty_size_eq with "Hown") as %<-.
      iDestruct ("Howni" $! _ with "Hown") as "Hown".
      iDestruct (ty_size_eq with "Hown") as %<-. iFrame.
      iExists _. by iFrame.
    - iDestruct "H" as (l') "[Hfb #Hvs]". iSplit; last done. iExists l'. iFrame.
      iIntros (q') "!#Hκ".
      iVs ("Hvs" $! _ with "Hκ") as "Hvs'". iIntros "!==>!>".
      iVs "Hvs'" as "[Hshr $]". iVsIntro.
      by iDestruct ("Hshri" $! _ _ _ with "Hshr") as "[$ _]".
  Qed.

  Lemma lft_incl_ty_incl_uniq_borrow ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&uniq{κ2}ty) (&uniq{κ1}ty).
  Proof.
    iIntros (tid) "#Hincl!==>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (lft_borrow_incl with "Hincl").
    - admit. (* TODO : fix the definition before *)
  Admitted.

  Lemma lft_incl_ty_incl_shared_borrow ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&shr{κ2}ty) (&shr{κ1}ty).
  Proof.
    iIntros (tid) "#Hincl!==>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (ty.(ty_shr_mono) with "Hincl").
    - iDestruct "H" as (vl) "#[Hfrac Hty]". iSplit; last done.
      iExists vl. iFrame "#". iNext.
      iDestruct "Hty" as (l0) "[% Hty]". subst. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "Hincl Hty").
  Qed.

  Lemma ty_incl_prod ρ tyl1 tyl2 :
    Duplicable ρ → Forall2 (ty_incl ρ) tyl1 tyl2 →
    ty_incl ρ (product tyl1) (product tyl2).
  Proof.
    intros Hρ HFA. eapply ty_incl_weaken. apply Hρ.
    iIntros (tid) "[Hρ1 Hρ2]". iSplitL "Hρ1".
    - assert (Himpl : ρ tid ={⊤}=>
         □ (∀ vll, length tyl1 = length vll →
               ([★ list] tyvl ∈ combine tyl1 vll, ty_own (tyvl.1) tid (tyvl.2))
             → ([★ list] tyvl ∈ combine tyl2 vll, ty_own (tyvl.1) tid (tyvl.2)))).
      { induction HFA as [|ty1 ty2 tyl1 tyl2 Hincl HFA IH].
        - iIntros "_!==>!#* _ _". by rewrite big_sepL_nil.
        - iIntros "Hρ". iVs (Hρ with "Hρ") as "[Hρ1 Hρ2]".
          iVs (IH with "Hρ1") as "#Hqimpl". iVs (Hincl with "Hρ2") as "[#Hhimpl _]".
          iIntros "!==>!#*%". destruct vll as [|vlh vllq]. done. rewrite !big_sepL_cons.
          iIntros "[Hh Hq]". iSplitL "Hh". by iApply "Hhimpl".
          iApply ("Hqimpl" with "[] Hq"). iPureIntro. simpl in *. congruence. }
      iVs (Himpl with "Hρ1") as "#Himpl". iIntros "!==>!#*H".
      iDestruct "H" as (vll) "(%&%&H)". iExists _. iSplit. done. iSplit.
      by rewrite -(Forall2_length _ _ _ HFA). by iApply ("Himpl" with "[] H").
    - rewrite /product /=. iRevert "Hρ2". generalize O.
      change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat). generalize O.
      induction HFA as [|ty1 ty2 tyl1 tyl2 Hincl HFA IH].
      + iIntros (i offs) "_!==>!#*_/=". rewrite big_sepL_nil. eauto.
      + iIntros (i offs) "Hρ". iVs (Hρ with "Hρ") as "[Hρ1 Hρ2]".
        iVs (IH with "[] Hρ1") as "#Hqimpl".
        done. (* TODO : get rid of this done by doing induction in the proof mode. *)
        iVs (Hincl with "Hρ2") as "[_ #Hhimpl]". iIntros "!==>!#*".
        rewrite !big_sepL_cons. iIntros "[Hh Hq]".
        setoid_rewrite <-Nat.add_succ_comm.
        iDestruct ("Hhimpl" $! _ _ _ with "Hh") as "[$ %]".
        replace ty2.(ty_size) with ty1.(ty_size) by done.
        iDestruct ("Hqimpl" $! _ _ _ with "Hq") as "[$ %]".
        iIntros "!%/=". congruence.
  Qed.

  Lemma ty_incl_prod_cons_l ρ ty tyl :
    ty_incl ρ (product (ty :: tyl)) (product [ty ; product tyl]).
  Proof.
    iIntros (tid) "_!==>". iSplit; iIntros "!#/=".
    - iIntros (vl) "H". iDestruct "H" as ([|vlh vllq]) "(%&%&H)". done. subst.
      iExists [_;_]. iSplit. by rewrite /= app_nil_r. iSplit. done.
      rewrite !big_sepL_cons big_sepL_nil right_id. iDestruct "H" as "[$ H]".
      iExists _. repeat iSplit; try done. iPureIntro. simpl in *; congruence.
    - iIntros (κ E l) "H". iSplit; last (iPureIntro; lia).
      rewrite !big_sepL_cons big_sepL_nil right_id. iDestruct "H" as "[$ H]".
      (* FIXME : namespaces do not match. *)
      admit.
  Admitted.

  (* TODO *)
  Lemma ty_incl_prod_flatten ρ tyl1 tyl2 tyl3 :
    ty_incl ρ (product (tyl1 ++ product tyl2 :: tyl3))
              (product (tyl1 ++ tyl2 ++ tyl3)).
  Admitted.

  Lemma ty_incl_sum ρ n tyl1 tyl2 (_ : LstTySize n tyl1) (_ : LstTySize n tyl2) :
    Duplicable ρ →
    Forall2 (ty_incl ρ) tyl1 tyl2 → ty_incl ρ (sum tyl1) (sum tyl2).
  Proof.
    iIntros (DUP FA tid) "Hρ". rewrite /sum /=.
    iVs (DUP with "Hρ") as "[Hρ1 Hρ2]". iSplitR "Hρ2".
    - assert (Hincl : ρ tid ={⊤}=>
         (□ ∀ i vl, (nth i tyl1 !%T).(ty_own) tid vl
                  → (nth i tyl2 !%T).(ty_own) tid vl)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "_!==>*!#". eauto.
        - iIntros "Hρ". iVs (DUP with "Hρ") as "[Hρ1 Hρ2]".
          iVs (IH with "Hρ1") as "#IH". iVs (Hincl with "Hρ2") as "[#Hh _]".
          iIntros "!==>*!#*Hown". destruct i as [|i]. by iApply "Hh". by iApply "IH". }
      iVs (Hincl with "Hρ1") as "#Hincl". iIntros "!==>!#*H".
      iDestruct "H" as (i vl') "[% Hown]". subst. iExists _, _. iSplit. done.
        by iApply "Hincl".
    - assert (Hincl : ρ tid ={⊤}=>
         (□ ∀ i κ E l, (nth i tyl1 !%T).(ty_shr) κ tid E l
                     → (nth i tyl2 !%T).(ty_shr) κ tid E l)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "_!==>*!#". eauto.
        - iIntros "Hρ". iVs (DUP with "Hρ") as "[Hρ1 Hρ2]".
          iVs (IH with "Hρ1") as "#IH". iVs (Hincl with "Hρ2") as "[_ #Hh]".
          iIntros "!==>*!#*Hown". destruct i as [|i]; last by iApply "IH".
          by iDestruct ("Hh" $! _ _ _ with "Hown") as "[$ _]". }
      iVs (Hincl with "Hρ2") as "#Hincl". iIntros "!==>!#*H". iSplit; last done.
      iDestruct "H" as (i) "[??]". iExists _. iSplit. done. by iApply "Hincl".
  Qed.

  Lemma ty_incl_uninit_split ρ n1 n2 :
    ty_incl ρ (uninit (n1+n2)) (product [uninit n1; uninit n2]).
  Proof.
    iIntros (tid) "_!==>". iSplit; iIntros "!#*H".
    - iDestruct "H" as %Hlen. iExists [take n1 vl; drop n1 vl].
      repeat iSplit. by rewrite /= app_nil_r take_drop. done.
      rewrite big_sepL_cons big_sepL_singleton. iSplit; iPureIntro.
      apply take_length_le. lia. rewrite drop_length. lia.
    - iSplit; last (iPureIntro; simpl; lia). iDestruct "H" as (vl) "[#Hf #Hlen]".
      rewrite /= big_sepL_cons big_sepL_singleton. iSplit.
      + iExists (take n1 vl). iSplit.
        (* FIXME : cannot split the fractured borrow. *)
        admit.
        iNext. iDestruct "Hlen" as %Hlen. rewrite /= take_length_le //. lia.
      + iExists (drop n1 vl). iSplit.
        (* FIXME : cannot split the fractured borrow. *)
        admit.
        iNext. iDestruct "Hlen" as %Hlen. rewrite /= drop_length. iPureIntro. lia.
  Admitted.

  Lemma ty_incl_uninit_combine ρ n1 n2 :
    ty_incl ρ (product [uninit n1; uninit n2]) (uninit (n1+n2)).
  Proof.
  (* FIXME : idem : cannot combine the fractured borrow. *)
  Admitted.

  Lemma ty_incl_cont {n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ vl : vec val n, ρ ★ ρ2 vl ⇒ ρ1 vl) →
    ty_incl ρ (cont ρ1) (cont ρ2).
  Proof.
    iIntros (? Hρ1ρ2 tid) "Hρ".
    iVs (inv_alloc lrustN _ (ρ tid) with "[Hρ]") as "#INV". by auto.
    iIntros "!==>". iSplit; iIntros "!#*H"; last by auto.
    iDestruct "H" as (f) "[% Hwp]". subst. iExists _. iSplit. done.
    iIntros (vl) "Htl Hown".
    iApply pvs_wp. iInv lrustN as "Hρ" "Hclose".
    (* FIXME : we need some kind of "Invariant of duplicable
       propositions" that we can open several times. *)
    admit.
  Admitted.

  Lemma ty_incl_fn {n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ vl : vec val n, ρ ★ ρ2 vl ⇒ ρ1 vl) →
    ty_incl ρ (fn ρ1) (fn ρ2).
    (* FIXME : idem. *)
    admit.
  Admitted.

  Lemma ty_incl_fn_cont {n} ρ ρf : ty_incl ρ (fn ρf) (cont (n:=n) ρf).
  Proof.
    iIntros (tid) "_!==>". iSplit; iIntros "!#*H"; last by iSplit.
    iDestruct "H" as (f) "[%#H]". subst. iExists _. iSplit. done.
    iIntros (vl) "Hρf Htl". iApply "H". by iFrame.
  Qed.

  (* TODO : forall, when we will have figured out the right definition. *)

  Lemma ty_incl_perm_incl ρ ty1 ty2 v :
    ty_incl ρ ty1 ty2 → ρ ★ v ◁ ty1 ⇒ v ◁ ty2.
  Proof.
    iIntros (Hincl tid) "[Hρ Hty1]". iVs (Hincl with "Hρ") as "[#Hownincl _]".
    by iApply "Hownincl".
  Qed.

End ty_incl.