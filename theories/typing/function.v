From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare.
From lrust.lifetime Require Import borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl typing lft_contexts type_context cont_context.

Section fn.
  Context `{typeG Σ}.

  Program Definition fn {A n} (E : A → elctx)
          (tys : A → vec type n) (ty : A → type) : type :=
    {| st_size := 1;
       st_own tid vl := (∃ f, ⌜vl = [f]⌝ ∗ □ ∀ (x : A) (args : vec val n) (k : val),
         typed_body (E x) []
                    [CctxElt k [] 1 (λ v, [TCtx_holds (v!!!0) (ty x)])]
                    (zip_with (TCtx_holds ∘ of_val) args (tys x))
                    (f (of_val <$> (args : list val))))%I |}.
  Next Obligation.
    iIntros (A n E tys ty tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.

  Lemma fn_subtype_ty A n E0 L0 E tys1 tys2 ty1 ty2 :
    (∀ x, Forall2 (subtype (E0 ++ E x) L0) (tys2 x : vec _ _) (tys1 x : vec _ _)) →
    (∀ x, subtype (E0 ++ E x) L0 (ty1 x) (ty2 x)) →
    subtype E0 L0 (@fn A n E tys1 ty1) (@fn A n E tys2 ty2).
  Proof.
    intros Htys Hty. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * _ HE HL HC HT".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iApply ("Hf" with "* LFT HE HL [HC] [HT]").
    - iIntros "HE". unfold cctx_interp. iIntros (e) "He".
      iDestruct "He" as %->%elem_of_list_singleton. iIntros (ret) "HL HT".
      iSpecialize ("HC" with "HE"). unfold cctx_elt_interp.
      iApply ("HC" $! (CctxElt _ _ _ _) with "[%] * HL >").
        by apply elem_of_list_singleton.
      iApply (subtype_tctx_incl with "LFT [HE0] HL0 HT"). by apply Hty.
      rewrite /elctx_interp_0 big_sepL_app. by iSplit.
    - rewrite /tctx_interp
         -(fst_zip (tys1 x) (tys2 x)) ?vec_to_list_length //
         -{1}(snd_zip (tys1 x) (tys2 x)) ?vec_to_list_length //
         !zip_with_fmap_r !(zip_with_zip (λ _ _, (_ ∘ _) _ _)) !big_sepL_fmap.
      iApply big_sepL_impl. iSplit; last done. iIntros "{HT}!#".
      iIntros (i [p [ty1' ty2']]) "#Hzip H /=".
      iDestruct "H" as (v) "[? Hown]". iExists v. iFrame.
      rewrite !lookup_zip_with.
      iDestruct "Hzip" as %(? & ? & ([? ?] & (? & Hty'1 &
        (? & Hty'2 & [=->->])%bind_Some)%bind_Some & [=->->->])%bind_Some)%bind_Some.
      specialize (Htys x). eapply Forall2_lookup_lr in Htys; try done.
      iApply (Htys.(subtype_own _ _ _ _) with "LFT [] HL0 Hown").
      rewrite /elctx_interp_0 big_sepL_app. by iSplit.
  Qed.

  Lemma fn_subtype_specialize {A B n} (σ : A → B) E0 L0 E tys ty :
    subtype E0 L0 (fn (n:=n) E tys ty) (fn (E ∘ σ) (tys ∘ σ) (ty ∘ σ)).
  Proof.
    apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT _ _ Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# *". iApply "Hf".
  Qed.

  Lemma fn_subtype_elctx_sat {A n} E0 L0 E E' tys ty :
    (∀ x, elctx_sat (E x) [] (E' x)) →
    subtype E0 L0 (@fn A n E' tys ty) (fn E tys ty).
  Proof.
    intros HEE'. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT _ _ Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * _ HE #HL HC HT".
    iMod (HEE' x with "[%] HE HL") as (qE') "[HE Hclose]". done.
    iApply ("Hf" with "* LFT HE HL [Hclose HC] HT"). iIntros "HE".
    iApply fupd_cctx_interp. iApply ("HC" with ">").
    by iMod ("Hclose" with "HE") as "[$ _]".
  Qed.

  Lemma fn_subtype_lft_incl {A n} E0 L0 E κ κ' tys ty :
    lctx_lft_incl E0 L0 κ κ' →
    subtype E0 L0 (@fn A n (λ x, ELCtx_Incl κ κ' :: E x) tys ty) (fn E tys ty).
  Proof.
    intros Hκκ'. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * _ HE #HL HC HT".
    iApply ("Hf" with "* LFT [HE] HL [HC] HT").
    { rewrite /elctx_interp big_sepL_cons. iFrame. iApply (Hκκ' with "HE0 HL0"). }
    rewrite /elctx_interp big_sepL_cons. iIntros "[_ HE]". by iApply "HC".
  Qed.
End fn.
