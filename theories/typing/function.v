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

  Lemma fn_subtype_ty A n E0 E L tys1 tys2 ty1 ty2:
    (∀ x, Forall2 (subtype (E0 ++ E x) L) (tys2 x : vec _ _) (tys1 x : vec _ _)) →
    (∀ x, subtype (E0 ++ E x) L (ty1 x) (ty2 x)) →
    subtype E0 L (@fn A n E tys1 ty1) (@fn A n E tys2 ty2).
  Proof.
    intros Htys Hty. apply subtype_simple_type=>//=.
    iIntros (_ ?) "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
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

  (* Lemma ty_incl_fn_specialize {A B n} (f : A → B) ρ ρfn : *)
  (*   ty_incl ρ (fn (n:=n) ρfn) (fn (ρfn ∘ f)). *)
  (* Proof. *)
  (*   iIntros (tid) "_ _!>". iSplit; iIntros "!#*H". *)
  (*   - iDestruct "H" as (fv) "[%#H]". subst. iExists _. iSplit. done. *)
  (*     iIntros (x vl). by iApply "H". *)
  (*   - iSplit; last done. *)
  (*     iDestruct "H" as (fvl) "[?[Hown|H†]]". *)
  (*     + iExists _. iFrame. iLeft. iNext. *)
  (*       iDestruct "Hown" as (fv) "[%H]". subst. iExists _. iSplit. done. *)
  (*       iIntros (x vl). by iApply "H". *)
  (*     + iExists _. iFrame. by iRight. *)
  (* Qed. *)

  (* Lemma typed_fn {A n} `{Duplicable _ ρ, Closed (f :b: xl +b+ []) e} θ : *)
  (*   length xl = n → *)
  (*   (∀ (a : A) (vl : vec val n) (fv : val) e', *)
  (*       subst_l xl (map of_val vl) e = Some e' → *)
  (*       typed_program (fv ◁ fn θ ∗ (θ a vl) ∗ ρ) (subst' f fv e')) → *)
  (*   typed_step_ty ρ (Rec f xl e) (fn θ). *)
  (* Proof. *)
  (*   iIntros (Hn He tid) "!#(#HEAP&#LFT&#Hρ&$)". *)
  (*   assert (Rec f xl e = RecV f xl e) as -> by done. iApply wp_value'. *)
  (*   rewrite has_type_value. *)
  (*   iLöb as "IH". iExists _. iSplit. done. iIntros (a vl) "!#[Hθ?]". *)
  (*   assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He']. *)
  (*   { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto. *)
  (*     intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. } *)
  (*   iApply wp_rec; try done. *)
  (*   { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]]. *)
  (*     rewrite to_of_val. eauto. } *)
  (*   iNext. iApply He. done. iFrame "∗#". by rewrite has_type_value. *)
  (* Qed. *)
End fn.
