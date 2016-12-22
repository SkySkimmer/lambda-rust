From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Section fn.
  Context `{typeG Σ}.

  Program Definition fn {A n} (E : A → elctx)
          (tys : A → vec type n) (ty : A → type) : type :=
    {| st_own tid vl := (∃ f, ⌜vl = [f]⌝ ∗ □ ∀ (x : A) (args : vec val n) (k : val),
         typed_body (E x) []
                    [CCtx_iscont k [] 1 (λ v, [TCtx_hasty (v!!!0) (ty x)])]
                    (zip_with (TCtx_hasty ∘ of_val) args (tys x))
                    (f (of_val <$> (k :: args : list val))))%I |}.
  Next Obligation.
    iIntros (A n E tys ty tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.

  Global Instance fn_send {A n} E tys ty : Send (@fn A n E tys ty).
  Proof. iIntros (tid1 tid2 vl). done. Qed.
End fn.

Section typing.
  Context `{typeG Σ}.

  Lemma fn_subtype_ty {A n} E0 L0 E (tys1 : A → vec type n) tys2 ty1 ty2 :
    (∀ x, Forall2 (subtype (E0 ++ E x) L0) (tys2 x : vec _ n) (tys1 x)) →
    (∀ x, subtype (E0 ++ E x) L0 (ty1 x) (ty2 x)) →
    subtype E0 L0 (fn E tys1 ty1) (fn E tys2 ty2).
  Proof.
    intros Htys Hty. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * #HEAP _ Htl HE HL HC HT".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iApply ("Hf" with "* HEAP LFT Htl HE HL [HC] [HT]").
    - iIntros "HE". unfold cctx_interp. iIntros (e) "He".
      iDestruct "He" as %->%elem_of_list_singleton. iIntros (ret) "Htl HL HT".
      iSpecialize ("HC" with "HE"). unfold cctx_elt_interp.
      iApply ("HC" $! (CCtx_iscont _ _ _ _) with "[%] * Htl HL >").
      {  by apply elem_of_list_singleton. }
      rewrite /tctx_interp !big_sepL_singleton /=.
      iDestruct "HT" as (v) "[HP Hown]". iExists v. iFrame "HP".
      iDestruct (Hty x with "LFT [HE0 HE'] HL0") as "(_ & #Hty & _)".
      { rewrite /elctx_interp_0 big_sepL_app. by iSplit. }
      by iApply "Hty".
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
      iDestruct (Htys with "* [] [] []") as "(_ & #Ho & _)"; [done| |done|].
      + rewrite /elctx_interp_0 big_sepL_app. by iSplit.
      + by iApply "Ho".
  Qed.

  Lemma fn_subtype_specialize {A B n} (σ : A → B) E0 L0 E tys ty :
    subtype E0 L0 (fn (n:=n) E tys ty) (fn (E ∘ σ) (tys ∘ σ) (ty ∘ σ)).
  Proof.
    apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT _ _ Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# *". iApply "Hf".
  Qed.

  Lemma fn_subtype_elctx_sat {A n} E0 L0 E E' (tys : A → vec type n) ty :
    (∀ x, elctx_sat (E x) [] (E' x)) →
    subtype E0 L0 (fn E' tys ty) (fn E tys ty).
  Proof.
    intros HEE'. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT _ _ Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * #HEAP _ Htl HE #HL HC HT".
    iMod (HEE' x with "[%] HE HL") as (qE') "[HE Hclose]". done.
    iApply ("Hf" with "* HEAP LFT Htl HE HL [Hclose HC] HT"). iIntros "HE".
    iApply fupd_cctx_interp. iApply ("HC" with ">").
    by iMod ("Hclose" with "HE") as "[$ _]".
  Qed.

  Lemma fn_subtype_lft_incl {A n} E0 L0 E κ κ' (tys : A → vec type n) ty :
    lctx_lft_incl E0 L0 κ κ' →
    subtype E0 L0 (fn (λ x, ELCtx_Incl κ κ' :: E x) tys ty) (fn E tys ty).
  Proof.
    intros Hκκ'. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (f) "[% #Hf]". subst.
    iExists f. iSplit. done. rewrite /typed_body. iIntros "!# * #HEAP _ Htl HE #HL HC HT".
    iApply ("Hf" with "* HEAP LFT Htl [HE] HL [HC] HT").
    { rewrite /elctx_interp big_sepL_cons. iFrame. iApply (Hκκ' with "HE0 HL0"). }
    rewrite /elctx_interp big_sepL_cons. iIntros "[_ HE]". by iApply "HC".
  Qed.

  (* TODO: Define some syntactic sugar for calling and letrec like we do on paper. *)
  Lemma type_call {A} E L E' T T' p (ps : list path)
                        (tys : A → vec type (length ps)) ty k x :
    tctx_incl E L T (zip_with TCtx_hasty ps (tys x) ++ T') → elctx_sat E L (E' x) →
    typed_body E L [CCtx_iscont k L 1 (λ v, (TCtx_hasty (v!!!0) (ty x)) :: T')]
               (TCtx_hasty p (fn E' tys ty) :: T) (p (of_val k :: ps)).
  Proof.
    iIntros (HTsat HEsat tid qE) "#HEAP #LFT Htl HE HL HC".
    rewrite tctx_interp_cons. iIntros "[Hf HT]".
    wp_bind p. iApply (wp_hasty with "Hf"). iIntros (v) "% Hf".
    iMod (HTsat with "LFT HE HL HT") as "(HE & HL & HT)". rewrite tctx_interp_app.
    iDestruct "HT" as "[Hargs HT']". clear HTsat.
    iApply (wp_app_vec _ _ (_::_) ((λ v, ⌜v = k⌝):::
               vmap (λ ty (v : val), tctx_elt_interp tid (TCtx_hasty v ty)) (tys x))%I
            with "* [Hargs]"); first wp_done.
    - rewrite /= big_sepL_cons. iSplitR "Hargs"; first by iApply wp_value'.
      clear dependent ty k p.
      rewrite /tctx_interp vec_to_list_map zip_with_fmap_r
              (zip_with_zip (λ e ty, (e, _))) zip_with_zip !big_sepL_fmap.
      iApply (big_sepL_mono' with "Hargs"). iIntros (i [p ty]) "HT/=".
      iApply (wp_hasty with "HT"). setoid_rewrite tctx_hasty_val. iIntros (?) "? $".
    - simpl. iIntros (vl'). inv_vec vl'=>kv vl. rewrite /= big_sepL_cons.
      iIntros "/= [% Hvl]". subst kv. iDestruct "Hf" as (f) "[EQ #Hf]".
      iDestruct "EQ" as %[=->]. iSpecialize ("Hf" $! x vl k).
      iMod (HEsat with "[%] HE HL") as (q') "[HE' Hclose]"; first done.
      iApply ("Hf" with "HEAP LFT Htl HE' [] [HC Hclose HT']").
      + by rewrite /llctx_interp big_sepL_nil.
      + iIntros "HE'". iApply fupd_cctx_interp. iMod ("Hclose" with "HE'") as "[HE HL]".
        iSpecialize ("HC" with "HE"). iModIntro. iIntros (y) "IN".
        iDestruct "IN" as %->%elem_of_list_singleton. iIntros (args) "Htl _ HT".
        iSpecialize ("HC" with "* []"); first by (iPureIntro; apply elem_of_list_singleton).
        iApply ("HC" $! args with "Htl HL"). rewrite tctx_interp_singleton tctx_interp_cons.
        iFrame.
      + rewrite /tctx_interp vec_to_list_map zip_with_fmap_r
                (zip_with_zip (λ v ty, (v, _))) zip_with_zip !big_sepL_fmap.
        iApply (big_sepL_mono' with "Hvl"). by iIntros (i [v ty']).
  Qed.

  Lemma type_fn {A m} E L E' fb kb (argsb : list binder) e
        (tys : A → vec type (length argsb)) ty
        (cps : vec path m) (ctyl : vec type m) `{!LstCopy ctyl, !LstSend ctyl} :
    Closed (fb :b: kb :b: argsb +b+ []) e →
    (∀ x f k (args : vec val _),
        typed_body (E' x) [] [CCtx_iscont k [] 1 (λ v, [TCtx_hasty (v!!!0) (ty x)])]
                   (TCtx_hasty f (fn E' tys ty) ::
                      zip_with (TCtx_hasty ∘ of_val) args (tys x) ++
                      zip_with TCtx_hasty cps ctyl)
                   (subst' fb f $ subst_v (kb :: argsb) (vmap of_val $ k ::: args) e)) →
    typed_instruction_ty E L (zip_with TCtx_hasty cps ctyl)
                         (Rec fb (kb :: argsb) e) (fn E' tys ty).
  Proof.
    iIntros (Hc Hbody tid qE) "#HEAP #LFT $ $ $ #HT". iApply wp_value.
    { simpl. rewrite decide_left. done. }
    rewrite tctx_interp_singleton. iLöb as "IH". iExists _. iSplit.
    { simpl. rewrite decide_left. done. }
    iExists _. iSplit; first done. iAlways. clear qE.
    iIntros (x args k tid' qE) "_ _ Htl HE HL HC HT'". iApply wp_rec; try done.
    { rewrite Forall_fmap Forall_forall=>? _. rewrite /= to_of_val. eauto. }
    { by rewrite -vec_to_list_cons -vec_to_list_map -subst_v_eq. }
    iApply (Hbody with "* HEAP LFT Htl HE HL HC").
    rewrite tctx_interp_cons tctx_interp_app. iFrame "HT' IH".
    iApply tctx_send. by iNext.
  Qed.
End typing.
