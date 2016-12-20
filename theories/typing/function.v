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
      iApply ("HC" $! (CCtx_iscont _ _ _ _) with "[%] * HL >").
        by apply elem_of_list_singleton.
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

  (* TODO: Define some syntactic sugar for calling and letrec like we do on paper. *)
  Lemma typed_call {A n} E L E' T T' (tys : A → vec type n) ty k p (ps : vec path n) x :
    tctx_incl E L T (zip_with TCtx_hasty ps (tys x) ++ T') → elctx_sat E L (E' x) →
    typed_body E L [CCtx_iscont k L 1 (λ v, (TCtx_hasty (v!!!0) (ty x)) :: T')]
               (TCtx_hasty p (fn E' tys ty) :: T) (p (of_val k :: ps)).
  Proof.
    (* FIXME: Why can't I merge these iIntros? *)
    iIntros (HTsat HEsat). iIntros (tid qE) "#LFT HE HL HC".
    rewrite tctx_interp_cons. iIntros "[Hf HT]".
    wp_bind p. iApply (wp_hasty with "Hf"). iIntros (v) "[% Hf]".
    iMod (HTsat with "LFT HE HL HT") as "(HE & HL & HT)". rewrite tctx_interp_app.
    iDestruct "HT" as "[Hargs HT']". clear HTsat. rewrite -vec_to_list_cons.
    iApply (wp_app_vec (λ i v, match i with O => ⌜v = k⌝ ∗ _ | S i =>
                           ∀ ty, ⌜(tys x : list type) !! i = Some ty⌝ →
                                 tctx_elt_interp tid (TCtx_hasty v ty) end)%I
            with "* [Hargs HC]"); first wp_done.
    - rewrite big_sepL_cons. iSplitR "Hargs".
      { iApply wp_value'. iSplit; first done. iApply "HC". }
      clear dependent ty k p.
      rewrite /tctx_interp. rewrite big_sepL_zip_with. iApply (big_sepL_mono with "Hargs").
      simpl. iIntros (i p Hp) "HT". assert (Hlen := lookup_lt_Some _ _ _ Hp).
      edestruct (lookup_lt_is_Some_2 (tys x)) as [ty Hty].
      { move: Hlen. rewrite !vec_to_list_length. done. }
      iSpecialize ("HT" with "* []"); first done.
      iApply (wp_hasty with "HT"). iIntros (v') "[% Hown]". iIntros (ty') "#EQ".
      rewrite Hty. iDestruct "EQ" as %[=<-]. iExists v'. iFrame "Hown".
      iPureIntro. exact: eval_path_of_val.
    - iIntros (vl'). assert (Hvl := Vector.eta vl'). remember (Vector.hd vl') as kv.
      remember (Vector.tl vl') as vl. rewrite Hvl. simpl in *. clear dependent vl'.
      rewrite big_sepL_cons. iIntros "[[% HC] Hvl]". subst kv.
      iDestruct "Hf" as (f) "[EQ #Hf]". iDestruct "EQ" as %[=->].
      iSpecialize ("Hf" $! x vl k). 
      iMod (HEsat with "[%] HE HL") as (q') "[HE' Hclose]"; first done.
      iApply ("Hf" with "LFT HE' [] [HC Hclose HT']").
      + by rewrite /llctx_interp big_sepL_nil.
      + iIntros "HE'". iApply fupd_cctx_interp. iMod ("Hclose" with "HE'") as "[HE HL]".
        iSpecialize ("HC" with "HE").  iModIntro. iIntros (y) "IN".
        iDestruct "IN" as %->%elem_of_list_singleton.
        iIntros (args) "_ HT". iSpecialize ("HC" with "* []"); first by (iPureIntro; apply elem_of_list_singleton).
        iApply ("HC" $! args with "HL"). rewrite tctx_interp_singleton tctx_interp_cons.
        iFrame.
      + rewrite /tctx_interp big_sepL_zip_with. done.
  Qed.

  Lemma typed_fn {A n m} E L E' (tys : A → vec type n) ty fb kb (argsb : vec binder n) ef e
       (cps : vec path m) (ctyl : vec type m) `{!LstCopy ctyl, !LstSend ctyl} :
    ef = Rec fb (kb :: argsb) e → Closed (fb :b: kb :b: argsb +b+ []) e →
    (∀ x f k (args : vec val n), typed_body (E' x) [] [CCtx_iscont k [] 1 (λ v, [TCtx_hasty (v!!!0) (ty x)])]
                 (TCtx_hasty f (fn E' tys ty) ::
                  zip_with (TCtx_hasty ∘ of_val) args (tys x) ++
                  zip_with TCtx_hasty cps ctyl)
                 (subst' fb f $ subst_vec (kb ::: argsb) (Vector.map of_val $ k ::: args) e)) →
    typed_instruction_ty E L (zip_with TCtx_hasty cps ctyl) ef (fn E' tys ty).
  Proof.
    iIntros (-> Hc Hbody). iIntros (tid qE) "!# #LFT $ $ #HT". iApply wp_value.
    { simpl. rewrite decide_left. done. }
    rewrite tctx_interp_singleton. iLöb as "IH". iExists _. iSplit.
    { simpl. rewrite decide_left. done. }
    iExists _. iSplit; first done. iAlways. clear qE. 
    iIntros (x args k). iIntros (tid' qE) "_ HE HL HC HT'".
    iApply wp_rec; try done.
    { apply Forall_of_val_is_val. }
    { rewrite -!vec_to_list_cons -vec_to_list_map -subst_vec_eq. eauto. }
    iApply (Hbody with "* LFT HE HL HC").
    rewrite tctx_interp_cons tctx_interp_app. iFrame "HT' IH".
    iApply tctx_send. by iNext.
  Qed.
End fn.
