From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import vector.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
Set Default Proof Using "Type".

Section fn.
  Context `{typeG Σ} {A : Type} {n : nat}.

  Program Definition fn (E : A → elctx)
          (tys : A → vec type n) (ty : A → type) : type :=
    {| st_own tid vl := (∃ fb kb xb e H,
         ⌜vl = [@RecV fb (kb::xb) e H]⌝ ∗ ⌜length xb = n⌝ ∗
         ▷ ∀ (x : A) (k : val) (xl : vec val (length xb)),
            typed_body (E x) []
                       [k◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (ty x)])]
                       (zip_with (TCtx_hasty ∘ of_val) xl
                                 ((λ ty, box ty) <$> (vec_to_list (tys x))))
                       (subst_v (fb::kb::xb) (RecV fb (kb::xb) e:::k:::xl) e))%I |}.
  Next Obligation.
    iIntros (E tys ty tid vl) "H". iDestruct "H" as (fb kb xb e ?) "[% _]". by subst.
  Qed.

  Global Instance fn_send E tys ty : Send (fn E tys ty).
  Proof. iIntros (tid1 tid2 vl). done. Qed.

  Lemma fn_contractive n' E :
    Proper (pointwise_relation A (dist_later n') ==>
            pointwise_relation A (dist_later n') ==> dist n') (fn E).
  Proof.
    intros ?? Htys ?? Hty. unfold fn. f_equiv. rewrite st_dist_unfold /=.
    f_contractive=>tid vl. unfold typed_body.
    do 12 f_equiv. f_contractive. do 18 f_equiv.
    - rewrite !cctx_interp_singleton /=. do 5 f_equiv.
      rewrite !tctx_interp_singleton /tctx_elt_interp /=. repeat f_equiv. apply Hty.
      by rewrite (ty_size_proper_d _ _ _ (Hty _)).
    - rewrite /tctx_interp !big_sepL_zip_with /=. do 3 f_equiv.
      cut (∀ n tid p i, Proper (dist (S n) ==> dist n)
        (λ (l : list _), ∀ ty, ⌜l !! i = Some ty⌝ → tctx_elt_interp tid (p ◁ ty))%I).
      { intros Hprop. apply Hprop, list_fmap_ne, Htys. intros ty1 ty2 Hty12.
        rewrite (ty_size_proper_d _ _ _ Hty12). by rewrite Hty12. }
      clear. intros n tid p i x y. rewrite list_dist_lookup=>Hxy.
      specialize (Hxy i). destruct (x !! i) as [tyx|], (y !! i) as [tyy|];
        inversion_clear Hxy; last done.
      transitivity (tctx_elt_interp tid (p ◁ tyx));
        last transitivity (tctx_elt_interp tid (p ◁ tyy)); last 2 first.
      + unfold tctx_elt_interp. do 3 f_equiv. by apply ty_own_ne.
      + apply equiv_dist. iSplit.
        * iIntros "H * #EQ". by iDestruct "EQ" as %[=->].
        * iIntros "H". by iApply "H".
      + apply equiv_dist. iSplit.
        * iIntros "H". by iApply "H".
        * iIntros "H * #EQ". by iDestruct "EQ" as %[=->].
  Qed.
  Global Existing Instance fn_contractive.

  Global Instance fn_ne n' E :
    Proper (pointwise_relation A (dist n') ==>
            pointwise_relation A (dist n') ==> dist n') (fn E).
  Proof.
    intros ?? H1 ?? H2.
    apply fn_contractive=>u; (destruct n'; [done|apply dist_S]);
      [apply (H1 u)|apply (H2 u)].
  Qed.
End fn.

Section typing.
  Context `{typeG Σ}.

  Lemma fn_subtype_full {A n} E0 L0 E E' (tys tys' : A → vec type n) ty ty' :
    (∀ x, elctx_incl E0 L0 (E x) (E' x)) →
    (∀ x, Forall2 (subtype (E0 ++ E x) L0) (tys' x) (tys x)) →
    (∀ x, subtype (E0 ++ E x) L0 (ty x) (ty' x)) →
    subtype E0 L0 (fn E' tys ty) (fn E tys' ty').
  Proof.
    intros HE Htys Hty. apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT #HE0 #HL0 Hf". iDestruct "Hf" as (fb kb xb e ?) "[% [% #Hf]]". subst.
    iExists fb, kb, xb, e, _. iSplit. done. iSplit. done. iNext.
    rewrite /typed_body. iIntros "* !# * #HEAP _ Htl HE HL HC HT".
    iDestruct (elctx_interp_persist with "HE") as "#HEp".
    iMod (HE with "HE0 HL0 * HE") as (qE') "[HE' Hclose]". done.
    iApply ("Hf" with "* HEAP LFT Htl HE' HL [HC Hclose] [HT]").
    - iIntros "HE'". unfold cctx_interp. iIntros (elt) "Helt".
      iDestruct "Helt" as %->%elem_of_list_singleton. iIntros (ret) "Htl HL HT".
      iMod ("Hclose" with "HE'") as "HE".
      iSpecialize ("HC" with "HE"). unfold cctx_elt_interp.
      iApply ("HC" $! (_ ◁cont(_, _)%CC) with "[%] * Htl HL >").
      { by apply elem_of_list_singleton. }
      rewrite /tctx_interp !big_sepL_singleton /=.
      iDestruct "HT" as (v) "[HP Hown]". iExists v. iFrame "HP".
      assert (Hst : subtype (E0 ++ E x) L0 (box (ty x)) (box (ty' x)))
        by by rewrite ->Hty.
      iDestruct (Hst with "LFT [HE0 HEp] HL0") as "(_ & Hty & _)".
      { rewrite /elctx_interp_0 big_sepL_app. by iSplit. }
      by iApply "Hty".
    - rewrite /tctx_interp
         -(fst_zip (tys x) (tys' x)) ?vec_to_list_length //
         -{1}(snd_zip (tys x) (tys' x)) ?vec_to_list_length //
         !zip_with_fmap_r !(zip_with_zip (λ _ _, (_ ∘ _) _ _)) !big_sepL_fmap.
      iApply big_sepL_impl. iSplit; last done. iIntros "{HT}!#".
      iIntros (i [p [ty1' ty2']]) "#Hzip H /=".
      iDestruct "H" as (v) "[? Hown]". iExists v. iFrame.
      rewrite !lookup_zip_with.
      iDestruct "Hzip" as %(? & ? & ([? ?] & (? & Hty'1 &
        (? & Hty'2 & [=->->])%bind_Some)%bind_Some & [=->->->])%bind_Some)%bind_Some.
      specialize (Htys x). eapply Forall2_lookup_lr in Htys; try done.
      assert (Hst : subtype (E0 ++ E x) L0 (box ty2') (box ty1'))
        by by rewrite ->Htys.
      iDestruct (Hst with "* [] [] []") as "(_ & #Ho & _)"; [done| |done|].
      { rewrite /elctx_interp_0 big_sepL_app. by iSplit. }
      by iApply "Ho".
  Qed.

  Lemma fn_subtype_ty {A n} E0 L0 E (tys1 tys2 : A → vec type n) ty1 ty2 :
    (∀ x, Forall2 (subtype (E0 ++ E x) L0) (tys2 x) (tys1 x)) →
    (∀ x, subtype (E0 ++ E x) L0 (ty1 x) (ty2 x)) →
    subtype E0 L0 (fn E tys1 ty1) (fn E tys2 ty2).
  Proof. intros. by apply fn_subtype_full. Qed.

  (* This proper and the next can probably not be inferred, but oh well. *)
  Global Instance fn_subtype_ty' {A n} E0 L0 E :
    Proper (flip (pointwise_relation A (λ (v1 v2 : vec type n), Forall2 (subtype E0 L0) v1 v2)) ==>
            pointwise_relation A (subtype E0 L0) ==> subtype E0 L0) (fn E).
  Proof.
    intros tys1 tys2 Htys ty1 ty2 Hty. apply fn_subtype_ty.
    - intros. eapply Forall2_impl; first eapply Htys. intros ??.
      eapply subtype_weaken; last done. by apply submseteq_inserts_r.
    - intros. eapply subtype_weaken, Hty; last done. by apply submseteq_inserts_r.
  Qed.

  Global Instance fn_eqtype_ty' {A n} E0 L0 E :
    Proper (pointwise_relation A (λ (v1 v2 : vec type n), Forall2 (eqtype E0 L0) v1 v2) ==>
            pointwise_relation A (eqtype E0 L0) ==> eqtype E0 L0) (fn E).
  Proof.
    intros tys1 tys2 Htys ty1 ty2 Hty. split; eapply fn_subtype_ty'; try (by intro; apply Hty);
      intros x; (apply Forall2_flip + idtac); (eapply Forall2_impl; first by eapply (Htys x)); by intros ??[].
  Qed.

  Lemma fn_subtype_elctx_sat {A n} E0 L0 E E' (tys : A → vec type n) ty :
    (∀ x, elctx_sat (E x) [] (E' x)) →
    subtype E0 L0 (fn E' tys ty) (fn E tys ty).
  Proof.
    intros. apply fn_subtype_full; try done. by intros; apply elctx_sat_incl.
  Qed.

  Lemma fn_subtype_lft_incl {A n} E0 L0 E κ κ' (tys : A → vec type n) ty :
    lctx_lft_incl E0 L0 κ κ' →
    subtype E0 L0 (fn (λ x, (κ ⊑ κ') :: E x)%EL tys ty) (fn E tys ty).
  Proof.
    intros Hκκ'. apply fn_subtype_full; try done. intros.
    apply elctx_incl_lft_incl; last by apply elctx_incl_refl.
    iIntros "#HE #HL". iApply (Hκκ' with "[HE] HL").
    rewrite /elctx_interp_0 big_sepL_app. iDestruct "HE" as "[$ _]".
  Qed.

  Lemma fn_subtype_specialize {A B n} (σ : A → B) E0 L0 E tys ty :
    subtype E0 L0 (fn (n:=n) E tys ty) (fn (E ∘ σ) (tys ∘ σ) (ty ∘ σ)).
  Proof.
    apply subtype_simple_type=>//= _ vl.
    iIntros "#LFT _ _ Hf". iDestruct "Hf" as (fb kb xb e ?) "[% [% #Hf]]". subst.
    iExists fb, kb, xb, e, _. iSplit. done. iSplit. done.
    rewrite /typed_body. iNext. iIntros "*". iApply "Hf".
  Qed.

  Lemma type_call' {A} E L E' T p (ps : list path)
                         (tys : A → vec type (length ps)) ty k x :
    elctx_sat E L (E' x) →
    typed_body E L [k ◁cont(L, λ v : vec _ 1, (v!!!0 ◁ box (ty x)) :: T)]
               ((p ◁ fn E' tys ty) ::
                zip_with TCtx_hasty ps ((λ ty, box ty) <$> (vec_to_list (tys x))) ++
                T)
               (call: p ps → k).
  Proof.
    iIntros (HE) "!# * #HEAP #LFT Htl HE HL HC".
    rewrite tctx_interp_cons tctx_interp_app. iIntros "(Hf & Hargs & HT)".
    wp_bind p. iApply (wp_hasty with "Hf"). iIntros (v) "% Hf".
    iApply (wp_app_vec _ _ (_::_) ((λ v, ⌜v = k⌝):::
               vmap (λ ty (v : val), tctx_elt_interp tid (v ◁ box ty)) (tys x))%I
            with "* [Hargs]"); first wp_done.
    - rewrite /= big_sepL_cons. iSplitR "Hargs"; first by iApply wp_value'.
      clear dependent ty k p.
      rewrite /tctx_interp vec_to_list_map !zip_with_fmap_r
              (zip_with_zip (λ e ty, (e, _))) zip_with_zip !big_sepL_fmap.
      iApply (big_sepL_mono' with "Hargs"). iIntros (i [p ty]) "HT/=".
      iApply (wp_hasty with "HT"). setoid_rewrite tctx_hasty_val. iIntros (?) "? $".
    - simpl. change (@length expr ps) with (length ps).
      iIntros (vl'). inv_vec vl'=>kv vl. rewrite /= big_sepL_cons.
      iIntros "/= [% Hvl]". subst kv. iDestruct "Hf" as (fb kb xb e ?) "[EQ [EQl #Hf]]".
      iDestruct "EQ" as %[=->]. iDestruct "EQl" as %EQl. revert vl tys.
      rewrite <-EQl=>vl tys. iApply wp_rec; try done.
      { rewrite -fmap_cons Forall_fmap Forall_forall=>? _. rewrite /= to_of_val. eauto. }
      { rewrite -fmap_cons -(subst_v_eq (fb::kb::xb) (_:::k:::vl)) //. }
      iNext. iSpecialize ("Hf" $! x k vl).
      iMod (HE with "HE HL") as (q') "[HE' Hclose]"; first done.
      iApply ("Hf" with "HEAP LFT Htl HE' [] [HC Hclose HT]").
      + by rewrite /llctx_interp big_sepL_nil.
      + iIntros "HE'". iApply fupd_cctx_interp. iMod ("Hclose" with "HE'") as "[HE HL]".
        iSpecialize ("HC" with "HE"). iModIntro. iIntros (y) "IN".
        iDestruct "IN" as %->%elem_of_list_singleton. iIntros (args) "Htl _ Hret".
        iSpecialize ("HC" with "* []"); first by (iPureIntro; apply elem_of_list_singleton).
        iApply ("HC" $! args with "Htl HL").
        rewrite tctx_interp_singleton tctx_interp_cons. iFrame.
      + rewrite /tctx_interp vec_to_list_map !zip_with_fmap_r
                (zip_with_zip (λ v ty, (v, _))) zip_with_zip !big_sepL_fmap.
        iApply (big_sepL_mono' with "Hvl"). by iIntros (i [v ty']).
  Qed.

  Lemma type_call {A} x E L E' C T T' T'' p (ps : list path)
                        (tys : A → vec type (length ps)) ty k :
    (p ◁ fn E' tys ty)%TC ∈ T →
    elctx_sat E L (E' x) →
    tctx_extract_ctx E L (zip_with TCtx_hasty ps
                                   ((λ ty, box ty) <$> vec_to_list (tys x))) T T' →
    (k ◁cont(L, T''))%CC ∈ C →
    (∀ ret : val, tctx_incl E L ((ret ◁ box (ty x))::T') (T'' [# ret])) →
    typed_body E L C T (call: p ps → k).
  Proof.
    intros Hfn HE HTT' HC HT'T''.
    rewrite -typed_body_mono /flip; last done; first by eapply type_call'.
    - etrans. eapply (incl_cctx_incl _ [_]); first by intros ? ->%elem_of_list_singleton.
      apply cctx_incl_cons_match; first done. intros args. by inv_vec args.
    - etrans; last by apply (tctx_incl_frame_l [_]).
      apply copy_elem_of_tctx_incl; last done. apply _.
  Qed.

  Lemma type_letcall {A} x E L E' C T T' p (ps : list path)
                        (tys : A → vec type (length ps)) ty b e :
    Closed (b :b: []) e → Closed [] p → Forall (Closed []) ps →
    (p ◁ fn E' tys ty)%TC ∈ T →
    elctx_sat E L (E' x) →
    tctx_extract_ctx E L (zip_with TCtx_hasty ps
                                   ((λ ty, box ty) <$> vec_to_list (tys x))) T T' →
    (∀ ret : val, typed_body E L C ((ret ◁ box (ty x))::T') (subst' b ret e)) →
    typed_body E L C T (letcall: b := p ps in e).
  Proof.
    intros ?? Hpsc ????. eapply (type_cont [_] _ (λ r, (r!!!0 ◁ box (ty x)) :: T')%TC).
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; first done. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl=>//.
        intros. eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - intros.
      (* TODO : make [simpl_subst] work here. *)
      change (subst' "_k" k (p (Var "_k" :: ps))) with
             ((subst "_k" k p) (of_val k :: map (subst "_k" k) ps)).
      rewrite is_closed_nil_subst //.
      assert (map (subst "_k" k) ps = ps) as ->.
      { clear -Hpsc. induction Hpsc=>//=. rewrite is_closed_nil_subst //. congruence. }
      eapply type_call; try done. constructor. done.
    - move=>/= k ret. inv_vec ret=>ret. rewrite /subst_v /=.
      rewrite ->(is_closed_subst []), incl_cctx_incl; first done; try set_solver+.
      apply subst'_is_closed; last done. apply is_closed_of_val.
  Qed.

  Lemma type_rec {A} E L E' fb (argsb : list binder) e
        (tys : A → vec type (length argsb)) ty
        T `{!CopyC T, !SendC T} :
    Closed (fb :b: "return" :b: argsb +b+ []) e →
    (∀ x (f : val) k (args : vec val (length argsb)),
        typed_body (E' x) [] [k ◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (ty x)])]
                   ((f ◁ fn E' tys ty) ::
                      zip_with (TCtx_hasty ∘ of_val) args
                               ((λ ty, box ty) <$> vec_to_list (tys x)) ++ T)
                   (subst_v (fb :: BNamed "return" :: argsb) (f ::: k ::: args) e)) →
    typed_instruction_ty E L T (funrec: fb argsb := e) (fn E' tys ty).
  Proof.
    iIntros (Hc Hbody) "!# * #HEAP #LFT $ $ $ #HT". iApply wp_value.
    { simpl. rewrite ->(decide_left Hc). done. }
    rewrite tctx_interp_singleton. iLöb as "IH". iExists _. iSplit.
    { simpl. rewrite decide_left. done. }
    iExists fb, _, argsb, e, _. iSplit. done. iSplit. done. iNext. clear qE.
    iIntros (x k args) "!#". iIntros (tid' qE) "_ _ Htl HE HL HC HT'".
    iApply (Hbody with "* HEAP LFT Htl HE HL HC").
    rewrite tctx_interp_cons tctx_interp_app. iFrame "HT' IH".
    by iApply sendc_change_tid.
  Qed.

  Lemma type_fn {A} E L E' (argsb : list binder) e
        (tys : A → vec type (length argsb)) ty
        T `{!CopyC T, !SendC T} :
    Closed ("return" :b: argsb +b+ []) e →
    (∀ x k (args : vec val (length argsb)),
        typed_body (E' x) [] [k ◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (ty x)])]
                   (zip_with (TCtx_hasty ∘ of_val) args
                             ((λ ty, box ty) <$> vec_to_list (tys x)) ++ T)
                   (subst_v (BNamed "return" :: argsb) (k ::: args) e)) →
    typed_instruction_ty E L T (funrec: <> argsb := e) (fn E' tys ty).
  Proof.
    intros. apply type_rec; try done. intros. rewrite -typed_body_mono //=.
    eapply contains_tctx_incl. by constructor.
  Qed.
End typing.

Hint Resolve fn_subtype_full : lrust_typing.
