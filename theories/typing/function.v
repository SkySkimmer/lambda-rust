From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import vector.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
Set Default Proof Using "Type".

Section fn.
  Context `{typeG Σ} {A : Type} {n : nat}.

  Record fn_params := FP { fp_tys : vec type n; fp_ty : type; fp_E : elctx }.

  Program Definition fn (fp : A → fn_params) : type :=
    {| st_own tid vl := (∃ fb kb xb e H,
         ⌜vl = [@RecV fb (kb::xb) e H]⌝ ∗ ⌜length xb = n⌝ ∗
         ▷ ∀ (x : A) (k : val) (xl : vec val (length xb)),
            □ typed_body (fp x).(fp_E) []
                         [k◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (fp x).(fp_ty)])]
                         (zip_with (TCtx_hasty ∘ of_val) xl
                                   (box <$> (vec_to_list (fp x).(fp_tys))))
                         (subst_v (fb::kb::xb) (RecV fb (kb::xb) e:::k:::xl) e))%I |}.
  Next Obligation.
    iIntros (fp tid vl) "H". iDestruct "H" as (fb kb xb e ?) "[% _]". by subst.
  Qed.

  Global Instance fn_send fp : Send (fn fp).
  Proof. iIntros (tid1 tid2 vl). done. Qed.

  Definition fn_params_rel (ty_rel : relation type) : relation fn_params :=
    λ fp1 fp2,
      Forall2 ty_rel fp2.(fp_tys) fp1.(fp_tys) ∧ ty_rel fp1.(fp_ty) fp2.(fp_ty) ∧
      fp1.(fp_E) = fp2.(fp_E).

  Global Instance fp_tys_proper R :
    Proper (flip (fn_params_rel R) ==> (Forall2 R : relation (vec _ _))) fp_tys.
  Proof. intros ?? HR. apply HR. Qed.
  Global Instance fp_tys_proper_flip R :
    Proper (fn_params_rel R ==> flip (Forall2 R : relation (vec _ _))) fp_tys.
  Proof. intros ?? HR. apply HR. Qed.

  Global Instance fp_ty_proper R :
    Proper (fn_params_rel R ==> R) fp_ty.
  Proof. intros ?? HR. apply HR. Qed.

  Global Instance fp_E_proper R :
    Proper (fn_params_rel R ==> eq) fp_E.
  Proof. intros ?? HR. apply HR. Qed.

  Global Instance FP_proper R :
    Proper (flip (Forall2 R : relation (vec _ _)) ==> R ==> eq ==> fn_params_rel R) FP.
  Proof. by split; [|split]. Qed.

  Global Instance fn_type_contractive n' :
    Proper (pointwise_relation A (fn_params_rel (type_dist2_later n')) ==>
            type_dist2 n') fn.
  Proof.
    intros fp1 fp2 Hfp. apply ty_of_st_type_ne. destruct n'; first done.
    constructor; simpl.
    (* TODO: 'f_equiv' is slow here because reflexivity is slow. *)
    (* The clean way to do this would be to have a metric on type contexts. Oh well. *)
    intros tid vl. unfold typed_body.
    do 12 f_equiv. f_contractive. do 17 (apply Hfp || f_equiv).
    - f_equiv. apply Hfp.
    - rewrite !cctx_interp_singleton /=. do 5 f_equiv.
      rewrite !tctx_interp_singleton /tctx_elt_interp /=. repeat (apply Hfp || f_equiv).
    - rewrite /tctx_interp !big_sepL_zip_with /=. do 3 f_equiv.
      cut (∀ n tid p i, Proper (dist n ==> dist n)
        (λ (l : list _), ∀ ty, ⌜l !! i = Some ty⌝ → tctx_elt_interp tid (p ◁ ty))%I).
      { intros Hprop. apply Hprop, list_fmap_ne; last first.
        - symmetry. eapply Forall2_impl; first apply Hfp. intros.
          apply dist_later_dist, type_dist2_dist_later. done.
        - apply _. }
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

  Global Instance fn_ne n' :
    Proper (pointwise_relation A (fn_params_rel (dist n')) ==> dist n') fn.
  Proof.
    intros ?? Hfp. apply dist_later_dist, type_dist2_dist_later.
    apply fn_type_contractive=>u. split; last split.
    - eapply Forall2_impl; first apply Hfp. intros. simpl.
      apply type_dist_dist2. done.
    - apply type_dist_dist2. apply Hfp.
    - apply Hfp.
  Qed.
End fn.

Arguments fn_params {_ _} _.

(* The parameter of [FP] are in the wrong order in order to make sure
   that type-checking is done in that order, so that the [ELCtx_Alive]
   is taken as a coercion. We reestablish the intuitive order with
   [FP'] *)
Notation FP' E tys ty := (FP tys ty E).

(* We use recursive notation for binders as well, to allow patterns
   like '(a, b) to be used. In practice, only one binder is ever used,
   but using recursive binders is the only way to make Coq accept
   patterns. *)
(* FIXME : because of a bug in Coq, such patterns only work for
   printing. Once on 8.6pl1, this should work.  *)
Notation "'fn(∀' x .. x' ',' E ';' T1 ',' .. ',' TN ')' '→' R" :=
  (fn (λ x, (.. (λ x',
      FP' E%EL (Vector.cons T1 .. (Vector.cons TN Vector.nil) ..)%T R%T)..)))
  (at level 99, R at level 200, x binder, x' binder,
   format "'fn(∀'  x .. x' ','  E ';'  T1 ','  .. ','  TN ')'  '→'  R") : lrust_type_scope.
Notation "'fn(∀' x .. x' ',' E ')' '→' R" :=
  (fn (λ x, (.. (λ x', FP' E%EL Vector.nil R%T)..)))
  (at level 99, R at level 200, x binder, x' binder,
   format "'fn(∀'  x .. x' ','  E ')'  '→'  R") : lrust_type_scope.
Notation "'fn(' E ';' T1 ',' .. ',' TN ')' '→' R" :=
  (fn (λ _:(), FP' E%EL (Vector.cons T1 .. (Vector.cons TN Vector.nil) ..) R%T))
  (at level 99, R at level 200,
   format "'fn(' E ';'  T1 ','  .. ','  TN ')'  '→'  R") : lrust_type_scope.
Notation "'fn(' E ')' '→' R" :=
  (fn (λ _:(), FP' E%EL Vector.nil R%T))
  (at level 99, R at level 200,
   format "'fn(' E ')'  '→'  R") : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma fn_subtype {A n} E0 L0 (fp fp' : A → fn_params n) :
    (∀ x, elctx_incl E0 L0 (fp' x).(fp_E) (fp x).(fp_E)) →
    (∀ x, Forall2 (subtype (E0 ++ (fp' x).(fp_E)) L0)
                  (fp' x).(fp_tys) (fp x).(fp_tys)) →
    (∀ x, subtype (E0 ++ (fp' x).(fp_E)) L0 (fp x).(fp_ty) (fp' x).(fp_ty)) →
    subtype E0 L0 (fn fp) (fn fp').
  Proof.
    intros HE Htys Hty. apply subtype_simple_type=>//= _ vl.
    iIntros "#HE0 #HL0 Hf". iDestruct "Hf" as (fb kb xb e ?) "[% [% #Hf]]". subst.
    iExists fb, kb, xb, e, _. iSplit. done. iSplit. done. iNext.
    rewrite /typed_body. iIntros (x k xl) "!# * #LFT Htl HE HL HC HT".
    iDestruct (elctx_interp_persist with "HE") as "#HEp".
    iMod (HE with "HE0 HL0 HE") as (qE') "[HE' Hclose]". done.
    iApply ("Hf" with "LFT Htl HE' HL [HC Hclose] [HT]").
    - iIntros "HE'". unfold cctx_interp. iIntros (elt) "Helt".
      iDestruct "Helt" as %->%elem_of_list_singleton. iIntros (ret) "Htl HL HT".
      iMod ("Hclose" with "HE'") as "HE".
      iSpecialize ("HC" with "HE"). unfold cctx_elt_interp.
      iApply ("HC" $! (_ ◁cont(_, _)%CC) with "[%] Htl HL >").
      { by apply elem_of_list_singleton. }
      rewrite /tctx_interp !big_sepL_singleton /=.
      iDestruct "HT" as (v) "[HP Hown]". iExists v. iFrame "HP".
      assert (Hst : subtype (E0 ++ (fp' x).(fp_E)) L0
                            (box (fp x).(fp_ty)) (box (fp' x).(fp_ty)))
        by by rewrite ->Hty.
      iDestruct (Hst with "[HE0 HEp] HL0") as "(_ & Hty & _)".
      { rewrite /elctx_interp_0 big_sepL_app. by iSplit. }
      by iApply "Hty".
    - rewrite /tctx_interp
         -(fst_zip (fp x).(fp_tys) (fp' x).(fp_tys)) ?vec_to_list_length //
         -{1}(snd_zip (fp x).(fp_tys) (fp' x).(fp_tys)) ?vec_to_list_length //
         !zip_with_fmap_r !(zip_with_zip (λ _ _, (_ ∘ _) _ _)) !big_sepL_fmap.
      iApply big_sepL_impl. iSplit; last done. iIntros "{HT}!#".
      iIntros (i [p [ty1' ty2']]) "#Hzip H /=".
      iDestruct "H" as (v) "[? Hown]". iExists v. iFrame.
      rewrite !lookup_zip_with.
      iDestruct "Hzip" as %(? & ? & ([? ?] & (? & Hty'1 &
        (? & Hty'2 & [=->->])%bind_Some)%bind_Some & [=->->->])%bind_Some)%bind_Some.
      eapply Forall2_lookup_lr in Htys; try done.
      assert (Hst : subtype (E0 ++ (fp' x).(fp_E)) L0 (box ty2') (box ty1'))
        by by rewrite ->Htys.
      iDestruct (Hst with "[] []") as "(_ & #Ho & _)"; [ |done|].
      { rewrite /elctx_interp_0 big_sepL_app. by iSplit. }
      by iApply "Ho".
  Qed.

  (* This proper and the next can probably not be inferred, but oh well. *)
  Global Instance fn_subtype' {A n} E0 L0 :
    Proper (pointwise_relation A (fn_params_rel (n:=n) (subtype E0 L0)) ==>
            subtype E0 L0) fn.
  Proof.
    intros fp1 fp2 Hfp. apply fn_subtype=>x; destruct (Hfp x) as (Htys & Hty & HE).
    - by rewrite HE.
    - eapply Forall2_impl; first eapply Htys. intros ??.
      eapply subtype_weaken; last done. by apply submseteq_inserts_r.
    - eapply subtype_weaken, Hty; last done. by apply submseteq_inserts_r.
  Qed.

  Global Instance fn_eqtype' {A n} E0 L0 :
    Proper (pointwise_relation A (fn_params_rel (n:=n) (eqtype E0 L0)) ==>
            eqtype E0 L0) fn.
  Proof.
    intros fp1 fp2 Hfp. split; eapply fn_subtype=>x; destruct (Hfp x) as (Htys & Hty & HE).
    - by rewrite HE.
    - eapply Forall2_impl; first eapply Htys. intros t1 t2 Ht.
      eapply subtype_weaken; last apply Ht; last done. by apply submseteq_inserts_r.
    - eapply subtype_weaken; last apply Hty; last done. by apply submseteq_inserts_r.
    - by rewrite HE.
    - symmetry in Htys. eapply Forall2_impl; first eapply Htys. intros t1 t2 Ht.
      eapply subtype_weaken; last apply Ht; last done. by apply submseteq_inserts_r.
    - eapply subtype_weaken; last apply Hty; last done. by apply submseteq_inserts_r.
  Qed.

  Lemma fn_subtype_specialize {A B n} (σ : A → B) E0 L0 fp :
    subtype E0 L0 (fn (n:=n) fp) (fn (fp ∘ σ)).
  Proof.
    apply subtype_simple_type=>//= _ vl.
    iIntros "_ _ Hf". iDestruct "Hf" as (fb kb xb e ?) "[% [% #Hf]]". subst.
    iExists fb, kb, xb, e, _. iSplit. done. iSplit. done.
    rewrite /typed_body. iNext. iIntros "*". iApply "Hf".
  Qed.

  Lemma type_call' {A} E L T p (ps : list path)
                         (fp : A → fn_params (length ps)) k x :
    elctx_sat E L (fp x).(fp_E) →
    typed_body E L [k ◁cont(L, λ v : vec _ 1, (v!!!0 ◁ box (fp x).(fp_ty)) :: T)]
               ((p ◁ fn fp) ::
                zip_with TCtx_hasty ps (box <$> (vec_to_list (fp x).(fp_tys))) ++
                T)
               (call: p ps → k).
  Proof.
    iIntros (HE tid qE) "#LFT Htl HE HL HC".
    rewrite tctx_interp_cons tctx_interp_app. iIntros "(Hf & Hargs & HT)".
    wp_apply (wp_hasty with "Hf"). iIntros (v) "% Hf".
    iApply (wp_app_vec _ _ (_::_) ((λ v, ⌜v = k⌝):::
               vmap (λ ty (v : val), tctx_elt_interp tid (v ◁ box ty)) (fp x).(fp_tys))%I
            with "[Hargs]"); first wp_done.
    - rewrite /= big_sepL_cons. iSplitR "Hargs"; first by iApply wp_value'.
      clear dependent k p.
      rewrite /tctx_interp vec_to_list_map !zip_with_fmap_r
              (zip_with_zip (λ e ty, (e, _))) zip_with_zip !big_sepL_fmap.
      iApply (big_sepL_mono' with "Hargs"). iIntros (i [p ty]) "HT/=".
      iApply (wp_hasty with "HT"). setoid_rewrite tctx_hasty_val. iIntros (?) "? $".
    - simpl. change (@length expr ps) with (length ps).
      iIntros (vl'). inv_vec vl'=>kv vl. rewrite /= big_sepL_cons.
      iIntros "/= [% Hvl]". subst kv. iDestruct "Hf" as (fb kb xb e ?) "[EQ [EQl #Hf]]".
      iDestruct "EQ" as %[=->]. iDestruct "EQl" as %EQl. revert vl fp HE.
      rewrite <-EQl=>vl fp HE. iApply wp_rec; try done.
      { rewrite -fmap_cons Forall_fmap Forall_forall=>? _. rewrite /= to_of_val. eauto. }
      { rewrite -fmap_cons -(subst_v_eq (fb::kb::xb) (_:::k:::vl)) //. }
      iNext. iSpecialize ("Hf" $! x k vl).
      iMod (HE with "HE HL") as (q') "[HE' Hclose]"; first done.
      iApply ("Hf" with "LFT Htl HE' [] [HC Hclose HT]").
      + by rewrite /llctx_interp big_sepL_nil.
      + iIntros "HE'". iApply fupd_cctx_interp. iMod ("Hclose" with "HE'") as "[HE HL]".
        iSpecialize ("HC" with "HE"). iModIntro. iIntros (y) "IN".
        iDestruct "IN" as %->%elem_of_list_singleton. iIntros (args) "Htl _ Hret".
        iSpecialize ("HC" with "[]"); first by (iPureIntro; apply elem_of_list_singleton).
        iApply ("HC" $! args with "Htl HL").
        rewrite tctx_interp_singleton tctx_interp_cons. iFrame.
      + rewrite /tctx_interp vec_to_list_map !zip_with_fmap_r
                (zip_with_zip (λ v ty, (v, _))) zip_with_zip !big_sepL_fmap.
        iApply (big_sepL_mono' with "Hvl"). by iIntros (i [v ty']).
  Qed.

  Lemma type_call {A} x E L C T T' T'' p (ps : list path)
                        (fp : A → fn_params (length ps)) k :
    (p ◁ fn fp)%TC ∈ T →
    elctx_sat E L (fp x).(fp_E) →
    tctx_extract_ctx E L (zip_with TCtx_hasty ps
                                   (box <$> vec_to_list (fp x).(fp_tys))) T T' →
    (k ◁cont(L, T''))%CC ∈ C →
    (∀ ret : val, tctx_incl E L ((ret ◁ box (fp x).(fp_ty))::T') (T'' [# ret])) →
    typed_body E L C T (call: p ps → k).
  Proof.
    intros Hfn HE HTT' HC HT'T''.
    rewrite -typed_body_mono /flip; last done; first by eapply type_call'.
    - etrans. eapply (incl_cctx_incl _ [_]); first by intros ? ->%elem_of_list_singleton.
      apply cctx_incl_cons_match; first done. intros args. by inv_vec args.
    - etrans; last by apply (tctx_incl_frame_l [_]).
      apply copy_elem_of_tctx_incl; last done. apply _.
  Qed.

  Lemma type_letcall {A} x E L C T T' p (ps : list path)
                        (fp : A → fn_params (length ps)) b e :
    Closed (b :b: []) e → Closed [] p → Forall (Closed []) ps →
    (p ◁ fn fp)%TC ∈ T →
    elctx_sat E L (fp x).(fp_E) →
    tctx_extract_ctx E L (zip_with TCtx_hasty ps
                                   (box <$> vec_to_list (fp x).(fp_tys))) T T' →
    (∀ ret : val, typed_body E L C ((ret ◁ box (fp x).(fp_ty))::T') (subst' b ret e)) -∗
    typed_body E L C T (letcall: b := p ps in e).
  Proof.
    iIntros (?? Hpsc ???) "He".
    iApply (type_cont_norec [_] _ (λ r, (r!!!0 ◁ box (fp x).(fp_ty)) :: T')%TC).
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; first done. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl=>//.
        intros. eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      (* TODO : make [simpl_subst] work here. *)
      change (subst' "_k" k (p (Var "_k" :: ps))) with
             ((subst "_k" k p) (of_val k :: map (subst "_k" k) ps)).
      rewrite is_closed_nil_subst //.
      assert (map (subst "_k" k) ps = ps) as ->.
      { clear -Hpsc. induction Hpsc=>//=. rewrite is_closed_nil_subst //. congruence. }
      iApply type_call; try done. constructor. done.
    - simpl. iIntros (k ret). inv_vec ret=>ret. rewrite /subst_v /=.
      rewrite ->(is_closed_subst []); last set_solver+; last first.
      { apply subst'_is_closed; last done. apply is_closed_of_val. }
      (iApply typed_body_mono; last by iApply "He"); [|done..].
      apply incl_cctx_incl. set_solver+.
  Qed.

  Lemma type_rec {A} E L fb (argsb : list binder) ef e n
        (fp : A → fn_params n) T `{!CopyC T, !SendC T} :
    ef = (funrec: fb argsb := e)%E →
    n = length argsb →
    Closed (fb :b: "return" :b: argsb +b+ []) e →
    □ (∀ x (f : val) k (args : vec val (length argsb)),
          typed_body (fp x).(fp_E) []
                     [k ◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (fp x).(fp_ty)])]
                     ((f ◁ fn fp) ::
                        zip_with (TCtx_hasty ∘ of_val) args
                                 (box <$> vec_to_list (fp x).(fp_tys)) ++ T)
                     (subst_v (fb :: BNamed "return" :: argsb) (f ::: k ::: args) e)) -∗
    typed_instruction_ty E L T ef (fn fp).
  Proof.
    iIntros (-> -> Hc) "#Hbody". iIntros (tid qE) " #LFT $ $ $ #HT". iApply wp_value.
    { simpl. rewrite ->(decide_left Hc). done. }
    rewrite tctx_interp_singleton. iLöb as "IH". iExists _. iSplit.
    { simpl. rewrite decide_left. done. }
    iExists fb, _, argsb, e, _. iSplit. done. iSplit. done. iNext. clear qE.
    iIntros (x k args) "!#". iIntros (tid' qE) "_ Htl HE HL HC HT'".
    iApply ("Hbody" with "LFT Htl HE HL HC").
    rewrite tctx_interp_cons tctx_interp_app. iFrame "HT' IH".
    by iApply sendc_change_tid.
  Qed.

  Lemma type_fn {A} E L (argsb : list binder) ef e n
        (fp : A → fn_params n) T `{!CopyC T, !SendC T} :
    ef = (funrec: <> argsb := e)%E →
    n = length argsb →
    Closed ("return" :b: argsb +b+ []) e →
    □ (∀ x k (args : vec val (length argsb)),
        typed_body (fp x).(fp_E) []
                   [k ◁cont([], λ v : vec _ 1, [v!!!0 ◁ box (fp x).(fp_ty)])]
                   (zip_with (TCtx_hasty ∘ of_val) args
                             (box <$> vec_to_list (fp x).(fp_tys)) ++ T)
                   (subst_v (BNamed "return" :: argsb) (k ::: args) e)) -∗
    typed_instruction_ty E L T ef (fn fp).
  Proof.
    iIntros (???) "#He". iApply type_rec; try done. iIntros "!# *".
    iApply typed_body_mono; last iApply "He"; try done.
    eapply contains_tctx_incl. by constructor.
  Qed.
End typing.

Hint Resolve fn_subtype : lrust_typing.
