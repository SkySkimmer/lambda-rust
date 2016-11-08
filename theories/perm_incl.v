From Coq Require Import Qcanon.
From iris.base_logic Require Import big_op.
From lrust Require Export type perm.

Import Perm Types.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Definitions *)
  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, ρ1 tid ={⊤}=∗ ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Definition borrowing κ (ρ ρ1 ρ2 : perm) :=
    ∀ tid, ρ tid ⊢ ρ1 tid ={⊤}=∗ ρ2 tid ∗ (κ ∋ ρ1)%P tid.

End defs.

Infix "⇒" := perm_incl (at level 95, no associativity) : C_scope.
Notation "(⇒)" := perm_incl (only parsing) : C_scope.

Notation "ρ1 ⇔ ρ2" := (equiv (A:=perm) ρ1%P ρ2%P)
   (at level 95, no associativity) : C_scope.
Notation "(⇔)" := (equiv (A:=perm)) (only parsing) : C_scope.

Section props.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Properties *)
  Global Instance perm_incl_preorder : PreOrder (⇒).
  Proof.
    split.
    - iIntros (? tid) "H". eauto.
    - iIntros (??? H12 H23 tid) "H". iMod (H12 with "H") as "H". by iApply H23.
  Qed.

  Global Instance perm_equiv_equiv : Equivalence (⇔).
  Proof.
    split.
    - by split.
    - by intros x y []; split.
    - intros x y z [] []. split; by transitivity y.
  Qed.

  Global Instance perm_incl_proper :
    Proper ((⇔) ==> (⇔) ==> iff) (⇒).
  Proof. intros ??[??]??[??]; split; intros ?; by simplify_order. Qed.

  Global Instance perm_sep_proper :
    Proper ((⇔) ==> (⇔) ==> (⇔)) (sep).
  Proof.
    intros ??[A B]??[C D]; split; iIntros (tid) "[A B]".
    iMod (A with "A") as "$". iApply (C with "B").
    iMod (B with "A") as "$". iApply (D with "B").
  Qed.

  Lemma uPred_equiv_perm_equiv ρ θ : (∀ tid, ρ tid ⊣⊢ θ tid) → (ρ ⇔ θ).
  Proof. intros Heq. split=>tid; rewrite Heq; by iIntros. Qed.

  Lemma perm_incl_top ρ : ρ ⇒ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 : ρ1 ⇒ ρ2 → ρ ∗ ρ1 ⇒ ρ ∗ ρ2.
  Proof. iIntros (Hρ tid) "[$?]". by iApply Hρ. Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    ρ1 ⇒ ρ2 → ρ1 ∗ ρ ⇒ ρ2 ∗ ρ.
  Proof. iIntros (Hρ tid) "[?$]". by iApply Hρ. Qed.

  Lemma perm_incl_exists_intro {A} P x : P x ⇒ ∃ x : A, P x.
  Proof. iIntros (tid) "H!>". by iExists x. Qed.

  Global Instance perm_sep_assoc : Assoc (⇔) sep.
  Proof. intros ???; split. by iIntros (tid) "[$[$$]]". by iIntros (tid) "[[$$]$]". Qed.

  Global Instance perm_sep_comm : Comm (⇔) sep.
  Proof. intros ??; split; by iIntros (tid) "[$$]". Qed.

  Global Instance perm_top_right_id : RightId (⇔) ⊤ sep.
  Proof. intros ρ; split. by iIntros (tid) "[? _]". by iIntros (tid) "$". Qed.

  Global Instance perm_top_left_id : LeftId (⇔) ⊤ sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

  Lemma perm_incl_duplicable ρ (_ : Duplicable ρ) : ρ ⇒ ρ ∗ ρ.
  Proof. iIntros (tid) "#H!>". by iSplit. Qed.

  Lemma perm_tok_plus κ q1 q2 :
    tok κ q1 ∗ tok κ q2 ⇔ tok κ (q1 + q2).
  Proof.
    rewrite /tok /sep /=; split; iIntros (tid) "?"; rewrite lft_own_frac_op //.
  Qed.

  Lemma perm_lftincl_refl κ : ⊤ ⇒ κ ⊑ κ.
  Proof. iIntros (tid) "_!>". iApply lft_incl_refl. Qed.

  Lemma perm_lftincl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 ∗ κ2 ⊑ κ3 ⇒ κ1 ⊑ κ3.
  Proof. iIntros (tid) "[#?#?]!>". iApply lft_incl_trans. auto. Qed.

  Lemma perm_incl_share q ν κ ty :
    ν ◁ &uniq{κ} ty ∗ q.[κ] ⇒ ν ◁ &shr{κ} ty ∗ q.[κ].
  Proof.
    iIntros (tid) "[Huniq [Htok $]]". unfold has_type.
    destruct (eval_expr ν); last by iDestruct "Huniq" as "[]".
    iDestruct "Huniq" as (l) "[% Hown]".
    iMod (ty.(ty_share) _ lrustN with "Hown Htok") as "[Hown $]".
    apply disjoint_union_l; solve_ndisj. done. iModIntro.
    simpl. eauto.
  Qed.

  Lemma split_own_prod tyl (q0: Qp) (ql : list Qp) (l : loc) tid :
    length tyl = length ql →
      (own (foldr Qp_plus q0 ql) (Π tyl)).(ty_own) tid [ #l] ⊣⊢
    ▷ †{q0}(shift_loc l (0 + (Π tyl).(ty_size))%nat)…0 ∗
    [∗ list] qtyoffs ∈ (combine ql (combine_offs tyl 0)),
         (own (qtyoffs.1) (qtyoffs.2.1)).(ty_own)
              tid [ #(shift_loc l (qtyoffs.2.2))].
  Proof.
    intros Hlen.
    assert (REW: ∀ (l : loc) (Φ : loc → iProp Σ),
               Φ l ⊣⊢ (∃ l0:loc, [ #l] = [ #l0] ∗ Φ l0)).
    { intros l0 Φ. iSplit; iIntros "H". eauto.
      iDestruct "H" as (l') "[Heq H]". iDestruct "Heq" as %[=]. subst. done. }
    setoid_rewrite <-REW. clear REW.
    rewrite big_sepL_sepL assoc split_prod_mt big_sepL_later. apply uPred.sep_proper.
    - rewrite -{1}(shift_loc_0_nat l). generalize 0%nat at -3. revert ql Hlen.
      induction tyl as [|ty tyl IH]; intros [|q ql] [=] offs.
      + by rewrite big_sepL_nil !right_id.
      + rewrite -heap_freeable_op_eq uPred.later_sep shift_loc_assoc_nat IH //
                Nat.add_assoc big_sepL_cons.
        iSplit; by iIntros "($&$&$)".
    - generalize 0%nat. revert ql Hlen.
      induction tyl as [|ty tyl IH]; intros [|q ql] [=] offs. done.
      rewrite !big_sepL_cons IH //.
  Qed.

  Lemma perm_split_own_prod tyl (q : Qp) (ql : list Qp) ν :
    length tyl = length ql →
    foldr (λ (q : Qp) acc, q + acc)%Qc 0%Qc ql = q →
    ν ◁ own q (Π tyl) ⇔
      foldr (λ qtyoffs acc,
             (ν +ₗ #(qtyoffs.2.2:nat))%E ◁ own (qtyoffs.1) (qtyoffs.2.1) ∗ acc)
            ⊤ (combine ql (combine_offs tyl 0)).
  Proof.
    intros Hlen Hq. assert (ql ≠ []).
    { destruct ql as [|q0 ql]; last done. destruct q. simpl in *. by subst. }
    unfold has_type. simpl eval_expr. destruct (eval_expr ν) as [[[|l|]|]|];
      try by (destruct tyl as [|ty0 tyl], ql as [|q0 ql]; try done;
        by split; iIntros (tid) "H"; try done;
          [iDestruct "H" as (l) "[% _]" || iDestruct "H" as "[]" |
           iDestruct "H" as "[[]_]"]).
    destruct (@exists_last _ ql) as (ql'&q0&->); first done.
    apply uPred_equiv_perm_equiv=>tid.
    assert (foldr Qp_plus (q0/2) (ql' ++ [q0/2]) = q)%Qp as <-.
    { destruct q as [q ?]. apply Qp_eq. simpl in *. subst. clear. induction ql'.
      by rewrite /fold_right /app Qp_div_2 Qcplus_0_r. by rewrite /= IHql'. }
    rewrite /has_type /from_option split_own_prod ?Hlen ?app_length //.
    clear -Hlen. revert ql' Hlen. generalize 0%nat at -2.
    induction tyl as [|ty tyl IH]; destruct ql' as [|q ql']; intros [= Hlen]; try done.
    - destruct tyl; last done. clear IH Hlen.
      rewrite big_sepL_singleton /= /sep !right_id comm uPred.sep_exist_r.
      apply uPred.exist_proper=>l0.
      rewrite -{3}(Qp_div_2 q0) -{3}(right_id O plus ty.(ty_size))
              -heap_freeable_op_eq uPred.later_sep -!assoc.
      iSplit; iIntros "[#Eq[?[??]]]"; iFrame "# ∗";
        iDestruct "Eq" as %[=]; subst; rewrite shift_loc_assoc_nat //.
    - rewrite /= big_sepL_cons /sep -IH // !uPred.sep_exist_r uPred.sep_exist_l.
      apply uPred.exist_proper=>l0. rewrite -!assoc /=.
      by iSplit; iIntros "[$[$[$[$$]]]]".
  Qed.

  Lemma perm_split_uniq_borrow_prod tyl κ ν :
    ν ◁ &uniq{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             (ν +ₗ #(tyoffs.2:nat))%E ◁ &uniq{κ} (tyoffs.1) ∗ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    intros tid. unfold has_type. simpl eval_expr.
    destruct (eval_expr ν) as [[[|l|]|]|];
      iIntros "H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "[EQ H]"; iDestruct "EQ" as %[=]. subst l0.
    rewrite split_prod_mt.
    iInduction (combine_offs tyl 0) as [|[ty offs] ll] "IH". by auto.
    rewrite big_sepL_cons /=.
    iMod (borrow_split with "H") as "[H0 H]". set_solver.
    iMod ("IH" with "H") as "$". iModIntro. iExists _. eauto.
  Qed.

  Lemma perm_split_shr_borrow_prod tyl κ ν :
    ν ◁ &shr{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             (ν +ₗ #(tyoffs.2:nat))%E ◁ &shr{κ} (tyoffs.1) ∗ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    intros tid. unfold has_type. simpl eval_expr.
    destruct (eval_expr ν) as [[[|l|]|]|];
      iIntros "H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "[EQ H]"; iDestruct "EQ" as %[=]. subst l0.
    simpl. iModIntro.
    change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat).
    generalize O at 2; intro i.
    iInduction (combine_offs tyl 0) as [|[ty offs] ll] "IH" forall (i). by auto.
    rewrite big_sepL_cons /=. iDestruct "H" as "[H0 H]".
    setoid_rewrite <-Nat.add_succ_comm. iDestruct ("IH" $! (S i) with "H") as "$".
    iExists _. iSplit. done. admit.
    (* FIXME : namespaces problem. *)
  Admitted.

  Lemma borrowing_perm_incl κ ρ ρ1 ρ2 θ :
    borrowing κ ρ ρ1 ρ2 → ρ ∗ κ ∋ θ ∗ ρ1 ⇒ ρ2 ∗ κ ∋ (θ ∗ ρ1).
  Proof.
    iIntros (Hbor tid) "(Hρ&Hθ&Hρ1)". iMod (Hbor with "Hρ Hρ1") as "[$ Hρ1]".
    iIntros "!>#H†". iSplitL "Hθ". by iApply "Hθ". by iApply "Hρ1".
  Qed.

  Lemma own_uniq_borrowing ν q ty κ :
    borrowing κ ⊤ (ν ◁ own q ty) (ν ◁ &uniq{κ} ty).
  Proof.
    iIntros (tid) "_ Hown". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "Hown" as "[]" || iDestruct "Hown" as (l) "[% _]").
    iDestruct "Hown" as (l') "[EQ [Hf Hown]]". iDestruct "EQ" as %[=]. subst l'.
    iApply (fupd_mask_mono lftN). done.
    iMod (borrow_create with "Hown") as "[Hbor Hext]". done.
    iSplitL "Hbor". by simpl; eauto.
    iMod (borrow_create with "Hf") as "[_ Hf]". done.
    iIntros "!>#H†".
    iMod ("Hext" with "H†") as "Hext". iMod ("Hf" with "H†") as "Hf". iIntros "!>/=".
    iExists _. iFrame. auto.
  Qed.

  Lemma reborrow_uniq_borrowing κ κ' ν ty :
    borrowing κ (κ ⊑ κ') (ν ◁ &uniq{κ'}ty) (ν ◁ &uniq{κ}ty).
  Proof.
    iIntros (tid) "#Hord H". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "H" as "[]" || iDestruct "H" as (l) "[% _]").
    iDestruct "H" as (l') "[EQ H]". iDestruct "EQ" as %[=]. subst l'.
    iApply (fupd_mask_mono lftN). done.
    iMod (reborrow with "Hord H") as "[H Hextr]". done.
    iModIntro. iSplitL "H". iExists _. by eauto.
    iIntros "H†". iMod ("Hextr" with "H†"). simpl. auto.
  Qed.

  Lemma reborrow_shr_perm_incl κ κ' ν ty :
    κ ⊑ κ' ∗ ν ◁ &shr{κ'}ty ⇒ ν ◁ &shr{κ}ty.
  Proof.
    iIntros (tid) "[#Hord #Hκ']". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "Hκ'" as "[]" || iDestruct "Hκ'" as (l) "[% _]").
    iDestruct "Hκ'" as (l') "[EQ Hκ']". iDestruct "EQ" as %[=]. subst l'.
    iModIntro. iExists _. iSplit. done.
    by iApply (ty_shr_mono with "Hord Hκ'").
  Qed.

  (* TODO *)
  (* Lemma lftincl_borrowing κ κ' q : borrowing κ ⊤ q.[κ'] (κ ⊑ κ'). *)
  (* Proof. *)
  (*   iIntros (tid) "_ Htok". iApply fupd_mask_mono. done. *)
  (*   iDestruct "Htok" as "[Htok1 Htok2]". *)
  (*   iMod (borrow_create with "[Htok1]") as "[Hbor Hclose]". reflexivity. *)
  (*   { iIntros "!>". iExact "Htok1". } *)
  (*   iMod (borrow_fracture (λ q', (q / 2 * q').[κ'])%I with "[Hbor $Htok2]") *)
  (*     as "[Hbor Htok]". done. *)
  (*   { by rewrite Qp_mult_1_r. } *)
  (*   iIntros "{$Htok}!>". iSplitL "Hbor". *)
  (*   iApply frac_borrow_incl. done. frac_borrow_incl *)

  (*     iExact "Hclose". iFrame. *)

  (*   iMod (frac_borrow_incl with "[-]"). *)
  (*   iMod (lft_mkincl' with "[#] Htok") as "[$ H]". done. by iFrame "#". *)
  (*   iMod (lft_borrow_create with "Hκ []") as "[_ H']". done. by iNext; iApply "Hκ'". *)
  (*   iApply lft_extract_combine. done. by iFrame. *)
  (* Qed. *)

End props.
