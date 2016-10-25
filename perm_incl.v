From Coq Require Import Qcanon.
From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm.

Import Perm Types.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Definitions *)
  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, ρ1 tid ={⊤}=> ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Definition borrowing κ (ρ ρ1 ρ2 : perm) :=
    ∀ tid, lft κ ⊢ ρ tid -★ ρ1 tid ={⊤}=★ ρ2 tid ★ κ ∋ ρ1 tid.

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
    - iIntros (??? H12 H23 tid) "H". iVs (H12 with "H") as "H". by iApply H23.
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
    iVs (A with "A") as "$". iApply (C with "B").
    iVs (B with "A") as "$". iApply (D with "B").
  Qed.

  Lemma uPred_equiv_perm_equiv ρ θ : (∀ tid, ρ tid ⊣⊢ θ tid) → (ρ ⇔ θ).
  Proof. intros Heq. split=>tid; rewrite Heq; by iIntros. Qed.

  Lemma perm_incl_top ρ : ρ ⇒ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 : ρ1 ⇒ ρ2 → ρ ★ ρ1 ⇒ ρ ★ ρ2.
  Proof. iIntros (Hρ tid) "[$?]". by iApply Hρ. Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    ρ1 ⇒ ρ2 → ρ1 ★ ρ ⇒ ρ2 ★ ρ.
  Proof. iIntros (Hρ tid) "[?$]". by iApply Hρ. Qed.

  Lemma perm_incl_exists_intro {A} P x : P x ⇒ ∃ x : A, P x.
  Proof. iIntros (tid) "H!==>". by iExists x. Qed.

  Global Instance perm_sep_assoc : Assoc (⇔) sep.
  Proof. intros ???; split. by iIntros (tid) "[$[$$]]". by iIntros (tid) "[[$$]$]". Qed.

  Global Instance perm_sep_comm : Comm (⇔) sep.
  Proof. intros ??; split; by iIntros (tid) "[$$]". Qed.

  Global Instance perm_top_right_id : RightId (⇔) ⊤ sep.
  Proof. intros ρ; split. by iIntros (tid) "[? _]". by iIntros (tid) "$". Qed.

  Global Instance perm_top_left_id : LeftId (⇔) ⊤ sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

  Lemma perm_incl_duplicable ρ (_ : Duplicable ρ) : ρ ⇒ ρ ★ ρ.
  Proof. iIntros (tid) "#H!==>". by iSplit. Qed.

  Lemma perm_tok_plus κ q1 q2 :
    tok κ q1 ★ tok κ q2 ⇔ tok κ (q1 + q2).
  Proof.
    rewrite /tok /sep /=; split; intros tid; rewrite -lft_own_op;
      iIntros "[[$$]H]!==>". by iDestruct "H" as "[$?]". by auto.
  Qed.

  Lemma perm_lftincl_refl κ : ⊤ ⇒ κ ⊑ κ.
  Proof. iIntros (tid) "_!==>". iApply lft_incl_refl. Qed.

  Lemma perm_lftincl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 ★ κ2 ⊑ κ3 ⇒ κ1 ⊑ κ3.
  Proof. iIntros (tid) "[#?#?]!==>". iApply lft_incl_trans. auto. Qed.

  Lemma perm_incl_share q v κ ty :
    v ◁ &uniq{κ} ty ★ [κ]{q} ⇒ v ◁ &shr{κ} ty ★ [κ]{q}.
  Proof.
    iIntros (tid) "[Huniq [Htok Hlft]]". destruct v; last by iDestruct "Huniq" as "[]".
    iDestruct "Huniq" as (l) "[% Hown]".
    iVs (ty.(ty_share) _ lrustN with "Hown Htok") as "[Hown Htok]".
    apply disjoint_union_l; solve_ndisj. set_solver. iVsIntro.
    iFrame. iExists _. iSplit. done. done.
  Qed.

  Lemma split_own_prod tyl (q0: Qp) (ql : list Qp) (l : loc) tid :
    length tyl = length ql →
      (own (foldr Qp_plus q0 ql) (Π tyl)).(ty_own) tid [ #l] ⊣⊢
    ▷ †{q0}(shift_loc l (0 + (Π tyl).(ty_size))%nat)…0 ★
    [★ list] qtyoffs ∈ (combine ql (combine_offs tyl 0)),
         (own (qtyoffs.1) (qtyoffs.2.1)).(ty_own)
              tid [ #(shift_loc l (qtyoffs.2.2))].
  Proof.
    intros Hlen.
    assert (REW: ∀ (l : loc) (Φ : loc → iProp Σ),
               Φ l ⊣⊢ (∃ l0:loc, [ #l] = [ #l0] ★ Φ l0)).
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

  Lemma perm_split_own_prod tyl (q : Qp) (ql : list Qp) v :
    length tyl = length ql →
    foldr (λ (q : Qp) acc, q + acc)%Qc 0%Qc ql = q →
    v ◁ own q (Π tyl) ⇔
      foldr (λ qtyoffs acc,
             proj_valuable (Z.of_nat (qtyoffs.2.2)) v ◁
                           own (qtyoffs.1) (qtyoffs.2.1) ★ acc)
            ⊤ (combine ql (combine_offs tyl 0)).
  Proof.
    intros Hlen Hq. assert (ql ≠ []).
    { destruct ql as [|q0 ql]; last done. destruct q. simpl in *. by subst. }
    destruct v as [[[|l|]|]|];
      try by (destruct tyl as [|ty0 tyl], ql as [|q0 ql]; try done;
        by split; iIntros (tid) "H"; try done;
          [iDestruct "H" as (l) "[% _]" || iDestruct "H" as "[]" |
           iDestruct "H" as "[[]_]"]).
    destruct (@exists_last _ ql) as (ql'&q0&->). done.
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
      iSplit; iIntros "[#Eq[?[??]]]"; iFrame "# ★";
        iDestruct "Eq" as %[=]; subst; rewrite shift_loc_assoc_nat //.
    - rewrite /= big_sepL_cons /sep -IH // !uPred.sep_exist_r uPred.sep_exist_l.
      apply uPred.exist_proper=>l0. rewrite -!assoc /=.
      by iSplit; iIntros "[$[$[$[$$]]]]".
  Qed.

  Lemma perm_split_uniq_borrow_prod tyl κ v :
    v ◁ &uniq{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             proj_valuable (Z.of_nat (tyoffs.2)) v ◁ &uniq{κ} (tyoffs.1) ★ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    intros tid.
    destruct v as [[[|l|]|]|];
      iIntros "H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "[EQ H]"; iDestruct "EQ" as %[=]. subst l0.
    rewrite split_prod_mt.
    iInduction (combine_offs tyl 0) as [|[ty offs] ll] "IH". by auto.
    rewrite big_sepL_cons /=.
    iVs (lft_borrow_split with "H") as "[H0 H]". set_solver.
    iVs ("IH" with "H") as "$". iVsIntro. iExists _. eauto.
  Qed.

  Lemma perm_split_shr_borrow_prod tyl κ v :
    v ◁ &shr{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             proj_valuable (Z.of_nat (tyoffs.2)) v ◁ &shr{κ} (tyoffs.1) ★ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    intros tid.
    destruct v as [[[|l|]|]|];
      iIntros "H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "[EQ H]"; iDestruct "EQ" as %[=]. subst l0.
    simpl. iVsIntro.
    change (ndot (A:=nat)) with (λ N i, N .@ (0+i)%nat).
    generalize O at 2; intro i.
    iInduction (combine_offs tyl 0) as [|[ty offs] ll] "IH" forall (i). by auto.
    rewrite big_sepL_cons /=. iDestruct "H" as "[H0 H]".
    setoid_rewrite <-Nat.add_succ_comm. iDestruct ("IH" $! (S i) with "H") as "$".
    iExists _. iSplit. done. admit.
    (* FIXME : namespaces problem. *)
  Admitted.

  Lemma borrowing_perm_incl κ ρ ρ1 ρ2 θ :
    borrowing κ ρ ρ1 ρ2 → ρ ★ κ ∋ θ ★ ρ1 ⇒ ρ2 ★ κ ∋ (θ ★ ρ1).
  Proof.
    iIntros (Hbor tid) "(Hρ&Hθ&Hρ1)".
    iVs (Hbor with "[#] Hρ Hρ1") as "[$ ?]". by iApply lft_extract_lft.
    iApply lft_extract_combine. set_solver. by iFrame.
  Qed.

  Lemma own_uniq_borrowing v q ty κ :
    borrowing κ ⊤ (v ◁ own q ty) (v ◁ &uniq{κ} ty).
  Proof.
    iIntros (tid) "#Hκ _ Hown".
    destruct v as [[[|l|]|]|];
      try by (iDestruct "Hown" as "[]" || iDestruct "Hown" as (l) "[% _]").
    iDestruct "Hown" as (l') "[EQ [Hf Hown]]". iDestruct "EQ" as %[=]. subst l'.
    iVs (lft_borrow_create with "Hκ Hown") as "[Hbor Hextract]". done.
    iSplitL "Hbor". by simpl; eauto.
    iVs (lft_borrow_create with "Hκ Hf") as "[_ Hf]". done.
    iVs (lft_extract_combine with "[-]"). done. by iFrame.
    iVsIntro. iApply lft_extract_mono; last done.
    iIntros "H/=". iExists _. iSplit. done. by iDestruct "H" as "[$$]".
  Qed.

  Lemma reborrow_uniq_borrowing κ κ' v ty :
    borrowing κ (κ ⊑ κ') (v ◁ &uniq{κ'}ty) (v ◁ &uniq{κ}ty).
  Proof.
    iIntros (tid) "_ #Hord H".
    destruct v as [[[|l|]|]|];
      try by (iDestruct "H" as "[]" || iDestruct "H" as (l) "[% _]").
    iDestruct "H" as (l') "[EQ H]". iDestruct "EQ" as %[=]. subst l'.
    iVs (lft_reborrow with "Hord H") as "[H Hextr]". done.
    iVsIntro. iSplitL "H". iExists _. by eauto.
    iApply (lft_extract_proper with "Hextr").
    iSplit; iIntros "H/=".
    - iDestruct "H" as (l') "[EQ H]". iDestruct "EQ" as %[=]. by subst l'.
    - iExists _. eauto.
  Qed.

  Lemma reborrow_shr_perm_incl κ κ' v ty :
    κ ⊑ κ' ★ v ◁ &shr{κ'}ty ⇒ v ◁ &shr{κ}ty.
  Proof.
    iIntros (tid) "[#Hord #Hκ']".
    destruct v as [[[|l|]|]|];
      try by (iDestruct "Hκ'" as "[]" || iDestruct "Hκ'" as (l) "[% _]").
    iDestruct "Hκ'" as (l') "[EQ Hκ']". iDestruct "EQ" as %[=]. subst l'.
    iVsIntro. iExists _. iSplit. done.
    by iApply (ty_shr_mono with "Hord Hκ'").
  Qed.

  Lemma lftincl_borrowing κ κ' q : borrowing κ ⊤ [κ']{q} (κ ⊑ κ').
  Proof.
    iIntros (tid) "#Hκ #Hord [Htok #Hκ']".
    iVs (lft_mkincl' with "[#] Htok") as "[$ H]". done. by iFrame "#".
    iVs (lft_borrow_create with "Hκ []") as "[_ H']". done. by iNext; iApply "Hκ'".
    iApply lft_extract_combine. done. by iFrame.
  Qed.

End props.
