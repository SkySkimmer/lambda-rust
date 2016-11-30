From Coq Require Import Qcanon.
From iris.base_logic Require Import big_op.
From lrust.typing Require Export type perm.
From lrust.lifetime Require Import borrow frac_borrow reborrow.

Import Perm Types.

Section defs.

  Context `{iris_typeG Σ}.

  (* Definitions *)
  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, lft_ctx -∗ ρ1 tid ={⊤}=∗ ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Definition borrowing κ (ρ ρ1 ρ2 : perm) :=
    ∀ tid, lft_ctx -∗ ρ tid -∗ ρ1 tid ={⊤}=∗ ρ2 tid ∗ (κ ∋ ρ1)%P tid.

End defs.

Infix "⇒" := perm_incl (at level 95, no associativity) : C_scope.
Notation "(⇒)" := perm_incl (only parsing) : C_scope.

Notation "ρ1 ⇔ ρ2" := (equiv (A:=perm) ρ1%P ρ2%P)
   (at level 95, no associativity) : C_scope.
Notation "(⇔)" := (equiv (A:=perm)) (only parsing) : C_scope.

Section props.

  Context `{iris_typeG Σ}.

  (* Properties *)
  Global Instance perm_incl_preorder : PreOrder (⇒).
  Proof.
    split.
    - iIntros (? tid) "H". eauto.
    - iIntros (??? H12 H23 tid) "#LFT H". iApply (H23 with "LFT >").
      by iApply (H12 with "LFT").
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
    intros ??[A B]??[C D]; split; iIntros (tid) "#LFT [A B]".
    iMod (A with "LFT A") as "$". iApply (C with "LFT B").
    iMod (B with "LFT A") as "$". iApply (D with "LFT B").
  Qed.

  Lemma uPred_equiv_perm_equiv ρ θ : (∀ tid, ρ tid ⊣⊢ θ tid) → (ρ ⇔ θ).
  Proof. intros Heq. split=>tid; rewrite Heq; by iIntros. Qed.

  Lemma perm_incl_top ρ : ρ ⇒ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 : ρ1 ⇒ ρ2 → ρ ∗ ρ1 ⇒ ρ ∗ ρ2.
  Proof. iIntros (Hρ tid) "#LFT [$?]". by iApply (Hρ with "LFT"). Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    ρ1 ⇒ ρ2 → ρ1 ∗ ρ ⇒ ρ2 ∗ ρ.
  Proof. iIntros (Hρ tid) "#LFT [?$]". by iApply (Hρ with "LFT"). Qed.

  Lemma perm_incl_exists_intro {A} P x : P x ⇒ ∃ x : A, P x.
  Proof. iIntros (tid) "_ H!>". by iExists x. Qed.

  Global Instance perm_sep_assoc : Assoc (⇔) sep.
  Proof. intros ???; split. by iIntros (tid) "_ [$[$$]]". by iIntros (tid) "_ [[$$]$]". Qed.

  Global Instance perm_sep_comm : Comm (⇔) sep.
  Proof. intros ??; split; by iIntros (tid) "_ [$$]". Qed.

  Global Instance perm_top_right_id : RightId (⇔) ⊤ sep.
  Proof. intros ρ; split. by iIntros (tid) "_ [? _]". by iIntros (tid) "_ $". Qed.

  Global Instance perm_top_left_id : LeftId (⇔) ⊤ sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

  Lemma perm_incl_duplicable ρ (_ : Duplicable ρ) : ρ ⇒ ρ ∗ ρ.
  Proof. iIntros (tid) "_ #H!>". by iSplit. Qed.

  Lemma perm_tok_plus κ q1 q2 :
    tok κ q1 ∗ tok κ q2 ⇔ tok κ (q1 + q2).
  Proof. rewrite /tok /sep /=; split; by iIntros (tid) "_ [$$]". Qed.

  Lemma perm_lftincl_refl κ : ⊤ ⇒ κ ⊑ κ.
  Proof. iIntros (tid) "_ _!>". iApply lft_incl_refl. Qed.

  Lemma perm_lftincl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 ∗ κ2 ⊑ κ3 ⇒ κ1 ⊑ κ3.
  Proof. iIntros (tid) "_ [#?#?]!>". iApply (lft_incl_trans with "[] []"); auto. Qed.

  Lemma perm_incl_share q ν κ ty :
    ν ◁ &uniq{κ} ty ∗ q.[κ] ⇒ ν ◁ &shr{κ} ty ∗ q.[κ].
  Proof.
    iIntros (tid) "#LFT [Huniq [Htok $]]". unfold has_type.
    destruct (eval_expr ν); last by iDestruct "Huniq" as "[]".
    iDestruct "Huniq" as (l) "[% Hown]".
    iMod (ty.(ty_share) _ lrustN with "LFT Hown Htok") as "[Hown $]".
    apply disjoint_union_l; solve_ndisj. done. iIntros "!>/=". eauto.
  Qed.

  Lemma perm_split_own_prod2 ty1 ty2 (q1 q2 : Qp) ν :
    ν ◁ own (q1 + q2) (product2 ty1 ty2) ⇔
      ν ◁ own q1 ty1 ∗ ν +ₗ #ty1.(ty_size) ◁ own q2 ty2.
  Proof.
    rewrite /has_type /own /sep /=.
    destruct (eval_expr ν) as [[[]|?]|]; last first; split; iIntros (tid) "_ H/=";
      (try by iDestruct "H" as "[_ []]"); (try by iDestruct "H" as (l) "[% _]").
    { by auto. }
    - iDestruct "H" as (l') "(EQ & H & H†)". iDestruct "EQ" as %[=<-].
      iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(>% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app -heap_freeable_op_eq.
      iDestruct "H†" as "[H†1 H†2]". iDestruct "H↦" as "[H↦1 H↦2]".
      iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
      { iNext. by iApply ty_size_eq. }
      iDestruct "EQ" as %->. iSplitL "H↦1 H†1 H1".
      + iExists _. iSplitR. done. iFrame. iExists _. by iFrame.
      + iExists _. iSplitR. done. iFrame. iExists _. by iFrame.
    - iDestruct "H" as "[H1 H2]".
      iDestruct "H1" as (l') "(EQ & H↦1 & H†1)". iDestruct "EQ" as %[=<-].
      iDestruct "H2" as (l') "(EQ & H↦2 & H†2)". iDestruct "EQ" as %[=<-].
      iExists l. iSplitR. done. rewrite -heap_freeable_op_eq. iFrame.
      iDestruct "H↦1" as (vl1) "[H↦1 H1]". iDestruct "H↦2" as (vl2) "[H↦2 H2]".
      iExists (vl1 ++ vl2). rewrite heap_mapsto_vec_app. iFrame.
      iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
      { iNext. by iApply ty_size_eq. }
      iDestruct "EQ" as %->. iFrame. iExists vl1, vl2. iFrame. auto.
  Qed.

  Fixpoint combine_offs (tyl : list type) (accu : nat) :=
    match tyl with
    | [] => []
    | ty :: q => (ty, accu) :: combine_offs q (accu + ty.(ty_size))
    end.

  Lemma perm_split_own_prod tyl (q : Qp) (ql : list Qp) ν :
    length tyl = length ql →
    foldr (λ (q : Qp) acc, q + acc)%Qc 0%Qc ql = q →
    ν ◁ own q (Π tyl) ⇔
      foldr (λ qtyoffs acc,
             ν +ₗ #(qtyoffs.2.2:nat) ◁ own (qtyoffs.1) (qtyoffs.2.1) ∗ acc)
            ⊤ (combine ql (combine_offs tyl 0)).
  Proof.
    revert q tyl ν. induction ql as [|q0 [|q1 ql] IH]=>q tyl ν Hlen Hq.
    { destruct q. intros. simpl in *. by subst. }
    - destruct tyl as [|ty0 [|ty1 tyl]]; try done. simpl in *.
      assert (q0 = q) as ->. { apply Qp_eq. by rewrite -Hq Qcplus_0_r. }
      rewrite /has_type /sep /=.
      destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
        (try by iDestruct "H" as "[[] _]"); (try by iDestruct "H" as (l) "[% _]");
        (try by auto); rewrite (shift_loc_0 l) Nat.add_0_r.
      + iSplitL; last done. iExists _. iSplitR. done.
        iDestruct "H" as (l') "[Heq [H↦ H†]]". iDestruct "Heq" as %[=<-].
        iDestruct "H↦" as (vl) "[H↦ H]".
        iDestruct "H" as (vl1 vl2) "(>% & Hown & >%)". subst.
        rewrite app_nil_r. iFrame. iExists _. by iFrame.
      + iExists l. iSplitR. done.
        iDestruct "H" as "[H _]". iDestruct "H" as (l') "[Heq [H↦ H†]]".
        iDestruct "Heq" as %[=<-]. iFrame. iDestruct "H↦" as (vl) "[H↦ Hown]".
        iExists vl. iFrame. iExists vl, []. iFrame. rewrite app_nil_r. auto.
    - destruct tyl as [|ty0 tyl]. done.
      assert (Hpos : (0 < foldr (λ (q : Qp) acc, (q + acc)%Qc) 0%Qc (q1 :: ql))%Qc).
      { apply Qcplus_pos_nonneg. apply Qp_prf. clear. induction ql. done.
        apply Qcplus_nonneg_nonneg. apply Qclt_le_weak, Qp_prf. done. }
      assert (q = q0 + mk_Qp _ Hpos)%Qp as ->. by by apply Qp_eq; rewrite -Hq.
      injection Hlen; intro Hlen'. rewrite perm_split_own_prod2 IH //.
      apply perm_sep_proper.
      + rewrite /has_type /sep /=.
        destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
        (try by iDestruct "H" as "[]"); (try by iDestruct "H" as (l) "[% _]");
        (try by auto); by rewrite shift_loc_0.
      + cut (length tyl = length (q1 :: ql)); last done. clear. revert tyl.
        generalize 0%nat. induction (q1 :: ql)=>offs -[|ty tyl] Hlen //.
        apply perm_sep_proper.
        * rewrite /has_type /sep /=.
          destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
          (try by iDestruct "H" as "[]"); (try by iDestruct "H" as (l) "[% _]");
          (try by auto); by rewrite shift_loc_assoc_nat (comm plus).
        * etransitivity. apply IHl. by injection Hlen. do 3 f_equiv. lia.
  Qed.

  Lemma perm_split_uniq_bor_prod2 ty1 ty2 κ ν :
    ν ◁ &uniq{κ} (product2 ty1 ty2) ⇒
    ν ◁ &uniq{κ} ty1 ∗ ν +ₗ #(ty1.(ty_size)) ◁ &uniq{κ} ty2.
  Proof.
    rewrite /has_type /sep /product2 /=.
    destruct (eval_expr ν) as [[[|l|]|]|];
      iIntros (tid) "#LFT H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "[EQ H]"; iDestruct "EQ" as %[=<-].
    rewrite /= split_prod_mt. iMod (bor_sep with "LFT H") as "[H1 H2]".
    set_solver. iSplitL "H1"; eauto.
  Qed.

  Lemma perm_split_uniq_bor_prod tyl κ ν :
    ν ◁ &uniq{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             ν +ₗ #(tyoffs.2:nat) ◁ &uniq{κ} (tyoffs.1) ∗ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    transitivity (ν +ₗ #0%nat ◁ &uniq{κ}Π tyl)%P.
    { iIntros (tid) "_ H/=". rewrite /has_type /=. destruct (eval_expr ν)=>//.
      iDestruct "H" as (l) "[Heq H]". iDestruct "Heq" as %[=->].
      rewrite shift_loc_0 /=. eauto. }
    generalize 0%nat. induction tyl as [|ty tyl IH]=>offs. by iIntros (tid) "_ H/=".
    etransitivity. apply perm_split_uniq_bor_prod2.
    iIntros (tid) "#LFT /=[$ H]". iApply (IH with "LFT"). rewrite /has_type /=.
    destruct (eval_expr ν) as [[[]|]|]=>//=. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma perm_split_shr_bor_prod2 ty1 ty2 κ ν :
    ν ◁ &shr{κ} (product2 ty1 ty2) ⇒
    ν ◁ &shr{κ} ty1 ∗ ν +ₗ #(ty1.(ty_size)) ◁ &shr{κ} ty2.
  Proof.
    rewrite /has_type /sep /product2 /=.
    destruct (eval_expr ν) as [[[|l|]|]|];
      iIntros (tid) "#LFT H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0) "(EQ & H)"; iDestruct "EQ" as %[=<-].
    iDestruct "H" as (E1 E2) "(% & H1 & H2)".
    iSplitL "H1"; iExists _; (iSplitR; [done|]); iApply (ty_shr_mono with "LFT []");
      try by iFrame.
    set_solver. iApply lft_incl_refl. set_solver. iApply lft_incl_refl.
  Qed.

  Lemma perm_split_shr_bor_prod tyl κ ν :
    ν ◁ &shr{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             (ν +ₗ #(tyoffs.2:nat))%E ◁ &shr{κ} (tyoffs.1) ∗ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    transitivity (ν +ₗ #0%nat ◁ &shr{κ}Π tyl)%P.
    { iIntros (tid) "#LFT H/=". rewrite /has_type /=. destruct (eval_expr ν)=>//.
      iDestruct "H" as (l) "[Heq H]". iDestruct "Heq" as %[=->].
      rewrite shift_loc_0 /=. iExists _. by iFrame "∗%". }
    generalize 0%nat. induction tyl as [|ty tyl IH]=>offs. by iIntros (tid) "_ H/=".
    etransitivity. apply perm_split_shr_bor_prod2.
    iIntros (tid) "#LFT /=[$ H]". iApply (IH with "LFT"). rewrite /has_type /=.
    destruct (eval_expr ν) as [[[]|]|]=>//=. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma rebor_shr_perm_incl κ κ' ν ty :
    κ ⊑ κ' ∗ ν ◁ &shr{κ'}ty ⇒ ν ◁ &shr{κ}ty.
  Proof.
    iIntros (tid) "#LFT [#Hord #Hκ']". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "Hκ'" as "[]" || iDestruct "Hκ'" as (l) "[% _]").
    iDestruct "Hκ'" as (l') "[EQ Hκ']". iDestruct "EQ" as %[=]. subst l'.
    iModIntro. iExists _. iSplit. done. by iApply (ty_shr_mono with "LFT Hord Hκ'").
  Qed.

  Lemma borrowing_perm_incl κ ρ ρ1 ρ2 θ :
    borrowing κ ρ ρ1 ρ2 → ρ ∗ κ ∋ θ ∗ ρ1 ⇒ ρ2 ∗ κ ∋ (θ ∗ ρ1).
  Proof.
    iIntros (Hbor tid) "LFT (Hρ&Hθ&Hρ1)". iMod (Hbor with "LFT Hρ Hρ1") as "[$ Hρ1]".
    iIntros "!>#H†". iSplitL "Hθ". by iApply "Hθ". by iApply "Hρ1".
  Qed.

  Lemma own_uniq_borrowing ν q ty κ :
    borrowing κ ⊤ (ν ◁ own q ty) (ν ◁ &uniq{κ} ty).
  Proof.
    iIntros (tid) "#LFT _ Hown". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "Hown" as "[]" || iDestruct "Hown" as (l) "[% _]").
    iDestruct "Hown" as (l') "[EQ [Hown Hf]]". iDestruct "EQ" as %[=]. subst l'.
    iApply (fupd_mask_mono (↑lftN)). done.
    iMod (bor_create with "LFT Hown") as "[Hbor Hext]". done.
    iSplitL "Hbor". by simpl; eauto.
    iIntros "!>#H†". iExists _. iMod ("Hext" with "H†") as "$". by iFrame.
  Qed.

  Lemma rebor_uniq_borrowing κ κ' ν ty :
    borrowing κ (κ ⊑ κ') (ν ◁ &uniq{κ'}ty) (ν ◁ &uniq{κ}ty).
  Proof.
    iIntros (tid) "#LFT #Hord H". unfold has_type.
    destruct (eval_expr ν) as [[[|l|]|]|];
      try by (iDestruct "H" as "[]" || iDestruct "H" as (l) "[% _]").
    iDestruct "H" as (l') "[EQ H]". iDestruct "EQ" as %[=]. subst l'.
    iApply (fupd_mask_mono (↑lftN)). done.
    iMod (rebor with "LFT Hord H") as "[H Hextr]". done.
    iModIntro. iSplitL "H". iExists _. by eauto.
    iIntros "H†". iExists _. by iMod ("Hextr" with "H†") as "$".
  Qed.

  Lemma lftincl_borrowing κ κ' q : borrowing κ ⊤ q.[κ'] (κ ⊑ κ').
  Proof.
    iIntros (tid) "#LFT _ Htok". iApply (fupd_mask_mono (↑lftN)). done.
    iMod (bor_create with "LFT [$Htok]") as "[Hbor Hclose]". done.
    iMod (bor_fracture (λ q', (q * q').[κ'])%I with "LFT [Hbor]") as "Hbor". done.
    { by rewrite Qp_mult_1_r. }
    iSplitL "Hbor". iApply (frac_bor_incl with "LFT Hbor").
    iIntros "!>H". by iMod ("Hclose" with "H") as ">$".
  Qed.

End props.
