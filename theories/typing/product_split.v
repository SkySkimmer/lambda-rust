From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl typing product own uniq_bor shr_bor.

Section product_split.
  Context `{iris_typeG Σ}.

  Fixpoint combine_offs (tyl : list type) (accu : nat) :=
    match tyl with
    | [] => []
    | ty :: q => (ty, accu) :: combine_offs q (accu + ty.(ty_size))
    end.

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
      set (q1l := q1::ql). cbn[combine_offs combine foldr]. apply perm_sep_proper.
      + rewrite /has_type /sep /=.
        destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
        (try by iDestruct "H" as "[]"); (try by iDestruct "H" as (l) "[% _]");
        (try by auto); by rewrite shift_loc_0.
      + cut (length tyl = length (q1 :: ql)); last done. clear. revert tyl.
        generalize 0%nat. induction (q1 :: ql)=>offs -[|ty tyl] Hlen //=.
        apply perm_sep_proper.
        * rewrite /has_type /sep /=.
          destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
          (try by iDestruct "H" as "[]"); [|]; by rewrite shift_loc_assoc_nat (comm plus).
        * etrans. apply IHl. by injection Hlen. do 3 f_equiv. lia.
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
    { iIntros (tid) "_ H/=". rewrite /has_type /=.
      destruct (eval_expr ν)=>//.
      iDestruct "H" as (l) "[Heq H]". iDestruct "Heq" as %[=->].
      rewrite shift_loc_0 /=. eauto. }
    generalize 0%nat. induction tyl as [|ty tyl IH]=>offs. by iIntros (tid) "_ H/=".
    etransitivity. apply perm_split_uniq_bor_prod2.
    iIntros (tid) "#LFT /=[$ H]". iApply (IH with "LFT").
    rewrite /has_type /=. destruct (eval_expr ν) as [[[]|]|]=>//=.
    by rewrite shift_loc_assoc_nat.
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
    { iIntros (tid) "#LFT H/=". rewrite /has_type /=.
      destruct (eval_expr ν)=>//.
      iDestruct "H" as (l) "[Heq H]". iDestruct "Heq" as %[=->].
      rewrite shift_loc_0 /=. iExists _. by iFrame "∗%". }
    generalize 0%nat. induction tyl as [|ty tyl IH]=>offs. by iIntros (tid) "_ H/=".
    etransitivity. apply perm_split_shr_bor_prod2.
    iIntros (tid) "#LFT /=[$ H]". iApply (IH with "LFT"). rewrite /has_type /=.
    destruct (eval_expr ν) as [[[]|]|]=>//=. by rewrite shift_loc_assoc_nat.
  Qed.
End product_split.
