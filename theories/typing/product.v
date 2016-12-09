From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm type_incl.

Section product.
  Context `{iris_typeG Σ}.

  Program Definition unit : type :=
    {| st_size := 0; st_own tid vl := ⌜vl = []⌝%I |}.
  Next Obligation. iIntros (tid vl) "%". simpl. by subst. Qed.

  Lemma split_prod_mt tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl,
       ∃ vl1 vl2, ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) tid ∗ shift_loc l ty1.(ty_size) ↦∗{q}: ty2.(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]". iDestruct "H1" as (vl1) "[H↦1 H1]".
      iDestruct "H2" as (vl2) "[H↦2 H2]". iExists (vl1 ++ vl2).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "H1") as %->.
      iFrame. iExists _, _. by iFrame.
  Qed.

  Program Definition product2 (ty1 ty2 : type) :=
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_own tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid E l :=
         (∃ E1 E2, ⌜E1 ⊥ E2 ∧ E1 ⊆ E ∧ E2 ⊆ E⌝ ∗
            ty1.(ty_shr) κ tid E1 l ∗
            ty2.(ty_shr) κ tid E2 (shift_loc l ty1.(ty_size)))%I |}.
  Next Obligation.
    iIntros (ty1 ty2 tid vl) "H". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
    subst. rewrite app_length !ty_size_eq.
    iDestruct "H1" as %->. iDestruct "H2" as %->. done.
  Qed.
  Next Obligation.
    intros ty1 ty2 E N κ l tid q ??. iIntros "#LFT /=H Htok".
    rewrite split_prod_mt.
    iMod (bor_sep with "LFT H") as "[H1 H2]". set_solver.
    iMod (ty1.(ty_share) _ (N .@ 1) with "LFT H1 Htok") as "[? Htok]". solve_ndisj. done.
    iMod (ty2.(ty_share) _ (N .@ 2) with "LFT H2 Htok") as "[? $]". solve_ndisj. done.
    iModIntro. iExists (↑N .@ 1). iExists (↑N .@ 2). iFrame.
    iPureIntro. split. solve_ndisj. split; apply nclose_subseteq.
  Qed.
  Next Obligation.
    intros ty1 ty2 κ κ' tid E E' l ?. iIntros "#LFT /= #H⊑ H".
    iDestruct "H" as (N1 N2) "(% & H1 & H2)". iExists N1, N2.
    iSplit. iPureIntro. set_solver.
    iSplitL "H1"; by iApply (ty_shr_mono with "LFT H⊑").
  Qed.

  Global Instance product2_mono E L:
    Proper (subtype E L ==> subtype E L ==> subtype E L) product2.
  Proof.
    iIntros (ty11 ty12 H1 ty21 ty22 H2). split.
    - by rewrite /= (subtype_sz _ _ _ _ H1) (subtype_sz _ _ _ _ H2).
    - iIntros (??) "#LFT HE HL".
      iDestruct (subtype_own _ _ _ _ H1 with "LFT HE HL") as "#H1".
      iDestruct (subtype_own _ _ _ _ H2 with "LFT HE HL") as "#H2".
      iIntros "{HE HL}!# * H". iDestruct "H" as (vl1 vl2) "(% & Hown1 & Hown2)".
      iExists _, _. iSplit. done. by iSplitL "Hown1"; [iApply "H1"|iApply "H2"].
    - iIntros (??) "#LFT HE HL".
      iDestruct (subtype_shr _ _ _ _ H1 with "LFT HE HL") as "#H1".
      iDestruct (subtype_shr _ _ _ _ H2 with "LFT HE HL") as "#H2".
      iIntros "{HE HL}!# * H". iDestruct "H" as (vl1 vl2) "(% & #Hshr1 & #Hshr2)".
      iExists _, _. iSplit. done. erewrite subtype_sz; last done.
      by iSplit; [iApply "H1"|iApply "H2"].
  Qed.
  Global Instance product2_proper E L:
    Proper (eqtype E L ==> eqtype E L ==> eqtype E L) product2.
  Proof. by intros ??[]??[]; split; apply product2_mono. Qed.

  Global Program Instance product2_copy `(!Copy ty1) `(!Copy ty2) :
    Copy (product2 ty1 ty2).
  Next Obligation.
    intros ty1 ? ty2 ? κ tid E F l q ?. iIntros "#LFT H [[Htok1 Htok2] Htl]".
    iDestruct "H" as (E1 E2) "(% & H1 & H2)".
    assert (F = E1 ∪ E2 ∪ F∖(E1 ∪ E2)) as ->.
    { rewrite -union_difference_L; set_solver. }
    repeat setoid_rewrite na_own_union; first last.
    set_solver. set_solver. set_solver. set_solver.
    iDestruct "Htl" as "[[Htl1 Htl2] $]".
    iMod (@copy_shr_acc with "LFT H1 [$Htok1 $Htl1]") as (q1) "[H1 Hclose1]". set_solver.
    iMod (@copy_shr_acc with "LFT H2 [$Htok2 $Htl2]") as (q2) "[H2 Hclose2]". set_solver.
    destruct (Qp_lower_bound q1 q2) as (qq & q'1 & q'2 & -> & ->). iExists qq.
    iDestruct "H1" as (vl1) "[H↦1 H1]". iDestruct "H2" as (vl2) "[H↦2 H2]".
    rewrite !split_prod_mt.
    iAssert (▷ ⌜length vl1 = ty1.(ty_size)⌝)%I with "[#]" as ">%".
    { iNext. by iApply ty_size_eq. }
    iAssert (▷ ⌜length vl2 = ty2.(ty_size)⌝)%I with "[#]" as ">%".
    { iNext. by iApply ty_size_eq. }
    iDestruct "H↦1" as "[H↦1 H↦1f]". iDestruct "H↦2" as "[H↦2 H↦2f]".
    iIntros "!>". iSplitL "H↦1 H1 H↦2 H2".
    - iNext. iSplitL "H↦1 H1". iExists vl1. by iFrame. iExists vl2. by iFrame.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (vl1') "[H↦1 H1]". iDestruct "H2" as (vl2') "[H↦2 H2]".
      iAssert (▷ ⌜length vl1' = ty1.(ty_size)⌝)%I with "[#]" as ">%".
      { iNext. by iApply ty_size_eq. }
      iAssert (▷ ⌜length vl2' = ty2.(ty_size)⌝)%I with "[#]" as ">%".
      { iNext. by iApply ty_size_eq. }
      iCombine "H↦1" "H↦1f" as "H↦1". iCombine "H↦2" "H↦2f" as "H↦2".
      rewrite !heap_mapsto_vec_op; try by congruence.
      iDestruct "H↦1" as "[_ H↦1]". iDestruct "H↦2" as "[_ H↦2]".
      iMod ("Hclose1" with "[H1 H↦1]") as "[$$]". by iExists _; iFrame.
      iMod ("Hclose2" with "[H2 H↦2]") as "[$$]". by iExists _; iFrame. done.
  Qed.

  Definition product := fold_right product2 unit.

  (* Given that in practice, product will be used with concrete lists,
     there should be no need to declare [Copy] and [Proper] instances
     for [product]. *)
End product.

Arguments product : simpl never.
Notation Π := product.

Section typing.
  Context `{iris_typeG Σ}.

  (* FIXME : do we still need this (flattening and unflattening)? *)

  Lemma ty_incl_prod2_assoc1 ρ ty1 ty2 ty3 :
    ty_incl ρ (product2 ty1 (product2 ty2 ty3)) (product2 (product2 ty1 ty2) ty3).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#/=*H".
    - iDestruct "H" as (vl1 vl') "(% & Ho1 & H)".
      iDestruct "H" as (vl2 vl3) "(% & Ho2 & Ho3)". subst.
      iExists _, _. iSplit. by rewrite assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as (E1 E2') "(% & Hs1 & H)".
      iDestruct "H" as (E2 E3) "(% & Hs2 & Hs3)". rewrite shift_loc_assoc_nat.
      iSplit; last by rewrite assoc.
      iExists (E1 ∪ E2), E3. iSplit. by iPureIntro; set_solver. iFrame.
      iExists E1, E2. iSplit. by iPureIntro; set_solver. by iFrame.
  Qed.

  Lemma ty_incl_prod2_assoc2 ρ ty1 ty2 ty3 :
    ty_incl ρ (product2 (product2 ty1 ty2) ty3) (product2 ty1 (product2 ty2 ty3)).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#/=*H".
    - iDestruct "H" as (vl1 vl') "(% & H & Ho3)".
      iDestruct "H" as (vl2 vl3) "(% & Ho1 & Ho2)". subst.
      iExists _, _. iSplit. by rewrite -assoc. iFrame. iExists _, _. by iFrame.
    - iDestruct "H" as (E1' E3) "(% & H & Hs3)".
      iDestruct "H" as (E1 E2) "(% & Hs1 & Hs2)". rewrite shift_loc_assoc_nat.
      iSplit; last by rewrite assoc.
      iExists E1, (E2 ∪ E3). iSplit. by iPureIntro; set_solver. iFrame.
      iExists E2, E3. iSplit. by iPureIntro; set_solver. by iFrame.
  Qed.

  Lemma ty_incl_prod_flatten ρ tyl1 tyl2 tyl3 :
    ty_incl ρ (Π(tyl1 ++ Π tyl2 :: tyl3))
              (Π(tyl1 ++ tyl2 ++ tyl3)).
  Proof.
  Admitted.
  (*   apply (ty_incl_weaken _ ⊤). apply perm_incl_top. *)
  (*   induction tyl1; last by apply (ty_incl_prod2 _ _ _ _ _ _). *)
  (*   induction tyl2 as [|ty tyl2 IH]; simpl. *)
  (*   - iIntros (tid) "#LFT _". iSplitL; iIntros "/=!>!#*H". *)
  (*     + iDestruct "H" as (vl1 vl2) "(% & % & Ho)". subst. done. *)
  (*     + iDestruct "H" as (E1 E2) "(% & H1 & Ho)". iSplit; last done. *)
  (*       rewrite shift_loc_0. iApply (ty_shr_mono with "LFT [] Ho"). set_solver. *)
  (*       iApply lft_incl_refl. *)
  (*   - etransitivity. apply ty_incl_prod2_assoc2. *)
  (*     eapply (ty_incl_prod2 _ _ _ _ _ _). done. apply IH. *)
  (* Qed. *)

  Lemma ty_incl_prod_unflatten ρ tyl1 tyl2 tyl3 :
    ty_incl ρ (Π(tyl1 ++ tyl2 ++ tyl3))
              (Π(tyl1 ++ Π tyl2 :: tyl3)).
  Proof.
  Admitted.
  (*   apply (ty_incl_weaken _ ⊤). apply perm_incl_top. *)
  (*   induction tyl1; last by apply (ty_incl_prod2 _ _ _ _ _ _). *)
  (*   induction tyl2 as [|ty tyl2 IH]; simpl. *)
  (*   - iIntros (tid) "#LFT _". iMod (bor_create with "LFT []") as "[Hbor _]". *)
  (*     done. instantiate (1:=True%I). by auto. instantiate (1:=static). *)
  (*     iMod (bor_fracture (λ _, True%I) with "LFT Hbor") as "#Hbor". done. *)
  (*     iSplitL; iIntros "/=!>!#*H". *)
  (*     + iExists [], vl. iFrame. auto. *)
  (*     + iSplit; last done. iExists ∅, E. iSplit. iPureIntro; set_solver. *)
  (*       rewrite shift_loc_0. iFrame. iExists []. iSplit; last auto. *)
  (*       setoid_rewrite heap_mapsto_vec_nil. *)
  (*       iApply (frac_bor_shorten with "[] Hbor"). iApply lft_incl_static. *)
  (*   - etransitivity; last apply ty_incl_prod2_assoc1. *)
  (*     eapply (ty_incl_prod2 _ _ _ _ _ _). done. apply IH. *)
  (* Qed. *)
End typing.
