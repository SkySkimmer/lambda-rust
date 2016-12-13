From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing type_context perm product own uniq_bor shr_bor.

Section product_split.
  Context `{typeG Σ}.

  Fixpoint combine_offs (tyl : list type) (accu : nat) :=
    match tyl with
    | [] => []
    | ty :: q => (ty, accu) :: combine_offs q (accu + ty.(ty_size))
    end.

  Lemma perm_split_own_prod2 ty1 ty2 n ν :
    ν ◁ own n (product2 ty1 ty2) ⇔
      ν ◁ own n ty1 ∗ ν +ₗ #ty1.(ty_size) ◁ own n ty2.
  Proof.
    rewrite /has_type /own /sep /=.
    destruct (eval_expr ν) as [[[]|?]|]; last first; split; iIntros (tid) "_ H/=";
      (try by iDestruct "H" as "[_ []]"); (try by iDestruct "H" as (l) "[% _]").
    { by auto. }
    - iDestruct "H" as (l') "(EQ & H & >H†)". iDestruct "EQ" as %[=<-].
      iDestruct "H" as (vl) "[>H↦ H]". iDestruct "H" as (vl1 vl2) "(>% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app -freeable_sz_split.
      iDestruct "H†" as "[H†1 H†2]". iDestruct "H↦" as "[H↦1 H↦2]".
      iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
      { iNext. by iApply ty_size_eq. }
      iDestruct "EQ" as %->. iSplitL "H↦1 H†1 H1".
      + iExists _. iSplitR. done. iFrame. iExists _. by iFrame.
      + iExists _. iSplitR. done. iFrame. iExists _. by iFrame.
    - iDestruct "H" as "[H1 H2]".
      iDestruct "H1" as (l') "(EQ & H↦1 & H†1)". iDestruct "EQ" as %[=<-].
      iDestruct "H2" as (l') "(EQ & H↦2 & H†2)". iDestruct "EQ" as %[=<-].
      iExists l. iSplitR. done. rewrite -freeable_sz_split. iFrame.
      iDestruct "H↦1" as (vl1) "[H↦1 H1]". iDestruct "H↦2" as (vl2) "[H↦2 H2]".
      iExists (vl1 ++ vl2). rewrite heap_mapsto_vec_app. iFrame.
      iAssert (▷ ⌜length vl1 = ty_size ty1⌝)%I with "[#]" as ">EQ".
      { iNext. by iApply ty_size_eq. }
      iDestruct "EQ" as %->. iFrame. iExists vl1, vl2. iFrame. auto.
  Qed.

  Lemma perm_split_own_prod tyl n ν :
    tyl ≠ [] →
    ν ◁ own n (Π tyl) ⇔
      foldr (λ qtyoffs acc,
             ν +ₗ #(qtyoffs.2:nat) ◁ own n (qtyoffs.1) ∗ acc)
            ⊤ (combine_offs tyl 0).
  Proof.
    intros ?. revert ν. rewrite /product /=. induction tyl as [|ty tyl IH]=>ν. done.
    rewrite /= perm_split_own_prod2. destruct tyl.
    - rewrite /has_type /sep /=.
      destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
        (try by iDestruct "H" as "[_ []]"); (try by iDestruct "H" as "[[] _]");
      rewrite shift_loc_0; iDestruct "H" as "[$ _]"; [done|].
      iExists _. iSplitL. done. iSplitL; iIntros "!>!>"; last done.
      iExists []. rewrite heap_mapsto_vec_nil. auto.
    - rewrite IH //. f_equiv.
      + rewrite /has_type /sep /=.
        destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
          (try by iDestruct "H" as "[]"); (try by iDestruct "H" as (l) "[% _]");
          (try by auto); rewrite (shift_loc_0 l) //.
      + clear. change (ty_size ty) with (0+ty_size ty)%nat at 2. generalize 0%nat.
        induction (t :: tyl) as [|ty' tyl' IH]=>offs //=. apply perm_sep_proper.
        * rewrite /has_type /sep /=.
          destruct (eval_expr ν) as [[[]|]|]; split; iIntros (tid) "_ H/=";
          (try by iDestruct "H" as "[]"); [|]; by rewrite shift_loc_assoc_nat (comm plus).
        * etrans. apply IH. do 2 f_equiv. lia.
  Qed.

  Lemma perm_split_uniq_bor_prod2 ty1 ty2 κ ν :
    ν ◁ &uniq{κ} (product2 ty1 ty2) ⇒
    ν ◁ &uniq{κ} ty1 ∗ ν +ₗ #(ty1.(ty_size)) ◁ &uniq{κ} ty2.
  Proof.
    rewrite /has_type /sep /product2 /=.
    destruct (eval_expr ν) as [[[|l|]|]|];
      iIntros (tid) "#LFT H"; try iDestruct "H" as "[]";
        iDestruct "H" as (l0 P) "[[EQ #HPiff] HP]"; iDestruct "EQ" as %[=<-].
    iMod (bor_iff with "LFT [] HP") as "Hown". set_solver. by eauto.
    rewrite /= split_prod_mt. iMod (bor_sep with "LFT Hown") as "[H1 H2]".
    set_solver. iSplitL "H1"; iExists _, _; erewrite <-uPred.iff_refl; auto.
  Qed.

  Lemma perm_split_uniq_bor_prod tyl κ ν :
    ν ◁ &uniq{κ} (Π tyl) ⇒
      foldr (λ tyoffs acc,
             ν +ₗ #(tyoffs.2:nat) ◁ &uniq{κ} (tyoffs.1) ∗ acc)%P
            ⊤ (combine_offs tyl 0).
  Proof.
    transitivity (ν +ₗ #0%nat ◁ &uniq{κ}Π tyl)%P.
    { iIntros (tid) "LFT H/=". rewrite /has_type /=. destruct (eval_expr ν)=>//.
      iDestruct "H" as (l P) "[[Heq #HPiff] HP]". iDestruct "Heq" as %[=->].
      iMod (bor_iff with "LFT [] HP") as "H". set_solver. by eauto.
      iExists _, _; erewrite <-uPred.iff_refl, shift_loc_0; auto. }
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
