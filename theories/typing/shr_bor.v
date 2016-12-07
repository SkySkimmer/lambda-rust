From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm type_incl typing own uniq_bor.

Section shr_bor.
  Context `{iris_typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_size := 1;
       st_own tid vl :=
         (∃ (l:loc), ⌜vl = [ #l ]⌝ ∗ ty.(ty_shr) κ tid (↑lrustN) l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

End shr_bor.

Notation "&shr{ κ } ty" := (shr_bor κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{iris_typeG Σ}.

  Lemma perm_incl_share q ν κ ty :
    ν ◁ &uniq{κ} ty ∗ q.[κ] ⇒ ν ◁ &shr{κ} ty ∗ q.[κ].
  Proof.
    iIntros (tid) "#LFT [Huniq [Htok $]]". unfold has_type.
    destruct (eval_expr ν); last by iDestruct "Huniq" as "[]".
    iDestruct "Huniq" as (l) "[% Hown]".
    iMod (ty.(ty_share) _ lrustN with "LFT Hown Htok") as "[Hown $]"; [solve_ndisj|done|].
    iIntros "!>/=". eauto.
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

  Lemma lft_incl_ty_incl_shr_bor ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&shr{κ2}ty) (&shr{κ1}ty).
  Proof.
    iIntros (tid) "#LFT #Hincl!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(% & H)". subst. iExists _.
      iSplit. done. by iApply (ty.(ty_shr_mono) with "LFT Hincl").
    - iDestruct "H" as (vl) "#[Hfrac Hty]". iSplit; last done.
      iExists vl. iFrame "#". iNext.
      iDestruct "Hty" as (l0) "(% & Hty)". subst. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "LFT Hincl Hty").
  Qed.

  Lemma consumes_copy_shr_bor ty κ κ' q:
    Copy ty →
    consumes ty (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (? ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l') "[Heq #Hshr]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    rewrite (union_difference_L (↑lrustN) ⊤); last done.
    setoid_rewrite ->na_own_union; try set_solver. iDestruct "Htl" as "[Htl ?]".
    iMod (copy_shr_acc with "LFT Hshr [$Htok $Htl]") as (q'') "[H↦ Hclose']"; try set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[Htok $]". iExists _; by iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma typed_deref_shr_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &shr{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &shr{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[[Htok1 Htok2] Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iApply (wp_fupd_step _ (⊤∖↑lrustN) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver.
    - wp_read. iIntros "!>[Hshr ?]". iFrame "H⊑".
      iSplitL "Hshr"; first by iExists _; auto. iApply ("Hclose" with ">").
      iFrame. iApply "Hclose'". auto.
  Qed.

  Lemma typed_deref_shr_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &shr{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &shr{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (lft_incl_acc with "H⊑1 Htok") as (q') "[[Htok1 Htok2] Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "H⊑3 Htok2") as (q''') "[Htok Hclose'']". done.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok]"); try done.
    - iApply ("Hown" with "* [%] Htok"). set_solver.
    - wp_read. iIntros "!>[Hshr Htok]". iFrame "H⊑1". iSplitL "Hshr".
      + iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
      + iApply ("Hclose" with ">"). iMod ("Hclose'" with "[$H↦]") as "$".
        by iMod ("Hclose''" with "Htok") as "$".
  Qed.
End typing.