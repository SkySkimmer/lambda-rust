From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context typing own uniq_bor.

Section shr_bor.
  Context `{typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_size := 1;
       st_own tid vl :=
         (∃ (l:loc), ⌜vl = [ #l ]⌝ ∗ ty.(ty_shr) κ tid (↑lrustN) l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Global Instance subtype_shr_bor_mono E L :
    Proper (flip (incl E L) ==> subtype E L ==> subtype E L) shr_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty. split.
    - done.
    - iIntros (qE qL) "#LFT HE HL *". iDestruct (Hκ with "HE HL") as "#Hκ".
      iDestruct (subtype_shr _ _ _ _ Hty with "LFT HE HL") as "#Hty".
      iIntros "{HE HL}!#*H". iDestruct "H" as (l) "(% & H)". subst. iExists _.
      iSplit. done. by iApply (ty2.(ty_shr_mono) with "LFT Hκ"); last iApply "Hty".
    - iIntros (qE qL) "#LFT HE HL *". iDestruct (Hκ with "HE HL") as "#Hκ".
      iDestruct (subtype_shr _ _ _ _ Hty with "LFT HE HL") as "#Hst".
      iIntros "{HE HL}!#*H". iDestruct "H" as (vl) "#[Hfrac [Hty|H†]]".
      + iExists vl. iFrame "#". iLeft. iNext. simpl.
        iDestruct "Hty" as (l0) "(% & Hty)". subst. iExists _. iSplit. done.
          by iApply (ty_shr_mono with "LFT Hκ"); last iApply "Hst".
      + simpl. eauto.
  Qed.
  Global Instance subtype_shr_bor_mono' E L :
    Proper (incl E L ==> flip (subtype E L) ==> flip (subtype E L)) shr_bor.
  Proof. intros ??????. by apply subtype_shr_bor_mono. Qed.
  Global Instance subtype_shr_bor_proper E L κ :
    Proper (eqtype E L ==> eqtype E L) (shr_bor κ).
  Proof. intros ??[]. by split; apply subtype_shr_bor_mono. Qed.
End shr_bor.

Notation "&shr{ κ } ty" := (shr_bor κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma tctx_incl_share E L p κ ty :
    tctx_incl E L [TCtx_holds p (&uniq{κ}ty)] [TCtx_holds p (&shr{κ}ty)].
  Proof.
    iIntros (??) "#LFT _ _ !# * Huniq". rewrite /tctx_interp !big_sepL_singleton /=.
    iDestruct "Huniq" as (v) "[% Huniq]". iExists _. iFrame "%".
    iDestruct "Huniq" as (l P) "[[% #HPiff] HP]".
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (ty.(ty_share) _ lrustN with "LFT H↦") as "Hown"; [solve_ndisj|done|].
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
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok") as (q''') "[>H↦ Hclose']". done.
    iApply (wp_fupd_step _ (⊤∖↑lrustN∖↑lftN) with "[Hown]"); try done.
    - iApply ("Hown" with "* [%]"). set_solver.
    - wp_read. iIntros "!>[Hshr|#H†]{$H⊑}".
      + iSplitL "Hshr"; first by iExists _; auto. iApply ("Hclose" with ">").
        iFrame. iApply "Hclose'". auto.
      + iMod ("Hclose'" with "[H↦]"). by auto.
        by iDestruct (lft_tok_dead with "[-] H†") as "[]".
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
    iMod (lft_incl_acc with "H⊑1 Htok") as (q') "[Htok Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iApply (wp_fupd_step _ (_∖_) with "[Hown]"); try done.
    - iApply ("Hown" with "* [%]"). set_solver.
    - wp_read. iIntros "!>[#Hshr|#H†]{$H⊑1}".
      + iSplitR.
        * iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
        * iApply ("Hclose" with ">"). iApply ("Hclose'" with "[$H↦]").
      + iMod ("Hclose'" with "[H↦]"). by auto.
        by iDestruct (lft_tok_dead with "[-] H†") as "[]".
  Qed.
End typing.