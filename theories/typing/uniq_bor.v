From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow reborrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm type_incl typing own.

Section uniq_bor.
  Context `{iris_typeG Σ}.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         (∃ l:loc, ⌜vl = [ #l ]⌝ ∗ &{κ} l ↦∗: ty.(ty_own) tid)%I;
       ty_shr κ' tid E l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
            □ ∀ q' F, ⌜E ∪ mgmtE ⊆ F⌝ → q'.[κ∪κ']
               ={F, F∖E∖↑lftN}▷=∗ ty.(ty_shr) (κ∪κ') tid E l' ∗ q'.[κ∪κ'])%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    move=> κ ty E N κ' l tid q' ??/=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (bor_exists with "LFT Hb2") as (l') "Hb2". set_solver.
    iMod (bor_sep with "LFT Hb2") as "[EQ Hb2]". set_solver.
    iMod (bor_persistent with "LFT EQ Htok") as "[>% $]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hbf". set_solver.
    rewrite {1}bor_unfold_idx. iDestruct "Hb2" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc N _ (idx_bor_own 1 i ∨ ty_shr ty (κ∪κ') tid (↑N) l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iExists l'. iIntros "!>{$Hbf}!#". iIntros (q'' F) "% Htok".
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest _ _ _ (l' ↦∗: ty_own ty tid)%I with "LFT [Hbtok]") as "Hb".
      { set_solver. } { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#$ $]"; try done. set_solver.
      iApply "Hclose". eauto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_mask_mono; last by eauto. done. set_solver.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid E E' l ?. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0∪κ' ⊑ κ0∪κ)%I as "#Hκ0".
    { iApply (lft_incl_glb with "[] []").
      - iApply lft_le_incl. apply gmultiset_union_subseteq_l.
      - iApply (lft_incl_trans with "[] Hκ").
        iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!#". iIntros (q F) "% Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖E∖ ↑lftN)). set_solver. set_solver.
    iMod (lft_incl_acc with "Hκ0 Htok") as (q') "[Htok Hclose]". set_solver.
    iMod ("Hvs" with "* [%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      by iApply (ty_shr_mono with "LFT Hκ0").
  Qed.

End uniq_bor.

Notation "&uniq{ κ } ty" := (uniq_bor κ ty)
  (format "&uniq{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{iris_typeG Σ}.

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

  Lemma lft_incl_ty_incl_uniq_bor ty κ1 κ2 :
    ty_incl (κ1 ⊑ κ2) (&uniq{κ2}ty) (&uniq{κ1}ty).
  Proof.
    iIntros (tid) "#LFT #Hincl!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "[% Hown]". subst. iExists _. iSplit. done.
      by iApply (bor_shorten with "Hincl").
    - iAssert (κ1 ∪ κ ⊑ κ2 ∪ κ)%I as "#Hincl'".
      { iApply (lft_incl_glb with "[] []").
        - iApply (lft_incl_trans with "[] Hincl"). iApply lft_le_incl.
            apply gmultiset_union_subseteq_l.
        - iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
      iSplitL; last done. iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'.
      iFrame. iIntros "!#". iIntros (q' F) "% Htok".
      iMod (lft_incl_acc with "Hincl' Htok") as (q'') "[Htok Hclose]". set_solver.
      iMod ("Hupd" with "* [%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H Htok]". iMod ("Hclose" with "Htok") as "$".
      by iApply (ty_shr_mono with "LFT Hincl' H").
  Qed.

  Lemma consumes_copy_uniq_bor `(!Copy ty) κ κ' q:
    consumes ty (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l') "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma typed_deref_uniq_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &uniq{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_acc_cons with "LFT H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "$". iFrame "#". iExists _. eauto.
    - iFrame "H↦ H† Hown".
    - iIntros "!>(?&?&?)!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame.
  Qed.

  Lemma typed_deref_uniq_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &uniq{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &uniq{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑1 Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_exists with "LFT H↦") as (vl) "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[Heq Hbor]". done.
    iMod (bor_persistent with "LFT Heq Htok") as "[>% Htok]". done. subst.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    rewrite heap_mapsto_vec_singleton.
    iApply (wp_fupd_step  _ (⊤∖↑lftN) with "[Hbor]"); try done.
      by iApply (bor_unnest with "LFT Hbor").
    wp_read. iIntros "!> Hbor". iFrame "#". iSplitL "Hbor".
    - iExists _. iSplitR; first by auto. iApply (bor_shorten with "[] Hbor").
      iApply (lft_incl_glb with "H⊑2"). iApply lft_incl_refl.
    - iApply ("Hclose" with ">"). by iMod ("Hclose'" with "[$H↦]") as "[_ $]".
  Qed.

  Lemma update_weak ty q κ κ':
    update ty (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
              (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦)". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%#". iIntros (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[Hbor Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.
End typing.