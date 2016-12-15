From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import borrow reborrow frac_borrow.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context typing own.

Section uniq_bor.
  Context `{typeG Σ}.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       (* We quantify over [P]s so that the Proper lemma
          (wrt. subtyping) works without an update. *)
       ty_own tid vl :=
         (∃ (l:loc) P, (⌜vl = [ #l ]⌝ ∗ □ (P ↔ l ↦∗: ty.(ty_own) tid)) ∗ &{κ} P)%I;
       ty_shr κ' tid E l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜E ∪ mgmtE ⊆ F⌝ -∗ q.[κ∪κ']
                ={F, F∖E∖↑lftN}▷=∗ ty.(ty_shr) (κ∪κ') tid E l' ∗ q.[κ∪κ'])%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l P) "[[% _] _]". by subst.
  Qed.
  Next Obligation.
    move=> κ ty E N κ' l tid ???/=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (bor_exists with "LFT Hb2") as (l') "Hb2". set_solver.
    iMod (bor_exists with "LFT Hb2") as (P) "Hb2". set_solver.
    iMod (bor_sep with "LFT Hb2") as "[H Hb2]". set_solver.
    iMod (bor_persistent_tok with "LFT H Htok") as "[[>% #HPiff] Htok]". set_solver.
    iFrame "Htok". iExists l'.
    subst. rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$". set_solver.
    rewrite {1}bor_unfold_idx. iDestruct "Hb2" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc N _ (idx_bor_own 1 i ∨ ty_shr ty (κ∪κ') tid (↑N) l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest _ _ _ P with "LFT [Hbtok]") as "Hb".
      { set_solver. } { iApply bor_unfold_idx. eauto. }
                      iModIntro. iNext. iMod "Hb".
      iMod (bor_iff with "LFT [] Hb") as "Hb". set_solver. by eauto.
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#Hshr $]". done. set_solver.
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid E E' l ?. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0∪κ' ⊑ κ0∪κ)%I as "#Hκ0".
    { iApply (lft_incl_glb with "[] []").
      - iApply lft_le_incl. apply gmultiset_union_subseteq_l.
      - iApply (lft_incl_trans with "[] Hκ").
        iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!# * % Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖E∖ ↑lftN)); try  set_solver.
    iMod (lft_incl_acc with "Hκ0 Htok") as (q') "[Htok Hclose]"; first set_solver.
    iMod ("Hvs" with "* [%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty_shr_mono with "LFT Hκ0").
  Qed.

  Global Instance subtype_uniq_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) uniq_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 [Hty1 Hty2]. iIntros. iSplit; first done.
    iDestruct (Hty1 with "* [] [] []") as "(_ & #Ho1 & #Hs1)"; [done..|clear Hty1].
    iDestruct (Hty2 with "* [] [] []") as "(_ & #Ho2 & #Hs2)"; [done..|clear Hty2].
    iDestruct (Hκ with "[] []") as "#Hκ"; [done..|].
    iSplit; iAlways.
    - iIntros (??) "H". iDestruct "H" as (l P) "[[% #HPiff] Hown]". subst.
      iExists _, _. iSplitR; last by iApply (bor_shorten with "Hκ"). iSplit. done.
      iIntros "!#". iSplit; iIntros "H".
      + iDestruct ("HPiff" with "H") as (vl) "[??]". iExists vl. iFrame.
        by iApply "Ho1".
      + iDestruct "H" as (vl) "[??]". iApply "HPiff". iExists vl. iFrame.
        by iApply "Ho2".
    - iIntros (κ ???) "H". iAssert (κ2 ∪ κ ⊑ κ1 ∪ κ)%I as "#Hincl'".
      { iApply (lft_incl_glb with "[] []").
        - iApply (lft_incl_trans with "[] Hκ"). iApply lft_le_incl.
          apply gmultiset_union_subseteq_l.
        - iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
      iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'. iIntros "{$Hbor}!# %%% Htok".
      iMod (lft_incl_acc with "Hincl' Htok") as (q') "[Htok Hclose]"; first set_solver.
      iMod ("Hupd" with "* [%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply (ty_shr_mono with "[] Hincl'"); [done..|]. by iApply "Hs1".
  Qed.
  Global Instance subtype_uniq_mono' E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) uniq_bor.
  Proof. intros ??????. apply subtype_uniq_mono. done. by symmetry. Qed.
  Global Instance subtype_uniq_proper E L κ :
    Proper (eqtype E L ==> eqtype E L) (uniq_bor κ).
  Proof. split; by apply subtype_uniq_mono. Qed.
End uniq_bor.

Notation "&uniq{ κ } ty" := (uniq_bor κ ty)
  (format "&uniq{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma tctx_borrow E L p n ty κ :
    tctx_incl E L [TCtx_hasty p (own n ty)]
                  [TCtx_hasty p (&uniq{κ}ty); TCtx_guarded p κ (own n ty)].
  Proof.
    iIntros (tid ??) "#LFT $ $ H".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% Hown]". iDestruct "Hown" as (l) "(EQ & Hmt & ?)".
    iDestruct "EQ" as %[=->]. iMod (bor_create with "LFT Hmt") as "[Hbor Hext]". done.
    iModIntro. iSplitL "Hbor".
    - iExists _. iSplit. done. iExists _, _. erewrite <-uPred.iff_refl. eauto.
    - iExists _. iSplit. done. iIntros "H†". iExists _. iFrame. iSplitR. by eauto.
        by iMod ("Hext" with "H†") as "$".
  Qed.

  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [TCtx_hasty p (&uniq{κ}ty)]
                  [TCtx_hasty p (&uniq{κ'}ty); TCtx_guarded p κ (&uniq{κ}ty)].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL".
    iDestruct (Hκκ' with "HE' HL'") as "Hκκ'".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% Hown]". iDestruct "Hown" as (l P) "[[EQ #Hiff] Hb]".
    iDestruct "EQ" as %[=->]. iMod (bor_iff with "LFT [] Hb") as "Hb". done. by eauto.
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]". done. iModIntro. iSplitL "Hb".
    - iExists _. iSplit. done. iExists _, _. erewrite <-uPred.iff_refl. eauto.
    - iExists _. iSplit. done. iIntros "#H†".
      iMod ("Hext" with ">[]") as "Hb". by iApply (lft_incl_dead with "Hκκ' H†").
      iExists _, _. erewrite <-uPred.iff_refl. eauto.
  Qed.

  Lemma consumes_copy_uniq_bor `(!Copy ty) κ κ' q:
    consumes ty (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l' P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv.
    iExists _, _. erewrite <-uPred.iff_refl. auto.
  Qed.

  Lemma typed_deref_uniq_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &uniq{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_acc_cons with "LFT H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep _ _ _ (l' ↦∗: ty_own ty tid) with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "$". iFrame "#". iExists _, _.
      iFrame. iSplitR. done. by rewrite -uPred.iff_refl.
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
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑1 Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_exists with "LFT H↦") as (vl) "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_exists with "LFT Hbor") as (P') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H Hbor]". done.
    iMod (bor_persistent_tok with "LFT H Htok") as "[[>% #HP'iff] Htok]". done. subst.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    rewrite heap_mapsto_vec_singleton.
    iApply (wp_fupd_step  _ (⊤∖↑lftN) with "[Hbor]"); try done.
      by iApply (bor_unnest with "LFT Hbor").
    wp_read. iIntros "!> Hbor". iFrame "#". iSplitL "Hbor".
    - iExists _, _. iSplitR. by auto.
      iApply (bor_shorten with "[] Hbor").
      iApply (lft_incl_glb with "H⊑2"). iApply lft_incl_refl.
    - iApply ("Hclose" with ">"). by iMod ("Hclose'" with "[$H↦]") as "[_ $]".
  Qed.

  Lemma update_weak ty q κ κ':
    update ty (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
              (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%#". iIntros (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[Hbor Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv.
    iExists _, _. erewrite <-uPred.iff_refl. auto.
  Qed.
End typing.
