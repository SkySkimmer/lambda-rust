From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import borrow reborrow frac_borrow.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import lft_contexts type_context shr_bor perm typing.

Section uniq_bor.
  Context `{typeG Σ}.

  Local Hint Extern 1000 (_ ⊆ _) => set_solver : ndisj.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       (* We quantify over [P]s so that the Proper lemma
          (wrt. subtyping) works without an update.

          An obvious alternative definition would be to allow
          an update in the ownership here, i.e. `|={lftE}=> &{κ} P`.
          The trouble with this definition is that bor_unnest as proven is too
          weak. The original unnesting with open borrows was strong enough. *)
       ty_own tid vl :=
         (∃ (l:loc) P, (⌜vl = [ #l ]⌝ ∗ □ (P ↔ l ↦∗: ty.(ty_own) tid)) ∗ &{κ} P)%I;
       ty_shr κ' tid l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ∪κ']
                ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (κ∪κ') tid l' ∗ q.[κ∪κ'])%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l P) "[[% _] _]". by subst.
  Qed.
  Next Obligation.
    move=> κ ty N κ' l tid ??/=. iIntros "#LFT Hshr Htok".
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
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (κ∪κ') tid l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest _ _ _ P with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (bor_iff with "LFT [] Hb") as "Hb". solve_ndisj.
      { by eauto. }
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#Hshr $]". solve_ndisj.
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid l. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0∪κ' ⊑ κ0∪κ)%I as "#Hκ0".
    { iApply (lft_incl_glb with "[] []").
      - iApply lft_le_incl. apply gmultiset_union_subseteq_l.
      - iApply (lft_incl_trans with "[] Hκ").
        iApply lft_le_incl. apply gmultiset_union_subseteq_r. }
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!# * % Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖↑shrN∖↑lftN)); try set_solver.
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
    - iIntros (κ ??) "H". iAssert (κ2 ∪ κ ⊑ κ1 ∪ κ)%I as "#Hincl'".
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

  Lemma tctx_incl_share E L p κ ty :
    lctx_lft_alive E L κ → tctx_incl E L [TCtx_hasty p (&uniq{κ}ty)] [TCtx_hasty p (&shr{κ}ty)].
  Proof.
    iIntros (Hκ ???) "#LFT HE HL Huniq".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; [try done..|].
    rewrite /tctx_interp !big_sepL_singleton /=.
    iDestruct "Huniq" as (v) "[% Huniq]". 
    iDestruct "Huniq" as (l P) "[[% #HPiff] HP]".
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (ty.(ty_share) with "LFT H↦ Htok") as "[Hown Htok]"; [solve_ndisj|].
    iMod ("Hclose" with "Htok") as "[$ $]". iExists _. iFrame "%".
    iIntros "!>/=". eauto.
  Qed.

  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [TCtx_hasty p (&uniq{κ}ty)]
                  [TCtx_hasty p (&uniq{κ'}ty); TCtx_blocked p κ (&uniq{κ}ty)].
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

End typing.
