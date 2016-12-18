From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context typing.

Section shr_bor.
  Context `{typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_own tid vl :=
         (∃ (l:loc), ⌜vl = [ #l ]⌝ ∗ ty.(ty_shr) κ tid l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Global Instance subtype_shr_bor_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L ==> subtype E L) shr_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty. apply subtype_simple_type.
    iIntros (??) "#LFT #HE #HL H". iDestruct (Hκ with "HE HL") as "#Hκ".
    iDestruct "H" as (l) "(% & H)". subst. iExists _. iSplit. done.
    iApply (ty2.(ty_shr_mono) with "LFT Hκ"). 
    iDestruct (Hty with "* [] [] []") as "(_ & _ & #Hs1)"; [done..|clear Hty].
    by iApply "Hs1".
  Qed.
  Global Instance subtype_shr_bor_mono' E L :
    Proper (lctx_lft_incl E L ==> flip (subtype E L) ==> flip (subtype E L)) shr_bor.
  Proof. intros ??????. by apply subtype_shr_bor_mono. Qed.
  Global Instance subtype_shr_bor_proper E L κ :
    Proper (eqtype E L ==> eqtype E L) (shr_bor κ).
  Proof. intros ??[]. by split; apply subtype_shr_bor_mono. Qed.
End shr_bor.

Notation "&shr{ κ } ty" := (shr_bor κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma tctx_reborrow_shr E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [TCtx_hasty p (&shr{κ}ty)]
                  [TCtx_hasty p (&shr{κ'}ty); TCtx_blocked p κ (&shr{κ}ty)].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL".
    iDestruct (Hκκ' with "HE' HL'") as "Hκκ'".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% #H]". iDestruct "H" as (l) "[EQ Hshr]".
    iDestruct "EQ" as %[=->]. simpl. iModIntro. iSplit.
    - iExists _. iSplit. done. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "LFT Hκκ' Hshr").
    - iExists _. iSplit. done. iIntros "_". eauto.
  Qed.

End typing.
