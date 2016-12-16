From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import perm lft_contexts type_context typing own uniq_bor.

Section shr_bor.
  Context `{typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_own tid vl :=
         (∃ (l:loc), ⌜vl = [ #l ]⌝ ∗ ty.(ty_shr) κ tid l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Global Instance subtype_shr_bor_mono E L :
    Proper (lctx_lft_incl E L --> subtype E L ==> subtype E L) shr_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty. apply subtype_simple_type.
    iIntros (??) "#LFT #HE #HL H". iDestruct (Hκ with "HE HL") as "#Hκ".
    iDestruct "H" as (l) "(% & H)". subst. iExists _. iSplit. done.
    iApply (ty2.(ty_shr_mono) with "LFT Hκ"). 
    iDestruct (Hty with "* [] [] []") as "(_ & _ & #Hs1)"; [done..|clear Hty].
    by iApply "Hs1".
  Qed.
  Global Instance subtype_shr_bor_mono' E L :
    Proper (lctx_lft_incl E L ==> subtype E L --> flip (subtype E L)) shr_bor.
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
    iMod (copy_shr_acc with "LFT Hshr [$Htok $Htl]") as (q'') "[H↦ Hclose']".
    { assert (↑shrN ⊆ (↑lrustN : coPset)) by solve_ndisj. set_solver. } (* FIXME: some tactic should solve this in one go. *)
    { rewrite ->shr_locsE_shrN. solve_ndisj. }
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
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & [Htok1 Htok2]) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok1") as (q'') "[Htok1 Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iMod (lft_incl_acc with "H⊑ Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[Hshr Htok2]{$H⊑}". iMod ("Hclose''" with "Htok2") as "$".
      iSplitL "Hshr"; first by iExists _; auto. iApply ("Hclose" with ">").
      iFrame. iApply "Hclose'". auto.
  Qed.

  Lemma typed_deref_shr_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &shr{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &shr{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & [Htok1 Htok2] & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (lft_incl_acc with "H⊑1 Htok1") as (q') "[Htok1 Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "[] Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    { iApply (lft_incl_trans with "[]"); done. }
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[#Hshr Htok2]{$H⊑1}".
      iMod ("Hclose''" with "Htok2") as "$". iSplitR.
      * iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
      * iApply ("Hclose" with ">"). iApply ("Hclose'" with "[$H↦]").
  Qed.
End typing.
