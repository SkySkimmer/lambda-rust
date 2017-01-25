From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import lft_contexts type_context shr_bor programs.
Set Default Proof Using "Type".

Section uniq_bor.
  Context `{typeG Σ}.
  Local Hint Extern 1000 (_ ⊆ _) => set_solver : ndisj.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => &{κ} l ↦∗: ty.(ty_own) tid
         | _ => False
         end%I;
       ty_shr κ' tid l :=
         (∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ∪κ']
                ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (κ∪κ') tid l' ∗ q.[κ∪κ'])%I
    |}.
  Next Obligation.
    iIntros (q ty tid [|[[]|][]]) "H"; try iDestruct "H" as "[]". done.
  Qed.
  Next Obligation.
    move=> κ ty N κ' l tid ??/=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as ([|[[|l'|]|][]]) "Hb"; first set_solver;
      (iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]"; first set_solver);
      try (iMod (bor_persistent_tok with "LFT Hb2 Htok") as "[>[] _]"; set_solver).
    iFrame. iExists l'. subst. rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$". set_solver.
    rewrite {1}bor_unfold_idx. iDestruct "Hb2" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (κ∪κ') tid l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#Hshr $]". solve_ndisj.
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid l. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]". iAssert (κ0∪κ' ⊑ κ0∪κ)%I as "#Hκ0".
    { iApply lft_glb_mono. iApply lft_incl_refl. done. }
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!# * % Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖↑shrN∖↑lftN)); try set_solver.
    iMod (lft_incl_acc with "Hκ0 Htok") as (q') "[Htok Hclose]"; first set_solver.
    iMod ("Hvs" with "[%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty_shr_mono with "LFT Hκ0").
  Qed.

  Global Instance uniq_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) uniq_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty%eqtype_unfold. iIntros. iSplit; first done.
    iDestruct (Hty with "[] [] []") as "(_ & #Ho & #Hs)"; [done..|clear Hty].
    iDestruct (Hκ with "[] []") as "#Hκ"; [done..|]. iSplit; iAlways.
    - iIntros (? [|[[]|][]]) "H"; try iDestruct "H" as "[]".
      iApply (bor_shorten with "Hκ"). iApply bor_iff_proper; last done.
      iSplit; iIntros "!>!# H"; iDestruct "H" as (vl) "[??]";
      iExists vl; iFrame; by iApply "Ho".
    - iIntros (κ ??) "H". iAssert (κ2 ∪ κ ⊑ κ1 ∪ κ)%I as "#Hincl'".
      { iApply lft_glb_mono. done. iApply lft_incl_refl. }
      iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'. iIntros "{$Hbor}!# %%% Htok".
      iMod (lft_incl_acc with "Hincl' Htok") as (q') "[Htok Hclose]"; first set_solver.
      iMod ("Hupd" with "[%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; [done..|]. by iApply "Hs".
  Qed.
  Global Instance uniq_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) uniq_bor.
  Proof. intros ??????. apply uniq_mono. done. by symmetry. Qed.
  Global Instance uniq_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) uniq_bor.
  Proof. intros ??[]; split; by apply uniq_mono. Qed.

  Global Instance uniq_contractive κ : Contractive (uniq_bor κ).
  Proof.
    intros n ?? EQ. split; [split|]; simpl.
    - done.
    - destruct n=>// tid vl /=. repeat (apply EQ || f_contractive || f_equiv).
    - intros κ' tid l. repeat (apply EQ || f_contractive || f_equiv).
  Qed.
  Global Instance uniq_ne κ n : Proper (dist n ==> dist n) (uniq_bor κ).
  Proof. apply contractive_ne, _. Qed.

  Global Instance uniq_send κ ty :
    Send ty → Send (uniq_bor κ ty).
  Proof.
    iIntros (Hsend tid1 tid2 [|[[]|][]]) "H"; try iDestruct "H" as "[]".
    iApply bor_iff_proper; last done. iNext. iAlways. iApply uPred.equiv_iff.
    do 3 f_equiv. iSplit; iIntros "."; by iApply Hsend.
  Qed.

  Global Instance uniq_sync κ ty :
    Sync ty → Sync (uniq_bor κ ty).
  Proof.
    iIntros (Hsync κ' tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists l'. iFrame "Hm". iAlways. iIntros (F q) "% Htok".
    iMod ("Hshr" with "[] Htok") as "Hfin"; first done. iClear "Hshr".
    iModIntro. iNext. iMod "Hfin" as "[Hshr $]". iApply Hsync. done.
  Qed.
End uniq_bor.

Notation "&uniq{ κ } ty" := (uniq_bor κ ty)
  (format "&uniq{ κ }  ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma uniq_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → eqtype E L ty1 ty2 →
    subtype E L (&uniq{κ1} ty1) (&uniq{κ2} ty2).
  Proof. by intros; apply uniq_mono. Qed.
  Lemma uniq_proper' E L κ ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (&uniq{κ} ty1) (&uniq{κ} ty2).
  Proof. by intros; apply uniq_proper. Qed.

  Lemma tctx_share E L p κ ty :
    lctx_lft_alive E L κ → tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &shr{κ}ty].
  Proof.
    iIntros (Hκ ???) "#LFT HE HL Huniq".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; [try done..|].
    rewrite !tctx_interp_singleton /=.
    iDestruct "Huniq" as ([[]|]) "[% Huniq]"; try iDestruct "Huniq" as "[]".
    iMod (ty.(ty_share) with "LFT Huniq Htok") as "[Hown Htok]"; [solve_ndisj|].
    iMod ("Hclose" with "Htok") as "[$ $]". iExists _. by iFrame "%∗".
  Qed.

  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &uniq{κ'}ty; p ◁{κ'} &uniq{κ}ty].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL".
    iDestruct (Hκκ' with "HE' HL'") as "Hκκ'".
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "[% Hb]"; try iDestruct "Hb" as "[]".
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]". done. iModIntro.
    iSplitL "Hb"; iExists _; auto.
  Qed.

  (* When sharing during extraction, we do the (arbitrary) choice of
     sharing at the lifetime requested (κ). In some cases, we could
     actually desire a longer lifetime and then use subtyping, because
     then we get, in the environment, a shared borrow at this longer
     lifetime.

     In the case the user wants to do the sharing at a longer
     lifetime, she has to manually perform the extraction herself at
     the desired lifetime. *)
  Lemma tctx_extract_hasty_share E L p ty ty' κ κ' T :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ &uniq{κ'}ty')::T)
                       ((p ◁ &shr{κ}ty')::(p ◁{κ} &uniq{κ'}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_;_]).
    rewrite tctx_reborrow_uniq //. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite tctx_share // {1}copy_tctx_incl.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, shr_mono'.
  Qed.

  Lemma tctx_extract_hasty_share_samelft E L p ty ty' κ T :
    lctx_lft_alive E L κ → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ &uniq{κ}ty')::T)
                                         ((p ◁ &shr{κ}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]).
    rewrite tctx_share // {1}copy_tctx_incl.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, shr_mono'.
  Qed.

  Lemma tctx_extract_hasty_reborrow E L p ty ty' κ κ' T :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' →
    tctx_extract_hasty E L p (&uniq{κ'}ty) ((p ◁ &uniq{κ}ty')::T)
                       ((p ◁{κ'} &uniq{κ}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]). rewrite tctx_reborrow_uniq //.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, uniq_mono'.
  Qed.

  Lemma read_uniq E L κ ty :
    Copy ty → lctx_lft_alive E L κ → typed_read E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    iIntros (Hcopy Halive) "!#". iIntros ([[]|] tid F qE qL ?) "#LFT Htl HE HL Hown";
      try iDestruct "Hown" as "[]".
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first set_solver.
    iMod (bor_acc with "LFT Hown Hκ") as "[H↦ Hclose']"; first set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; first done. iFrame "∗#". iIntros "H↦".
    iMod ("Hclose'" with "[H↦]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.

  Lemma write_uniq E L κ ty :
    lctx_lft_alive E L κ → typed_write E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    iIntros (Halive) "!#". iIntros ([[]|] tid F qE qL ?) "#LFT HE HL Hown";
      try iDestruct "Hown" as "[]".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first set_solver.
    iMod (bor_acc with "LFT Hown Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iModIntro. iExists _, _. iSplit; first done.
    iFrame. iIntros "Hown". iDestruct "Hown" as (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.
End typing.

Hint Resolve uniq_mono' uniq_proper' : lrust_typing.
Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
Hint Resolve tctx_extract_hasty_share | 10 : lrust_typing.
Hint Resolve tctx_extract_hasty_share_samelft | 9 : lrust_typing.
