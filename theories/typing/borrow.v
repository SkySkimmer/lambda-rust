From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import reborrow frac_borrow.
From lrust.lang Require Import heap.
From lrust.typing Require Export uniq_bor shr_bor own.
From lrust.typing Require Import lft_contexts type_context programs.

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{typeG Σ}.

  Lemma tctx_borrow E L p n ty κ :
    tctx_incl E L [p ◁ own n ty] [p ◁ &uniq{κ}ty; p ◁{κ} own n ty].
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

  Lemma tctx_extract_hasty_borrow E L p n ty κ T :
    tctx_extract_hasty E L p (&uniq{κ}ty) ((p ◁ own n ty)::T)
                       ((p ◁{κ} own n ty)::T).
  Proof. apply (tctx_incl_frame_r E L _ [_] [_;_]), tctx_borrow. Qed.

  (* See the comment above [tctx_extract_hasty_share] in [uniq_bor.v]. *)
  Lemma tctx_extract_hasty_borrow_share E L p ty ty' κ n T :
    lctx_lft_alive E L κ → subtype E L ty' ty →
    tctx_extract_hasty E L p (&shr{κ}ty) ((p ◁ own n ty')::T)
                       ((p ◁ &shr{κ}ty')::(p ◁{κ} own n ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r E L _ [_] [_;_;_]). etrans.
    { by apply tctx_borrow. }
    apply (tctx_incl_frame_r E L _ [_] [_;_]). etrans.
    by apply tctx_share. etrans. by apply copy_tctx_incl, _.
    by apply (tctx_incl_frame_r E L _ [_] [_]), subtype_tctx_incl, shr_mono'.
  Qed.

  Lemma type_deref_uniq_own {E L} κ p n ty :
    lctx_lft_alive E L κ →
    typed_instruction_ty E L [p ◁ &uniq{κ} own n ty] (!p) (&uniq{κ} ty).
  Proof.
    iIntros (Hκ tid eq) "#HEAP #LFT $ HE HL Hp". rewrite tctx_interp_singleton.
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first set_solver.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (l P) "[[Heq #HPiff] HP]". iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (bor_acc_cons with "LFT H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep _ _ _ (l' ↦∗: ty_own ty tid) with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "($ & $)".
      rewrite tctx_interp_singleton tctx_hasty_val' //. iExists _, _.
      iFrame. iSplitR. done. rewrite -uPred.iff_refl. auto.
    - iFrame "H↦ H† Hown".
    - iIntros "!>(?&?&?)!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame.
  Qed.

  Lemma type_deref_shr_own {E L} κ p n ty :
    lctx_lft_alive E L κ →
    typed_instruction_ty E L [p ◁ &shr{κ} own n ty] (!p) (&shr{κ} ty).
  Proof.
    iIntros (Hκ tid eq) "#HEAP #LFT $ HE HL Hp". rewrite tctx_interp_singleton.
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first set_solver.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[#Hshr Htok2]". iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
      iMod ("Hclose" with "[Htok1 Htok2]") as "($ & $)"; first by iFrame.
      rewrite tctx_interp_singleton tctx_hasty_val' //. iExists _. auto.
  Qed.

  Lemma type_deref_uniq_uniq {E L} κ κ' p ty :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    typed_instruction_ty E L [p ◁ &uniq{κ} &uniq{κ'} ty] (!p) (&uniq{κ} ty).
  Proof.
    iIntros (Hκ Hincl tid eq) "#HEAP #LFT $ HE HL Hp". rewrite tctx_interp_singleton.
    iPoseProof (Hincl with "[#] [#]") as "Hincl".
    { by iApply elctx_interp_persist. } { by iApply llctx_interp_persist. }
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first set_solver.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (l P) "[[Heq #HPiff] HP]". iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
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
    wp_read. iIntros "!> Hbor". iFrame "#".
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]"; first by auto.
    iMod ("Hclose" with "Htok") as "($ & $)".
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    iExists _, _. iSplitR; first by auto.
    iApply (bor_shorten with "[] Hbor").
    iApply (lft_incl_glb with "Hincl"). iApply lft_incl_refl.
  Qed.

  Lemma type_deref_shr_uniq {E L} κ κ' p ty :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    typed_instruction_ty E L [p ◁ &shr{κ} &uniq{κ'} ty] (!p) (&shr{κ} ty).
  Proof.
    iIntros (Hκ Hincl tid eq) "#HEAP #LFT $ HE HL Hp". rewrite tctx_interp_singleton.
    iPoseProof (Hincl with "[#] [#]") as "Hincl".
    { by iApply elctx_interp_persist. } { by iApply llctx_interp_persist. }
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first set_solver.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ ⊑ κ' ∪ κ)%I as "#Hincl'".
    { iApply (lft_incl_glb with "Hincl []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "Hincl' Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[#Hshr Htok2]". iMod ("Hclose''" with "Htok2") as "Htok2".
      iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
      iMod ("Hclose" with "[Htok1 Htok2]") as "($ & $)"; first by iFrame.
      rewrite tctx_interp_singleton tctx_hasty_val' //.
      iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT Hincl' Hshr").
  Qed.
End borrow.

Hint Resolve tctx_extract_hasty_borrow
     tctx_extract_hasty_borrow_share : lrust_typing.
