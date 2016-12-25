From iris.proofmode Require Import tactics.
From lrust.lang Require Import heap.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs.

Section case.
  Context `{typeG Σ}.

  (* FIXME : the doc does not give [p +ₗ #(S (ty.(ty_size))) ◁ ...]. *)
  Lemma type_case_own E L C T p n tyl el:
    Forall2 (λ ty e,
      typed_body E L C ((p +ₗ #0 ◁ own n (uninit 1)) :: (p +ₗ #1 ◁ own n ty) ::
         (p +ₗ #(S (ty.(ty_size))) ◁
            own n (uninit (list_max (map ty_size tyl) - ty_size ty))) :: T) e ∨
      typed_body E L C ((p ◁ own n (sum tyl)) :: T) e) tyl el →
    typed_body E L C ((p ◁ own n (sum tyl)) :: T) (case: !p of el).
  Proof.
    iIntros (Hel tid qE) "#HEAP #LFT Hna HE HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros (v Hv) "Hp".
    iDestruct "Hp" as (l) "[EQ [H↦ Hf]]". iDestruct "EQ" as %[=->].
    iDestruct "H↦" as (vl) "[H↦ Hown]".
    iDestruct "Hown" as (i vl' vl'') "(>% & >EQlen & Hown)". subst.
    simpl ty_size. iDestruct "EQlen" as %[=EQlen]. rewrite -EQlen. simpl length.
    rewrite -Nat.add_1_l app_length -!freeable_sz_split
            heap_mapsto_vec_cons heap_mapsto_vec_app.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')".
    iDestruct "Hf" as "(Hfi & Hfvl' & Hfvl'')".
    rewrite nth_lookup.
    destruct (tyl !! i) as [ty|] eqn:EQty; last iDestruct "Hown" as ">[]".
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. iApply wp_case; [lia|by rewrite Nat2Z.id|]. iNext.
    destruct Hety as [Hety|Hety]; iApply (Hety with "HEAP LFT Hna HE HL HC");
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //; iFrame "HT".
    - iDestruct (ty.(ty_size_eq) with "Hown") as %<-.
      iSplitL "H↦i Hfi"; last iSplitR "H↦vl'' Hfvl''".
      + rewrite shift_loc_0. iExists _. iFrame. iSplit. done. iExists [ #i].
        rewrite heap_mapsto_vec_singleton.
        iFrame. iExists [_], []. auto.
      + iExists _. iFrame. iSplit. done. iExists _. iFrame.
      + rewrite -EQlen app_length minus_plus uninit_sz -(shift_loc_assoc_nat _ 1).
        iExists _. iFrame. iSplit. done. iExists _. iFrame. rewrite uninit_own. auto.
    - iExists _. iSplit. done.
      assert (EQf:=freeable_sz_split n 1). simpl in EQf. rewrite -EQf. clear EQf.
      rewrite -EQlen app_length -freeable_sz_split. iFrame.
      iExists (#i :: vl' ++ vl''). iNext.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
      iFrame. iExists i, vl', vl''. rewrite /= app_length nth_lookup EQty. auto.
  Qed.

  Lemma type_case_uniq E L C T p κ tyl el:
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T) e ∨
      typed_body E L C ((p ◁ &uniq{κ}sum tyl) :: T) e) tyl el →
    typed_body E L C ((p ◁ &uniq{κ}sum tyl) :: T) (case: !p of el).
  Proof.
    iIntros (Halive Hel tid qE) "#HEAP #LFT Hna HE HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros (v Hv) "Hp".
    iDestruct "Hp" as (l P) "[[EQ HP] Hb]". iDestruct "EQ" as %[=->].
    iMod (bor_iff with "LFT HP Hb") as "Hb". done.
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]". done.
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[H↦ Hown]".
    iDestruct "Hown" as (i vl' vl'') "(>% & >EQlen & Hown)". subst.
    iDestruct "EQlen" as %[=EQlen].
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app nth_lookup.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')".
    destruct (tyl !! i) as [ty|] eqn:EQty; last iDestruct "Hown" as ">[]".
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. iApply wp_case; [lia|by rewrite Nat2Z.id|]. iNext.
    iDestruct (ty.(ty_size_eq) with "Hown") as %EQlenvl'.
    destruct Hety as [Hety|Hety].
    - iMod ("Hclose'" $! (shift_loc l 1 ↦∗: ty.(ty_own) tid)%I
            with "[H↦vl' Hown] [H↦i H↦vl'']") as "[Hb Htok]".
      { iExists vl'. iFrame. }
      { iIntros "!>Hown". iDestruct "Hown" as (vl'2) "[H↦ Hown]".
        iExists (#i::vl'2++vl''). iIntros "!>". iNext.
        iDestruct (ty.(ty_size_eq) with "Hown") as %EQlenvl'2.
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app EQlenvl' EQlenvl'2.
        iFrame. iExists _, _, _. iSplit. by auto.
        rewrite /= -EQlen !app_length EQlenvl' EQlenvl'2 nth_lookup EQty /=. auto. }
      iMod ("Hclose" with "Htok") as "[HE HL]".
      iApply (Hety with "HEAP LFT Hna HE HL HC").
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //. iFrame "HT".
      iExists _, _. iFrame. iSplit. done. iSplit; iIntros "!>!#$".
    - iMod ("Hclose'" with "* [H↦i H↦vl' H↦vl'' Hown] []") as "[Hb Htok]";
        [|by iIntros "!>$"|].
      { iExists (#i::vl'++vl'').
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app -EQlen. iFrame. iNext.
        iExists i, vl', vl''. rewrite nth_lookup EQty. auto. }
      iMod ("Hclose" with "Htok") as "[HE HL]".
      iApply (Hety with "HEAP LFT Hna HE HL HC").
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //. iFrame "HT".
      iExists _, _. iFrame. iSplit. done. iSplit; iIntros "!>!#$".
  Qed.

  Lemma type_case_shr E L C T p κ tyl el:
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) :: T) e ∨
      typed_body E L C ((p ◁ &shr{κ}sum tyl) :: T) e) tyl el →
    typed_body E L C ((p ◁ &shr{κ}sum tyl) :: T) (case: !p of el).
  Proof.
    iIntros (Halive Hel tid qE) "#HEAP #LFT Hna HE HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros (v Hv) "Hp".
    iDestruct "Hp" as (l) "[EQ Hl]". iDestruct "EQ" as %[=->].
    iDestruct "Hl" as (i) "[#Hb Hshr]".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]". done.
    iMod (frac_bor_acc with "LFT Hb Htok") as (q') "[[H↦i H↦vl''] Hclose']". done.
    rewrite nth_lookup.
    destruct (tyl !! i) as [ty|] eqn:EQty; last iDestruct "Hshr" as "[]".
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. iApply wp_case; [lia|by rewrite Nat2Z.id|]. iNext.
    iMod ("Hclose'" with "[$H↦i $H↦vl'']") as "Htok".
    iMod ("Hclose" with "Htok") as "[HE HL]".
    destruct Hety as [Hety|Hety]; iApply (Hety with "HEAP LFT Hna HE HL HC");
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //; iFrame "HT".
    - iExists _. auto.
    - iExists _. iSplit. done. iExists i. rewrite nth_lookup EQty /=. auto.
  Qed.
End case.