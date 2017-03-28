From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
Set Default Proof Using "Type".

Definition rc_stR :=
  optionUR (prodR fracR positiveR).
Class rcG Σ :=
  RcG :> inG Σ (authR rc_stR).
Definition rcΣ : gFunctors := #[GFunctor (authR rc_stR)].
Instance subG_rcΣ {Σ} : subG rcΣ Σ → rcG Σ.
Proof. solve_inG. Qed.

Definition rcN := lrustN .@ "rc".
Definition rc_invN := rcN .@ "inv".
Definition rc_shrN := rcN .@ "shr".

Section rc.
  Context `{!typeG Σ, !rcG Σ}.

  Definition rc_inv tid ν (γ : gname) (l : loc) (ty : type) : iProp Σ :=
    (∃ st, own γ (● st) ∗
      match st with
      | Some (q, c) => ∃ q',
       l ↦ #(Zpos c) ∗ †{1%Qp}l…(S ty.(ty_size)) ∗
         ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν] ∗
         (* We keep this view shift decomposed because we store the persistent part
            also in ty_own, to make it available with one step less. *)
         ([†ν] ={↑lftN}=∗ ▷ shift_loc l 1 ↦∗: ty.(ty_own) tid) ∗
         □ (1.[ν] ={↑lftN,∅}▷=∗ [†ν])
      | None => True
      end)%I.

  Global Instance rc_type_ne n :
    Proper (type_dist2 n ==> dist n) (rc_inv tid ν γ l).
  Proof.
    solve_proper_core
      ltac:(fun _ => exact: type_dist2_S || f_type_equiv || f_contractive || f_equiv).
  Qed.

  Program Definition rc (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           (l ↦ #1 ∗ ▷ †{1%Qp}l…(S ty.(ty_size)) ∗ ▷ shift_loc l 1 ↦∗: ty.(ty_own) tid) ∨
           (∃ γ ν q ty', ▷ type_incl ty' ty ∗
                     na_inv tid rc_invN (rc_inv tid ν γ l ty') ∗
                     own γ (◯ Some (q, 1%positive)) ∗
                     ty.(ty_shr) ν tid (shift_loc l 1) ∗
                     q.[ν] ∗ □ (1.[ν] ={↑lftN,∅}▷=∗ [†ν]))
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦∗{q} [ #l']) ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ]
             ={F, F∖↑shrN}▷=∗ q.[κ] ∗ ∃ γ ν q' ty', κ ⊑ ν ∗
                ▷ type_incl ty' ty ∗
                na_inv tid rc_invN (rc_inv tid ν γ l' ty') ∗
                &na{κ, tid, rc_shrN}(own γ (◯ Some (q', 1%positive))) ∗
                ty.(ty_shr) ν tid (shift_loc l' 1)
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    (* Ideally, we'd change ty_shr to say "l ↦{q} #l" in the fractured borrow,
       but that would be additional work here... *)
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _ _ _, _ ∗ _ ∗ _ ∗ &na{_,_,_} _ ∗ _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I
          with "[Hpbown]") as "#Hinv"; first by iLeft.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose2]"; first solve_ndisj.
      set (X := (∃ _ _ _, _)%I).
      iModIntro. iNext. iAssert X with "[>HP]" as "HX".
      { iDestruct "HP" as "[[Hl' [H† Hown]]|$]"; last done.
        iMod (lft_create with "LFT") as (ν) "[[Hν1 Hν2] #Hν†]"; first solve_ndisj.
        (* TODO: We should consider changing the statement of
           bor_create to dis-entangle the two masks such that this is no
          longer necessary. *)
        iApply (fupd_mask_mono (↑lftN)); first solve_ndisj.
        iMod (bor_create with "LFT Hown") as "[HP HPend]"; first solve_ndisj.
        iMod (own_alloc (● Some ((1/2)%Qp, 1%positive) ⋅
                         ◯ Some ((1/2)%Qp, 1%positive))) as (γ) "[Ha Hf]".
        { apply auth_valid_discrete_2. done. }
        iMod (na_inv_alloc tid _ _ (rc_inv tid ν γ l' ty) with "[Ha Hν2 Hl' H† HPend]").
        { rewrite /rc_inv. iExists (Some (_, _)). iFrame. iExists _. iFrame "#∗".
          rewrite Qp_div_2; auto. }
        iMod (ty_share with "LFT HP Hν1") as "[??]"; first solve_ndisj.
        iExists _, _, _, _. iFrame. iModIntro. iSplit; last done.
        by iApply type_incl_refl. }
      iDestruct "HX" as (γ ν q' ty') "(#Hincl & #Hinv & Hrc & #Hshr & Htok & #Hν†)".
      iMod ("Hclose2" with "[] [Hrc Htok]") as "[HX Htok]".
      { iNext. iIntros "HX". iModIntro. iNext.
        iRight. iExists γ, ν, q', _. iExact "HX". }
      { iNext.  by iFrame "#∗". }
      iAssert C with "[>HX]" as "#HC".
      { iExists _, _, _, _. iFrame "Hinv".
        iMod (bor_sep with "LFT HX") as "[_ HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[_ HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[Hrc HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[_ HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[Hlft _]"; first solve_ndisj.
        iDestruct (frac_bor_lft_incl with "LFT [> Hlft]") as "#Hlft".
        { iApply (bor_fracture with "LFT"); first solve_ndisj. by rewrite Qp_mult_1_r. }
        iMod (bor_na with "Hrc") as "$"; first solve_ndisj.
        by iFrame "#". }
      iMod ("Hclose1" with "[]") as "_"; first by auto.
      by iFrame "#∗".
    - iMod ("Hclose1" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. by iFrame.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iAlways. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (? ν ??) "(? & ? & ? & ? & ?)".
    iExists _, _, _, _. iModIntro. iFrame. iSplit.
    - by iApply lft_incl_trans.
    - by iApply na_bor_shorten.
  Qed.

  Global Instance rc_wf ty `{!TyWf ty} : TyWf (rc ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Global Instance rc_type_contractive : TypeContractive rc.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || exact: type_dist2_dist ||
                                       (eapply refcell_inv_type_ne; try reflexivity) ||
                                       f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance rc_ne : NonExpansive rc.
  Proof. apply type_contractive_ne, _. Qed.

  Lemma rc_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (rc ty1) (rc ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(#Hsz & #Hoincl & #Hsincl)".
    iSplit; first done. iSplit; iAlways.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as "[(Hl & H† & Hc) | Hvl]".
      { iLeft. iFrame "Hl". iNext. iDestruct "Hsz" as %->.
        iFrame. iApply (heap_mapsto_pred_wand with "Hc").
        iApply "Hoincl". }
      iDestruct "Hvl" as (γ ν q ty') "(#Hincl' & #Hinc & Htk & #Hsr & Hν)".
      iRight. iExists _, _, _, _. iFrame "#∗". iSplit.
      + iNext. iApply type_incl_trans; done.
      + iApply "Hsincl". done.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iFrame "Hfrac". iIntros "!# * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[Htok H]". iModIntro. iFrame "Htok".
      iDestruct "H" as (γ ν q' ty') "(Hlft & #Hincl' & Hinv & Hna & Hshr)". iExists _, _, _, _.
      iFrame. iSplit.
      + iNext. iApply type_incl_trans; done.
      + iApply "Hsincl". done.
  Qed.

  Global Instance rc_mono E L :
    Proper (subtype E L ==> subtype E L) rc.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!# #HE". iApply rc_subtype. iApply "Hsub"; done.
  Qed.
  Global Instance rc_proper E L :
    Proper (eqtype E L ==> eqtype E L) rc.
  Proof. intros ??[]. by split; apply rc_mono. Qed.
End rc.

Section code.
  Context `{!typeG Σ, !rcG Σ}.

  Lemma rc_check_unique ty F tid (l : loc) :
    ↑rc_invN ⊆ F →
    {{{ na_own tid F ∗ ty_own (rc ty) tid [ #l ] }}}
    !#l
    {{{ c, RET #(Zpos c); l ↦ #(Zpos c) ∗
        ((⌜c = 1%positive⌝ ∗ †{1%Qp}l…(S ty.(ty_size)) ∗ na_own tid F ∗ ▷ shift_loc l 1 ↦∗: ty.(ty_own) tid) ∨
         (⌜(1 < c)%positive⌝ ∗ na_own tid (F ∖ ↑rc_invN) ∗
          ∃ γ ν q q' ty', ▷ type_incl ty' ty ∗ na_inv tid rc_invN (rc_inv tid ν γ l ty') ∗
            own γ (◯ Some (q, 1%positive)) ∗ own γ (● Some ((q + q')%Qp, c)) ∗
            q.[ν] ∗ □ ((1).[ν] ={↑lftN,∅}▷=∗ [†ν]) ∗
            ty.(ty_shr) ν tid (shift_loc l 1) ∗
            (∀ c' q'', own γ (● Some (q'', c')) ∗ l ↦ #(Zpos c') ∗
                       (⌜(q + q')%Qp = q''⌝ ∨ ∃ qg, ⌜(q + q' = qg + q'')%Qp⌝ ∗ qg.[ν]) ∗ na_own tid (F ∖ ↑rc_invN) ={⊤}=∗ 
                       na_own tid F) )
        ) }}}.
  Proof.
    iIntros (? Φ) "[Hna [(Hl & H† & Hown)|Hown]] HΦ".
    - wp_read. iApply "HΦ". auto with iFrame.
    - iDestruct "Hown" as (γ ν q ty') "(#Hincl & #Hinv & Htok & #Hshr & Hν1 & #Hνend)".
      iMod (na_inv_open with "Hinv Hna") as "(Hproto & Hna & Hclose)"; [solve_ndisj..|].
      iDestruct "Hproto" as (st) "[>Hst Hproto]".
      iDestruct (own_valid_2 with "Hst Htok")
        as %[[Hval|(? &(qa,c) & [=<-] & -> & Hst)]%option_included _]%auth_valid_discrete_2;
        first done. (* Oh my, what a pattern... *)
      iDestruct "Hproto" as (q') "(>Hl & H† & >% & >Hν2 & Hν† & _)". iApply wp_fupd.
      destruct (decide (c ≤ 1)%positive) as [Hle|Hnle].
      + (* Tear down the protocol. *)
        assert (c = 1%positive) as ->.
        { apply Pos.le_antisym; first done. exact: Pos.le_1_l. } clear Hle.
        destruct Hst as [[??]|[_ Hle%pos_included]%prod_included]; last first.
        { exfalso. eapply Pos.nlt_1_r. done. }
        setoid_subst. iMod (own_update_2 with "Hst Htok") as "Hst".
        { apply auth_update_dealloc. rewrite -(right_id None _ (Some _)).
          apply cancel_local_update_empty, _. }
        iMod ("Hclose" with "[$Hna Hst]") as "Hna".
        { iExists None. auto. }
        iSpecialize ("Hνend" with "[Hν1 Hν2]").
        { rewrite -H0. iFrame. }
        iApply wp_mask_mono; last iApply (wp_step_fupd with "Hνend"); [done..|solve_ndisj|].
        wp_read. iIntros "#Hν". iMod ("Hν†" with "Hν") as "Hown". iModIntro.
        iApply "HΦ". iFrame. iLeft. iModIntro. iSplit; first done.
        iDestruct "Hincl" as "(#Hsz & #Hincl & _)". iDestruct "Hsz" as %->. iFrame.
        iApply (heap_mapsto_pred_wand with "Hown"). iApply "Hincl".
      + destruct Hst as [[??%leibniz_equiv]|[[q'' Hqa%leibniz_equiv] ?%pos_included]%prod_included].
        { exfalso. simpl in *. subst c. apply Hnle. done. }
        simpl in *. subst qa. wp_read. iApply "HΦ". iFrame. iRight. iModIntro. iSplit.
        { iPureIntro. apply Pos.lt_nle. done. }
        iFrame "Hna". iExists _, _, q, q'', _. iFrame "#∗%".
        iIntros (c' qx) "(Hst & Hl & Hq'' & Hna)". iApply "Hclose". iFrame "Hna".
        iExists _. iFrame "Hst". iDestruct "Hq''" as "[%|Hq'']".
        * iExists _. subst qx. iFrame "∗%". by iIntros "!> !#".
        * iDestruct "Hq''" as (qg) "[% Hν']". iExists _.
          iCombine "Hν2 Hν'" as "Hν". iFrame. iNext. iSplit; last by iAlways.
          iPureIntro. rewrite [(q' + _)%Qp]comm_L assoc [(qx + _)%Qp]comm_L -H1. done.
  Qed.

  Definition rc_new ty : val :=
    funrec: <> ["x"] :=
      let: "rcbox" := new [ #(S ty.(ty_size)) ] in
      let: "rc" := new [ #1 ] in
      "rcbox" +ₗ #0 <- #1;;
      "rcbox" +ₗ #1 <-{ty.(ty_size)} !"x";;
      "rc" +ₗ #0 <- "rcbox";;
      delete [ #ty.(ty_size); "x"];; return: ["rc"].

  Lemma rc_new_type ty `{!TyWf ty} :
    typed_val (rc_new ty) (fn(∅; ty) → rc ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (rcbox); simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (rc); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrc [Hrcbox [Hx _]]]".
    rewrite (Nat2Z.id (S ty.(ty_size))) !tctx_hasty_val.
    iDestruct (ownptr_own with "Hx") as (lx vlx) "(% & Hx↦ & Hx & Hx†)". subst x.
    iDestruct (ownptr_uninit_own with "Hrcbox") as (lrcbox vlrcbox) "(% & Hrcbox↦ & Hrcbox†)". subst rcbox.
    inv_vec vlrcbox=>??. iDestruct (heap_mapsto_vec_cons with "Hrcbox↦") as "[Hrcbox↦0 Hrcbox↦1]".
    iDestruct (ownptr_uninit_own with "Hrc") as (lrc vlrc) "(% & Hrc↦ & Hrc†)". subst rc.
    inv_vec vlrc=>?. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hrcbox↦1 $Hx↦]"); [by auto using vec_to_list_length..|].
    iIntros "[Hrcbox↦1 Hx↦]". wp_seq. wp_op. rewrite shift_loc_0. wp_write.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lrc ◁ box (rc ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      { iExists _. rewrite uninit_own. auto. }
      iNext. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. iFrame. iLeft.
      rewrite freeable_sz_full_S. iFrame. iExists _. iFrame.  }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_clone : val :=
    funrec: <> ["rc"] :=
      let: "rc2" := new [ #1 ] in
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "count" := !("rc''" +ₗ #0) in
      "rc''" +ₗ #0 <- "count" +#1;;
      "rc2" <- "rc''";;
      delete [ #1; "rc" ];; return: ["rc2"].

  Lemma rc_clone_type ty `{!TyWf ty} :
    typed_val rc_clone (fn(∀ α, ∅; &shr{α} rc ty) → rc ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (rc2); simpl_subst.
    rewrite (Nat2Z.id 1). (* Having to do this is rather annoying... *) 
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hrc2 _]]]".
    rewrite !tctx_hasty_val [[x]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    iDestruct (ownptr_uninit_own with "Hrc2") as (lrc2 vlrc2) "(% & Hrc2 & Hrc2†)".
    subst rc2. inv_vec vlrc2=>rc2. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    rewrite heap_mapsto_vec_singleton. iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'' ty') "(#Hincl & #Hty & #Hinv & #Hrctokb & #Hshr)". iModIntro.
    wp_let. wp_op. rewrite shift_loc_0.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iMod (na_inv_open with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hrctokb Hα1 Hna") as "(>Hrctok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as (st) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hrctok") as
        %[[Hval|(_ & (qa, c) & _ & -> & _)]%option_included _]%auth_valid_discrete_2;
      first done. (* Oh my, what a pattern... *)
    iDestruct "Hrcst" as (qb) "(>Hl' & >Hl'† & >% & Hνtok & Hν† & #Hνend)".
    wp_read. wp_let. wp_op. rewrite shift_loc_0. wp_op. wp_write. wp_write.
    (* And closing it again. *)
    iMod (own_update with "Hrc●") as "[Hrc● Hrctok2]".
    { apply auth_update_alloc,
      (op_local_update_discrete _ _ (Some ((qb/2)%Qp, 1%positive)))=>-[/= Hqa _].
      split; simpl; last done. apply frac_valid'. rewrite -H comm_L -{2}(Qp_div_2 qb).
      apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (_ / _)%Qp).
      apply Qcplus_le_mono_r, Qp_ge_0. }
    rewrite right_id -Some_op pair_op. iDestruct "Hνtok" as "[Hνtok1 Hνtok2]".
    iMod ("Hclose3" with "[$Hrctok] Hna") as "[Hα1 Hna]".
    iMod ("Hclose2" with "[Hrc● Hl' Hl'† Hνtok2 Hν† $Hna]") as "Hna".
    { iExists _. iFrame "Hrc●". iExists _. rewrite Z.add_comm. iFrame "∗ Hνend".
      rewrite [_ ⋅ _]comm frac_op' -[(_ + _)%Qp]assoc. rewrite Qp_div_2. auto. }
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α} rc ty); #lrc2 ◁ box (rc ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hx". iFrame "Hrc2†". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "Hrc2". iNext. iRight. iExists _, ν, _, _. iFrame "#∗". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_deref : val :=
    funrec: <> ["rc"] :=
      let: "x" := new [ #1 ] in
      let: "rc'" := !"rc" in
      "x" <- (!"rc'" +ₗ #1);;
      delete [ #1; "rc" ];; return: ["x"].

  Lemma rc_deref_type ty `{!TyWf ty} :
    typed_val rc_deref (fn(∀ α, ∅; &shr{α} rc ty) → &shr{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (x); simpl_subst. rewrite (Nat2Z.id 1).
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hx _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock.
    iDestruct (ownptr_uninit_own with "Hx") as (lrc2 vlrc2) "(% & Hx & Hx†)".
    subst x. inv_vec vlrc2=>?. rewrite heap_mapsto_vec_singleton. 
    destruct rc' as [[|rc'|]|]; try done. simpl of_val.
    iDestruct "Hrc'" as (l') "[#Hrc' #Hdelay]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hdelay" with "[] Hα1"); last iApply (wp_step_fupd with "Hdelay"); [done..|].
    iMod (frac_bor_acc with "LFT Hrc' Hα2") as (q') "[Hrc'↦ Hclose2]"; first solve_ndisj.
    rewrite heap_mapsto_vec_singleton. iApply wp_fupd. wp_read.
    iMod ("Hclose2" with "[$Hrc'↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'' ty') "(#? & #? & #Hinv & #Hrctokb & #Hshr)". iModIntro.
    wp_op. wp_write.
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ rcx ◁ box (&shr{α} rc ty); #lrc2 ◁ box (&shr{α} ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hrcx". iFrame "Hx†". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "Hx". iNext. iApply ty_shr_mono; done. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_try_unwrap ty : val :=
    funrec: <> ["rc"] :=
      let: "r" := new [ #(Σ[ ty; rc ty ]).(ty_size) ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "count" := !("rc'" +ₗ #0) in
      if: "count" = #1 then
        (* Return content, delete Rc heap allocation. *)
        "r" <-{ty.(ty_size),Σ 0} !("rc'" +ₗ #1);;
        delete [ #(S ty.(ty_size)); "rc'" ];;
        "k" []
      else
        "r" <-{Σ 1} "rc'";;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["r"].

  Lemma rc_try_unwrap_type ty `{!TyWf ty} :
    typed_val (rc_try_unwrap ty) (fn(∅; rc ty) → Σ[ ty; rc ty ]).
  Proof.
    (* TODO: There is a *lot* of duplication between this proof and the one for drop. *)
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (x); simpl_subst.
    rewrite (Nat2Z.id (Σ[ ty; rc ty ]).(ty_size)).
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); x ◁ box (Σ[ ty; rc ty ])])) ;
      [solve_typing..| |]; last first.
    { simpl. iAlways. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hx _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[x]]lock.
    destruct rc' as [[|rc'|]|]; try done.
    rewrite [[ #rc' ]]lock. wp_op. rewrite shift_loc_0 -(lock [ #rc' ]).
    wp_apply (rc_check_unique with "[$Hna $Hrc']"); first solve_ndisj.
    iIntros (c) "(Hrc & Hc)". wp_let.
    iDestruct "Hc" as "[(% & Hrc† & Hna & Hown)|(% & Hna & Hproto)]".
    - subst c. wp_op=>[_|?]; last done. wp_if.
      iApply (type_type _ _ _ [ x ◁ own_ptr (ty_size Σ[ ty; rc ty ]) (uninit _);
                                rcx ◁ box (uninit 1);
                                #rc' +ₗ #1 ◁ own_ptr (S ty.(ty_size)) ty;
                                #rc' +ₗ #0 ◁ own_ptr (S ty.(ty_size)) (uninit 1%nat)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { unlock. rewrite 3!tctx_interp_cons tctx_interp_singleton.
        rewrite 2!tctx_hasty_val tctx_hasty_val' // tctx_hasty_val' //.
        rewrite -freeable_sz_full_S -(freeable_sz_split _ 1%nat).
        iDestruct "Hrc†" as "[Hrc†1 Hrc†2]". iFrame.
        rewrite shift_loc_0. iFrame. iExists [_].
        rewrite uninit_own heap_mapsto_vec_singleton. auto with iFrame. }
      iApply (type_sum_memcpy Σ[ ty; rc ty ]); [solve_typing..|].
      iApply (type_delete (Π[uninit _; uninit _])); [solve_typing..|].
      iApply type_jump; solve_typing.
    - iDestruct "Hproto" as (γ ν q q' ty')
          "(#Hincl & #Hinv & Hrctok & Hrc● & Hν & #Hν† & #Hshr & Hclose)".
      wp_op; intros Hc.
      { exfalso. move:Hc. move/Zpos_eq_iff. intros ->. exact: Pos.lt_irrefl. }
      wp_if. iMod ("Hclose" with "[> $Hrc● $Hrc $Hna]") as "Hna"; first by eauto.
      iApply (type_type _ _ _ [ x ◁ own_ptr (ty_size Σ[ ty; rc ty ]) (uninit _);
                                rcx ◁ box (uninit 1);
                                #rc' ◁ rc ty ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton.
        rewrite !tctx_hasty_val tctx_hasty_val' //. unlock. iFrame.
        iRight. iExists _, _, _, _. iFrame "∗#". }
      iApply (type_sum_assign Σ[ ty; rc ty ]); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition rc_drop ty : val :=
    funrec: <> ["rc"] :=
      let: "x" := new [ #(option ty).(ty_size) ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "count" := !("rc'" +ₗ #0) in
      "rc'" +ₗ #0 <- "count" - #1;;
      if: "count" = #1 then
        (* Return content, delete Rc heap allocation. *)
        "x" <-{ty.(ty_size),Σ some} !("rc'" +ₗ #1);;
        delete [ #(S ty.(ty_size)); "rc'" ];;
        "k" []
      else
        "x" <-{Σ none} ();;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["x"].

  Lemma rc_drop_type ty `{!TyWf ty} :
    typed_val (rc_drop ty) (fn(∅; rc ty) → option ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (x); simpl_subst.
    rewrite (Nat2Z.id (option ty).(ty_size)).
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); x ◁ box (option ty)]));
      [solve_typing..| |]; last first.
    { simpl. iAlways. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hx _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[x]]lock.
    destruct rc' as [[|rc'|]|]; try done. rewrite [[ #rc' ]]lock.
    wp_op. rewrite shift_loc_0. rewrite -(lock [ #rc' ]).
    wp_apply (rc_check_unique with "[$Hna $Hrc']"); first solve_ndisj.
    iIntros (c) "(Hrc & Hc)". wp_let. wp_op. rewrite shift_loc_0.
    rewrite {3}[Z.pos c]lock. wp_op.
    iDestruct "Hc" as "[(% & Hrc† & Hna & Hown)|(% & Hna & Hproto)]".
    - subst c. wp_write. wp_op=>[_|?]; last done. wp_if.
      iApply (type_type _ _ _ [ x ◁ own_ptr (ty_size (option ty)) (uninit _);
                                rcx ◁ box (uninit 1);
                                #rc' +ₗ #1 ◁ own_ptr (S ty.(ty_size)) ty;
                                #rc' +ₗ #0 ◁ own_ptr (S ty.(ty_size)) (uninit 1%nat)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { unlock. rewrite 3!tctx_interp_cons tctx_interp_singleton.
        rewrite 2!tctx_hasty_val tctx_hasty_val' // tctx_hasty_val' //.
        rewrite -freeable_sz_full_S -(freeable_sz_split _ 1%nat).
        iDestruct "Hrc†" as "[Hrc†1 Hrc†2]". iFrame.
        rewrite shift_loc_0. iFrame. iExists [_].
        rewrite uninit_own heap_mapsto_vec_singleton. auto with iFrame. }
      iApply (type_sum_memcpy (option _)); [solve_typing..|].
      iApply (type_delete (Π[uninit _; uninit _])); [solve_typing..|].
      iApply type_jump; solve_typing.
    - iDestruct "Hproto" as (γ ν q q' ty')
                              "(#Hincl & #Hinv & Hrctok & Hrc● & Hν & _ & _ & Hclose)".
      wp_write. wp_op; intros Hc.
      { exfalso. move:Hc. move/Zpos_eq_iff. intros ->. exact: Pos.lt_irrefl. }
      wp_if. iMod ("Hclose" $! (c-1)%positive q' with "[> Hrc● Hrctok Hrc Hν $Hna]") as "Hna".
      { unlock. iMod (own_update_2 with "Hrc● Hrctok") as "$".
        { apply auth_update_dealloc. rewrite -{1}(Pplus_minus c 1%positive); last first.
          { apply Pos.lt_gt. done. }
          rewrite -pair_op Some_op. apply: cancel_local_update_empty.
          (* For some reason, Coq's apply doesn't work here. whatever. *) }
        rewrite Pos2Z.inj_sub //. iFrame "Hrc". iRight. iExists _.
        auto with iFrame. }
      iApply (type_type _ _ _ [ x ◁ own_ptr (ty_size (option ty)) (uninit _);
                                rcx ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton.
        rewrite !tctx_hasty_val. unlock. iFrame. }
      iApply (type_sum_unit (option ty)); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition rc_get_mut : val :=
    funrec: <> ["rc"] :=
      let: "x" := new [ #2 ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "count" := !("rc''" +ₗ #0) in
      if: "count" = #1 then
        "x" <-{Σ some} ("rc''" +ₗ #1);;
        "k" []
      else
        "x" <-{Σ none} ();;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["x"].

  Lemma rc_get_mut_type ty `{!TyWf ty} :
    typed_val rc_get_mut (fn(∀ α, ∅; &uniq{α} rc ty) → option (&uniq{α} ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (x); simpl_subst. rewrite (Nat2Z.id 2%nat).
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ r, [rcx ◁ box (uninit 1); x ◁ box (option $ &uniq{α} ty)]));
      [solve_typing..| |]; last first.
    { simpl. iAlways. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hx _]]]".
    rewrite !tctx_hasty_val  [[rcx]]lock [[x]]lock.
    destruct rc' as [[|rc'|]|]; try done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hrc' Hα") as "[Hrc' Hclose2]"; first solve_ndisj.
    iDestruct (heap_mapsto_ty_own with "Hrc'") as (vl) "[>Hrc' Hrcown]".
    inv_vec vl=>l. rewrite heap_mapsto_vec_singleton.
    wp_read. destruct l as [[|l|]|]; try done.
    wp_let. wp_op. rewrite shift_loc_0.
    wp_apply (rc_check_unique with "[$Hna Hrcown]"); first done.
    { (* Boy this is silly... *) iDestruct "Hrcown" as "[(?&?&?)|?]"; last by iRight.
      iLeft. by iFrame. }
    iIntros (c) "(Hrc & Hc)". wp_let. wp_op; intros Hc.
    - wp_if. iDestruct "Hc" as "[(% & Hl† & Hna & Hown)|(% & _)]"; last first.
      { exfalso. move:Hc. move/Zpos_eq_iff. intros->. exact: Pos.lt_irrefl. }
      subst c. iMod ("Hclose2" with "[Hrc Hrc' Hl†] [Hown]") as "[Hown Hα]"; [|iNext; iExact "Hown"|].
      { iIntros "!> Hown". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hrc'".
        iLeft. by iFrame. }
      iMod ("Hclose1" with "Hα HL") as "HL".
      iApply (type_type _ _ _ [ x ◁ box (uninit 2);
                                 #l +ₗ #1 ◁ &uniq{α} ty;
                                rcx ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. }
      iApply (type_sum_assign (option (&uniq{_} _))); [solve_typing..|].
      iApply type_jump; solve_typing.
    - wp_if. iDestruct "Hc" as "[(% & _)|(% & Hna & Hproto)]".
      { exfalso. subst c. done. }
      iDestruct "Hproto" as (γ ν q' q'' ty')
              "(#Hincl & #Hinv & Hrctok & Hrc● & Hν & #Hshr & #Hν† & Hclose3)".
      iMod ("Hclose3" with "[$Hrc● $Hrc $Hna]") as "Hna"; first by auto.
      iMod ("Hclose2" with "[] [Hrc' Hrctok Hν]") as "[Hrc' Hα]".
      { iIntros "!> HX". iModIntro. iExact "HX". }
      { iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hrc'".
        iRight. iExists _, _, _, _. iFrame "#∗". }
      iMod ("Hclose1" with "Hα HL") as "HL".
      iApply (type_type _ _ _ [ x ◁ box (uninit 2);
                                rcx ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
        unlock. iFrame. }
      iApply (type_sum_unit (option (&uniq{_} _))); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  (* TODO: * fn make_mut(this: &mut Rc<T>) -> &mut T
             Needs a Clone bound, how do we model this?
           * Weak references?
   *)

End code.
