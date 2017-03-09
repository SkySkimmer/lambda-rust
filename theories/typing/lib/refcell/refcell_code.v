From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing option.
From lrust.typing.lib.refcell Require Import refcell ref refmut.
Set Default Proof Using "Type".

Section refcell_functions.
  Context `{typeG Σ, refcellG Σ}.

  (* Constructing a refcell. *)
  Definition refcell_new ty : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #(S ty.(ty_size))] in
      "r" +ₗ #0 <- #0;;
      "r" +ₗ #1 <-{ty.(ty_size)} !"x";;
      delete [ #ty.(ty_size) ; "x"];; "return" ["r"].

  Lemma refcell_new_type ty :
    typed_val (refcell_new ty) (fn([]; ty) → refcell ty).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|].
    iIntros (r tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite (Nat2Z.id (S ty.(ty_size))) tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]". destruct x as [[|lx|]|]; try done.
    iDestruct "Hx" as "[Hx Hx†]". iDestruct "Hx" as (vl) "[Hx↦ Hx]".
    destruct r as [[|lr|]|]; try done. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own.
    iDestruct "Hr" as "[Hr↦ >SZ]". destruct vl' as [|]; iDestruct "SZ" as %[=].
    rewrite heap_mapsto_vec_cons. iDestruct "Hr↦" as "[Hr↦0 Hr↦1]". wp_op.
    rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hr↦1 $Hx↦]"); [done||lia..|].
    iIntros "[Hr↦1 Hx↦]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lr ◁ box (refcell ty)]%TC
        with "[] LFT Hna HE HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      - iExists _. rewrite uninit_own. auto.
      - iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply (type_jump [ #_]); solve_typing.
  Qed.

  (* The other direction: getting ownership out of a refcell. *)
  Definition refcell_into_inner ty : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #ty.(ty_size)] in
      "r" <-{ty.(ty_size)} !("x" +ₗ #1);;
          (* TODO RJ: Can we make it so that the parenthesis above are mandatory?
             Leaving them away is inconsistent with `let ... := !"x" +ₗ #1`. *)
       delete [ #(S ty.(ty_size)) ; "x"];; "return" ["r"].

  Lemma refcell_into_inner_type ty :
    typed_val (refcell_into_inner ty) (fn([]; refcell ty) → ty).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|].
    iIntros (r tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite (Nat2Z.id (ty.(ty_size))) tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]". destruct x as [[|lx|]|]; try done.
    iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[]|]vl]) "[Hx↦ Hx]"; try iDestruct "Hx" as ">[]".
    destruct r as [[|lr|]|]; try done. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own heap_mapsto_vec_cons.
    iDestruct "Hr" as "[Hr↦ >%]". iDestruct "Hx↦" as "[Hx↦0 Hx↦1]". wp_op.
    iDestruct "Hx" as "[% Hx]". iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hr↦ $Hx↦1]"); [done||lia..|].
    iIntros "[Hr↦ Hx↦1]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (S (ty_size ty))); #lr ◁ box ty]%TC
        with "[] LFT Hna HE HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iSplitR "Hr↦ Hx".
      - iExists (_::_). rewrite heap_mapsto_vec_cons uninit_own -Hsz. iFrame. auto.
      - iExists vl. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply (type_jump [ #_]); solve_typing.
  Qed.

  Definition refcell_get_mut : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      "x" <- "x'" +ₗ #1;;
      "return" ["x"].

  Lemma refcell_get_mut_type ty :
    typed_val refcell_get_mut (fn(∀ α, [α]; &uniq{α} (refcell ty)) → &uniq{α} ty)%T.
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iIntros (tid qE) "#LFT Hna HE HL HC HT".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|];  try iDestruct "Hx'" as "[]".
    iAssert (&{α} (∃ (z : Z), lx' ↦ #z ∗ ⌜-1 ≤ z⌝) ∗
        (&uniq{α} ty).(ty_own) tid [ #(shift_loc lx' 1)])%I with ">[Hx']" as "[_ Hx']".
    { iApply bor_sep; [done..|]. iApply (bor_proper with "Hx'"). iSplit.
      - iIntros "[H1 H2]". iDestruct "H1" as (z) "[??]". iDestruct "H2" as (vl) "[??]".
        iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame. iFrame.
      - iIntros "H". iDestruct "H" as ([|[[| |z]|]vl]) "[H↦ H]"; try iDestruct "H" as "[]".
        rewrite heap_mapsto_vec_cons.
        iDestruct "H" as "[H1 H2]". iDestruct "H↦" as "[H↦1 H↦2]".
        iSplitL "H1 H↦1"; eauto. iExists _. iFrame. }
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as (vl) "[Hx↦ Hx]". rewrite uninit_own. wp_op.
    iApply (type_type _ _ _
            [ #lx ◁ box (uninit 1); #(shift_loc lx' 1) ◁ &uniq{α}ty]%TC
            with "[] LFT Hna HE HL HC [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iNext. iExists _. rewrite uninit_own. iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply (type_jump [ #_]); solve_typing.
  Qed.

  (* Shared borrowing. *)
  Definition refcell_try_borrow : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #3 ] in
      let: "x'" := !"x" in
      let: "n" := !"x'" in
      if: "n" ≤ #-1 then
        "r" <-{Σ 0} ();;
        "k" ["r"] (* FIXME RJ: this is very confusing, "k" does not even look like it is bound here... *)
      else
        "x'" <- "n" + #1;;
        let: "ref" := new [ #2 ] in
        "ref" <- "x'" +ₗ #1;;
        "ref" +ₗ #1 <- "x'";;
        "r" <-{2,Σ 1} !"ref";;
        delete [ #2; "ref"];;
        "k" ["r"]
      cont: "k" ["r"] :=
        delete [ #1; "x"];; "return" ["r"].

  Lemma refcell_try_borrow_type ty :
    typed_val refcell_try_borrow (fn(∀ α, [α] ; &shr{α}(refcell ty)) → option (ref α ty)).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_cont [_] [] (λ r, [x ◁ box (&shr{α} refcell ty);
                                    r!!!0 ◁ box (option (ref α ty))])%TC);
      [iIntros (k)|iIntros "/= !#"; iIntros (k arg); inv_vec arg=>r]; simpl_subst; last first.
    { iApply type_delete; [solve_typing..|].
      iApply (type_jump [_]); solve_typing. }
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|].
    iIntros (x' tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]; try done.
    iDestruct "Hx'" as (β γ) "#[Hαβ Hinv]".
    rewrite {1}/elctx_interp big_sepL_singleton.
    iMod (lft_incl_acc with "Hαβ HE") as (qβ) "[[Hβtok1 Hβtok2] Hclose]". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok1 Hna") as "(INV & Hna & Hclose')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hst)". wp_read. wp_let. wp_op=>?; wp_if.
    - iMod ("Hclose'" with "[Hlx Hownst Hst] Hna") as "[Hβtok1 Hna]";
        first by iExists st; iFrame.
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]%TC
              with "[] LFT Hna >[Hclose Hβtok1 Hβtok2] HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_assign_unit [unit; ref α ty]); [solve_typing..|]; first last.
      simpl. iApply (type_jump [_]); solve_typing.
    - wp_op. wp_write. wp_apply wp_new; [done..|].
      iIntros (lref vl) "(EQ & H† & Hlref)". iDestruct "EQ" as %?%(inj Z.of_nat 2%nat).
      destruct vl as [|?[|?[]]]; try done. wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      iAssert (∃ qν ν, (qβ / 2).[β] ∗ (qν).[ν] ∗
                       ty_shr ty (β ⊓ ν) tid (shift_loc lx 1) ∗
                       own γ (◯ reading_st qν ν) ∗ refcell_inv tid lx γ β ty)%I
        with ">[Hlx Hownst Hst Hβtok2]" as (q' ν) "(Hβtok2 & Hν & Hshr & Hreading & INV)".
      { destruct st as [[agν [|[q n]|]]|]; try done.
        - iDestruct "Hst" as (ν) "(Hag & H† & #Hshr & Hst)".
          iDestruct "Hst" as (q') "(#Hqq' & [Hν1 Hν2])".
          iExists _, _. iFrame "Hν1". iDestruct "Hag" as %Hag. iDestruct "Hqq'" as %Hqq'.
          iMod (own_update with "Hownst") as "[Hownst ?]".
          { apply auth_update_alloc,
            (op_local_update_discrete _ _ (reading_st (q'/2)%Qp ν))=>-[Hagv _].
            split; [|split].
            - by rewrite /= -Hag agree_idemp.
            - change ((q'/2+q)%Qp ≤ 1%Qp)%Qc. rewrite -Hqq' comm -{2}(Qp_div_2 q').
              apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (q'/2)%Qp).
              apply Qcplus_le_mono_r, Qp_ge_0.
            - done. }
          iFrame "∗#". iExists _. rewrite Z.add_comm /=. iFrame. iExists _. iFrame.
          iSplitR; first by rewrite /= Hag agree_idemp. iFrame "Hshr". iExists _. iFrame.
          rewrite (comm Qp_plus) (assoc Qp_plus) Qp_div_2 (comm Qp_plus). auto.
        - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
          iMod (own_update with "Hownst") as "[Hownst Hreading]"; first by apply
            auth_update_alloc, (op_local_update_discrete _ _ (reading_st (1/2)%Qp ν)).
          rewrite right_id. iExists _, _. iFrame "Htok1 Hreading".
          iDestruct (lft_intersect_acc with "Hβtok2 Htok2") as (q) "[Htok Hclose]".
          iApply (fupd_mask_mono (↑lftN)); first done.
          iMod (rebor _ _ (β ⊓ ν) with "LFT [] Hst") as "[Hst Hh]". done.
          { iApply lft_intersect_incl_l. }
          iMod (ty_share with "LFT Hst Htok") as "[#Hshr Htok]". done. iFrame "Hshr".
          iDestruct ("Hclose" with "Htok") as "[$ Htok2]". iExists _. iFrame.
          iExists _. iSplitR; first done. iFrame "Hshr". iSplitR "Htok2".
          + iIntros "!> Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro.
            iNext. iMod "Hν". iApply "Hh". rewrite -lft_dead_or. auto.
          + iExists _. iFrame. by rewrite Qp_div_2. }
      iMod ("Hclose'" with "[$INV] Hna") as "[Hβtok1 Hna]".
      iApply (type_type  _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (ref α ty)]%TC
              with "[] LFT Hna >[Hclose Hβtok1 Hβtok2] HL Hk");
        first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. iExists _, _, _, _, _. iFrame "∗#". iApply ty_shr_mono; try by auto.
        iApply lft_intersect_mono. done. iApply lft_incl_refl. }
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_memcpy [unit; ref α ty]); [solve_typing..|].
      simpl. iApply type_delete; [solve_typing..|].
      iApply (type_jump [_]); solve_typing.
  Qed.

  (* Unique borrowing. *)
  Definition refcell_try_borrow_mut : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #3 ] in
      let: "x'" := !"x" in
      let: "n" := !"x'" in
      if: "n" = #0 then
        "x'" <- #(-1);;
        let: "ref" := new [ #2 ] in
        "ref" <- "x'" +ₗ #1;;
        "ref" +ₗ #1 <- "x'";;
        "r" <-{2,Σ 1} !"ref";;
        delete [ #2; "ref"];;
        "k" ["r"]
      else
        "r" <-{Σ 0} ();;
        "k" ["r"]
      cont: "k" ["r"] :=
        delete [ #1; "x"];; "return" ["r"].

  Lemma refcell_try_borrow_mut_type ty :
    typed_val refcell_try_borrow_mut
              (fn(∀ α, [α]; &shr{α}(refcell ty)) → option (refmut α ty))%T.
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_cont [_] [] (λ r, [x ◁ box (&shr{α} refcell ty);
                                    r!!!0 ◁ box (option (refmut α ty))]%TC));
      [iIntros (k)|iIntros "/= !#"; iIntros (k arg); inv_vec arg=>r];
      simpl_subst; last first.
    { iApply type_delete; [solve_typing..|].
      iApply (type_jump [_]); solve_typing. }
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|].
    iIntros (x' tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]; try done.
    iDestruct "Hx'" as (β γ) "#[Hαβ Hinv]".
    rewrite {1}/elctx_interp big_sepL_singleton.
    iMod (lft_incl_acc with "Hαβ HE") as (qβ) "[Hβtok Hclose]". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok Hna") as "(INV & Hna & Hclose')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hb)". wp_read. wp_let. wp_op=>?; wp_if.
    - wp_write. wp_apply wp_new; [done..|].
      iIntros (lref vl) "(EQ & H† & Hlref)". iDestruct "EQ" as %?%(inj Z.of_nat 2%nat).
      destruct vl as [|?[|?[]]]; try done. wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      destruct st as [[?[|[]|]]|]; try done.
      iMod (lft_create with "LFT") as (ν) "[Htok #Hhν]". done.
      iMod (own_update with "Hownst") as "[Hownst ?]".
      { by eapply auth_update_alloc, (op_local_update_discrete _ _ (writing_st ν)). }
      iApply fupd_wp. iApply (fupd_mask_mono (↑lftN)); first done.
      iMod (rebor _ _ (β ⊓ ν) with "LFT [] Hb") as "[Hb Hbh]". done.
      { iApply lft_intersect_incl_l. }
      iModIntro. iMod ("Hclose'" with "[Hlx Hownst Hbh] Hna") as "[Hβtok Hna]".
      { iExists _. iFrame. iExists ν. iSplit; first by auto. iNext. iSplitL; last by auto.
        iIntros "Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro. iNext. iMod "Hν".
        iApply "Hbh". rewrite -lft_dead_or. auto. }
      iApply (type_type _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (refmut α ty)]%TC
              with "[] LFT Hna >[Hclose Hβtok] HL Hk"); first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. iExists _, _, _, _. iFrame "#∗". iApply (bor_shorten with "[] [$Hb]").
        iApply lft_intersect_mono; first done. iApply lft_incl_refl. }
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_memcpy [unit; refmut α ty]); [solve_typing..|].
      simpl. iApply type_delete; [solve_typing..|].
      iApply (type_jump [_]); solve_typing.
    - iMod ("Hclose'" with "[Hlx Hownst Hb] Hna") as "[Hβtok Hna]";
        first by iExists st; iFrame.
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]%TC
              with "[] LFT Hna >[Hclose Hβtok] HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_assign_unit [unit; refmut α ty]); [solve_typing..|].
      simpl. iApply (type_jump [_]); solve_typing.
  Qed.
End refcell_functions.
