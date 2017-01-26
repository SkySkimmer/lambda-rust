From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.refcell Require Import refcell ref refmut.
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
    typed_instruction_ty [] [] [] (refcell_new ty)
        (fn (λ _, []) (λ _, [# ty]) (λ _:(), refcell ty)).
  Proof.
    apply type_fn; [apply _..|]. move=>/= _ ret arg. inv_vec arg=>x. simpl_subst.
    eapply type_new; [solve_typing..|].
    iIntros (r) "!# * #HEAP #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite (Nat2Z.id (S ty.(ty_size))) tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]".
    destruct x as [[|lx|]|]; try iDestruct "Hx" as "[]". iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as (vl) "[Hx↦ Hx]".
    destruct r as [[|lr|]|]; try iDestruct "Hr" as "[]". iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own.
    iDestruct "Hr" as "[Hr↦ >SZ]". destruct vl' as [|]; iDestruct "SZ" as %[=].
    rewrite heap_mapsto_vec_cons. iDestruct "Hr↦" as "[Hr↦0 Hr↦1]". wp_op.
    rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_bind (_ <-{_} !_)%E. iApply (wp_memcpy with "[$HEAP $Hr↦1 $Hx↦]"); [done||lia..|].
    iIntros "!> [Hr↦1 Hx↦]". wp_seq.
    iApply (type_delete _ _ [ #lx ◁ box (uninit (ty_size ty)); #lr ◁ box (refcell ty)]%TC
        with "HEAP LFT Hna HE HL Hk [-]"); [solve_typing..| |]; last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      - iExists _. rewrite uninit_own. auto.
      - iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame. auto. }
    eapply (type_jump [ #_]); solve_typing.
  Qed.

  (* The other direction: getting ownership out of a refcell. *)
  Definition refcell_into_inner ty : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #ty.(ty_size)] in
      "r" <-{ty.(ty_size)} !"x" +ₗ #1;;
       delete [ #(S ty.(ty_size)) ; "x"];; "return" ["r"].

  Lemma refcell_into_inner_type ty :
    typed_instruction_ty [] [] [] (refcell_into_inner ty)
        (fn (λ _, []) (λ _, [# refcell ty]) (λ _:(), ty)).
  Proof.
    apply type_fn; [apply _..|]. move=>/= _ ret arg. inv_vec arg=>x. simpl_subst.
    eapply type_new; [solve_typing..|].
    iIntros (r) "!# * #HEAP #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite (Nat2Z.id (ty.(ty_size))) tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]". destruct x as [[|lx|]|]; try iDestruct "Hx" as "[]".
    iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[]|]vl]) "[Hx↦ Hx]"; try iDestruct "Hx" as ">[]".
    destruct r as [[|lr|]|]; try iDestruct "Hr" as "[]". iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own heap_mapsto_vec_cons.
    iDestruct "Hr" as "[Hr↦ >%]". iDestruct "Hx↦" as "[Hx↦0 Hx↦1]". wp_op.
    iDestruct "Hx" as "[% Hx]". iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_bind (_ <-{_} !_)%E. iApply (wp_memcpy with "[$HEAP $Hr↦ $Hx↦1]"); [done||lia..|].
    iIntros "!> [Hr↦ Hx↦1]". wp_seq.
    iApply (type_delete _ _ [ #lx ◁ box (uninit (S (ty_size ty))); #lr ◁ box ty]%TC
        with "HEAP LFT Hna HE HL Hk [-]"); [solve_typing..| |]; last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iSplitR "Hr↦ Hx".
      - iExists (_::_). rewrite heap_mapsto_vec_cons uninit_own -Hsz. iFrame. auto.
      - iExists vl. iFrame. }
    eapply (type_jump [ #_]); solve_typing.
  Qed.

  Definition refcell_get_mut : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      "x" <- "x'" +ₗ #1;;
      "return" ["x"].

  Lemma refcell_get_mut_type ty :
    typed_instruction_ty [] [] [] refcell_get_mut
        (fn (λ α, [☀α])%EL (λ α, [# &uniq{α} (refcell ty)])%T (λ α, &uniq{α} ty)%T).
  Proof.
    apply type_fn; [apply _..|]. move=>/= α ret arg. inv_vec arg=>x. simpl_subst.
    eapply type_deref; [solve_typing..|by eapply read_own_move|done|]=>x'. simpl_subst.
    iIntros "!# * #HEAP #LFT Hna HE HL HC HT".
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
    destruct x as [[|lx|]|]; try iDestruct "Hx" as "[]". iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as (vl) "[Hx↦ Hx]". rewrite uninit_own. wp_op.
    iApply (type_assign _ _ _ _
            [ #lx ◁ box (uninit 1); #(shift_loc lx' 1) ◁ &uniq{α}ty]%TC
            with "HEAP LFT Hna HE HL HC [-]");
      [solve_typing..|by apply write_own| |]; last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iNext. iExists _. rewrite uninit_own. iFrame. }
    eapply (type_jump [ #_]); solve_typing.
  Qed.

  (* Shared borrowing. *)
  Definition refcell_try_borrow : val :=
    funrec: <> ["x"] :=
      let: "r" := new [ #3 ] in
      let: "x'" := !"x" in
      let: "n" := !"x'" in
      if: "n" ≤ #-1 then
        "r" <-{Σ 1} ();;
        "k" ["r"]
      else
        "x'" <- "n" + #1;;
        let: "ref" := new [ #2 ] in
        "ref" <- "x'" +ₗ #1;;
        "ref" +ₗ #1 <- "x'";;
        "r" <-{2,Σ 0} !"ref";;
        delete [ #2; "ref"];;
        "k" ["r"]
      cont: "k" ["r"] :=
        delete [ #1; "x"];; "return" ["r"].

  Lemma refcell_try_borrow_type ty :
    typed_instruction_ty [] [] [] refcell_try_borrow
        (fn (λ α, [☀α])%EL (λ α, [# &shr{α}(refcell ty)]%T) (λ α, Σ[ref α ty; unit])%T).
  Proof.
    apply type_fn; [apply _..|]. move=>/= α ret arg. inv_vec arg=>x. simpl_subst.
    eapply (type_cont [_] [] (λ r, [x ◁ box (&shr{α} refcell ty);
                                    r!!!0 ◁ box Σ[ref α ty; unit]])%TC);
      [solve_typing..|intros k|move=>/= k arg; inv_vec arg=>r]; simpl_subst; last first.
    { eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing. }
    eapply type_new; [solve_typing..|]=>r. simpl_subst.
    eapply type_deref; [solve_typing..|apply read_own_copy, _|done|].
    iIntros (x') "!# * #HEAP #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)".
    destruct x' as [[|lx|]|]; try iDestruct "Hx'" as "[]".
    iDestruct "Hx'" as (β γ) "#[Hαβ Hinv]".
    rewrite {1}/elctx_interp big_sepL_singleton.
    iMod (lft_incl_acc with "Hαβ HE") as (qβ) "[[Hβtok1 Hβtok2] Hclose]". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok1 Hna") as "(INV & Hna & Hclose')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hst)". wp_read. wp_let. wp_op=>?; wp_if.
    - iMod ("Hclose'" with "[Hlx Hownst Hst] Hna") as "[Hβtok1 Hna]";
        first by iExists st; iFrame.
      iAssert (elctx_interp [☀α] qE)%I with ">[Hclose Hβtok1 Hβtok2]" as "HE".
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_assign_unit [ref α ty; unit] _ _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]%TC
              with "HEAP LFT Hna HE HL Hk");
        [solve_typing..|by eapply write_own|done| |]; first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      simpl. eapply (type_jump [_]); solve_typing.
    - wp_op. wp_write. wp_bind (new _). iApply wp_new; [done..|]. iNext.
      iIntros (lref vl) "(EQ & H† & Hlref)". iDestruct "EQ" as %?%(inj Z.of_nat 2%nat).
      destruct vl as [|?[|?[]]]; try done. wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      iAssert (∃ qν ν, (qβ / 2).[β] ∗ (qν).[ν] ∗
                       ty_shr ty (β ∪ ν) tid (shift_loc lx 1) ∗
                       own γ (◯ reading_st qν ν) ∗ refcell_inv tid lx γ β ty)%I
        with ">[Hlx Hownst Hst Hβtok2]" as (q' ν) "(Hβtok2 & Hν & Hshr & Hreading & INV)".
      { destruct st as [[|[[agν q] n]|]|]; try done.
        - iDestruct "Hst" as (q' ν) "(Hag & #Hqq' & [Hν1 Hν2] & #Hshr & H†)".
          iExists _, _. iFrame "Hν1". iDestruct "Hag" as %Hag. iDestruct "Hqq'" as %Hqq'.
          iMod (own_update with "Hownst") as "[Hownst ?]".
          { apply auth_update_alloc,
               (op_local_update_discrete _ _ (reading_st (q'/2)%Qp ν))=>-[[Hagv _]_].
            split; [split|].
            - by rewrite -Hag /= agree_idemp.
            - change ((q'/2+q)%Qp ≤ 1%Qp)%Qc. rewrite -Hqq' comm -{2}(Qp_div_2 q').
              apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (q'/2)%Qp).
              apply Qcplus_le_mono_r, Qp_ge_0.
            - done. }
          iFrame "∗#". iExists _. rewrite Z.add_comm /=. iFrame. iExists _, _. iFrame.
          rewrite /= Hag agree_idemp (comm Qp_plus) (assoc Qp_plus) Qp_div_2
                  (comm Qp_plus). auto.
        - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
          iMod (own_update with "Hownst") as "[Hownst Hreading]"; first by apply
            auth_update_alloc, (op_local_update_discrete _ _ (reading_st (1/2)%Qp ν)).
          rewrite right_id. iExists _, _. iFrame "Htok1 Hreading".
          iDestruct (lft_glb_acc with "Hβtok2 Htok2") as (q) "[Htok Hclose]".
          iMod (rebor _ _ (β ∪ ν) with "LFT [] Hst") as "[Hst Hh]". done.
          { iApply lft_le_incl. apply gmultiset_union_subseteq_l. }
          iMod (ty_share with "LFT Hst Htok") as "[#Hshr Htok]". done. iFrame "Hshr".
          iDestruct ("Hclose" with "Htok") as "[$ Htok2]". iExists _. iFrame.
          iExists _, _. iFrame. rewrite Qp_div_2. iSplitR; first done. iSplitR; first done.
          iIntros "{$Hshr} !> Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro.
          iNext. iMod "Hν". iApply "Hh". rewrite -lft_dead_or. auto. }
      iMod ("Hclose'" with "[$INV] Hna") as "[Hβtok1 Hna]".
      iAssert (elctx_interp [☀α] qE)%I with ">[Hclose Hβtok1 Hβtok2]" as "HE".
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_memcpy [ref α ty; unit] _ _ _ _ _ _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (ref α ty)]%TC
              with "HEAP LFT Hna HE HL Hk");
        [solve_typing..|by eapply write_own|by eapply read_own_move|done|done| |];
        first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. iExists _, _, _, _, _. iFrame "∗#". iApply ty_shr_mono; try by auto.
        iApply lft_glb_mono. done. iApply lft_incl_refl. }
      simpl. eapply type_delete; [solve_typing..|]. eapply (type_jump [_]); solve_typing.
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
        "r" <-{2,Σ 0} !"ref";;
        delete [ #2; "ref"];;
        "k" ["r"]
      else
        "r" <-{Σ 1} ();;
        "k" ["r"]
      cont: "k" ["r"] :=
        delete [ #1; "x"];; "return" ["r"].

  Lemma refcell_try_borrow_mut_type ty :
    typed_instruction_ty [] [] [] refcell_try_borrow_mut
        (fn (λ α, [☀α])%EL (λ α, [# &shr{α}(refcell ty)]%T) (λ α, Σ[refmut α ty; unit])%T).
  Proof.
    apply type_fn; [apply _..|]. move=>/= α ret arg. inv_vec arg=>x. simpl_subst.
    eapply (type_cont [_] [] (λ r, [x ◁ box (&shr{α} refcell ty);
                                    r!!!0 ◁ box Σ[refmut α ty; unit]])%TC);
      [solve_typing..|intros k|move=>/= k arg; inv_vec arg=>r]; simpl_subst; last first.
    { eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing. }
    eapply type_new; [solve_typing..|]=>r. simpl_subst.
    eapply type_deref; [solve_typing..|apply read_own_copy, _|done|].
    iIntros (x') "!# * #HEAP #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)".
    destruct x' as [[|lx|]|]; try iDestruct "Hx'" as "[]".
    iDestruct "Hx'" as (β γ) "#[Hαβ Hinv]".
    rewrite {1}/elctx_interp big_sepL_singleton.
    iMod (lft_incl_acc with "Hαβ HE") as (qβ) "[Hβtok Hclose]". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok Hna") as "(INV & Hna & Hclose')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hst)". wp_read. wp_let. wp_op=>?; wp_if.
    - wp_write. wp_bind (new _). iApply wp_new; [done..|]. iNext.
      iIntros (lref vl) "(EQ & H† & Hlref)". iDestruct "EQ" as %?%(inj Z.of_nat 2%nat).
      destruct vl as [|?[|?[]]]; try done. wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      destruct st as [[|[[]]|]|]; try done.
      iMod (own_update with "Hownst") as "[Hownst ?]".
      { apply auth_update_alloc, (op_local_update_discrete _ _ writing_st)=>//. }
      iMod ("Hclose'" with "[Hlx Hownst] Hna") as "[Hβtok Hna]";
        first by iExists _; iFrame.
      iAssert (elctx_interp [☀α] qE)%I with ">[Hclose Hβtok]" as "HE".
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_memcpy [refmut α ty; unit] _ _ _ _ _ _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (refmut α ty)]%TC
              with "HEAP LFT Hna HE HL Hk");
        [solve_typing..|by eapply write_own|by eapply read_own_move|done|done| |];
        first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. iExists _, _, _. iFrame "∗#". }
      simpl. eapply type_delete; [solve_typing..|]. eapply (type_jump [_]); solve_typing.
    - iMod ("Hclose'" with "[Hlx Hownst Hst] Hna") as "[Hβtok Hna]";
        first by iExists st; iFrame.
      iAssert (elctx_interp [☀α] qE)%I with ">[Hclose Hβtok]" as "HE".
      { rewrite {1}/elctx_interp big_sepL_singleton /=. iApply "Hclose". by iFrame. }
      iApply (type_sum_assign_unit [refmut α ty; unit] _ _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]%TC
              with "HEAP LFT Hna HE HL Hk");
        [solve_typing..|by eapply write_own|done| |]; first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      simpl. eapply (type_jump [_]); solve_typing.
  Qed.
End refcell_functions.
