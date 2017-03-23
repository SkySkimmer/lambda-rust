From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import lifetime na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell ref.
Set Default Proof Using "Type".

Section ref_functions.
  Context `{typeG Σ, refcellG Σ}.

  Lemma refcell_inv_reading_inv tid l γ α ty q ν :
    refcell_inv tid l γ α ty -∗
    own γ (◯ reading_st q ν) -∗
    ∃ (q' : Qp) n, l ↦ #(Zpos n) ∗ ⌜(q ≤ q')%Qc⌝ ∗
            own γ (● Some (to_agree ν, Cinr (q', n)) ⋅ ◯ reading_st q ν) ∗
            ty.(ty_shr) (α ⊓ ν) tid (shift_loc l 1) ∗
            ((1).[ν] ={↑lftN,∅}▷=∗ &{α} shift_loc l 1 ↦∗: ty_own ty tid) ∗
            ∃ q'', ⌜(q' + q'' = 1)%Qp⌝ ∗ q''.[ν].
  Proof.
    iIntros "INV H◯".
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)".
    iAssert (∃ q' n, st ≡ Some (to_agree ν, Cinr (q', n)) ∗ ⌜q ≤ q'⌝%Qc)%I with
       "[#]" as (q' n) "[Hst %]".
    { iDestruct (own_valid_2 with "H● H◯") as %[[[=]|
       (? & [agν st'] & [=<-] & -> & [Heq|Hle])]%option_included Hv]%auth_valid_discrete_2.
      - iExists q, xH. iSplit; iPureIntro. by constructor. done.
      - iClear "∗#".
        revert Hle Hv=>/prod_included [/= /agree_included Hag /csum_included
              [-> [//] | [[?[?[//]]] | [?[[q' n] [Heq [-> Hle]]]]]]] [Hagok _].
        revert Heq. intros [= <-]. revert Hle=>/prod_included [/= Hqq' _].
        iExists q', n. iSplit.
        + iPureIntro. rewrite (agree_op_inv agν) //. by rewrite comm -Hag.
        + by revert Hqq'=>/frac_included_weak. }
    iDestruct "Hst" as %[st' [-> Hst']]%equiv_Some_inv_r'.
    destruct st' as [?[|[]|]]; destruct Hst' as [Hag Hst']; try by inversion Hst'.
    apply (inj Cinr), (inj2 pair) in Hst'.
    destruct Hst' as [<-%leibniz_equiv <-%leibniz_equiv]. simpl in *.
    setoid_rewrite <-Hag. iDestruct "INV" as (ν') "(Hag & Hν & Hshr & Hq')".
    iDestruct "Hag" as %<-%(inj to_agree)%leibniz_equiv.
    iExists q', n. rewrite own_op. by iFrame.
  Qed.

  (* Cloning a ref. We need to increment the counter. *)
  Definition ref_clone : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "rc" := !("x'" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
      letalloc: "r" <-{2} !"x'" in
      delete [ #1; "x"];; return: ["r"].

  (* FIXME : using λ instead of fun triggers an anomaly.
     See: https://coq.inria.fr/bugs/show_bug.cgi?id=5326 *)
  Lemma ref_clone_type ty :
    typed_val ref_clone
              (fn (fun '(α, β) => FP (λ ϝ, [ϝ ⊑ α; α ⊑ β]%EL)
                                     [# &shr{α}(ref β ty)]%T (ref β ty)%T)).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').

Typeclasses Opaque llctx_interp.
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hβδ & Hinv & H◯inv)".
    wp_op.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hβδ Hβ") as (qδ) "[Hδ Hcloseβ]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose')";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    iMod (na_bor_acc with "LFT Hinv Hδ Hna") as "(INV & Hna & Hcloseδ)"; [done..|].
    iMod (na_bor_acc with "LFT H◯inv Hα2 Hna") as "(H◯ & Hna & Hcloseα2)"; [solve_ndisj..|].
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iDestruct (refcell_inv_reading_inv with "INV H◯")
      as (q' n) "(H↦lrc & _ & [H● H◯] & Hshr' & H† & Hq')".
    wp_read. wp_let. wp_op. wp_write. iDestruct "Hq'" as (q'') "(Hq'q'' & Hν1 & Hν2)".
    iDestruct "Hq'q''" as %Hq'q''. iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (reading_st (q''/2)%Qp ν))=>-[Hagv _].
      split; [|split; last done].
      - by rewrite /= agree_idemp.
      - apply frac_valid'. rewrite -Hq'q'' comm -{2}(Qp_div_2 q'').
        apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (q''/2)%Qp).
        apply Qcplus_le_mono_r, Qp_ge_0. }
    wp_apply wp_new; [done..|]. iIntros (lr ?) "(%&?&Hlr)".
    iAssert (lx' ↦∗{qlx'} [ #lv; #lrc])%I  with "[H↦1 H↦2]" as "H↦".
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    wp_let. wp_apply (wp_memcpy with "[$Hlr $H↦]"); [done..|].
    iIntros "[Hlr H↦]". wp_seq. iMod ("Hcloseα2" with "[$H◯] Hna") as "[Hα1 Hna]".
    iMod ("Hcloseδ" with "[H↦lrc H● Hν1 Hshr' H†] Hna") as "[Hδ Hna]".
    { iExists _. rewrite Z.add_comm. iFrame. iExists _. iFrame. iSplitR.
      - rewrite /= agree_idemp. auto.
      - iExists _. iFrame.
        rewrite (comm Qp_plus) (assoc Qp_plus) Qp_div_2 (comm Qp_plus). auto. }
    iMod ("Hcloseβ" with "Hδ") as "Hβ". iMod ("Hcloseα1" with "[$H↦]") as "Hα2".
    iMod ("Hclose'" with "[$Hα1 $Hα2] HL") as "HL". iMod ("Hclose" with "Hβ HL") as "HL".
    iApply (type_type _ _ _
           [ x ◁ box (&shr{α} ref β ty); #lr ◁ box(ref β ty)]%TC
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      rewrite /= freeable_sz_full. iFrame. iExists _. iFrame. iExists _, _, _, _, _.
      iFrame "∗#". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a ref into a shared borrow. *)
  Definition ref_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma ref_deref_type ty :
    typed_val ref_deref
      (fn (fun '(α, β) => FP (λ ϝ, [ϝ ⊑ α; α ⊑ β]%EL)
                             [# &shr{α}(ref β ty)]%T (&shr{α}ty)%T)).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hx')".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα") as (qlx') "[H↦ Hcloseα]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iMod ("Hcloseα" with "[$H↦1 $H↦2]") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iApply (type_type _ _ _
        [ x ◁ box (&shr{α} ref β ty); #lv ◁ &shr{α}ty]%TC
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr"). iApply lft_incl_glb; last done.
      rewrite /elctx_interp. iDestruct "HE" as "(_ & $ & _)". }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Dropping a ref and decrement the count in the corresponding refcell. *)
  Definition ref_drop : val :=
    funrec: <> ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" - #1;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma ref_drop_type ty :
    typed_val ref_drop (fn(∀ α, (λ ϝ, [ϝ ⊑ α]); ref α ty) → unit).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk Hx". rewrite tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν q γ β ty') "(_ & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct (refcell_inv_reading_inv with "INV [$H◯]")
      as (q' n) "(H↦lrc & >% & H●◯ & Hshr & H† & Hq')". iDestruct "Hq'" as (q'') ">[% Hν']".
    wp_read. wp_let. wp_op. wp_write.
    iAssert (|={↑lftN,∅}▷=> refcell_inv tid lrc γ β ty')%I
      with "[H↦lrc H●◯ Hν Hν' Hshr H†]" as "INV".
    { iDestruct (own_valid with "H●◯") as %[[ _ [Heq%(inj Cinr)|Hincl%csum_included]
        %Some_included]%Some_pair_included [_ Hv]]%auth_valid_discrete_2.
      - destruct Heq as [?%leibniz_equiv ?%leibniz_equiv]. simpl in *. subst.
        iExists None. iFrame. iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
          apply cancel_local_update_empty, _. }
        iApply "H†". replace 1%Qp with (q'+q'')%Qp by naive_solver. iFrame.
      - destruct Hincl as [ [=] |[ (?&?&[=]&?) | (?&?&[=<-]&[=<-]&[[q0 n']EQ]) ]].
        destruct EQ as [?%leibniz_equiv ?%leibniz_equiv]. simpl in *. subst.
        iAssert (lrc ↦ #(Z.pos n'))%I with "[H↦lrc]" as "H↦lrc".
        { destruct n'; [|done..]. by rewrite /= Pos.pred_double_succ. }
        iExists (Some (_, Cinr (q0, n'))). iFrame. iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc.
          rewrite -(agree_idemp (to_agree _)) -pair_op -Cinr_op -pair_op Some_op.
          apply (cancel_local_update_empty (reading_st q ν)), _. }
        iExists ν. iFrame. iApply step_fupd_intro; first set_solver. iIntros "!>".
        iSplitR; first done. iExists (q+q'')%Qp. iFrame.
        by rewrite assoc (comm _ q0 q). }
    wp_bind Endlft. iApply (wp_mask_mono (↑lftN)); first done.
    iApply (wp_step_fupd with "INV"); [set_solver..|]. wp_seq.
    iIntros "INV !>". wp_seq. iMod ("Hcloseβ" with "[$INV] Hna") as "[Hβ Hna]".
    iMod ("Hcloseα" with "Hβ") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)]%TC with "[] LFT HE Hna HL Hk");
      first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the ref, typically for accessing a component. *)
  Definition ref_map : val :=
    funrec: <> ["ref"; "f"; "env"] :=
    withcont: "k":
      let: "x'" := !"ref" in
      let: "f'" := !"f" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "f'" ["env"; "x"]%E in
      let: "r'" := !"r" in
      "ref" <- "r'";;
      delete [ #1; "f"];; "k" []
    cont: "k" [] :=
      return: ["ref"].

  Lemma ref_map_type ty1 ty2 envty E :
    typed_val ref_map
      (fn(∀ β, [β]%EL ++ E;
            ref β ty1, fn(∀ α, [α]%EL ++ E; envty, &shr{α}ty1) → &shr{α}ty2, envty)
       → ref β ty2).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros (α ret arg).
       inv_vec arg=>ref f env. simpl_subst.
    iIntros (tid qE) "#LFT Hna HE HL Hk HT".
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Href & Hf & Henv)".
    destruct ref as [[|lref|]|]; try done. iDestruct "Href" as "[Href Href†]".
    iDestruct "Href" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Href";
      try iDestruct "Href" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Href" as "[[Href↦1 Href↦2] Href]".
    iDestruct "Href" as (ν qν γ β ty') "(#Hshr & #Hαβ & #Hinv & >Hν & Hγ)".
    rewrite -(freeable_sz_split _ 1 1). iDestruct "Href†" as "[Href†1 Href†2]".
    destruct (Qp_lower_bound qE qν) as (q & qE' & qν' & -> & ->).
    iDestruct (@fractional_split with "HE") as "[[Hα HE] HE']".
    iDestruct "Hν" as "[Hν Hν']".
    remember (RecV "k" [] (ret [ LitV lref])%E)%V as k eqn:EQk.
    iApply (wp_let' _ _ _ _ k). { subst. solve_to_val. } simpl_subst.
    iApply (type_type ((α ⊓ ν) :: E)%EL []
        [k ◁cont([], λ _:vec val 0, [ #lref ◁ own_ptr 2 (&shr{α ⊓ ν}ty2)])]%CC
        [ f ◁ box (fn(∀ α, [α]%EL ++ E; envty, &shr{α}ty1) → &shr{α}ty2);
          #lref ◁ own_ptr 2 (&shr{α ⊓ ν}ty1); env ◁ box envty ]%TC
       with "[] LFT Hna [$HE Hα Hν] HL [Hk HE' Hν' Href↦2 Hγ Href†2]"); first last.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
      iFrame. iApply tctx_hasty_val'. done. iFrame. iExists [_].
      rewrite heap_mapsto_vec_singleton. by iFrame. }
    { rewrite !cctx_interp_singleton /=. iIntros "HE". iIntros (args) "Hna HL HT".
      inv_vec args. subst. simpl. wp_rec. iDestruct "HE" as "[Hαν HE]".
      iDestruct (lft_tok_sep with "Hαν") as "[Hα Hν]".
      iSpecialize ("Hk" with "[$HE' $Hα $HE]").
      iApply ("Hk" $! [# #lref] with "Hna HL").
      rewrite !tctx_interp_singleton !tctx_hasty_val' //.
      iDestruct "HT" as "[Href Ḥref†2]".
      rewrite /= -(freeable_sz_split _ 1 1). iFrame.
      iDestruct "Href" as ([|[[|lv'|]|] [|]]) "[H↦ Href]"; auto.
      iExists [ #lv'; #lrc].
      rewrite (heap_mapsto_vec_cons _ _ _ [_]) !heap_mapsto_vec_singleton. iFrame.
      iExists ν, (q+qν')%Qp. eauto 10 with iFrame. }
    { rewrite /= -lft_tok_sep. iFrame. }
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (f'). simpl_subst.
    iApply type_letalloc_1; [solve_typing..|]. iIntros (x). simpl_subst.
    iApply (type_letcall); [simpl; solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (r'). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End ref_functions.
