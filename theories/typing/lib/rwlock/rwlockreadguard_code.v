From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import lifetime na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.rwlock Require Import rwlock rwlockreadguard.
Set Default Proof Using "Type".

Section rwlockreadguard_functions.
  Context `{typeG Σ, rwlockG Σ}.

  (* Turning a rwlockreadguard into a shared borrow. *)
  Definition rwlockreadguard_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" +ₗ #1 in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma rwlockreadguard_deref_type ty :
    typed_val rwlockreadguard_deref
      (fn (fun '(α, β) => FP [# &shr{α}(rwlockreadguard β ty)]
                             (&shr{α}ty) [α; β; α ⊑ β]%EL)).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (l') "#[Hfrac Hshr]".
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "(Hα & Hβ & #Hαβ)".
    iMod (frac_bor_acc with "LFT Hfrac Hα") as (qlx') "[H↦ Hcloseα]". done.
    rewrite heap_mapsto_vec_singleton. wp_read. wp_op. wp_let.
    iMod ("Hcloseα" with "[$H↦]") as "Hα".
    iApply (type_type _ _ _ [ x ◁ box (&shr{α} rwlockreadguard β ty);
                              #(shift_loc l' 1) ◁ &shr{α}ty]%TC
      with "[] LFT Hna [Hα Hβ Hαβ] HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr"). iApply lft_incl_glb. done.
      iApply lft_incl_refl. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.

  (* Dropping a rwlockreadguard and releasing the corresponding lock. *)
  Definition rwlockreadguard_drop : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      ("loop" []
       cont: "loop" [] :=
         let: "n" := !ˢᶜ"x'" in
         if: CAS "x'" "n" ("n" - #1) then
           delete [ #1; "x"];;
           let: "r" := new [ #0] in "return" ["r"]
         else "loop" []).

  Lemma rwlockreadguard_drop_type ty :
    typed_val rwlockreadguard_drop
              (fn(∀ α, [α]; rwlockreadguard α ty) → unit).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|].
      iIntros (x'). simpl_subst.
    iApply (type_cont [] [] (λ _, [x ◁ _; x' ◁ _])%TC);
      [iIntros (loop)|iIntros "/= !#"; iIntros (loop arg); inv_vec arg];
      simpl_subst.
    { iApply (type_jump []); solve_typing. }
    iIntros (tid qE) "#LFT Hna Hα HL Hk HT".
    rewrite {1}/elctx_interp big_sepL_singleton tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    destruct x' as [[|lx'|]|]; try done. simpl.
    iDestruct "Hx'" as (ν q γ β) "(Hx' & #Hαβ & #Hinv & Hν & H◯ & H†)".
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    wp_bind (!ˢᶜ#lx')%E.
    iMod (shr_bor_acc_tok with "LFT Hinv Hβ") as "[INV Hcloseβ]"; [done..|].
    iDestruct "INV" as (st) "[H↦ INV]". wp_read.
    iMod ("Hcloseβ" with "[H↦ INV]") as "Hβ"; first by iExists _; iFrame.
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _).
    iMod (shr_bor_acc_tok with "LFT Hinv Hβ") as "[INV Hcloseβ]"; [done..|].
    iDestruct "INV" as (st') "(Hlx & >H● & Hst)".
    destruct (decide (Z_of_rwlock_st st = Z_of_rwlock_st st')) as [->|?].
    + iAssert (|={⊤ ∖ ↑rwlockN,⊤ ∖ ↑rwlockN ∖ ↑lftN}▷=>
               (lx' ↦ #(Z_of_rwlock_st st'-1) ==∗ rwlock_inv tid lx' γ β ty))%I
        with "[H● H◯ Hx' Hν Hst H†]" as "INV".
      { iDestruct (own_valid_2 with "H● H◯") as %[[[=]| (? & st0 & [=<-] & -> & [Heq|Hle])]
           %option_included Hv]%auth_valid_discrete_2.
        - destruct st0 as [|[[agν q']n]|]; try by inversion Heq. revert Heq. simpl.
          intros [[EQ <-%leibniz_equiv]%(inj2 pair) <-%leibniz_equiv]
                 %(inj Cinr)%(inj2 pair).
          iDestruct "Hst" as (ν' q') "(>EQν & _ & Hh & _ & >Hq & >Hν')".
          rewrite -EQ. iDestruct "EQν" as %<-%(inj to_agree)%leibniz_equiv.
          iCombine "Hν" "Hν'" as "Hν". iDestruct "Hq" as %->.
          iApply (step_fupd_mask_mono (↑lftN ∪ (⊤ ∖ ↑rwlockN ∖ ↑lftN)));
            last iApply (step_fupd_mask_frame_r _ ∅); [try set_solver..|];
            [apply union_least; solve_ndisj|].
          iMod ("H†" with "Hν") as "H†". iModIntro. iNext. iMod "H†".
          iMod ("Hh" with "H†") as "Hb". iIntros "!> Hlx". iExists None. iFrame.
          iApply (own_update_2 with "H● H◯"). apply auth_update_dealloc.
          rewrite -(right_id None op (Some _)). apply cancel_local_update_empty, _.
        - iApply step_fupd_intro. set_solver. iNext. iIntros "Hlx".
          apply csum_included in Hle.
          destruct Hle as [|[(?&?&[=]&?)|(?&[[agν q']n]&[=<-]&->&Hle%prod_included)]];
            [by subst|].
          destruct Hle as [[Hag [q0 Hq]]%prod_included Hn%pos_included].
          iDestruct "Hst" as (ν' q'') "(EQν & H†' & Hh & Hshr & Hq & Hν')".
          iDestruct "EQν" as %EQν. revert Hag Hq. rewrite /= EQν to_agree_included.
          intros <-%leibniz_equiv ->%leibniz_equiv.
          iExists (Some (Cinr (to_agree ν, q0, Pos.pred n))).
          iSplitL "Hlx"; first by destruct n.
          replace (q ⋅ q0 + q'')%Qp with (q0 + (q + q''))%Qp by
              by rewrite (comm _ q q0) assoc. iCombine "Hν" "Hν'" as "Hν".
          iSplitL "H● H◯"; last by eauto with iFrame.
          iApply (own_update_2 with "H● H◯"). apply auth_update_dealloc.
          assert (n = 1%positive ⋅ Pos.pred n) as EQn.
          { rewrite pos_op_plus -Pplus_one_succ_l Pos.succ_pred // =>?. by subst. }
          rewrite {1}EQn -{1}(agree_idemp (to_agree _)) -2!pair_op -Cinr_op Some_op.
          apply (cancel_local_update_empty (reading_st q ν)) , _. }
      iApply (wp_fupd_step with "INV"). done. set_solver.
      iApply (wp_cas_int_suc with "Hlx"); try done. iNext. iIntros "Hlx INV !>".
      iMod ("INV" with "Hlx") as "INV". iMod ("Hcloseβ" with "[$INV]") as "Hβ".
      iMod ("Hcloseα" with "Hβ") as "HE". iApply (wp_if _ true). iIntros "!>!>".
      iApply (type_type _ _ _ [ x ◁ box (uninit 1)]%TC
              with "[] LFT Hna [HE] HL Hk"); first last.
      { rewrite tctx_interp_singleton tctx_hasty_val //. }
      { rewrite /elctx_interp big_sepL_singleton //. }
      iApply type_delete; [solve_typing..|].
      iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_jump [_]); solve_typing.
    + iApply (wp_cas_int_fail with "Hlx"); try done. iNext. iIntros "Hlx".
      iMod ("Hcloseβ" with "[Hlx H● Hst]") as "Hβ". by iExists _; iFrame.
      iMod ("Hcloseα" with "Hβ") as "HE". iApply (wp_if _ false). iIntros "!> !>".
      iApply (type_type _ _ _ [ x ◁ box (uninit 1); #lx' ◁ rwlockreadguard α ty]%TC
              with "[] LFT Hna [HE] HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val
                tctx_hasty_val' //. iFrame. iExists _, _, _, _. iFrame "∗#". }
      { rewrite /elctx_interp big_sepL_singleton //. }
      iApply (type_jump []); solve_typing.
  Qed.
End rwlockreadguard_functions.
