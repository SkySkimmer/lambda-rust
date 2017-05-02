From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section code.
  Context `{typeG Σ}.

  Definition take ty (f : val) : val :=
    funrec: <> ["x"; "env"] :=
      let: "x'" := !"x" in
      let: "f" := f in
      letalloc: "t" <-{ty.(ty_size)} !"x'" in
      letcall: "r" := "f" ["env"; "t"]%E in
      Endlft;;
      "x'" <-{ty.(ty_size)} !"r";;
      delete [ #1; "x"];;  delete [ #ty.(ty_size); "r"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma take_type ty envty f `{!TyWf ty, !TyWf envty} :
    typed_val f (fn(∅; envty, ty) → ty) →
    typed_val (take ty f) (fn(∀ α, ∅; &uniq{α} ty, envty) → unit).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros (α ϝ ret arg).
      inv_vec arg=>x env. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (x'); simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]; iIntros (f'); simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|]; iIntros (t); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk (Ht & Hf' & Hx & Hx' & Henv & _)".
    rewrite !tctx_hasty_val [[x]]lock [[f']]lock [[env]]lock.
    iDestruct (ownptr_uninit_own with "Ht") as (tl tvl) "(% & >Htl & Htl†)". subst t. simpl.
    destruct x' as [[|lx'|]|]; try done. simpl.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose1)"; [solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (qϝ) "(Hϝ & HL & Hclose2)"; [solve_typing..|].
    iMod (bor_acc with "LFT Hx' Hα") as "[Hx' Hclose3]"; first done.
    iDestruct (heap_mapsto_ty_own with "Hx'") as (x'vl) "[>Hx'↦ Hx'vl]".
    wp_apply (wp_memcpy with "[$Htl $Hx'↦]"); [by auto using vec_to_list_length..|].
    iIntros "[Htl Hx'↦]". wp_seq.
    (* Prepare the lifetime, call the function.
       In principle, we could try to make the β we create here the ϝ of the called
       function, but that seems to actually be more work because we could not use
       the lemmas proven in function.v. *)
    iMod (lft_create with "LFT") as (β) "[Hβ Hβ†]"; first done.
    iMod (bor_create with "LFT Hϝ") as "[Hβϝ Hβ†ϝ]"; first done.
    iDestruct (frac_bor_lft_incl β ϝ with "LFT [>Hβϝ]") as "#Hβϝ".
    { iApply (bor_fracture with "LFT"); first done. by rewrite Qp_mult_1_r. }
    match goal with | |- context [(WP (_ [?k']) {{_, _}})%I] =>
      assert (∃ k, to_val k' = Some k) as [k EQk] by (eexists; solve_to_val) end.
    iApply (wp_let' _ _ _ _ k _ EQk). simpl_subst. iNext.
    iApply (type_type ((β ⊑ₑ ϝ) :: _) [β ⊑ₗ []]
        [k ◁cont(_, λ x:vec val 1, [ x!!!0 ◁ box ty])]
        [ f' ◁ fn(∅; envty, ty) → ty; #tl ◁ box ty; env ◁ box envty ]
       with "[] LFT [] Hna [Hβ Hβ†] [-Hf' Htl Htl† Hx'vl Henv]"); swap 1 3; swap 4 5.
    { rewrite /llctx_interp. iSplitL; last done. (* FIXME: iSplit should work as one side is 'True', thus persistent. *)
      iExists β. simpl. iSplit; first by rewrite left_id. iFrame "∗#". }
    { iSplitL; last iApply "HE". iExact "Hβϝ". }
    { iApply (type_call ()); solve_typing. (* This is showing that the lifetime bounds of f' are satisfied. *) }
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists _. iFrame. }
    (* Prove the continuation of the function call. *)
    iIntros (? ->%elem_of_list_singleton arg) "Hna Hβ". inv_vec arg=>r.
    iIntros "[Hr _]". rewrite tctx_hasty_val /=.
    iDestruct (ownptr_own with "Hr") as (lr rvl) "(% & Hlr & Hrvl & Hlr†)". subst r.
    apply of_to_val in EQk. rewrite EQk. iApply wp_rec; try (done || apply _).
    { repeat econstructor. } simpl_subst. iNext.
    iDestruct "Hβ" as "[Hβ _]". iDestruct "Hβ" as (Λ) "(% & Hβ & #Hβ†)".
    simpl in *. subst β. rewrite (left_id static). iSpecialize ("Hβ†" with "Hβ").
    wp_bind Endlft. iApply wp_mask_mono; last iApply (wp_step_fupd with "Hβ†"); auto with ndisj.
    wp_seq. iIntros "#Hβ† !>". wp_seq.
    wp_apply (wp_memcpy with "[$Hx'↦ $Hlr]"); [by auto using vec_to_list_length..|].
    iIntros "[Hlx' Hlr]". wp_seq. iMod ("Hβ†ϝ" with "Hβ†") as ">Hϝ".
    iMod ("Hclose3" with "[Hlx' Hrvl]") as "[Hlx' Hα]".
    { iExists _. iFrame. }
    iMod ("Hclose2" with "Hϝ HL") as "HL".
    iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ _; #lr ◁ box (uninit ty.(ty_size)) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists _. rewrite uninit_own. iFrame. auto using vec_to_list_length. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply (type_new _); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End code.
