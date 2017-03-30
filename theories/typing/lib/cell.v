From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section cell.
  Context `{typeG Σ}.

  Program Definition cell (ty : type) :=
    {| ty_size := ty.(ty_size);
       ty_own := ty.(ty_own);
       ty_shr κ tid l := (&na{κ, tid, shrN.@l}l ↦∗: ty.(ty_own) tid)%I |}.
  Next Obligation. apply ty_size_eq. Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hown $". by iApply (bor_na with "Hown").
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#H⊑ H". by iApply (na_bor_shorten with "H⊑").
  Qed.

  Global Instance cell_wf ty `{!TyWf ty} : TyWf (cell ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Global Instance cell_type_ne : TypeNonExpansive cell.
  Proof. solve_type_proper. Qed.

  Global Instance cell_ne : NonExpansive cell.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance cell_mono E L : Proper (eqtype E L ==> subtype E L) cell.
  Proof.
    move=>?? /eqtype_unfold EQ. iIntros (?) "HL".
    iDestruct (EQ with "HL") as "#EQ". iIntros "!# #HE".
    iDestruct ("EQ" with "HE") as "(% & #Hown & #Hshr)".
    iSplit; [done|iSplit; iIntros "!# * H"].
    - iApply ("Hown" with "H").
    - iApply na_bor_iff; last done. iSplit; iIntros "!>!# H";
      iDestruct "H" as (vl) "[??]"; iExists vl; iFrame; by iApply "Hown".
  Qed.
  Lemma cell_mono' E L ty1 ty2 : eqtype E L ty1 ty2 → subtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_mono. Qed.
  Global Instance cell_proper E L : Proper (eqtype E L ==> eqtype E L) cell.
  Proof. by split; apply cell_mono. Qed.
  Lemma cell_proper' E L ty1 ty2 : eqtype E L ty1 ty2 → eqtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_proper. Qed.

  Global Instance cell_copy :
    Copy ty → Copy (cell ty).
  Proof.
    intros ty Hcopy. split; first by intros; simpl; unfold ty_own; apply _.
    iIntros (κ tid E F l q ??) "#LFT #Hshr Htl Htok". iExists 1%Qp. simpl in *.
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    destruct (ty_size ty) as [|sz] eqn:Hsz; simpl in *.
    { iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct "Hown" as (vl) "[H↦ #Hown]".
      simpl. assert (F ∖ ∅ = F) as -> by set_solver+.
      iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
      iMod ("Hclose" with "[H↦] Htl") as "[$ $]".
      { iExists vl. by iFrame. }
      iModIntro. iSplitL "".
      { iNext. iExists vl. destruct vl; last done. iFrame "Hown".
        by iApply heap_mapsto_vec_nil. }
      by iIntros "$ _". }
    (* Now we are in the non-0 case. *)
    iMod (na_bor_acc with "LFT Hshr Htok Htl") as "($ & Htl & Hclose)"; [solve_ndisj..|].
    iDestruct (na_own_acc with "Htl") as "($ & Hclose')"; first by set_solver.
    iIntros "!> Htl Hown". iPoseProof ("Hclose'" with "Htl") as "Htl".
    by iMod ("Hclose" with "Hown Htl") as "[$ $]".
  Qed.

  Global Instance cell_send :
    Send ty → Send (cell ty).
  Proof. by unfold cell, Send. Qed.
End cell.

Section typing.
  Context `{typeG Σ}.

  (* TODO RJ: Consider setting this globally. *)
  Arguments ty_own : simpl never.

  (* Constructing a cell. *)
  Definition cell_new : val := funrec: <> ["x"] := return: ["x"].

  Lemma cell_new_type ty `{!TyWf ty} : typed_val cell_new (fn(∅; ty) → cell ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_jump; [solve_typing..|].
    iIntros (??) "#LFT _ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  (* The other direction: getting ownership out of a cell. *)
  Definition cell_into_inner : val := funrec: <> ["x"] := return: ["x"].

  Lemma cell_into_inner_type ty `{!TyWf ty} :
    typed_val cell_into_inner (fn(∅; cell ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_jump; [solve_typing..|].
    iIntros (??) "#LFT _ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  Definition cell_get_mut : val :=
    funrec: <> ["x"] := return: ["x"].

  Lemma cell_get_mut_type ty `{!TyWf ty} :
    typed_val cell_get_mut (fn(∀ α, ∅; &uniq{α} (cell ty)) → &uniq{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_jump; [solve_typing..|]. rewrite /tctx_incl /=.
    iIntros (??) "_ _ $". rewrite !tctx_interp_singleton /tctx_elt_interp /=.
    by iIntros "$".
  Qed.

  (* Reading from a cell *)
  Definition cell_get ty : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      letalloc: "r" <-{ty.(ty_size)} !"x'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma cell_get_type ty `{!TyWf ty} `(!Copy ty) :
    typed_val (cell_get ty) (fn(∀ α, ∅; &shr{α} (cell ty)) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply type_letalloc_n; [solve_typing| |iIntros (r); simpl_subst].
    { apply (read_shr _ _ _ (cell ty)); solve_typing. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Writing to a cell *)
  Definition cell_replace ty : val :=
    funrec: <> ["c"; "x"] :=
      let: "c'" := !"c" in
      letalloc: "r" <-{ty.(ty_size)} !"c'" in
      "c'" <-{ty.(ty_size)} !"x";;
      delete [ #1; "c"] ;; delete [ #ty.(ty_size); "x"] ;; return: ["r"].

  Lemma cell_replace_type ty `{!TyWf ty} :
    typed_val (cell_replace ty) (fn(∀ α, ∅; &shr{α} cell ty, ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>c x. simpl_subst.
    iApply type_deref; [solve_typing..|].
    iIntros (c'); simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r); simpl_subst.
    (* Drop to Iris level. *)
    iIntros (tid) "#LFT #HE Htl HL HC".
    rewrite 3!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iIntros "(Hr & Hc & #Hc' & Hx)".
    destruct c' as [[|c'|]|]; try done. destruct x as [[|x|]|]; try done.
    destruct r as [[|r|]|]; try done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q') "(Htok & HL & Hclose1)"; [solve_typing..|].
    iMod (na_bor_acc with "LFT Hc' Htok Htl") as "(Hc'↦ & Htl & Hclose2)"; [solve_ndisj..|].
    iDestruct "Hc'↦" as (vc') "[>Hc'↦ Hc'own]".
    iDestruct (ty_size_eq with "Hc'own") as "#>%".
    iDestruct "Hr" as "[Hr↦ Hr†]". iDestruct "Hr↦" as (vr) "[>Hr↦ Hrown]".
    iDestruct (ty_size_eq with "Hrown") as ">Heq". iDestruct "Heq" as %Heq.
    (* FIXME: Changing the order of $Hr↦ $Hc'↦ breaks applying...?? *)
    wp_apply (wp_memcpy with "[$Hr↦ $Hc'↦]").
    { by rewrite Heq Nat2Z.id. }
    { f_equal. done. }
    iIntros "[Hr↦ Hc'↦]". wp_seq.
    iDestruct "Hx" as "[Hx↦ Hx†]". iDestruct "Hx↦" as (vx) "[Hx↦ Hxown]".
    rewrite Nat2Z.id. iDestruct (ty_size_eq with "Hxown") as "#%".
    wp_apply (wp_memcpy with "[$Hc'↦ $Hx↦]"); try by f_equal.
    iIntros "[Hc'↦ Hx↦]". wp_seq.
    iMod ("Hclose2" with "[Hc'↦ Hxown] Htl") as "[Htok Htl]"; first by auto with iFrame.
    iMod ("Hclose1" with "Htok HL") as "HL".
    (* Now go back to typing level. *)
    iApply (type_type _ _ _
           [c ◁ box (&shr{α} cell ty); #x ◁ box (uninit ty.(ty_size)); #r ◁ box ty]
    with "[] LFT HE Htl HL HC"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
      iFrame "Hc". rewrite !tctx_hasty_val' //. iSplitL "Hx↦ Hx†".
      - iFrame. iExists _. iFrame. iNext. iApply uninit_own. done.
      - iFrame. iExists _. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End typing.

Hint Resolve cell_mono' cell_proper' : lrust_typing.
