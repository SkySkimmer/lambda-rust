From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition spawnN := lrustN .@ "spawn".

Section join_handle.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition join_inv tid (ty : type) (v : val) :=
    (box ty).(ty_own) tid [v].

  Program Definition join_handle (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>join_handle spawnN l (join_inv tid ty)
         | _ => False
         end%I;
       ty_shr κ tid l := True%I |}.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation. iIntros "* _ _ _ $". auto. Qed.
  Next Obligation. iIntros (?) "**"; auto. Qed.

  Global Instance join_handle_wf ty `{!TyWf ty} : TyWf (join_handle ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Lemma join_handle_subtype ty1 ty2 :
    ▷ type_incl ty1 ty2 -∗ type_incl (join_handle ty1) (join_handle ty2).
  Proof.
    iIntros "#Hincl". iSplit; first done. iSplit; iAlways.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      simpl. iApply (join_handle_impl with "[] Hvl"). iIntros "!# * Hown".
      iDestruct (box_type_incl with "Hincl") as "{Hincl} (_ & Hincl & _)".
      iApply "Hincl". done.
    - iIntros "* _". auto.
  Qed.

  Global Instance join_handle_mono E L :
    Proper (subtype E L ==> subtype E L) join_handle.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!# #HE". iApply join_handle_subtype. iApply "Hsub"; done.
  Qed.
  Global Instance join_handle_proper E L :
    Proper (eqtype E L ==> eqtype E L) join_handle.
  Proof. intros ??[]. by split; apply join_handle_mono. Qed.

  Global Instance join_handle_type_contractive : TypeContractive join_handle.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_dist || f_type_equiv || f_contractive || f_equiv).
  Qed.
  Global Instance join_handle_ne : NonExpansive join_handle.
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance join_handle_send ty :
    Send ty → Send (join_handle ty).
  Proof.
    iIntros (??? vl) "Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
    simpl. iApply (join_handle_impl with "[] Hvl"). iIntros "!# * Hv".
    unfold join_inv. iApply @send_change_tid. done.
  Qed.

  Global Instance join_handle_sync ty :
    Sync (join_handle ty).
  Proof.
    iIntros (????) "**". (* FIXME: Why did it throw away the assumption we should have gotten? *)
    done.
  Qed.

End join_handle.

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition spawn (call_once : val) : val :=
    funrec: <> ["f"] :=
      let: "call_once" := call_once in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "call_once" ["f":expr] in
                            finish ["c"; "r"]] in
      letalloc: "r" <- "join" in
      return: ["r"].

  Lemma spawn_type fty retty call_once `{!TyWf fty, !TyWf retty}
        `(!Send fty, !Send retty) :
    typed_val call_once (fn(∅; fty) → retty) → (* fty : FnOnce() -> retty, as witnessed by the impl call_once *)
    let E ϝ := fty.(ty_outlives_E) static ++ retty.(ty_outlives_E) static in
    typed_val (spawn call_once) (fn(E; fty) → join_handle retty).
  Proof.
    intros Hf ? E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>env. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (f'). simpl_subst.
    iApply (type_let _ _ _ _ ([f' ◁ _; env ◁ _])
                     (λ j, [j ◁ join_handle retty])); try solve_typing; [|].
    { (* The core of the proof: showing that spawn is safe. *)
      iIntros (tid) "#LFT #HE $ $ [Hf' [Henv _]]". rewrite !tctx_hasty_val [fn _]lock.
      iApply (spawn_spec _ (join_inv tid retty) with "[-]");
                              first solve_to_val; last first; last simpl_subst.
      { iIntros "!> *". rewrite tctx_interp_singleton tctx_hasty_val.
        iIntros "?". by iFrame. }
      iIntros (c) "Hfin". iMod na_alloc as (tid') "Htl". wp_let. wp_let. unlock.
      iApply (type_call_iris _ [] tt 1%Qp with "LFT HE Htl [] [Hf'] [Henv]"). 4: iExact "Hf'". (* FIXME: Removing the [ ] around Hf' in the spec pattern diverges. *)
      - solve_typing.
      - solve_to_val.
      - iApply lft_tok_static.
      - iSplitL; last done. (* FIXME: iSplit should work, the RHS is persistent. *)
        rewrite tctx_hasty_val. iApply @send_change_tid. done.
      - iIntros (r) "Htl _ Hret".
        wp_rec. iApply (finish_spec with "[$Hfin Hret]"); last auto.
        by iApply @send_change_tid. }
    iIntros (v). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition join : val :=
    funrec: <> ["c"] :=
      let: "c'" := !"c" in
      let: "r" := join ["c'"] in
      delete [ #1; "c"];; return: ["r"].

  Lemma join_type retty `{!TyWf retty} :
    typed_val join (fn(∅; join_handle retty) → retty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>c. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (c'); simpl_subst.
    iApply (type_let _ _ _ _ ([c' ◁ _])
                             (λ r, [r ◁ box retty])); try solve_typing; [|].
    { iIntros (tid) "#LFT _ $ $".
      rewrite tctx_interp_singleton tctx_hasty_val. iIntros "Hc".
      destruct c' as [[|c'|]|]; try done.
      iApply (join_spec with "Hc"). iNext. iIntros "* Hret".
      rewrite tctx_interp_singleton tctx_hasty_val. done. }
    iIntros (r); simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End spawn.
