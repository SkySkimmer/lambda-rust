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
         | [ #(LitLoc l) ] =>
           ∃ ty', ▷ type_incl ty' ty ∗ join_handle spawnN l (join_inv tid ty')
         | _ => False
         end%I;
       ty_shr κ tid l := True%I |}.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation. iIntros "* _ _ _ $". auto. Qed.
  Next Obligation. iIntros (?) "**"; auto. Qed.

  Lemma join_handle_subtype ty1 ty2 :
    ▷ type_incl ty1 ty2 -∗ type_incl (join_handle ty1) (join_handle ty2).
  Proof.
    iIntros "#Hincl". iSplit; first done. iSplit; iAlways.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as (ty) "[Hincl' ?]". iExists ty. iFrame.
      iApply (type_incl_trans with "Hincl'"). done.
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
End join_handle.

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition spawn : val :=
    funrec: <> ["f"; "env"] :=
      let: "f'" := !"f" in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "f'" ["env":expr] in
                            finish ["c"; "r"]] in
      letalloc: "r" <- "join" in
      delete [ #1; "f"];; return: ["r"].

  Lemma spawn_type `(!Send envty, !Send retty) :
    typed_val spawn (fn(λ _, []; fn(λ _, [] ; envty) → retty, envty) → join_handle retty).
  Proof. (* FIXME: typed_instruction_ty is not used for printing. *)
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>f env. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (f'). simpl_subst.
    iApply (type_let _ _ _ _ ([f' ◁ _; env ◁ _]%TC)
                     (λ j, [j ◁ join_handle retty]%TC)); try solve_typing; [|].
    { (* The core of the proof: showing that spawn is safe. *)
      iIntros (tid) "#LFT #HE $ $".
      rewrite tctx_interp_cons tctx_interp_singleton.
      iIntros "[Hf' Henv]". iApply (spawn_spec _ (join_inv tid retty) with "[-]");
                              first solve_to_val; last first; last simpl_subst.
      { iIntros "!> *". rewrite tctx_interp_singleton tctx_hasty_val.
        iIntros "?". iExists retty. iFrame. iApply type_incl_refl. }
      iIntros (c) "Hfin". iMod na_alloc as (tid') "Htl". wp_let. wp_let.
      (* FIXME this is horrible. *)
      assert (Hcall := type_call' [] [] [] f' [] [env:expr] (λ _:(), FP (λ _, []) [# envty] retty)).
      specialize (Hcall (rec: "_k" ["r"] := finish [ #c; "r"])%V ()).
      erewrite of_val_unlock in Hcall; last done.
      iApply (Hcall with "LFT [] Htl [] [Hfin]").
      - constructor.
      - intros. apply elctx_sat_nil.
      - rewrite /elctx_interp big_sepL_nil. done.
      - rewrite /llctx_interp big_sepL_nil. done.
      - rewrite /cctx_interp. iIntros "* Hin".
        iDestruct "Hin" as %Hin%elem_of_list_singleton. subst x.
        rewrite /cctx_elt_interp. iIntros "* ?? Hret". inv_vec args=>arg /=.
        wp_rec. iApply (finish_spec with "[$Hfin Hret]"); last auto.
        rewrite tctx_interp_singleton tctx_hasty_val. by iApply @send_change_tid.
      - rewrite tctx_interp_cons tctx_interp_singleton. iSplitL "Hf'".
        + rewrite !tctx_hasty_val.
          iApply @send_change_tid. done.
        + rewrite !tctx_hasty_val. iApply @send_change_tid. done. }
    iIntros (v). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition join : val :=
    funrec: <> ["c"] :=
      let: "c'" := !"c" in
      let: "r" := join ["c'"] in
      delete [ #1; "c"];; return: ["r"].

  Lemma join_type retty :
    typed_val join (fn(λ _, []; join_handle retty) → retty).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ϝ ret arg). inv_vec arg=>c. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (c'); simpl_subst.
    iApply (type_let _ _ _ _ ([c' ◁ _]%TC)
                             (λ r, [r ◁ box retty]%TC)); try solve_typing; [|].
    { iIntros (tid) "#LFT _ $ $".
      rewrite tctx_interp_singleton tctx_hasty_val. iIntros "Hc'".
      destruct c' as [[|c'|]|]; try done. iDestruct "Hc'" as (ty') "[#Hsub Hc']".
      iApply (join_spec with "Hc'"). iNext. iIntros "* Hret".
      rewrite tctx_interp_singleton tctx_hasty_val.
      iDestruct (box_type_incl with "[$Hsub]") as "(_ & Hincl & _)".
      iApply "Hincl". done. }
    iIntros (r); simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End spawn.
