From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section spawn.
  Context `{typeG Σ}.

  Definition thread_cont : val := λ: [<>], #().

  Definition spawn : val :=
    funrec: <> ["f"; "env"] :=
      let: "f'" := !"f" in
      Fork (call: "f'" ["env":expr] → thread_cont);;
      let: "r" := new [ #0 ] in
      delete [ #1; "f"];; "return" ["r"].

  Lemma spawn_type `(!Send envty) :
    typed_instruction_ty [] [] [] spawn
        (fn([]; fn([] ; envty) → unit, envty) → unit).
  Proof. (* FIXME: typed_instruction_ty is not used for printing. *)
    eapply type_fn; [solve_typing..|]=>- _ ret /= arg. inv_vec arg=>f env. simpl_subst.
    eapply type_deref; [solve_typing..|exact: read_own_move|done|].
    move=>f'. simpl_subst.
    eapply type_let with (T1 := [f' ◁ _; env ◁ _]%TC)
                         (T2 := λ _, []); try solve_typing; [|].
    { (* The core of the proof: showing that Forking is safe. *)
      iAlways. iIntros (tid qE) "#LFT $ $ $".
      rewrite tctx_interp_cons tctx_interp_singleton.
      iIntros "[Hf' Henv]". iApply (wp_fork with "[-]"); last first.
      { rewrite tctx_interp_nil. auto. }
      iNext. iMod na_alloc as (tid') "Htl".
      iApply (type_call' [] [] (λ _:(), []) [] f' [env:expr]
              (λ _, [# envty]) (λ _, unit) thread_cont () $! _ 1%Qp with "LFT Htl").
      - apply elctx_sat_nil.
      - rewrite /elctx_interp big_sepL_nil. done.
      - rewrite /llctx_interp big_sepL_nil. done.
      - rewrite /cctx_interp. iIntros "_ * Hin".
        iDestruct "Hin" as %Hin%elem_of_list_singleton. subst x.
        rewrite /cctx_elt_interp. iIntros "* ???". inv_vec args=>arg /=.
        wp_seq. auto.
      - rewrite tctx_interp_cons tctx_interp_singleton. iSplitL "Hf'".
        + rewrite !tctx_hasty_val.
          (* FIXME: The following should work, but does not. TC inference is doing sth. wrong.
             iApply (send_change_tid with "Hf'"). *)
          iApply @send_change_tid. done.
        + rewrite !tctx_hasty_val. iApply @send_change_tid. done. }
    move=>v. simpl_subst. clear v.
    eapply type_new; [solve_typing..|].
    intros r. simpl_subst.
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.
End spawn.
