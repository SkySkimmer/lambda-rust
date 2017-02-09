From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section lazy_lft.
  Context `{typeG Σ}.

  Definition lazy_lft : val :=
    funrec: <> [] :=
      Newlft;;
      let: "t" := new [ #2] in let: "f" := new [ #1] in let: "g" := new [ #1] in
      let: "42" := #42 in "f" <- "42";;
      "t" +ₗ #0 <- "f";; "t" +ₗ #1 <- "f";;
      let: "t0'" := !("t" +ₗ #0) in "t0'";;
      let: "23" := #23 in "g" <- "23";;
      "t" +ₗ #1 <- "g";;
      let: "r" := new [ #0] in
      Endlft;; delete [ #2; "t"];; delete [ #1; "f"];; delete [ #1; "g"];; "return" ["r"].

  Lemma lazy_lft_type :
    typed_instruction_ty [] [] [] lazy_lft
        (fn([]) → unit).
  Proof.
    apply type_fn; try apply _. move=> /= [] ret p. inv_vec p. simpl_subst.
    eapply (type_newlft []); [solve_typing|]=>α.
    eapply (type_new_subtype (Π[uninit 1;uninit 1])); [solve_typing..|].
      intros t. simpl_subst.
    eapply type_new; [solve_typing..|]=>f. simpl_subst.
    eapply type_new; [solve_typing..|]=>g. simpl_subst.
    eapply type_int; [solve_typing|]=>v42. simpl_subst.
    eapply type_assign; [solve_typing..|by eapply write_own|].
    eapply (type_assign _ (&shr{α}_)); [solve_typing..|by eapply write_own|].
    eapply type_assign; [solve_typing..|by eapply write_own|].
    eapply type_deref; [solve_typing..|apply: read_own_copy|done|]=>t0'. simpl_subst.
    eapply type_letpath; [solve_typing..|]=>dummy. simpl_subst.
    eapply type_int; [solve_typing|]=>v23. simpl_subst.
    eapply type_assign; [solve_typing..|by eapply write_own|].
    eapply (type_assign _ (&shr{α}int)); [solve_typing..|by eapply write_own|].
    eapply type_new; [solve_typing..|] =>r. simpl_subst.
    eapply type_endlft; [solve_typing..|].
    eapply (type_delete (Π[&shr{_}_;&shr{_}_])%T); [solve_typing..|].
    eapply type_delete; [solve_typing..|].
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.
End lazy_lft.
