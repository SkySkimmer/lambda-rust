From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section unbox.
  Context `{typeG Σ}.

  Definition unbox : val :=
    funrec: <> ["b"] :=
       let: "b'" := !"b" in let: "bx" := !"b'" in
       letalloc: "r" <- "bx" +ₗ #0 in
       delete [ #1; "b"] ;; "return" ["r"].

  Lemma ubox_type :
    typed_instruction_ty [] [] [] unbox
        (fn(∀ α, [☀α]; &uniq{α}box (Π[int; int])) → &uniq{α} int).
  Proof.
    eapply type_fn; [solve_typing..|]=> /= α ret b. inv_vec b=>b. simpl_subst.
    eapply type_deref; [solve_typing..|by apply read_own_move|done|].
    intros b'; simpl_subst.
    eapply type_deref_uniq_own; [solve_typing..|]=>bx; simpl_subst.
    eapply type_letalloc_1; [solve_typing..|]=>r. simpl_subst.
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.
End unbox.
