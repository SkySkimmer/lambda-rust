From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section get_x.
  Context `{typeG Σ}.

  Definition get_x : val :=
    funrec: <> ["p"] :=
       let: "p'" := !"p" in
       letalloc: "r" <- "p'" +ₗ #0 in
       delete [ #1; "p"] ;; "return" ["r"].

  Lemma get_x_type :
    typed_instruction_ty [] [] [] get_x
        (fn(∀ α, [☀α]; &uniq{α} Π[int; int]) → &shr{α} int).
  (* FIXME: The above is pretty-printed with some explicit scope annotations,
     and without using 'typed_instruction_ty'.  I think that's related to
     the list notation that we added to %TC. *)
  Proof.
    apply type_fn; try apply _. move=> /= α ret p. inv_vec p=>p. simpl_subst.
    eapply type_deref; [solve_typing..|by apply read_own_move|done|].
      intros p'; simpl_subst.
    eapply (type_letalloc_1 (&shr{α}int)); [solve_typing..|]=>r. simpl_subst.
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.
End get_x.
