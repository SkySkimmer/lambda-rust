From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section option_as_mut.
  Context `{typeG Σ}.

  Definition option_as_mut : val :=
    funrec: <> ["o"] :=
      let: "o'" := !"o" in
      let: "r" := new [ #2 ] in
      case: !"o'" of
        [ "r" <-{Σ 0} ();; "k" ["r"];
          "r" <-{Σ 1} "o'" +ₗ #1;; "k" ["r"] ]
      cont: "k" ["r"] :=
        delete [ #1; "o"];; "return" ["r"].

  Lemma option_as_mut_type τ :
    typed_instruction_ty [] [] [] option_as_mut
        (fn(∀ α, [☀α]; &uniq{α} Σ[unit; τ]) → Σ[unit; &uniq{α}τ]).
  Proof.
    eapply type_fn; [solve_typing..|]=> /= α ret p. inv_vec p=>o. simpl_subst.
    eapply (type_cont [_] [] (λ r, [o ◁ _; r!!!0 ◁ _])%TC) ; [solve_typing..| |].
    - intros k. simpl_subst.
      eapply type_deref; [solve_typing..|apply read_own_move|done|]=>o'. simpl_subst.
      eapply type_new; [solve_typing..|]. intros r. simpl_subst.
      eapply type_case_uniq; [solve_typing..|].
        constructor; last constructor; last constructor; left.
      + eapply (type_sum_assign_unit [unit; &uniq{α}τ]%T); [solve_typing..|by apply write_own|].
        eapply (type_jump [_]); solve_typing.
      + eapply (type_sum_assign [unit; &uniq{α}τ]%T); [solve_typing..|by apply write_own|].
        eapply (type_jump [_]); solve_typing.
    - move=>/= k r. inv_vec r=>r. simpl_subst.
      eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing.
  Qed.
End option_as_mut.
