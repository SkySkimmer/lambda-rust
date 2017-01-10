From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont borrow type_sum.
Set Default Proof Using "Type".

Section option_as_mut.
  Context `{typeG Σ}.

  Definition option_as_mut :=
    (funrec: <> ["o"] :=
       let: "o'" := !"o" in case: !"o'" of
       [ let: "r" := new [ #2 ] in "r" <-{0} ☇;;
         "k" ["r"];
         let: "r" := new [ #2 ] in "r" <-{1} "o'" +ₗ #1;;
         "k" ["r"] ]
       cont: "k" ["r"] :=
         delete [ #1; "o"];; "return" ["r"])%E.

  Lemma option_as_mut_type τ :
    typed_instruction_ty [] [] [] option_as_mut
        (fn (λ α, [☀α])%EL (λ α, [# own 1 (&uniq{α}Σ[unit; τ])])
            (λ α, own 2 (Σ[unit; &uniq{α}τ]))).
  Proof.
    apply type_fn; try apply _. move=> /= α ret p. inv_vec p=>o. simpl_subst.
    eapply (type_cont [_] [] (λ r, [o ◁ _; r!!!0 ◁ _])%TC) ; try solve_typing.
    - intros k. simpl_subst.
      eapply type_deref; try solve_typing; [apply read_own_move|done|]=>o'. simpl_subst.
      eapply type_case_uniq; try solve_typing. constructor; last constructor; last constructor.
      + left. eapply type_new; try solve_typing. intros r. simpl_subst.
        eapply (type_sum_assign_unit [unit; &uniq{α}τ]%T); try solve_typing. by apply write_own.
        eapply (type_jump [_]); solve_typing.
      + left. eapply type_new; try solve_typing. intros r. simpl_subst.
        eapply (type_sum_assign [unit; &uniq{α}τ]%T); try solve_typing. by apply write_own.
        eapply (type_jump [_]); solve_typing.
    - move=>/= k r. inv_vec r=>r. simpl_subst.
      eapply type_delete; try solve_typing.
      eapply (type_jump [_]); solve_typing.
  Qed.
End option_as_mut.
