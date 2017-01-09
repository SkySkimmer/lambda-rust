From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont borrow.
Set Default Proof Using "Type".

Section rebor.
  Context `{typeG Σ}.

  Definition init_prod :=
    (funrec: <> ["x"; "y"] :=
       let: "x'" := !"x" in let: "y'" := !"y" in
       let: "r" := new [ #2] in
       "r" +ₗ #0 <- "x'";; "r" +ₗ #1 <- "y'";;
       delete [ #1; "x"] ;; delete [ #1; "y"] ;; "return" ["r":expr])%E.

  Lemma init_prod_type :
    typed_instruction_ty [] [] [] init_prod
        (fn (λ _, []) (λ _, [# own 1 int; own 1 int])
            (λ (_ : ()), own 2 (Π[int;int]))).
  Proof.
    apply type_fn; try apply _. move=> /= [] ret p. inv_vec p=>x y. simpl_subst.
    eapply type_deref; try solve_typing; [apply read_own_move|done|]=>x'. simpl_subst.
    eapply type_deref; try solve_typing; [apply read_own_move|done|]=>y'. simpl_subst.
    eapply (type_new_subtype (Π[uninit 1; uninit 1])); [apply _|done| |].
      { apply (uninit_product_subtype [] [] [1;1]%nat). }
      intros r. simpl_subst. unfold Z.to_nat, Pos.to_nat; simpl.
    eapply (type_assign (own 2 (uninit 1))); try solve_typing. by apply write_own.
    eapply type_assign; try solve_typing. by apply write_own.
    eapply type_delete; try solve_typing.
    eapply type_delete; try solve_typing.
    eapply (type_jump [_]); solve_typing.
  Qed.
End rebor.
