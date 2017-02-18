From iris.proofmode Require Export tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section init_prod.
  Context `{typeG Σ}.

  Definition init_prod : val :=
    funrec: <> ["x"; "y"] :=
       let: "x'" := !"x" in let: "y'" := !"y" in
       let: "r" := new [ #2] in
       "r" +ₗ #0 <- "x'";; "r" +ₗ #1 <- "y'";;
       delete [ #1; "x"] ;; delete [ #1; "y"] ;; "return" ["r"].

  Lemma init_prod_type :
    typed_instruction_ty [] [] [] init_prod
        (fn([]; int, int) → Π[int;int]).
  Proof.
    iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros ([] ret p).
      inv_vec p=>x y. simpl_subst.
    iApply type_deref; [solve_typing..|apply read_own_move|done|]. iIntros (x'). simpl_subst.
    iApply type_deref; [solve_typing..|apply read_own_move|done|]. iIntros (y'). simpl_subst.
    iApply (type_new_subtype (Π[uninit 1; uninit 1])); [solve_typing..|].
      iIntros (r). simpl_subst. unfold Z.to_nat, Pos.to_nat; simpl.
    iApply (type_assign (own_ptr 2 (uninit 1))); [solve_typing..|by apply write_own|].
    iApply type_assign; [solve_typing..|by apply write_own|].
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.
End init_prod.
