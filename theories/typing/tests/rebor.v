From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont borrow.
Set Default Proof Using "Type".

Section rebor.
  Context `{typeG Σ}.

  Definition rebor :=
    (funrec: <> ["t1"; "t2"] :=
       Newlft;;
       letalloc: "x" <- "t1" in
       let: "x'" := !"x" in let: "y" := "x'" +ₗ #0 in
       "x" <- "t2";;
       let: "y'" := !"y" in
       letalloc: "r" <- "y'" in
       Endlft ;; delete [ #2; "t1"] ;; delete [ #2; "t2"] ;;
                 delete [ #1; "x"] ;; "return" ["r":expr])%E.

  Lemma rebor_type :
    typed_instruction_ty [] [] [] rebor
        (fn (λ _, []) (λ _, [# own 2 (Π[int; int]); own 2 (Π[int; int])])
            (λ (_ : ()), own 1 int)).
  Proof.
    apply type_fn; try apply _. move=> /= [] ret p. inv_vec p=>t1 t2. simpl_subst.
    eapply (type_newlft []). apply _. move=> α.
    eapply (type_letalloc_1 (&uniq{α}Π[int; int])); (try solve_typing)=>x. simpl_subst.
    eapply type_deref; try solve_typing; [apply read_own_move|done|]=>x'. simpl_subst.
    eapply (type_letpath (&uniq{α}int)); (try solve_typing)=>y. simpl_subst.
    eapply (type_assign _ (&uniq{α}Π [int; int])); try solve_typing. by apply write_own.
    eapply type_deref; try solve_typing; [apply: read_uniq; solve_typing|done|]=>y'.
      simpl_subst.
    eapply type_letalloc_1; (try solve_typing)=>r. simpl_subst.
    eapply type_endlft; try solve_typing.
    eapply type_delete; try solve_typing.
    eapply type_delete; try solve_typing.
    eapply type_delete; try solve_typing.
    eapply (type_jump [_]); solve_typing.
  Qed.
End rebor.
