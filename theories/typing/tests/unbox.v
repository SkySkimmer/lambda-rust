From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont borrow.
Set Default Proof Using "Type".

Section unbox.
  Context `{typeG Σ}.

  Definition unbox : val :=
    funrec: <> ["b"] :=
       let: "b'" := !"b" in let: "bx" := !"b'" in
       letalloc: "r" := "bx" +ₗ #0 in
       delete [ #1; "b"] ;; "return" ["r"].

  Lemma ubox_type :
    typed_instruction_ty [] [] [] unbox
        (fn (λ α, [☀α])%EL (λ α, [# own 1 (&uniq{α}own 2 (Π[int; int]))])
            (λ α, own 1 (&uniq{α} int))).
  Proof.
    apply type_fn; try apply _. move=> /= α ret b. inv_vec b=>b. simpl_subst.
    eapply type_deref; try solve_typing. by apply read_own_move. done.
    intros b'; simpl_subst.
    eapply type_deref_uniq_own; (try solve_typing)=>bx; simpl_subst.
    eapply type_letalloc_1; (try solve_typing)=>r. simpl_subst.
    eapply type_delete; try solve_typing.
    eapply (type_jump [_]); solve_typing.
  Qed.
End unbox.
