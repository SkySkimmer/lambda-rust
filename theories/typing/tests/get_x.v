From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont.

Section get_x.
  Context `{typeG Σ}.

  Definition get_x :=
    (funrec: <> ["p"] → "ret" :=
       let: "p'" := !"p" in
       letalloc: "r" := "p'" +ₗ #0 in
       delete [ #1; "p"] ;; "ret" ["r":expr])%E.

  Lemma get_x_type :
    typed_instruction_ty [] [] [] get_x
        (fn (λ α, [☀α])%EL (λ α, [# own 1 (&uniq{α}Π[int; int])])
            (λ α, own 1 (&shr{α} int))).
  Proof.
    apply type_fn; try apply _. move=> /= α ret p. inv_vec p=>p. simpl_subst.

    eapply type_deref; try solve_typing. by apply read_own_move. done.
    intros p'; simpl_subst.

    eapply (type_letalloc_1 (&shr{α}int)); (try solve_typing)=>r. simpl_subst.

    eapply type_delete; try solve_typing.

    eapply type_jump with (args := [r]); solve_typing.
  Qed.
End get_x.
