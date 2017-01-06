From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont.

Section get_x.
  Context `{typeG Σ}.

  Definition get_x :=
    (funrec: "get_x" ["p"] → "ret" :=
       let: "p'" := !"p" in
       letalloc: "r" := "p'" +ₗ #0 in
       delete [ #1; "p"] ;; "ret" ["r":expr])%E.

  Lemma get_x_type :
    typed_instruction_ty [] [] [] get_x
        (fn (λ α, [☀α])%EL (λ α, [# own 1 (&uniq{α}Π[int; int])])
            (λ α, own 1 (&shr{α} int))).
  Proof.
    apply type_fn; try apply _. intros α get_x ret args. inv_vec args=>p args.
    inv_vec args. simpl_subst.

    eapply type_let'.
    { apply _. }
    { by apply (type_deref (&uniq{α}Π [int; int])), read_own_move. }
    { solve_typing. }
    intros p'. simpl_subst.

    eapply (type_letalloc_1 (&shr{α}int)); (try solve_typing)=>r. simpl_subst.

    eapply type_let'.
    { apply _. }
    { eapply (type_delete (uninit 1) 1); solve_typing. }
    { solve_typing. }
    move=> /= _.

    eapply type_jump with (args := [r]); solve_typing.
  Qed.
End get_x.
