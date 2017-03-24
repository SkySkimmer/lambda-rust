From iris.proofmode Require Import tactics.
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
    typed_val unbox (fn(∀ α, ∅; &uniq{α}box (Π[int; int])) → &uniq{α} int).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret b). inv_vec b=>b. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (b'); simpl_subst.
    iApply type_deref_uniq_own; [solve_typing..|]. iIntros (bx); simpl_subst.
    iApply type_letalloc_1; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.
End unbox.
