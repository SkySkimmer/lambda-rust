From iris.proofmode Require Export tactics.
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
    iApply type_fn; [solve_typing..|]. iIntros "/= !#". iIntros (α ret p).
      inv_vec p=>o. simpl_subst.
    iApply (type_cont [_] [] (λ r, [o ◁ _; r!!!0 ◁ _])%TC) ; [solve_typing..| |].
    - iIntros (k). simpl_subst.
      iApply type_deref; [solve_typing|apply read_own_move|done|].
        iIntros (o'). simpl_subst.
      iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply type_case_uniq; [solve_typing..|].
        constructor; last constructor; last constructor; left.
      + iApply (type_sum_assign_unit [unit; &uniq{α}τ]%T); [solve_typing..|by apply write_own|].
        iApply (type_jump [_]); solve_typing.
      + iApply (type_sum_assign [unit; &uniq{α}τ]%T); [solve_typing..|by apply write_own|].
        iApply (type_jump [_]); solve_typing.
    - iIntros "/= !#". iIntros (k r). inv_vec r=>r. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply (type_jump [_]); solve_typing.
  Qed.
End option_as_mut.
