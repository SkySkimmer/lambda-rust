From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section unwrap_or.
  Context `{typeG Σ}.

  Definition unwrap_or τ : val :=
    funrec: <> ["o"; "def"] :=
      case: !"o" of
      [ delete [ #(S τ.(ty_size)); "o"];; "return" ["def"];
        letalloc: "r" <-{τ.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];; delete [ #τ.(ty_size); "def"];; "return" ["r"]].

  Lemma unwrap_or_type τ :
    typed_instruction_ty [] [] [] (unwrap_or τ)
        (fn([]; Σ[unit; τ], τ) → τ).
  Proof.
    eapply type_fn; [solve_typing..|]=>- /= [] ret p. inv_vec p=>o def. simpl_subst.
    eapply type_case_own; [solve_typing..|]. constructor; last constructor; last constructor.
    + right. eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing.
    + left. eapply type_letalloc_n; [solve_typing..|by apply read_own_move|]=>r.
        simpl_subst.
      eapply (type_delete (Π[uninit _;uninit _;uninit _])); [solve_typing..|].
      eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing.
  Qed.
End unwrap_or.
