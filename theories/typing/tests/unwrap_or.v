From lrust.lifetime Require Import definitions.
From lrust.lang Require Import new_delete.
From lrust.typing Require Import programs product product_split own uniq_bor
                    shr_bor int function lft_contexts uninit cont borrow type_sum.
Set Default Proof Using "Type".

Section unwrap_or.
  Context `{typeG Σ}.

  Definition unwrap_or τ : val :=
    funrec: <> ["o"; "def"] :=
      case: !"o" of
      [ delete [ #(S τ.(ty_size)); "o"];; "return" ["def"];
        letalloc: "r" <⋯ !{τ.(ty_size)}("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];; delete [ #τ.(ty_size); "def"];; "return" ["r"]].

  Lemma unwrap_or_type τ :
    typed_instruction_ty [] [] [] (unwrap_or τ)
        (fn (λ _, [])%EL (λ _, [# box (Σ[unit; τ]); box τ]) (λ _:(), box τ)).
  Proof.
    apply type_fn; try apply _. move=> /= [] ret p. inv_vec p=>o def. simpl_subst.
    eapply type_case_own; [solve_typing..|]. constructor; last constructor; last constructor.
    + right. eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing.
    + left. eapply type_letalloc_n; [solve_typing..|by apply read_own_move|solve_typing|]=>r.
        simpl_subst.
      eapply (type_delete (Π[_;_;_])); [solve_typing..|].
      eapply type_delete; [solve_typing..|].
      eapply (type_jump [_]); solve_typing.
  Qed.
End unwrap_or.
