From iris.proofmode Require Import tactics.
From lrust Require Export type lifetime.

Section lft_contexts.

  Context `{iris_typeG Σ}.

  Inductive ext_lft_ctx_elt :=
  | 

  Definition ext_lft_ctx := Qp → iProp Σ.

  Global Instance empty_ext_lft_ctx : Empty ext_lft_ctx := λ _, True%I.

  


  Definition int_lft_ctx := iProp Σ.

  