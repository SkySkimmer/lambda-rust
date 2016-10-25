From lrust Require Export lang notation proofmode wp_tactics.

Module Valuable.

Definition t := option val.
Definition proj (n : Z) : t → t :=
  (≫= λ v, match v with LitV (LitLoc l) => Some (#(shift_loc l n)) | _ => None end).

Fixpoint of_expr (e : expr) : t :=
  match e with
  | BinOp ProjOp e (Lit (LitInt n)) => proj n (of_expr e)
  | e => to_val e
  end.

Lemma of_expr_wp `{irisG lrust_lang Σ} e v Φ :
  of_expr e = Some v → Φ v ⊢ WP e {{ Φ }}.
Proof.
  revert v Φ. induction e=>v Φ Hv; iIntros; try done.
  - inversion Hv; subst. by wp_value.
  - by wp_value.
  - destruct op; try done.
    destruct e2; try done.
    destruct l; try done.
    wp_bind e1. simpl in Hv.
    destruct (of_expr e1) as [v1|]; last done.
    iApply IHe1. done. destruct v1; try done. destruct l; try done.
    inversion Hv. subst. wp_op. eauto.
Qed.

End Valuable.