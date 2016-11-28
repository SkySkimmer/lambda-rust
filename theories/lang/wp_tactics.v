From lrust.lang Require Export tactics derived.
Import uPred.

(** wp-specific helper tactics *)
Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind K)]; simpl
  end.

(* FIXME : the [reflexivity] tactic is not able to solve trivial
   reflexivity proofs, while [exact (reflexivity _)] does. *)
Ltac wp_done :=
  rewrite /= ?to_of_val;
  match goal with
  | |- _ = _ => exact (reflexivity _)
  | |- Forall _ [] => fast_by apply List.Forall_nil
  | |- Forall _ (_ :: _) => apply List.Forall_cons; wp_done
  | |- is_Some (Some ?v) => exists v; reflexivity
  | |- _ => fast_done
  end.

(* sometimes, we will have to do a final view shift, so only apply
pvs_intro if we obtain a consecutive wp *)
Ltac wp_strip_pvs :=
  lazymatch goal with
  | |- _ ⊢ |={?E}=> _ =>
    etrans; [|apply fupd_intro];
    match goal with |- _ ⊢ wp E _ _ => simpl | _ => fail end
  end.

Ltac wp_value_head := etrans; [|eapply wp_value_fupd; wp_done]; lazy beta.

Ltac wp_strip_later := idtac. (* a hook to be redefined later *)

Ltac wp_seq_head :=
  lazymatch goal with
  | |- _ ⊢ wp ?E (Seq _ _) ?Q =>
    etrans; [|eapply wp_seq; wp_done]; wp_strip_later
  end.

Ltac wp_finish := intros_revert ltac:(
  rewrite /= ?to_of_val;
  try wp_strip_later;
  repeat lazymatch goal with
  | |- _ ⊢ wp ?E (Seq _ _) ?Q =>
     etrans; [|eapply wp_seq; wp_done]; wp_strip_later
  | |- _ ⊢ wp ?E _ ?Q => wp_value_head
  | |- _ ⊢ |={_}=> _ => wp_strip_pvs
  end).

Tactic Notation "wp_value" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind_core K; wp_value_head) || fail "wp_value: cannot find value in" e
  | _ => fail "wp_value: not a wp"
  end.

Tactic Notation "wp_rec" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(* hnf does not reduce through an of_val *)
(*      match eval hnf in e1 with Rec _ _ _ => *)
    wp_bind_core K; etrans; [|eapply wp_rec; wp_done]; simpl_subst; wp_finish
(*      end *) end) || fail "wp_rec: cannot find 'Rec' in" e
  | _ => fail "wp_rec: not a 'wp'"
  end.

Tactic Notation "wp_lam" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with App ?e1 _ =>
(*    match eval hnf in e1 with Rec BAnon _ _ => *)
    wp_bind_core K; etrans; [|eapply wp_lam; wp_done]; simpl_subst; wp_finish
(*    end *) end) || fail "wp_lam: cannot find 'Lam' in" e
  | _ => fail "wp_lam: not a 'wp'"
  end.

Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.

Tactic Notation "wp_op" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | BinOp LeOp _ _ => wp_bind_core K; apply wp_le; wp_finish
    | BinOp _ _ _ =>
       wp_bind_core K; etrans; [|eapply wp_bin_op; try fast_done]; wp_finish
    end) || fail "wp_op: cannot find 'BinOp' in" e
  | _ => fail "wp_op: not a 'wp'"
  end.

Tactic Notation "wp_if" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | If _ _ _ =>
      wp_bind_core K;
      etrans; [|eapply wp_if]; wp_finish
    end) || fail "wp_if: cannot find 'If' in" e
  | _ => fail "wp_if: not a 'wp'"
  end.

Tactic Notation "wp_case" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match eval hnf in e' with
    | Case _ _ _ =>
      wp_bind_core K;
      etrans; [|eapply wp_case; wp_done];
      simpl_subst; wp_finish
    end) || fail "wp_case: cannot find 'Case' in" e
  | _ => fail "wp_case: not a 'wp'"
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.
