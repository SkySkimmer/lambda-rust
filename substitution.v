From lrust Require Export lang.

(** The tactic [simpl_subst] performs substitutions in the goal. Its behavior
can be tuned by declaring [WExpr] and [WSubst] instances. *)

(** * Weakening *)
Class WExpr {X Y} (H : X `included` Y) (e : expr X) (er : expr Y) :=
  do_wexpr : wexpr H e = er.
Class WExprL {X Y} (H : X `included` Y) (el : list (expr X))
                   (elr : list (expr Y)) :=
  do_wexprl : List.map (wexpr H) el = elr.
Hint Mode WExpr + + + + - : typeclass_instances.
Hint Mode WExprL + + + + - : typeclass_instances.

(* Variables *)
Hint Extern 0 (WExpr _ (Var ?y) _) =>
  apply var_proof_irrel : typeclass_instances.

(* Rec *)
Global Instance do_wexpr_rec_true {X Y f y e} (H : X `included` Y) er :
  WExpr (wexpr_rec_prf H) e er → WExpr H (Rec f y e) (Rec f y er) | 10.
Proof. intros; red; f_equal/=. by etrans; [apply wexpr_proof_irrel|]. Qed.

(* Values *)
Instance do_wexpr_wexpr X Y Z (H1 : X `included` Y) (H2 : Y `included` Z) e er :
  WExpr (transitivity H1 H2) e er → WExpr H2 (wexpr H1 e) er | 0.
Proof. by rewrite /WExpr wexpr_wexpr'. Qed.
Instance do_wexpr_closed_closed (H : [] `included` []) e : WExpr H e e | 1.
Proof. apply wexpr_id. Qed.
Instance do_wexpr_closed_wexpr Y (H : [] `included` Y) e :
  WExpr H e (wexpr' e) | 2.
Proof. apply wexpr_proof_irrel. Qed.

(* Boring connectives *)
Section do_wexpr.
Context {X Y : list string} (H : X `included` Y).
Notation W := (WExpr H).
Notation WL := (WExprL H).

(* List constructors *)
Instance do_wexprl_nil : WL [] [].
Proof. done. Qed.
Instance do_wexprl_cons {h q hr qr} : W h hr → WL q qr → WL (h::q) (hr::qr).
Proof. by intros; red; f_equal/=. Qed.

(* Ground terms *)
Global Instance do_wexpr_lit l : W (Lit l) (Lit l).
Proof. done. Qed.
Global Instance do_wexpr_binop op e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (BinOp op e1 e2) (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_app e el er elr :
  W e er → WL el elr → W (App e el) (App er elr).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_read o e er : W e er → W (Read o e) (Read o er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_write o e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (Write o e1 e2) (Write o e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_cas e0 e1 e2 e0r e1r e2r :
  W e0 e0r → W e1 e1r → W e2 e2r → W (CAS e0 e1 e2) (CAS e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_alloc e er : W e er → W (Alloc e) (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_free e1 e2 e1r e2r :
  W e1 e1r → W e2 e2r → W (Free e1 e2) (Free e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_case e el er elr :
  W e er → WL el elr → W (Case e el) (Case er elr).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wexpr_fork e er : W e er → W (Fork e) (Fork er).
Proof. by intros; red; f_equal/=. Qed.
End do_wexpr.

(** * WSubstitution *)
Class WSubst {X Y} (x : string) (es : expr []) H (e : expr X) (er : expr Y) :=
  do_wsubst : wsubst x es H e = er.
Class WSubstL {X Y} (x : string) (es : expr []) H
              (el : list (expr X)) (elr : list (expr Y)) :=
  do_wsubstl : List.map (wsubst x es H) el = elr.
Hint Mode WSubst + + + + + + - : typeclass_instances.
Hint Mode WSubstL + + + + + + - : typeclass_instances.

Lemma do_wsubst_closed (e: ∀ {X}, expr X) {X Y} x es (H : X `included` x :: Y) :
  (∀ X, WExpr (included_nil X) e e) → WSubst x es H e e.
Proof.
  rewrite /WSubst /WExpr=> He. rewrite -(He X) wsubst_wexpr'.
  by rewrite (wsubst_closed _ _ _ _ _ (included_nil _)); last set_solver.
Qed.

(* Variables *)
Lemma do_wsubst_var_eq {X Y x es} {H : X `included` x :: Y} `{VarBound x X} er :
  WExpr (included_nil _) es er → WSubst x es H (Var x) er.
Proof.
  intros; red; simpl. case_decide; last done.
  by etrans; [apply wexpr_proof_irrel|].
Qed.
Hint Extern 0 (WSubst ?x ?v _ (Var ?y) _) => first
  [ apply var_proof_irrel
  | apply do_wsubst_var_eq ] : typeclass_instances.

(** Rec *)
Lemma do_wsubst_rec_true {X Y x es f} {xl:list string} {e}
      {H : X `included` x :: Y} (Hfy : x ≠ f ∧ x ∉ xl) er :
  WSubst x es (wsubst_rec_true_prf H Hfy) e er →
  WSubst x es H (Rec f xl e) (Rec f xl er).
Proof.
  intros ?; red; f_equal/=; case_decide; last done.
  by etrans; [apply wsubst_proof_irrel|].
Qed.
Lemma do_wsubst_rec_false {X Y x es f} {xl:list string} {e}
      {H : X `included` x :: Y} (Hfy : ¬(x ≠ f ∧ x ∉ xl)) er :
  WExpr (wsubst_rec_false_prf H Hfy) e er →
  WSubst x es H (Rec f xl e) (Rec f xl er).
Proof.
  intros; red; f_equal/=; case_decide; first done.
  by etrans; [apply wexpr_proof_irrel|].
Qed.

Ltac bool_decide_no_check := apply (bool_decide_unpack _); vm_cast_no_check I.
Hint Extern 0 (WSubst ?x ?v _ (Rec ?f ?xl ?e) _) =>
  match eval vm_compute in (bool_decide (x ≠ f ∧ x ∉ xl)) with
  | true => eapply (do_wsubst_rec_true ltac:(bool_decide_no_check))
  | false => eapply (do_wsubst_rec_false ltac:(bool_decide_no_check))
  end : typeclass_instances.

(* Values *)
Instance do_wsubst_wexpr X Y Z x es
    (H1 : X `included` Y) (H2 : Y `included` x :: Z) e er :
  WSubst x es (transitivity H1 H2) e er → WSubst x es H2 (wexpr H1 e) er | 0.
Proof. by rewrite /WSubst wsubst_wexpr'. Qed.
Instance do_wsubst_closed_closed x es (H : [] `included` [x]) e :
  WSubst x es H e e | 1.
Proof. apply wsubst_closed_nil. Qed.
Instance do_wsubst_closed_wexpr Y x es (H : [] `included` x :: Y) e :
  WSubst x es H e (wexpr' e) | 2.
Proof. apply wsubst_closed, not_elem_of_nil. Qed.

(* Boring connectives *)
Section wsubst.
Context {X Y} (x : string) (es : expr []) (H : X `included` x :: Y).
Notation Sub := (WSubst x es H).
Notation SubL := (WSubstL x es H).

(* Ground terms *)
Global Instance do_wsubst_lit l : Sub (Lit l) (Lit l).
Proof. done. Qed.
Global Instance do_wsubst_binop op e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (BinOp op e1 e2) (BinOp op e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_app e el er elr :
  Sub e er → SubL el elr → Sub (App e el) (App er elr).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_read o e er : Sub e er → Sub (Read o e) (Read o er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_write o e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Write o e1 e2) (Write o e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_cas e0 e1 e2 e0r e1r e2r :
  Sub e0 e0r → Sub e1 e1r → Sub e2 e2r → Sub (CAS e0 e1 e2) (CAS e0r e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_alloc e er : Sub e er → Sub (Alloc e) (Alloc er).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_free e1 e2 e1r e2r :
  Sub e1 e1r → Sub e2 e2r → Sub (Free e1 e2) (Free e1r e2r).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_case e el er elr :
  Sub e er → SubL el elr → Sub (Case e el) (Case er elr).
Proof. by intros; red; f_equal/=. Qed.
Global Instance do_wsubst_fork e er : Sub e er → Sub (Fork e) (Fork er).
Proof. by intros; red; f_equal/=. Qed.
End wsubst.

(** * The tactic *)
Lemma do_subst {X} (x: string) (es: expr []) (e: expr (x :: X)) (er: expr X) :
  WSubst x es (λ _, id) e er → subst x es e = er.
Proof. done. Qed.

Ltac simpl_subst :=
  repeat match goal with
  | |- context [subst ?x ?es ?e] => progress rewrite (@do_subst _ x es e)
  | |- _ => progress csimpl
  end.
Arguments wexpr : simpl never.
Arguments subst : simpl never.
Arguments wsubst : simpl never.
