From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Export cofe.
From iris.prelude Require Export strings.
From iris.prelude Require Import gmap.

Open Scope Z_scope.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Inductive base_lit : Set :=
| LitUnit | LitLoc (l : loc) | LitInt (n : Z).
Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | ProjOp.
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope lrust_binder_scope with RustB.
Bind Scope lrust_binder_scope with binder.

Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (mxl : list binder) (X : list string) : list string :=
  match mxl with [] => X | b :: mxl => b :b: app_binder mxl X end.
Infix "+b+" := app_binder (at level 60, right associativity).
Instance binder_dec_eq (x1 x2 : binder) : Decision (x1 = x2).
Proof. solve_decision. Defined.

Instance set_unfold_cons_binder x mx X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  destruct mx; rewrite /= ?elem_of_cons; naive_solver.
Qed.
Instance set_unfold_app_binder x mxl X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mxl +b+ X) (BNamed x ∈ mxl ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  induction mxl as [|?? IH]; set_solver.
Qed.

Inductive expr :=
| Var (x : string)
| Lit (l : base_lit)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| App (e : expr) (el : list expr)
| Read (o : order) (e : expr)
| Write (o : order) (e1 e2: expr)
| CAS (e0 e1 e2 : expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr)
| Fork (e : expr).

Arguments App _%E _%E.
Arguments Case _%E _%E.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Lit _ => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | Read _ e | Alloc e | Fork e => is_closed X e
  | CAS e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_decision env e : Decision (Closed env e).
Proof. rewrite /Closed. apply _. Qed.

Inductive val :=
| LitV (l : base_lit)
| RecV (f : binder) (xl : list binder) (e : expr) `{Closed (f :b: xl +b+ []) e}.

Bind Scope val_scope with val.

Definition of_val (v : val) : expr :=
  match v with
  | RecV f x e _ => Rec f x e
  | LitV l => Lit l
  end.

Definition to_val (e : expr) : option val :=
  match e with
  | Rec f xl e =>
    if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.

(** The state: heaps of vals*lockstate. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Definition state := gmap loc (lock_state * val).

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr)
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list expr)
| AppRCtx (v : val) (vl : list val) (el : list expr)
| ReadCtx (o : order)
| WriteLCtx (o : order) (e2 : expr)
| WriteRCtx (o : order) (v1 : val)
| CasLCtx (e1 e2: expr)
| CasMCtx (v0 : val) (e2 : expr)
| CasRCtx (v0 : val) (v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr)
| FreeRCtx (v1 : val)
| CaseCtx (el : list expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) (map of_val vl ++ e :: el)
  | ReadCtx o => Read o e
  | WriteLCtx o e2 => Write o e e2
  | WriteRCtx o v1 => Write o (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | AllocCtx => Alloc e
  | FreeLCtx e2 => Free e e2
  | FreeRCtx v1 => Free (of_val v1) e
  | CaseCtx el => Case e el
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (y = x) then es else Var y
  | Lit l => Lit l
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | App e el => App (subst x es e) (map (subst x es) el)
  | Read o e => Read o (subst x es e)
  | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  end.

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.
Fixpoint subst_l (xl : list binder) (esl : list expr) : expr → option expr :=
  match xl, esl with
  | [], [] => λ e, Some e
  | x::xl, es::esl => λ e, subst_l xl esl (subst' x es e)
  | _, _ => λ _, None
  end.

(** The stepping relation *)
Definition lit_of_bool (b:bool) : base_lit :=
  LitInt (if b then 1 else 0).

Definition shift_loc (l : loc) (n : Z) : loc := (l.1, l.2+n).

Definition bin_op_eval (op : bin_op) (l1 l2 : base_lit) : option base_lit :=
  match op, l1, l2 with
  | PlusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 + n2)
  | MinusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 - n2)
  | LeOp, LitInt n1, LitInt n2 =>
    Some $ lit_of_bool $ bool_decide (n1 ≤ n2)
  | ProjOp, LitLoc l, LitInt n => Some $ LitLoc $ shift_loc l n
  | _, _, _ => None
  end.

Fixpoint init_mem (l:loc) (init:list val) (σ:state) : state :=
  match init with
  | [] => σ
  | inith :: initq =>
    <[l:=(RSt 0, inith)]>(init_mem (shift_loc l 1) initq σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => delete l (free_mem (shift_loc l 1) n σ)
  end.

Definition value_eq (σ : state) (v1 v2 : val) : option bool :=
  match v1, v2 with
  | LitV (LitInt z1), LitV (LitInt z2) => Some (bool_decide (z1 = z2))
  | LitV (LitLoc l1), LitV (LitLoc l2) =>
    if bool_decide (l1 = l2) then Some true
    else match σ !! l1, σ !! l2 with
         | Some _, Some _ => Some false
         | _, _ => None
         end
  | _, _ => None
  end.

Inductive head_step : expr → state → expr → state → list expr → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval op l1 l2 = Some l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ (Lit l') σ []
| BetaS f xl e e' el σ:
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l xl el e = Some e' →
    head_step (App (Rec f xl e) el) σ (subst' f (Rec f xl e) e') σ []
| ReadScS l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read ScOrd (Lit $ LitLoc l)) σ (of_val v) σ []
| ReadNa1S l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read Na1Ord (Lit $ LitLoc l)) σ
              (Read Na2Ord (Lit $ LitLoc l)) (<[l:=(RSt $ S n, v)]>σ)
              []
| ReadNa2S l n v σ:
    σ !! l = Some (RSt $ S n, v) →
    head_step (Read Na2Ord (Lit $ LitLoc l)) σ
              (of_val v) (<[l:=(RSt n, v)]>σ)
              []
| WriteScS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write ScOrd (Lit $ LitLoc l) e) σ
              (Lit LitUnit) (<[l:=(RSt 0, v)]>σ)
              []
| WriteNa1S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write Na1Ord (Lit $ LitLoc l) e) σ
              (Write Na2Ord (Lit $ LitLoc l) e) (<[l:=(WSt, v')]>σ)
              []
| WriteNa2S l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (WSt, v') →
    head_step (Write Na2Ord (Lit $ LitLoc l) e) σ
              (Lit LitUnit) (<[l:=(RSt 0, v)]>σ)
              []
| CasFailS l n e1 v1 e2 v2 vl σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    σ !! l = Some (RSt n, vl) →
    value_eq σ v1 vl = Some false →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ lit_of_bool false) σ  []
| CasSucS l e1 v1 e2 v2 vl σ :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    σ !! l = Some (RSt 0, vl) →
    value_eq σ v1 vl = Some true →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              (Lit $ lit_of_bool true) (<[l:=(RSt 0, v2)]>σ)
              []
| AllocS n l init σ :
    0 < n →
    (∀ m, σ !! (shift_loc l m) = None) →
    Z.of_nat (length init) = n →
    head_step (Alloc $ Lit $ LitInt n) σ
              (Lit $ LitLoc l) (init_mem l init σ) []
| FreeS n l σ :
    0 < n →
    (∀ m, is_Some (σ !! (shift_loc l m)) ↔ 0 ≤ m < n) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              (Lit LitUnit) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    nth_error el (Z.to_nat i) = Some e →
    head_step (Case (Lit $ LitInt i) el) σ e σ []
| ForkS e σ:
    head_step (Fork e) σ (Lit LitUnit) σ [e].

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_stuck e1 σ1 e2 σ2 ef :
  head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki; inversion_clear 1; decompose_Forall_hyps;
    simplify_option_eq; by eauto.
Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 →
  vl1 = vl2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by rewrite to_of_val in H1.
  - subst. by rewrite to_of_val in H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto. by apply (inj of_val).
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1 as [| | |v1 vl1 el1| | | | | | | | | |],
           Ki2 as [| | |v2 vl2 el2| | | | | | | | | |];
  intros He1 He2 EQ; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
  destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto. congruence.
Qed.

Lemma shift_loc_assoc:
  ∀ l n n', shift_loc (shift_loc l n) n' = shift_loc l (n+n').
Proof. unfold shift_loc=>/= l n n'. f_equal. lia. Qed.
Lemma shift_loc_0:
  ∀ l, shift_loc l 0 = l.
Proof. unfold shift_loc=>[[??]] /=. f_equal. lia. Qed.

Definition fresh_block (σ : state) : block :=
  let blocklst := (elements (dom _ σ : gset loc)).*1 in
  let blockset : gset block := foldr (fun b s => {[b]} ∪ s)%C ∅ blocklst in
  fresh blockset.

Lemma alloc_fresh n σ :
  let l := (fresh_block σ, 0) in
  let init := repeat (LitV $ LitInt 0) (Z.to_nat n) in
  0 < n →
  head_step (Alloc $ Lit $ LitInt n) σ (Lit $ LitLoc l) (init_mem l init σ) [].
Proof.
  intros l init Hn. apply AllocS. auto.
  - clear init n Hn. unfold l, fresh_block. intro m.
    match goal with
    | |- context [foldr ?f ?e] =>
      assert (FOLD:∀ lst (l:loc), l ∈ lst → l.1 ∈ (foldr f e (lst.*1)))
    end.
    { induction lst; simpl; inversion 1; subst; set_solver. }
    rewrite -not_elem_of_dom -elem_of_elements=>/FOLD. apply is_fresh.
  - rewrite repeat_length. apply Z2Nat.id. lia.
Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X `included` Y → is_closed Y e.
Proof.
  revert e X Y. fix 1; destruct e=>X Y/=; try naive_solver.
  - naive_solver set_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], included_nil. Qed.

Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert e X. fix 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
    repeat case_bool_decide; simplify_eq/=; f_equal;
    try by intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
  - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
    f_equal; intuition eauto with set_solver.
Qed.

Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply is_closed_subst with []; set_solver. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

(** Equality and other typeclass stuff *)
Instance base_lit_dec_eq (l1 l2 : base_lit) : Decision (l1 = l2).
Proof. solve_decision. Defined.
Instance bin_op_dec_eq (op1 op2 : bin_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance un_op_dec_eq (ord1 ord2 : order) : Decision (ord1 = ord2).
Proof. solve_decision. Defined.

Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Var x, Var x' => bool_decide (x = x')
  | Lit l, Lit l' => bool_decide (l = l')
  | Rec f xl e, Rec f' xl' e' =>
    bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
    bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
  | App e el, App e' el' | Case e el, Case e' el' =>
    expr_beq e e' && expr_list_beq el el'
  | Read o e, Read o' e' => bool_decide (o = o') && expr_beq e e'
  | Write o e1 e2, Write o' e1' e2' =>
    bool_decide (o = o') && expr_beq e1 e1' && expr_beq e2 e2'
  | CAS e0 e1 e2, CAS e0' e1' e2' =>
    expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | Alloc e, Alloc e' | Fork e, Fork e' => expr_beq e e'
  | Free e1 e2, Free e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | _, _ => false
  end.
Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert e1 e2; fix 1;
    destruct e1 as [| | | |? el1| | | | | |? el1|],
             e2 as [| | | |? el2| | | | | |? el2|]; simpl; try done;
  rewrite ?andb_True ?bool_decide_spec ?expr_beq_correct;
  try (split; intro; [destruct_and?|split_and?]; congruence).
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (expr_beq_correct el1h). naive_solver. }
    clear expr_beq_correct. naive_solver.
  - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (expr_beq_correct el1h). naive_solver. }
    clear expr_beq_correct. naive_solver.
Qed.
Instance expr_dec_eq (e1 e2 : expr) : Decision (e1 = e2).
Proof.
 refine (cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Instance val_dec_eq (v1 v2 : val) : Decision (v1 = v2).
Proof.
 refine (cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.

(** Language *)
Program Instance lrust_ectxi_lang: EctxiLanguage expr val ectx_item state :=
  {| ectxi_language.of_val := of_val;
     ectxi_language.to_val := to_val;
     ectxi_language.fill_item := fill_item;
     ectxi_language.head_step := head_step |}.
Solve Obligations with eauto using to_of_val, of_to_val,
  val_stuck, fill_item_val, fill_item_no_val_inj, head_ctx_step_val.

Canonical Structure lrust_lang := ectx_lang expr.
