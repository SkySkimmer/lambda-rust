From iris.program_logic Require Export ectx_language ectxi_language.
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
| ScOrd | NaOrd | InOrd.

(** A typeclass for whether a variable is bound in a given
   context. Making this a typeclass means we can use typeclass search
   to program solving these constraints, so this becomes extensible.
   Also, since typeclass search runs *after* unification, Coq has already
   inferred the X for us; if we were to go for embedded proof terms ot
   tactics, Coq would do things in the wrong order. *)
Class VarBound (x : string) (X : list string) :=
  var_bound : bool_decide (x ∈ X).
(* There is no need to restrict this hint to terms without evars, [vm_compute]
will fail in case evars are arround. *)
Hint Extern 0 (VarBound _ _) => vm_compute; exact I : typeclass_instances.

Instance var_bound_proof_irrel x X : ProofIrrel (VarBound x X).
Proof. rewrite /VarBound. apply _. Qed.
Instance set_unfold_var_bound x X P :
  SetUnfold (x ∈ X) P → SetUnfold (VarBound x X) P.
Proof.
  constructor. by rewrite /VarBound bool_decide_spec (set_unfold (x ∈ X) P).
Qed.

Inductive expr (X : list string) :=
(* Var is the only place where the terms contain a proof. The fact that they
   contain a proof at all is suboptimal, since this means two seeminlgy
   convertible terms could differ in their proofs. However, this also has
   some advantages:
   * We can make the [X] an index, so we can do non-dependent match.
   * In expr_weaken, we can push the proof all the way into Var, making
     sure that proofs never block computation. *)
| Var (x : string) `{VarBound x X}
| Lit (l : base_lit)
| Rec (f : string) (xl : list string) (e : expr (xl ++ f :: X))
| BinOp (op : bin_op) (e1 e2 : expr X)
| App (e : expr X) (el : list (expr X))
| Read (o : order) (e : expr X)
| Write (o : order) (e1 e2: expr X)
| CAS (e0 e1 e2 : expr X)
| Alloc (e : expr X)
| Free (e1 e2 : expr X)
| Case (e : expr X) (el : list (expr X))
| Fork (e : expr X).

Bind Scope rust_expr_scope with expr.
Bind Scope rust_expr_scope with list expr.
Delimit Scope rust_expr_scope with Rust.
Arguments Var {_} _ {_}.
Arguments Lit {_} _.
Arguments Rec {_} _ _ _%Rust.
Arguments BinOp {_} _ _%Rust _%Rust.
Arguments App {_} _%Rust _%Rust.
Arguments Read {_} _ _%Rust.
Arguments Write {_} _ _%Rust _%Rust.
Arguments CAS {_} _%Rust _%Rust _%Rust.
Arguments Alloc {_} _%Rust.
Arguments Free {_} _%Rust _%Rust.
Arguments Case {_} _%Rust _%Rust.
Arguments Fork {_} _%Rust.

Inductive val :=
| LitV (l : base_lit)
| RecV (f : string) (xl : list string) (e : expr (xl ++ [f])).

Definition of_val (v : val) : expr [] :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  end.

Definition to_val (e : expr []) : option val :=
  match e with
  | Rec f x e => Some (RecV f x e)
  | Lit l => Some (LitV l)
  | _ => None
  end.

(** The state: heaps of vals*lockstate. *)
Inductive lock_state :=
| WSt | RSt (n : nat).
Definition state := gmap loc (lock_state * val).

(** Evaluation contexts *)
Inductive ectx_item :=
| BinOpLCtx (op : bin_op) (e2 : expr [])
| BinOpRCtx (op : bin_op) (v1 : val)
| AppLCtx (e2 : list (expr []))
| AppRCtx (v : val) (vl : list val) (el : list (expr []))
| ReadCtx (o : order)
| WriteLCtx (o : order) (e2 : expr [])
| WriteRCtx (o : order) (v1 : val)
| CasLCtx (e1 e2: expr [])
| CasMCtx (v0 : val) (e2 : expr [])
| CasRCtx (v0 : val) (v1 : val)
| AllocCtx
| FreeLCtx (e2 : expr [])
| FreeRCtx (v1 : val)
| CaseCtx (el : list (expr [])).

Definition fill_item (Ki : ectx_item) (e : expr []) : expr [] :=
  match Ki with
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | AppLCtx e2 => App e e2
  | AppRCtx v vl el => App (of_val v) (List.app (List.map of_val vl) (e :: el))
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
Program Fixpoint wexpr {X Y} (H : X `included` Y) (e : expr X) : expr Y :=
  match e return expr Y with
  | Var x _ => @Var _ x _
  | Lit l => Lit l
  | Rec f xl e => Rec f xl (wexpr _ e)
  | BinOp op e1 e2 => BinOp op (wexpr H e1) (wexpr H e2)
  | App e el => App (wexpr H e) (List.map (wexpr H) el)
  | Read o e => Read o (wexpr H e)
  | Write o e1 e2 => Write o (wexpr H e1) (wexpr H e2)
  | CAS e0 e1 e2 => CAS (wexpr H e0) (wexpr H e1) (wexpr H e2)
  | Alloc e => Alloc (wexpr H e)
  | Free e1 e2 => Free (wexpr H e1) (wexpr H e2)
  | Case e el => Case (wexpr H e) (List.map (wexpr H) el)
  | Fork e => Fork (wexpr H e)
  end.
Solve Obligations with set_solver.

Definition wexpr' {X} (e : expr []) : expr X := wexpr (included_nil _) e.

Definition of_val' {X} (v : val) : expr X := wexpr (included_nil _) (of_val v).

Lemma wsubst_rec_true_prf {X Y x} (H : X `included` x :: Y)
      {f} {xl : list string} (Hfxl : x ≠ f ∧ x ∉ xl) :
  xl ++ f :: X `included` x :: xl ++ f :: Y.
Proof. set_solver. Qed.

Lemma wsubst_rec_false_prf {X Y x} (H : X `included` x :: Y)
      {f} {xl : list string} (Hfxl : ¬ (x ≠ f ∧ x ∉ xl)) :
  xl ++ f :: X `included` xl ++ f :: Y.
Proof. move: Hfxl=>/not_and_l [/dec_stable|/dec_stable]; set_solver. Qed.

Program Fixpoint wsubst {X Y} (x : string) (es : expr [])
    (H : X `included` x :: Y) (e : expr X)  : expr Y :=
  match e return expr Y with
  | Var y _ => if decide (x = y) then wexpr' es else @Var _ y _
  | Lit l => Lit l
  | Rec f xl e =>
     Rec f xl $ match decide (x ≠ f ∧ x ∉ xl) return _ with
                | left Hfy => wsubst x es (wsubst_rec_true_prf H Hfy) e
                | right Hfy => wexpr (wsubst_rec_false_prf H Hfy) e
                end
  | BinOp op e1 e2 => BinOp op (wsubst x es H e1) (wsubst x es H e2)
  | App e el => App (wsubst x es H e) (List.map (wsubst x es H) el)
  | Read o e => Read o (wsubst x es H e)
  | Write o e1 e2 => Write o (wsubst x es H e1) (wsubst x es H e2)
  | CAS e0 e1 e2 => CAS (wsubst x es H e0) (wsubst x es H e1) (wsubst x es H e2)
  | Alloc e => Alloc (wsubst x es H e)
  | Free e1 e2 => Free (wsubst x es H e1) (wsubst x es H e2)
  | Case e el => Case (wsubst x es H e) (List.map (wsubst x es H) el)
  | Fork e => Fork (wsubst x es H e)
  end.
Solve Obligations with set_solver.

Definition subst {X} (x : string) (es : expr []) (e : expr (x :: X)) : expr X :=
  wsubst x es (λ z, id) e.
Fixpoint subst_l {X} (xl : list string) (esl : list (expr [])) :
                     expr (List.app xl X) → option (expr X) :=
  match xl, esl return expr (List.app xl X) → option (expr X) with
  | [], [] => λ e, Some e
  | x::xl, es::esl => λ e, subst_l xl esl (subst x es e)
  | _, _ => λ _, None
  end.

(** The stepping relation *)
Definition lit_of_bool (b:bool) : base_lit :=
  LitInt (if b then 1 else 0).

Definition bin_op_eval (op : bin_op) (l1 l2 : base_lit) : option base_lit :=
  match op, l1, l2 with
  | PlusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 + n2)
  | MinusOp, LitInt n1, LitInt n2 => Some $ LitInt (n1 - n2)
  | LeOp, LitInt n1, LitInt n2 =>
    Some $ lit_of_bool $ bool_decide (n1 ≤ n2)
  | ProjOp, LitLoc (blk, offs), LitInt n => Some $ LitLoc(blk, offs + n)
  | _, _, _ => None
  end.

Fixpoint init_mem (blk:block) (i0:Z) (init:list val) (σ:state) : state :=
  match init with
  | [] => σ
  | inith :: initq =>
    <[(blk, i0):=(RSt 0, inith)]>(init_mem blk (Z.succ i0) initq σ)
  end.

Fixpoint free_mem (blk:block) (i0:Z) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => free_mem blk i0 n (delete (blk, i0+n) σ)
  end.

Inductive head_step : expr [] → state → expr [] → state → option (expr []) → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval op l1 l2 = Some l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ (Lit l') σ None
| BetaS f xl e e' el σ:
    List.Forall (λ ei, is_Some (to_val ei)) el →
    subst_l xl el e = Some e' →
    head_step (App (Rec f xl e) el) σ (subst f (Rec f xl e) e') σ None
| ReadScS l v σ:
    σ !! l = Some (RSt 0, v) →
    head_step (Read ScOrd (Lit $ LitLoc l)) σ (of_val v) σ None
| ReadNaS l n v σ:
    σ !! l = Some (RSt n, v) →
    head_step (Read NaOrd (Lit $ LitLoc l)) σ
              (Read InOrd (Lit $ LitLoc l)) (<[l:=(RSt $ S n, v)]>σ)
              None
| ReadInS l n v σ:
    σ !! l = Some (RSt $ S n, v) →
    head_step (Read InOrd (Lit $ LitLoc l)) σ
              (of_val v) (<[l:=(RSt n, v)]>σ)
              None
| WriteScS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (RSt 0, v') →
    head_step (Write ScOrd (Lit $ LitLoc l) e) σ
              (Lit LitUnit) (<[l:=(RSt 0, v)]>σ)
              None
| WriteNaS l e v' σ:
    is_Some (to_val e) →
    σ !! l = Some (RSt 0, v') →
    head_step (Write NaOrd (Lit $ LitLoc l) e) σ
              (Write InOrd (Lit $ LitLoc l) e) (<[l:=(WSt, v')]>σ)
              None
| WriteInS l e v v' σ:
    to_val e = Some v →
    σ !! l = Some (WSt, v') →
    head_step (Write InOrd (Lit $ LitLoc l) e) σ
              (Lit LitUnit) (<[l:=(RSt 0, v)]>σ)
              None
| CasFailS l z1 z2 zl σ :
    σ !! l = Some (RSt 0, LitV $ LitInt zl) →
    zl ≠ z1 →
    head_step (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) (Lit $ LitInt z2)) σ
              (Lit $ lit_of_bool false) σ  None
| CasSucS l z1 z2 σ :
    σ !! l = Some (RSt 0, LitV $ LitInt z1) →
    head_step (CAS (Lit $ LitLoc l) (Lit $ LitInt z1) (Lit $ LitInt z2)) σ
              (Lit $ lit_of_bool true) (<[l:=(RSt 0, LitV $ LitInt z2)]>σ)
              None
| AllocS n l init σ :
    0 < n →
    (∀ i, σ !! (l.1, i) = None) →
    Z.of_nat (List.length init) = n →
    head_step (Alloc $ Lit $ LitInt n) σ
              (Lit $ LitLoc l) (init_mem (l.1) (l.2) init σ) None
| FreeS n l σ :
    0 < n →
    (∀ i, is_Some (σ !! (l.1, i)) ↔ (l.2 ≤ i ∧ i < l.2 + n)) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              (Lit LitUnit) (free_mem (l.1) (l.2) (Z.to_nat n) σ)
              None
| CaseS i el e σ :
    0 ≤ i →
    List.nth_error el (Z.to_nat i) = Some e →
    head_step (Case (Lit $ LitInt i) el) σ e σ None
| ForkS e σ:
    head_step (Fork e) σ (Lit LitUnit) σ (Some e).

(** Atomic expressions *)
Definition atomic (e: expr []) : bool :=
  match e with
  | Read (ScOrd | InOrd) e | Alloc e => bool_decide (is_Some (to_val e))
  | Write (ScOrd | InOrd) e1 e2 | Free e1 e2 =>
    bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | CAS e0 e1 e2 =>
    bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  | _ => false
  end.

(** Substitution *)
Lemma var_proof_irrel X x H1 H2 : @Var X x H1 = @Var X x H2.
Proof. f_equal. by apply (proof_irrel _). Qed.

Lemma wexpr_id X (H : X `included` X) e : wexpr H e = e.
Proof.
  revert X H e; fix 3.
  destruct e as [| | | |? el| | | | | |? el|]; f_equal/=;
    auto using proof_irrel;
  induction el; f_equal/=; auto.
Qed.
Lemma wexpr_proof_irrel X Y (H1 H2 : X `included` Y) e : wexpr H1 e = wexpr H2 e.
Proof.
  revert X Y H1 H2 e; fix 5.
  destruct e as [| | | |? el| | | | | |? el|]; f_equal/=;
    auto using proof_irrel;
  induction el; f_equal/=; auto.
Qed.
Lemma wexpr_wexpr X Y Z (H1 : X `included` Y) (H2 : Y `included` Z) H3 e :
  wexpr H2 (wexpr H1 e) = wexpr H3 e.
Proof.
  revert X Y Z H1 H2 H3 e; fix 7.
  destruct e as [| | | |? el| | | | | |? el|]; f_equal/=;
    auto using proof_irrel;
  induction el; f_equal/=; auto.
Qed.
Lemma wexpr_wexpr' X Y Z (H1 : X `included` Y) (H2 : Y `included` Z) e :
  wexpr H2 (wexpr H1 e) = wexpr (transitivity H1 H2) e.
Proof. apply wexpr_wexpr. Qed.

Lemma wsubst_proof_irrel X Y x es (H1 H2 : X `included` x :: Y) e :
  wsubst x es H1 e = wsubst x es H2 e.
Proof.
  revert X Y H1 H2 e; fix 5.
  destruct e as [| | | |? el| | | | | |? el|];
    simpl; intros; try case_decide; f_equal;
    auto using proof_irrel, wexpr_proof_irrel;
  induction el; f_equal/=; auto.
Qed.
Lemma wexpr_wsubst X Y Z x es (H1: X `included` x::Y) (H2: Y `included` Z) H3 e:
  wexpr H2 (wsubst x es H1 e) = wsubst x es H3 e.
Proof.
  revert X Y Z H1 H2 H3 e; fix 7.
  destruct e; intros; rewrite /=/wexpr'/=; try case_decide; f_equal; simpl;
    auto using var_proof_irrel, wexpr_wexpr;
  induction el; f_equal/=; auto.
Qed.
Lemma wsubst_wexpr X Y Z x es (H1: X `included` Y) (H2: Y `included` x::Z) H3 e:
  wsubst x es H2 (wexpr H1 e) = wsubst x es H3 e.
Proof.
  revert X Y Z H1 H2 H3 e; fix 7.
  destruct e as [| | | |? el| | | | | |? el|];
    intros; simpl; try case_decide; f_equal;
    auto using proof_irrel, wexpr_wexpr;
  induction el; f_equal/=; auto.
Qed.
Lemma wsubst_wexpr' X Y Z x es (H1: X `included` Y) (H2: Y `included` x::Z) e:
  wsubst x es H2 (wexpr H1 e) = wsubst x es (transitivity H1 H2) e.
Proof. apply wsubst_wexpr. Qed.

Lemma wsubst_closed X Y x es (H1 : X `included` x :: Y) H2 (e : expr X) :
  x ∉ X → wsubst x es H1 e = wexpr H2 e.
Proof.
  revert X Y H1 H2 e; fix 5.
  destruct e as [| | | |? el| | | | | |? el|];
    intros; rewrite /=/wexpr'/=; try case_decide; f_equal;
    auto using proof_irrel, wexpr_proof_irrel with set_solver;
    try (induction el; f_equal/=; auto).
  clear wsubst_closed. exfalso; set_solver.
Qed.
Lemma wsubst_closed_nil x es H (e : expr []) : wsubst x es H e = e.
Proof.
  rewrite -{2}(wexpr_id _ (reflexivity []) e).
  apply wsubst_closed, not_elem_of_nil.
Qed.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by induction v; simplify_option_eq. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert e v. cut (∀ X (e : expr X) (H : X = ∅) v,
    to_val (eq_rect _ expr e _ H) = Some v → of_val v = eq_rect _ expr e _ H).
  { intros help e v. apply (help ∅ e eq_refl). }
  intros X e; induction e; intros HX ??; simplify_option_eq;
    repeat match goal with
    | IH : ∀ _ : ∅ = ∅, _ |- _ => specialize (IH eq_refl); simpl in IH
    end; auto with f_equal.
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

Lemma atomic_not_val e : atomic e → to_val e = None.
Proof. by destruct e. Qed.

Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
Proof.
  by intros; destruct Ki; repeat (case_match || simplify_eq/= || destruct_and?).
Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  by destruct 2; simpl; rewrite ?to_of_val; eauto.
Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; eauto. by decompose_Forall_hyps. Qed.

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

Definition fresh_block (σ : state) : block :=
  let blocklst := (elements (dom _ σ : gset loc)).*1 in
  let blockset : gset block := foldr (fun b s => {[b]} ∪ s)%C ∅ blocklst in
  fresh blockset.

Lemma alloc_fresh n σ :
  let blk := fresh_block σ in
  let init := repeat (LitV $ LitInt 0) (Z.to_nat n) in
  0 < n →
  head_step (Alloc $ Lit $ LitInt n) σ (Lit $ LitLoc (blk, 0))
            (init_mem blk 0 init σ)
            None.
Proof.
  intros blk init Hn. apply AllocS. auto.
  - clear init n Hn. unfold blk, fresh_block. intro i.
    match goal with
    | |- appcontext [foldr ?f ?e] =>
      assert (FOLD:∀ l x, (x, i) ∈ l → x ∈ (foldr f e (l.*1)))
    end.
    { induction l; simpl; inversion 1; subst; set_solver. }
    rewrite -not_elem_of_dom -elem_of_elements=>/FOLD. apply is_fresh.
  - rewrite repeat_length. apply Z2Nat.id. lia.
Qed.

Definition init_mem_spec (l:loc) (n:Z) (σ σ':state) : Prop :=
  (∀ l', l'.1 ≠ l.1 → σ !! l' =  σ' !! l') ∧
  (∀ i, l.2 ≤ i < l.2 + n ↔ is_Some (σ' !! (l.1, i))).

Lemma init_mem_sound l init σ:
  (∀ i, σ !! (l.1, i) = None) →
  init_mem_spec l (List.length init) σ (init_mem (l.1) (l.2) init σ).
Proof.
  destruct l as [blk i0]. unfold init_mem_spec.
  revert i0. induction init=>/= i0 FRESH; split.
  - auto.
  - intro i. rewrite FRESH. split. lia. move=>/is_Some_None[].
  - intros. rewrite lookup_insert_ne. by apply IHinit. clear IHinit; naive_solver.
  - intro i.
    rewrite lookup_insert_is_Some -(proj2 (IHinit (Z.succ i0) _)) //.
    clear -FRESH. destruct (decide (i = i0)); naive_solver lia.
Qed.

Definition free_mem_spec (l:loc) (n:Z) (σ σ':state) : Prop :=
  (∀ l', l'.1 ≠ l.1 → σ !! l' =  σ' !! l') ∧
  (∀ i, σ' !! (l.1, i) = None).

Lemma free_mem_sound l n σ:
  0 < n →
  (∀ i, is_Some (σ !! (l.1, i)) ↔ (l.2 ≤ i ∧ i < l.2 + n)) →
  free_mem_spec l n σ (free_mem (l.1) (l.2) (Z.to_nat n) σ).
Proof.
  intro. rewrite -(Z2Nat.id n) ?Nat2Z.id. 2:lia.
  destruct l as [blk i0]. unfold free_mem_spec.
  revert σ. induction (Z.to_nat n) as [|n' IH] =>/= σ Hσ.
  - split. auto. intro i. rewrite eq_None_not_Some Hσ. lia.
  - destruct (IH (delete (blk, i0 + n') σ)) as [IH1 IH2].
    { intro i. rewrite lookup_delete_is_Some Hσ.
      clear; destruct (decide (i = i0 + n')); naive_solver lia. }
    split. 2:done.
    intros l' Hl'. rewrite -IH1 ?lookup_delete_ne //. clear -Hl'; naive_solver.
Qed.

(** Equality and other typeclass stuff *)
Instance base_lit_dec_eq (l1 l2 : base_lit) : Decision (l1 = l2).
Proof. solve_decision. Defined.
Instance bin_op_dec_eq (op1 op2 : bin_op) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance un_op_dec_eq (ord1 ord2 : order) : Decision (ord1 = ord2).
Proof. solve_decision. Defined.

Fixpoint expr_beq {X Y} (e : expr X) (e' : expr Y) : bool :=
  let fix expr_list_beq el el' :=
    match el, el' with
    | [], [] => true
    | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
    | _, _ => false
    end
  in
  match e, e' with
  | Var x _, Var x' _ => bool_decide (x = x')
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
Lemma expr_beq_correct {X} (e1 e2 : expr X) : expr_beq e1 e2 ↔ e1 = e2.
Proof.
  revert X e1 e2; fix 2;
    destruct e1 as [| | | |? el1| | | | | |? el1|],
             e2 as [| | | |? el2| | | | | |? el2|]; simpl; try done;
  rewrite ?andb_True ?bool_decide_spec ?expr_beq_correct;
  try (split; intro; [destruct_and?|split_and?]; congruence).
  - split; intro. subst. apply var_proof_irrel. congruence.
  - specialize (expr_beq_correct _ e1). naive_solver.
  - match goal with |- appcontext [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (expr_beq_correct _ el1h). naive_solver. }
    clear expr_beq_correct. naive_solver.
  - match goal with |- appcontext [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
    { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
      specialize (expr_beq_correct _ el1h). naive_solver. }
    clear expr_beq_correct. naive_solver.
Qed.
Instance expr_dec_eq {X} (e1 e2 : expr X) : Decision (e1 = e2).
Proof.
 refine (cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Instance val_dec_eq (v1 v2 : val) : Decision (v1 = v2).
Proof.
 refine (cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
Defined.

Instance expr_inhabited X : Inhabited (expr X) := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC X := leibnizC (expr X).

(** Language *)
Program Instance lrust_ectxi_lang: EctxiLanguage (expr []) val ectx_item state :=
  {| ectxi_language.of_val := of_val;
     ectxi_language.to_val := to_val;
     ectxi_language.fill_item := fill_item;
     ectxi_language.atomic := atomic;
     ectxi_language.head_step := head_step |}.
Solve Obligations with eauto using to_of_val, of_to_val,
  val_stuck, atomic_not_val, atomic_step,
  fill_item_val, atomic_fill_item,
  fill_item_no_val_inj, head_ctx_step_val.

Canonical Structure lrust_lang := ectx_lang (expr []).
