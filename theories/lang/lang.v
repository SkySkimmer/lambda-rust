From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** Expressions and vals. *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Inductive base_lit : Set :=
| LitUnit | LitLoc (l : loc) | LitInt (n : Z).
Inductive bin_op : Set :=
| PlusOp | MinusOp | LeOp | EqOp | OffsetOp.
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope lrust_binder_scope with RustB.
Bind Scope lrust_binder_scope with binder.

Notation "a :: b" := (@cons binder a%RustB b%RustB)
  (at level 60, right associativity) : lrust_binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%RustB (@cons binder x2%RustB
        (..(@cons binder xn%RustB (@nil binder))..))) : lrust_binder_scope.
Notation "[ x ]" := (@cons binder x%RustB (@nil binder)) : lrust_binder_scope.

Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (mxl : list binder) (X : list string) : list string :=
  match mxl with [] => X | b :: mxl => b :b: app_binder mxl X end.
Infix "+b+" := app_binder (at level 60, right associativity).
Instance binder_dec_eq : EqDecision binder.
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
  | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
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
Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
  match xl, esl with
  | [], [] => Some e
  | x::xl, es::esl => subst' x es <$> subst_l xl esl e
  | _, _ => None
  end.

Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                   (e : expr) : expr :=
  Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
  Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
Proof.
  revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
Qed.

(** The stepping relation *)
Definition lit_of_bool (b : bool) : base_lit :=
  LitInt (if b then 1 else 0).

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).

Fixpoint init_mem (l:loc) (init:list val) (σ:state) : state :=
  match init with
  | [] => σ
  | inith :: initq => <[l:=(RSt 0, inith)]>(init_mem (shift_loc l 1) initq σ)
  end.

Fixpoint free_mem (l:loc) (n:nat) (σ:state) : state :=
  match n with
  | O => σ
  | S n => delete l (free_mem (shift_loc l 1) n σ)
  end.

Inductive lit_eq (σ : state) : base_lit → base_lit → Prop :=
| IntRefl z : lit_eq σ (LitInt z) (LitInt z)
| LocRefl l : lit_eq σ (LitLoc l) (LitLoc l)
| LocUnallocL l1 l2 :
    σ !! l1 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2)
| LocUnallocR l1 l2 :
    σ !! l2 = None →
    lit_eq σ (LitLoc l1) (LitLoc l2).

Inductive lit_neq (σ : state) : base_lit → base_lit → Prop :=
| IntNeq z1 z2 :
    z1 ≠ z2 → lit_neq σ (LitInt z1) (LitInt z2)
| LocNeq l1 l2 :
    l1 ≠ l2 → lit_neq σ (LitLoc l1) (LitLoc l2).

Inductive bin_op_eval (σ : state) : bin_op → base_lit → base_lit → base_lit → Prop :=
| BinOpPlus z1 z2 :
    bin_op_eval σ PlusOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
| BinOpMinus z1 z2 :
    bin_op_eval σ MinusOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
| BinOpLe z1 z2 :
    bin_op_eval σ LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
| BinOpEqTrue l1 l2 :
    lit_eq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool true)
| BinOpEqFalse l1 l2 :
    lit_neq σ l1 l2 → bin_op_eval σ EqOp l1 l2 (lit_of_bool false)
| BinOpOffset l z :
    bin_op_eval σ OffsetOp (LitLoc l) (LitInt z) (LitLoc $ shift_loc l z).

Definition stuck_term := App (Lit $ LitInt 0) [].

Inductive head_step : expr → state → expr → state → list expr → Prop :=
| BinOpS op l1 l2 l' σ :
    bin_op_eval σ op l1 l2 l' →
    head_step (BinOp op (Lit l1) (Lit l2)) σ (Lit l') σ []
| BetaS f xl e e' el σ:
    Forall (λ ei, is_Some (to_val ei)) el →
    Closed (f :b: xl +b+ []) e →
    subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
    head_step (App (Rec f xl e) el) σ e' σ []
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
| CasFailS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) →
    lit_neq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ lit_of_bool false) σ  []
| CasSucS l e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt 0, LitV litl) →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              (Lit $ lit_of_bool true) (<[l:=(RSt 0, LitV lit2)]>σ)
              []
| CasStuckS l n e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ LitV lit2 →
    σ !! l = Some (RSt n, LitV litl) → 0 < n →
    lit_eq σ lit1 litl →
    head_step (CAS (Lit $ LitLoc l) e1 e2) σ
              stuck_term σ
              []
| AllocS n l init σ :
    0 < n →
    (∀ m, σ !! shift_loc l m = None) →
    Z.of_nat (length init) = n →
    head_step (Alloc $ Lit $ LitInt n) σ
              (Lit $ LitLoc l) (init_mem l init σ) []
| FreeS n l σ :
    0 < n →
    (∀ m, is_Some (σ !! shift_loc l m) ↔ 0 ≤ m < n) →
    head_step (Free (Lit $ LitInt n) (Lit $ LitLoc l)) σ
              (Lit LitUnit) (free_mem l (Z.to_nat n) σ)
              []
| CaseS i el e σ :
    0 ≤ i →
    el !! (Z.to_nat i) = Some e →
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

Lemma shift_loc_assoc l n n' :
  shift_loc (shift_loc l n) n' = shift_loc l (n+n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : shift_loc l 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) :
  shift_loc (shift_loc l n) n' = shift_loc l (n+n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : shift_loc l 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Instance shift_loc_inj l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_loc_block l n : (shift_loc l n).1 = l.1.
Proof. done. Qed.

Lemma lookup_init_mem σ (l l' : loc) vl :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + length vl →
  init_mem l vl σ !! l' = (RSt 0,) <$> vl !! Z.to_nat (l'.2 - l.2).
Proof.
  intros ?. destruct l' as [? n]; simplify_eq/=.
  revert n l. induction vl as [|v vl IH]=> /= n l Hl; [lia|].
  assert (n = l.2 ∨ l.2 + 1 ≤ n) as [->|?] by lia.
  { by rewrite -surjective_pairing lookup_insert Z.sub_diag. }
  rewrite lookup_insert_ne; last by destruct l; intros ?; simplify_eq/=; lia.
  rewrite -(shift_loc_block l 1) IH /=; last lia.
  cut (Z.to_nat (n - l.2) = S (Z.to_nat (n - (l.2 + 1)))); [by intros ->|].
  rewrite -Z2Nat.inj_succ; last lia. f_equal; lia.
Qed.

Lemma lookup_init_mem_Some σ (l l' : loc) vl :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + length vl → ∃ v,
  vl !! Z.to_nat (l'.2 - l.2) = Some v ∧
  init_mem l vl σ !! l' = Some (RSt 0,v).
Proof.
  intros. destruct (lookup_lt_is_Some_2 vl (Z.to_nat (l'.2 - l.2))) as [v Hv].
  { rewrite -(Nat2Z.id (length vl)). apply Z2Nat.inj_lt; lia. }
  exists v. by rewrite lookup_init_mem ?Hv.
Qed.

Lemma lookup_init_mem_ne σ (l l' : loc) vl :
  l.1 ≠ l'.1 ∨ l'.2 < l.2 ∨ l.2 + length vl ≤ l'.2 →
  init_mem l vl σ !! l' = σ !! l'.
Proof.
  revert l. induction vl as [|v vl IH]=> /= l Hl; auto.
  rewrite -(IH (shift_loc l 1)); last (simpl; intuition lia).
  apply lookup_insert_ne. intros ->; intuition lia.
Qed.

Definition fresh_block (σ : state) : block :=
  let loclst : list loc := elements (dom _ σ : gset loc) in
  let blockset : gset block := foldr (λ l, ({[l.1]} ∪)) ∅ loclst in
  fresh blockset.

Lemma is_fresh_block σ i : σ !! (fresh_block σ,i) = None.
Proof.
  assert (∀ (l : loc) ls (X : gset block),
    l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪)) X ls) as help.
  { induction 1; set_solver. }
  rewrite /fresh_block /shift_loc /= -not_elem_of_dom -elem_of_elements.
  move=> /(help _ _ ∅) /=. apply is_fresh.
Qed.

Lemma alloc_fresh n σ :
  let l := (fresh_block σ, 0) in
  let init := repeat (LitV $ LitInt 0) (Z.to_nat n) in
  0 < n →
  head_step (Alloc $ Lit $ LitInt n) σ (Lit $ LitLoc l) (init_mem l init σ) [].
Proof.
  intros l init Hn. apply AllocS. auto.
  - intros i. apply (is_fresh_block _ i).
  - rewrite repeat_length Z2Nat.id; lia.
Qed.

Lemma lookup_free_mem_ne σ l l' n : l.1 ≠ l'.1 → free_mem l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> l ? //=.
  rewrite lookup_delete_ne; last congruence.
  apply IH. by rewrite shift_loc_block.
Qed.

Lemma delete_free_mem σ l l' n :
  delete l (free_mem l' n σ) = free_mem l' n (delete l σ).
Proof.
  revert l'. induction n as [|n IH]=> l' //=. by rewrite delete_commute IH.
Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof.
  revert e X Y. fix 1; destruct e=>X Y/=; try naive_solver.
  - naive_solver set_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
  - rewrite !andb_True. intros [He Hel] HXY. split. by eauto.
    induction el=>/=; naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

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

Lemma subst_is_closed X x es e :
  is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
Proof.
  revert e X. fix 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
    try naive_solver; rewrite ?andb_True; intros.
  - set_solver.
  - eauto using is_closed_weaken with set_solver.
  - eapply is_closed_weaken; first done.
    destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
  - split; first naive_solver. induction el; naive_solver.
  - split; first naive_solver. induction el; naive_solver.
Qed.

Lemma subst'_is_closed X b es e :
  is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
Proof. destruct b; first done. apply subst_is_closed. Qed.

(* Operations on literals *)
Lemma lit_eq_state σ1 σ2 l1 l2 :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  lit_eq σ1 l1 l2 → lit_eq σ2 l1 l2.
Proof. intros Heq. inversion 1; econstructor; eauto; eapply Heq; done. Qed.

Lemma lit_neq_state σ1 σ2 l1 l2 :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  lit_neq σ1 l1 l2 → lit_neq σ2 l1 l2.
Proof. intros Heq. inversion 1; econstructor; eauto; eapply Heq; done. Qed.

Lemma bin_op_eval_state σ1 σ2 op l1 l2 l' :
  (∀ l, σ1 !! l = None ↔ σ2 !! l = None) →
  bin_op_eval σ1 op l1 l2 l' → bin_op_eval σ2 op l1 l2 l'.
Proof.
  intros Heq. inversion 1; econstructor; eauto using lit_eq_state, lit_neq_state.
Qed.

(* Misc *)
Lemma stuck_not_head_step σ e' σ' ef :
  ¬head_step stuck_term σ e' σ' ef.
Proof. inversion 1. Qed.

(** Equality and other typeclass stuff *)
Instance base_lit_dec_eq : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance bin_op_dec_eq : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance un_op_dec_eq : EqDecision order.
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
Instance expr_dec_eq : EqDecision expr.
Proof.
 refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
Defined.
Instance val_dec_eq : EqDecision val.
Proof.
 refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
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

(* Lemmas about the language. *)
Lemma stuck_irreducible K σ : irreducible (fill K stuck_term) σ.
Proof.
  intros ??? Hstep. edestruct step_is_head as (?&?&?&?); [..|by do 3 eexists|].
  - done.
  - clear. intros Ki K e' Heq (?&?&? & Hstep). destruct Ki; inversion Heq.
    + destruct K as [|Ki K].
      * simpl in *. subst. inversion Hstep.
      * destruct Ki; simpl in *; done.
    + destruct (of_val <$> vl); last done. destruct (fill K e'); done.
  - by eapply stuck_not_head_step.
Qed.

(* Define some derived forms *)
Notation Lam xl e := (Rec BAnon xl e).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV xl e := (RecV BAnon xl e).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Coercion lit_of_bool : bool >-> base_lit.
Notation If e0 e1 e2 := (Case e0 [e2;e1]).
Notation Newlft := (Lit LitUnit) (only parsing).
Notation Endlft := Skip (only parsing).
