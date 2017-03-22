From lrust.lang Require Export lang.
Set Default Proof Using "Type".

Coercion LitInt : Z >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion Var : string >-> expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : lrust_binder_scope.

Notation "[ x ]" := (@cons expr x%E (@nil expr)) : expr_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons expr x1%E (@cons expr x2%E
        (..(@cons expr xn%E (@nil expr))..))) : expr_scope.

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%V) (at level 8, format "# l") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "'case:' e0 'of' el" := (Case e0%E el%E)
  (at level 102, e0, el at level 150) : expr_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (only parsing, at level 102, e1, e2, e3 at level 150) : expr_scope.
Notation "()" := LitUnit : val_scope.
Notation "! e" := (Read Na1Ord e%E) (at level 9, format "! e") : expr_scope.
Notation "!ˢᶜ e" := (Read ScOrd e%E) (at level 9, format "!ˢᶜ e") : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E)
  (at level 70) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <-ˢᶜ e2" := (Write ScOrd e1%E e2%E)
  (at level 80) : expr_scope.
Notation "e1 <- e2" := (Write Na1Ord e1%E e2%E)
  (at level 80) : expr_scope.
Notation "'rec:' f xl := e" := (Rec f%RustB xl%RustB e%E)
  (at level 102, f, xl at level 1, e at level 200) : expr_scope.
Notation "'rec:' f xl := e" := (locked (RecV f%RustB xl%RustB e%E))
  (at level 102, f, xl at level 1, e at level 200) : val_scope.
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.

(** Derived notions. The notations for let and seq are stated
explicitly instead of relying on the Notations Let and Seq as defined
above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)

Notation "λ: xl , e" := (Lam xl%RustB e%E)
  (at level 102, xl at level 1, e at level 200) : expr_scope.
Notation "λ: xl , e" := (locked (LamV xl%RustB e%E))
  (at level 102, xl at level 1, e at level 200) : val_scope.

Notation "'funrec:' f xl := e" := (rec: f ("return"::xl) := e)%E
  (only parsing, at level 102, f, xl at level 1, e at level 200) : expr_scope.
Notation "'funrec:' f xl := e" := (rec: f ("return"::xl) := e)%V
  (only parsing, at level 102, f, xl at level 1, e at level 200) : val_scope.
Notation "'return:'" := "return" : expr_scope.

Notation "'let:' x := e1 'in' e2" :=
  ((Lam (@cons binder x%RustB nil) e2%E) (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%E
  (at level 100, e2 at level 150, format "e1  ;;  e2") : expr_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" :=
  (LamV (@cons binder x%RustB nil) e2%E (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : val_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%V
  (at level 100, e2 at level 150, format "e1  ;;  e2") : val_scope.

Notation "'letcont:' k xl := e1 'in' e2" :=
  ((Lam (@cons binder k%RustB nil) e2%E) [Rec k%RustB xl%RustB e1%E])
  (at level 102, k, xl at level 1, e1, e2 at level 150) : expr_scope.
Notation "'withcont:' k1 ':' e1 'cont:' k2 xl := e2" :=
  ((Lam (@cons binder k1%RustB nil) e1%E) [Rec k2%RustB ((fun _ : eq k1%RustB k2%RustB => xl%RustB) eq_refl) e2%E])
  (only parsing, at level 151, k1, k2, xl at level 1, e2 at level 150) : expr_scope.

Notation "'call:' f args → k" := (f (@cons expr (λ: ["_r"], Endlft ;; k ["_r"]) args))%E
  (only parsing, at level 102, f, args, k at level 1) : expr_scope.
Notation "'letcall:' x := f args 'in' e" :=
  (letcont: "_k" [ x ] := e in call: f args → "_k")%E
  (at level 102, x, f, args at level 1, e at level 150) : expr_scope.

(* RJ: These notations unfortunately do not print.  Also, I don't think
   we would even want them to print in general.
   TODO: Introduce a Definition. *)
Notation "e1 '<-{Σ' i } '()'" := (e1 <- #i)%E
  (only parsing, at level 80, format "e1  <-{Σ  i }  ()" ) : expr_scope.
Notation "e1 '<-{Σ' i } e2" := (e1 <-{Σ i} () ;; e1+ₗ#1 <- e2)%E
  (at level 80, format "e1 <-{Σ  i }  e2") : expr_scope.
