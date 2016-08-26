From lrust Require Export derived.

Coercion LitInt : Z >-> base_lit.
Coercion LitLoc : loc >-> base_lit.

Coercion App : expr >-> Funclass.
Coercion of_val : val >-> expr.

Coercion Var : string >-> expr.

Coercion BNamed : string >-> binder.
Notation "<>" := BAnon : lrust_binder_scope.

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%V) (at level 8, format "# l") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "'case:' e0 'of' [ e1 , .. , en ]" :=
  (Case e0%E (cons e1%E .. (cons en%E nil) ..))
  (e0, e1, en at level 200) : expr_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (at level 200, e1, e2, e3 at level 200) : expr_scope.
Notation "()" := LitUnit : val_scope.
Notation "* e" := (Read Na1Ord e%E)
  (at level 9, right associativity) : expr_scope.
Notation "*ˢᶜ e" := (Read ScOrd e%E)
  (at level 9, right associativity) : expr_scope.
Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <-ˢᶜ e2" := (Write ScOrd e1%E e2%E)
  (at level 80) : expr_scope.
Notation "e1 <- e2" := (Write Na1Ord e1%E e2%E)
  (at level 80) : expr_scope.
Notation "'rec:' f [ x1 ; .. ; xn ] := e" :=
  (Rec f%RustB ( @cons binder x1%RustB ( .. (@cons binder xn%RustB nil) ..)) e%E)
  (at level 102, f at level 1, x1 at level 1, xn at level 1, e at level 200) : expr_scope.
Notation "'rec:' f [ x1 ; .. ; xn ] := e" :=
  (RecV f%RustB ( @cons binder x1%RustB ( .. (@cons binder xn%RustB nil) ..)) e%E)
  (at level 102, f at level 1, x1 at level 1, xn at level 1, e at level 200) : val_scope.
Notation "'rec:' f [ ] := e" := (Rec f%RustB nil e%E)
  (at level 102, f at level 1, e at level 200) : expr_scope.
Notation "'rec:' f [ ] := e" := (RecV f%RustB nil e%E)
  (at level 102, f at level 1, e at level 200) : val_scope.
Notation "e1 +ₗ e2" := (BinOp ProjOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.

(** Derived notions, in order of declaration. The notations for let and seq
are stated explicitly instead of relying on the Notations Let and Seq as
defined above. This is needed because App is now a coercion, and these
notations are otherwise not pretty printed back accordingly. *)
Notation "λ: [ x1 ; .. ; xn ] , e" :=
  (Lam ( @cons binder x1%RustB ( .. (@cons binder xn%RustB nil) ..)) e%E)
  (at level 102, x1 at level 1, xn at level 1, e at level 200) : expr_scope.
Notation "λ: [ x1 ; .. ; xn ] , e" :=
  (LamV ( @cons binder x1%RustB ( .. (@cons binder xn%RustB nil) ..)) e%E)
  (at level 102, x1 at level 1, xn at level 1, e at level 200) : val_scope.
Notation "λ: [ ] , e" := (Lam nil e%E)
  (at level 102, e at level 200) : expr_scope.
Notation "λ: [ ] , e" := (LamV nil e%E)
  (at level 102, e at level 200) : val_scope.

Notation "'let:' x := e1 'in' e2" := (Lam [x%RustB] e2%E [e1%E])
  (at level 102, x at level 1, e1, e2 at level 200) : expr_scope.
Notation "e1 ;; e2" := (Lam [BAnon] e2%E [e1%E])
  (at level 100, e2 at level 200, format "e1  ;;  e2") : expr_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" := (LamV [x%RustB] e2%E [e1%E])
  (at level 102, x at level 1, e1, e2 at level 200) : val_scope.
Notation "e1 ;; e2" := (LamV [BAnon] e2%E [e1%E])
  (at level 100, e2 at level 200, format "e1  ;;  e2") : val_scope.

Notation "e1 <-[ i ] '☇'" := (e1 <- #i)%E
  (only parsing, at level 80) : expr_scope.
Notation "e1 <-[ i ] e2" := (e1<-[i] ☇ ;; e1+ₗ#1 <- e2)%E
 (at level 80) : expr_scope.
