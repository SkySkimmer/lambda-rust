From lrust.lang Require Export proofmode.
From lrust.lifetime Require Export frac_borrow.

Create HintDb lrust_typing.
Create HintDb lrust_typing_merge.

(* We first try to solve everything without the merging rules, and
   then start from scratch with them.

   The reason is that we want we want the search proof search for
   [tctx_extract_hasty] to suceed even if the type is an evar, and
   merging makes it diverge in this case. *)
Ltac solve_typing :=
  (typeclasses eauto with lrust_typing typeclass_instances core; fail) ||
  (typeclasses eauto with lrust_typing lrust_typing_merge typeclass_instances core; fail).

Lemma of_val_unlock v e : of_val v = e → of_val (locked v) = e.
Proof. by unlock. Qed.

Hint Constructors Forall Forall2 elem_of_list : lrust_typing.
Hint Resolve
     of_val_unlock
     submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : lrust_typing.

Hint Extern 1 (@eq nat _ (Z.to_nat _)) =>
  (etrans; [symmetry; exact: Nat2Z.id | reflexivity]) : lrust_typing.
Hint Extern 1 (@eq nat (Z.to_nat _) _) =>
  (etrans; [exact: Nat2Z.id | reflexivity]) : lrust_typing.

(* FIXME : I would prefer using a [Hint Resolve <-] for this, but
   unfortunately, this is not preserved across modules. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5189
   This should be fixed in the next version of Coq. *)
Hint Extern 1 (_ ∈ _ ++ _) => apply <- @elem_of_app : lrust_typing.
