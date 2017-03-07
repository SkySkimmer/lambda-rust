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
