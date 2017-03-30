From iris.base_logic.lib Require Import namespaces.
From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode memcpy.
Set Default Proof Using "Type".

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #()
    else Free "n" "loc".

Section specs.
  Context `{lrustG Σ}.

  Lemma wp_new E n:
    0 ≤ n →
    {{{ True }}} new [ #n ] @ E
    {{{ l vl, RET LitV $ LitLoc l;
        ⌜n = length vl⌝ ∗ (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗ l ↦∗ vl }}}.
  Proof.
    iIntros (? Φ) "HΦ". wp_lam. wp_op; intros ?.
    - wp_if. assert (n = 0) as -> by lia. iApply ("HΦ" $! _ []).
      rewrite heap_mapsto_vec_nil. auto.
    - wp_if. wp_alloc l vl as "H↦" "H†". iApply ("HΦ" $! _ vl).
      rewrite vec_to_list_length -{2}Hsz Z2Nat.id //. iFrame. auto.
  Qed.

  Lemma wp_delete E (n:Z) l vl :
    n = length vl →
    {{{ l ↦∗ vl ∗ (†l…(length vl) ∨ ⌜n = 0⌝) }}}
      delete [ #n; #l] @ E
    {{{ RET LitV LitUnit; True }}}.
  Proof.
    iIntros (? Φ) "(H↦ & [H†|%]) HΦ";
      wp_lam; wp_op; intros ?; try lia; wp_if; try wp_free; by iApply "HΦ".
  Qed.
End specs.

(* FIXME : why are these notations not pretty-printed? *)
Notation "'letalloc:' x <- e1 'in' e2" :=
  ((Lam (@cons binder x%E%E%E nil) (x <- e1 ;; e2)) [new [ #1]])%E
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
Notation "'letalloc:' x <-{ n } ! e1 'in' e2" :=
  ((Lam (@cons binder x%E%E%E nil) (x <-{n%Z%V} !e1 ;; e2)) [new [ #n]])%E
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
