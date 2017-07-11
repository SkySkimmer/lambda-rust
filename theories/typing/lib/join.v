From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition joinN := lrustN .@ "join".

Section join.
  Context `{!typeG Σ}.

  (* This model is very far from rayon::join, which uses a persistent work-stealing thread-pool.
     Still, the important bits are right:  One of the closures is executed in another thread,
     and the closures can refer to on-stack data (no 'static' bound). *)
  Definition join (call_once_A call_once_B : val) (R_A R_B : type) : val :=
    funrec: <> ["fA"; "fB"] :=
      let: "call_once_A" := call_once_A in
      let: "call_once_B" := call_once_B in
      let: "join" := spawn [λ: ["c"],
                            letcall: "r" := "call_once_A" ["fA":expr] in
                            finish ["c"; "r"]] in
      let: "retB" := "call_once_B" ["fB":expr] in
      let: "retA" := join ["join"] in
      (* Put the results in a pair. *)
      let: "ret" := new [ #(R_A.(ty_size) + R_B.(ty_size)) ] in
      "ret" +ₗ #0 <- "retA";; "ret" +ₗ #R_A.(ty_size) <- "retB";;
      delete [ #R_A.(ty_size); "retA"] ;; delete [ #R_B.(ty_size); "retB"] ;;
      return: ["ret"].

  Lemma join_type A B R_A R_B call_once_A call_once_B
        `{!TyWf A, !TyWf B, !TyWf R_A, !TyWf R_B}
        `(!Send A, !Send B, !Send R_A, !Send R_B) :
    typed_val call_once_A (fn(∅; A) → R_A) → (* A : FnOnce() -> R_A, as witnessed by the impl call_once_A *)
    typed_val call_once_B (fn(∅; B) → R_B) → (* B : FnOnce() -> R_B, as witnessed by the impl call_once_B *)
    typed_val (join call_once_A call_once_B R_A R_B) (fn(∅; A, B) → Π[R_A; R_B]).
  Proof.
  Abort.

End join.
