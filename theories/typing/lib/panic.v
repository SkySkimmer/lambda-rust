From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

(* Minimal support for panic. Lambdarust does not support unwinding the
   stack. Instead, we just end the current thread by not calling any
   continuation.

   This properly models "panic=abort", but fails to take into account the
   trouble caused by unwinding. This is why we do not get into trouble with
   [take_mut]. *)

Section panic.
  Context `{typeG Σ}.

  Definition panic : val :=
    funrec: <> [] := #☠.

  Lemma panic_type : typed_val panic (fn(∅) → emp).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "!# *".
    inv_vec args.  iIntros (tid) "LFT HE Hna HL Hk HT /=". simpl_subst.
    wp_value. done.
  Qed.
End panic.
