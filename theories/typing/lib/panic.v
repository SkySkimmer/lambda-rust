From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

(* Minimal support for panic. Lambdarust does not support unwinding
   the stack. Instead, we just end the current thread by not calling
   any continuation.

   Note that this is not very faithfull, because e.g., [spawn] will
   not be notified that the thread has finished. This is why we do not
   get into trouble with [take_mut]. *)

Section panic.
  Context `{typeG Σ}.

  Definition panic : val :=
    funrec: <> [] := #().

  Lemma panic_type ty `{!TyWf ty} : typed_val panic (fn(∅) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "!# *".
    inv_vec args.  iIntros (tid) "LFT HE Hna HL Hk HT /=". simpl_subst.
    wp_value. done.
  Qed.
End panic.