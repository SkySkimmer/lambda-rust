From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Section typing.
  Context `{typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump {n} E L k T' T (args : vec val n) :
    tctx_incl E L T (T' args) →
    typed_body E L [CCtx_iscont k L n T'] T (k (of_val <$> (args : list _))).
  Proof.
    iIntros (Hincl tid qE) "#HEAP #LFT HE HL HC HT".
    iMod (Hincl with "LFT HE HL HT") as "(HE & HL & HT)".
    iSpecialize ("HC" with "HE * []"); first by (iPureIntro; apply elem_of_list_singleton).
    simpl. iApply ("HC" with "* HL HT").
  Qed.

  Lemma type_cont {n} E L1 L2 C T T' kb (argsb : vec binder n) e1 econt e2 :
    e1 = Rec kb argsb econt → Closed (kb :b: argsb +b+ []) econt → Closed (kb :b: []) e2 →
    (∀ k args, typed_body E L1 (CCtx_iscont k L1 n T' :: C) (T' args)
                          (subst' kb k $ subst_vec argsb (Vector.map of_val $ args) econt)) →
    (∀ k, typed_body E (L1 ++ L2) (CCtx_iscont k L1 n T' :: C) T (subst' kb k e2)) →
    typed_body E (L1 ++ L2) C T (let: kb := e1 in e2).
  Proof.
    iIntros (-> Hc1 Hc2 Hecont He2 tid qE) "#HEAP #LFT HE HL HC HT". iApply wp_let'.
    { simpl. rewrite decide_left. done. }
    iModIntro. iApply (He2 with "* HEAP LFT HE HL [HC] HT"). clear He2.
    iIntros "HE". iLöb as "IH". iIntros (x) "H".
    iDestruct "H" as %[->|?]%elem_of_cons; last by iApply ("HC" with "HE *").
    iIntros (args) "HL HT". iApply wp_rec; try done.
    { apply Forall_of_val_is_val. }
    { rewrite -vec_to_list_map -subst_vec_eq. eauto. }
    (* FIXME: iNext here unfolds things in the context. *)
    iNext. iApply (Hecont with "* HEAP LFT HE HL [HC] HT").
    by iApply "IH".
  Qed.

End typing.
