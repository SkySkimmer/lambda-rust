From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Section typing.
  Context `{typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump E L C T k args T' :
    CCtx_iscont k L _ T' ∈ C →
    tctx_incl E L T (T' (list_to_vec args)) →
    typed_body E L C T (k (of_val <$> args)).
  Proof.
    iIntros (HC Hincl tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iMod (Hincl with "LFT HE HL HT") as "(HE & HL & HT)".
    iSpecialize ("HC" with "HE * []"); first done.
    rewrite -{3}(vec_to_list_of_list args). iApply ("HC" with "* Htl HL HT").
  Qed.

  Lemma type_cont E L1 L2 C T argsb econt e2 T' kb :
    Closed (kb :b: argsb +b+ []) econt → Closed (kb :b: []) e2 →
    (∀ k args, typed_body E L1 (CCtx_iscont k L1 _ T' :: C) (T' args)
                          (subst_v (kb::argsb) (k:::args) econt)) →
    (∀ k, typed_body E L2 (CCtx_iscont k L1 _ T' :: C) T (subst' kb k e2)) →
    typed_body E L2 C T (let: kb := Rec kb argsb econt in e2).
  Proof.
    iIntros (Hc1 Hc2 Hecont He2 tid qE) "#HEAP #LFT Htl HE HL HC HT". iApply wp_let'.
    { simpl. rewrite decide_left. done. }
    iModIntro. iApply (He2 with "* HEAP LFT Htl HE HL [HC] HT"). clear He2.
    iIntros "HE". iLöb as "IH". iIntros (x) "H".
    iDestruct "H" as %[->|?]%elem_of_cons; last by iApply ("HC" with "HE *").
    iIntros (args) "Htl HL HT". iApply wp_rec; try done.
    { rewrite Forall_fmap Forall_forall=>? _. rewrite /= to_of_val. eauto. }
    { by rewrite -(subst_v_eq (_ :: _) (RecV _ _ _ ::: _)). }
    (* FIXME: iNext here unfolds things in the context. *)
    iNext. iApply (Hecont with "* HEAP LFT Htl HE HL [HC] HT").
    by iApply "IH".
  Qed.
End typing.
