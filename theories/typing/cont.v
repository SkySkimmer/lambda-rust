From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section typing.
  Context `{typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump args E L C T k T' :
    (k ◁cont(L, T'))%CC ∈ C →
    tctx_incl E L T (T' (list_to_vec args)) →
    typed_body E L C T (k (of_val <$> args)).
  Proof.
    iIntros (HC Hincl) "!#". iIntros (tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iMod (Hincl with "LFT HE HL HT") as "(HE & HL & HT)".
    iSpecialize ("HC" with "HE * []"); first done.
    rewrite -{3}(vec_to_list_of_list args). iApply ("HC" with "* Htl HL HT").
  Qed.

  Lemma type_cont argsb L1 (T' : vec val (length argsb) → _) E L2 C T econt e2 kb :
    Closed (kb :b: argsb +b+ []) econt → Closed (kb :b: []) e2 →
    (∀ k, typed_body E L2 (k ◁cont(L1, T') :: C) T (subst' kb k e2)) →
    (∀ k (args : vec val (length argsb)),
       typed_body E L1 (k ◁cont(L1, T') :: C) (T' args) (subst_v (kb::argsb) (k:::args) econt)) →
    typed_body E L2 C T (e2 cont: kb argsb := econt).
  Proof.
    iIntros (Hc1 Hc2 He2 Hecont) "!#". iIntros (tid qE) "#HEAP #LFT Htl HE HL HC HT". iApply wp_let'.
    { simpl. rewrite decide_left. done. }
    iModIntro. iApply (He2 with "* HEAP LFT Htl HE HL [HC] HT"). clear He2.
    iIntros "HE". iLöb as "IH". iIntros (x) "H".
    iDestruct "H" as %[->|?]%elem_of_cons; last by iApply ("HC" with "HE *").
    iIntros (args) "Htl HL HT". iApply wp_rec; try done.
    { rewrite Forall_fmap Forall_forall=>? _. rewrite /= to_of_val. eauto. }
    { by rewrite -(subst_v_eq (_ :: _) (RecV _ _ _ ::: _)). }
    iNext. iApply (Hecont with "* HEAP LFT Htl HE HL [HC] HT").
    by iApply "IH".
  Qed.
End typing.
