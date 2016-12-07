From iris.proofmode Require Import tactics.
From iris.program_logic Require Import hoare.
From lrust.lifetime Require Import borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl typing.

Section fn.
  Context `{iris_typeG Σ}.

  Program Definition cont {n : nat} (ρ : vec val n → @perm Σ) :=
    {| ty_size := 1;
       ty_own tid vl := (∃ f, ⌜vl = [f]⌝ ∗
          ∀ vl, ρ vl tid -∗ na_own tid ⊤
                 -∗ WP f (map of_val vl) {{λ _, False}})%I;
       ty_shr κ tid N l := True%I |}.
  Next Obligation.
    iIntros (n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.
  Next Obligation. intros. by iIntros "_ _ $". Qed.
  Next Obligation. intros. by iIntros "_ _ _". Qed.

  (* TODO : For now, functions are not Send. This means they cannot be
     called in another thread than the one that created it.  We will
     need Send functions when dealing with multithreading ([fork]
     needs a Send closure). *)
  Program Definition fn {A n} (ρ : A -> vec val n → @perm Σ) : type :=
    {| st_size := 1;
       st_own tid vl := (∃ f, ⌜vl = [f]⌝ ∗ ∀ x vl,
         {{ ρ x vl tid ∗ na_own tid ⊤ }} f (map of_val vl) {{λ _, False}})%I |}.
  Next Obligation.
    iIntros (x n ρ tid vl) "H". iDestruct "H" as (f) "[% _]". by subst.
  Qed.

  Lemma ty_incl_cont {n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ vl : vec val n, ρ ∗ ρ2 vl ⇒ ρ1 vl) →
    ty_incl ρ (cont ρ1) (cont ρ2).
  Proof.
    iIntros (? Hρ1ρ2 tid) "#LFT #Hρ!>". iSplit; iIntros "!#*H"; last by auto.
    iDestruct "H" as (f) "[% Hwp]". subst. iExists _. iSplit. done.
    iIntros (vl) "Hρ2 Htl". iApply ("Hwp" with ">[-Htl] Htl").
    iApply (Hρ1ρ2 with "LFT"). by iFrame.
  Qed.

  Lemma ty_incl_fn {A n} ρ ρ1 ρ2 :
    Duplicable ρ → (∀ (x : A) (vl : vec val n), ρ ∗ ρ2 x vl ⇒ ρ1 x vl) →
    ty_incl ρ (fn ρ1) (fn ρ2).
  Proof.
    iIntros (? Hρ1ρ2 tid) "#LFT #Hρ!>". iSplit; iIntros "!#*#H".
    - iDestruct "H" as (f) "[% Hwp]". subst. iExists _. iSplit. done.
      iIntros (x vl) "!#[Hρ2 Htl]". iApply ("Hwp" with ">").
      iFrame. iApply (Hρ1ρ2 with "LFT"). by iFrame.
    - iSplit; last done. simpl. iDestruct "H" as (vl0) "[? Hvl]".
      iExists vl0. iFrame "#". iNext. iDestruct "Hvl" as (f) "[% Hwp]".
      iExists f. iSplit. done. iIntros (x vl) "!#[Hρ2 Htl]".
      iApply ("Hwp" with ">"). iFrame. iApply (Hρ1ρ2 with "LFT >"). by iFrame.
  Qed.

  Lemma ty_incl_fn_cont {A n} ρ ρf (x : A) :
    ty_incl ρ (fn ρf) (cont (n:=n) (ρf x)).
  Proof.
    iIntros (tid) "#LFT _!>". iSplit; iIntros "!#*H"; last by iSplit.
    iDestruct "H" as (f) "[%#H]". subst. iExists _. iSplit. done.
    iIntros (vl) "Hρf Htl". iApply "H". by iFrame.
  Qed.

  Lemma ty_incl_fn_specialize {A B n} (f : A → B) ρ ρfn :
    ty_incl ρ (fn (n:=n) ρfn) (fn (ρfn ∘ f)).
  Proof.
    iIntros (tid) "_ _!>". iSplit; iIntros "!#*H".
    - iDestruct "H" as (fv) "[%#H]". subst. iExists _. iSplit. done.
      iIntros (x vl). by iApply "H".
    - iSplit; last done.
      iDestruct "H" as (fvl) "[?Hown]". iExists _. iFrame. iNext.
      iDestruct "Hown" as (fv) "[%H]". subst. iExists _. iSplit. done.
      iIntros (x vl). by iApply "H".
  Qed.

  Lemma typed_fn {A n} `{Duplicable _ ρ, Closed (f :b: xl +b+ []) e} θ :
    length xl = n →
    (∀ (a : A) (vl : vec val n) (fv : val) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (fv ◁ fn θ ∗ (θ a vl) ∗ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (fn θ).
  Proof.
    iIntros (Hn He tid) "!#(#HEAP&#LFT&#Hρ&$)".
    assert (Rec f xl e = RecV f xl e) as -> by done. iApply wp_value'.
    rewrite has_type_value.
    iLöb as "IH". iExists _. iSplit. done. iIntros (a vl) "!#[Hθ?]".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply He. done. iFrame "∗#". by rewrite has_type_value.
  Qed.

  Lemma typed_cont {n} `{Closed (f :b: xl +b+ []) e} ρ θ :
    length xl = n →
    (∀ (fv : val) (vl : vec val n) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (fv ◁ cont (λ vl, ρ ∗ θ vl)%P ∗ (θ vl) ∗ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (cont θ).
  Proof.
    iIntros (Hn He tid) "!#(#HEAP&#LFT&Hρ&$)". specialize (He (RecV f xl e)).
    assert (Rec f xl e = RecV f xl e) as -> by done. iApply wp_value'.
    rewrite has_type_value.
    iLöb as "IH". iExists _. iSplit. done. iIntros (vl) "Hθ ?".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply He. done. iFrame "∗#". rewrite has_type_value.
    iExists _. iSplit. done. iIntros (vl') "[Hρ Hθ] Htl".
    iDestruct ("IH" with "Hρ") as (f') "[Hf' IH']".
    iDestruct "Hf'" as %[=<-]. iApply ("IH'" with "Hθ Htl").
  Qed.

End fn.
