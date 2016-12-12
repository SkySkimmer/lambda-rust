From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl.

Section sum.
  Context `{typeG Σ}.

  Program Definition emp : type := {| st_size := 0; st_own tid vl := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Global Instance emp_empty : Empty type := emp.

  Lemma split_sum_mt l tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl', ⌜vl = #i :: vl'⌝ ∗ ty_own (nth i tyl ∅) tid vl')%I
    ⊣⊢ ∃ (i : nat), l ↦{q} #i ∗ shift_loc l 1 ↦∗{q}: ty_own (nth i tyl ∅) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl') "[% Hown]".
      subst. iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[Hmt1 Hown]". iDestruct "Hown" as (vl) "[Hmt2 Hown]".
      iExists (#i::vl). rewrite heap_mapsto_vec_cons. iFrame. eauto.
  Qed.

  Class LstTySize (n : nat) (tyl : list type) :=
    size_eq : Forall ((= n) ∘ ty_size) tyl.
  Instance LstTySize_nil n : LstTySize n nil := List.Forall_nil _.
  Lemma LstTySize_cons n ty tyl :
    ty.(ty_size) = n → LstTySize n tyl → LstTySize n (ty :: tyl).
  Proof. intros. constructor; done. Qed.

  Lemma sum_size_eq n tid i tyl vl {Hn : LstTySize n tyl} :
    ty_own (nth i tyl ∅) tid vl -∗ ⌜length vl = n⌝.
  Proof.
    iIntros "Hown". iDestruct (ty_size_eq with "Hown") as %->.
    revert Hn. rewrite /LstTySize List.Forall_forall /= =>Hn.
    edestruct nth_in_or_default as [| ->]. by eauto.
    iDestruct "Hown" as "[]".
  Qed.

  Program Definition sum {n} (tyl : list type) {_:LstTySize n tyl} :=
    {| ty_size := S n;
       ty_own tid vl :=
         (∃ (i : nat) vl', ⌜vl = #i :: vl'⌝ ∗ (nth i tyl ∅).(ty_own) tid vl')%I;
       ty_shr κ tid N l :=
         (∃ (i : nat), (&frac{κ} λ q, l ↦{q} #i) ∗
               (nth i tyl ∅).(ty_shr) κ tid N (shift_loc l 1))%I
    |}.
  Next Obligation.
    iIntros (n tyl Hn tid vl) "Hown". iDestruct "Hown" as (i vl') "(%&Hown)".
    subst. simpl. by iDestruct (sum_size_eq with "Hown") as %->.
  Qed.
  Next Obligation.
    intros n tyl Hn E N κ l tid ??. iIntros "#LFT Hown". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Hown") as (i) "Hown". set_solver.
    iMod (bor_sep with "LFT Hown") as "[Hmt Hown]". set_solver.
    iMod ((nth i tyl ∅).(ty_share) with "LFT Hown") as "#Hshr"; try done.
    iMod (bor_fracture with "LFT [-]") as "H"; last by eauto. set_solver. iFrame.
  Qed.
  Next Obligation.
    intros n tyl Hn κ κ' tid E E' l ?. iIntros "#LFT #Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i. iSplitL "Hown0".
    by iApply (frac_bor_shorten with "Hord").
    iApply ((nth i tyl ∅).(ty_shr_mono) with "LFT Hord"); last done. done.
  Qed.

  (* TODO : Make the Forall parameter a typeclass *)
  Global Program Instance sum_copy `(LstTySize n tyl) :
    Forall Copy tyl → Copy (sum tyl).
  Next Obligation.
    intros n tyl Hn HFA tid vl.
    cut (∀ i vl', PersistentP (ty_own (nth i tyl ∅) tid vl')). by apply _.
    intros. apply @copy_persistent. edestruct nth_in_or_default as [| ->];
      [by eapply List.Forall_forall| apply _].
  Qed.
  Next Obligation.
    intros n tyl Hn HFA κ tid E F l q ?.
    iIntros "#LFT #H[[Htok1 Htok2] Htl]".
    setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 Hshr]".
    iMod (frac_bor_acc with "LFT Hshr0 Htok1") as (q'1) "[Hown Hclose]". set_solver.
    iMod (@copy_shr_acc _ _ (nth i tyl ∅) with "LFT Hshr [Htok2 $Htl]")
      as (q'2) "[Hownq Hclose']"; try done.
    { edestruct nth_in_or_default as [| ->]; last by apply _.
        by eapply List.Forall_forall. }
    destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
    rewrite -{1}heap_mapsto_vec_prop_op; last (by intros; apply sum_size_eq, Hn).
    iDestruct "Hownq" as "[Hownq1 Hownq2]". iDestruct "Hown" as "[Hown1 >Hown2]".
    iExists q'. iModIntro. iSplitL "Hown1 Hownq1".
    - iNext. iExists i. by iFrame.
    - iIntros "H". iDestruct "H" as (i') "[>Hown1 Hownq1]".
      iDestruct (heap_mapsto_agree with "[$Hown1 $Hown2]") as %[= ->%Z_of_nat_inj].
      iCombine "Hown1" "Hown2" as "Hown". iMod ("Hclose" with "[Hown]") as "$"; first by eauto.
      iCombine "Hownq1" "Hownq2" as "Hownq".
      rewrite heap_mapsto_vec_prop_op; last (by intros; apply sum_size_eq, Hn).
      by iApply "Hclose'".
  Qed.
End sum.

Existing Instance LstTySize_nil.
Hint Extern 1 (LstTySize _ (_ :: _)) =>
  apply LstTySize_cons; [compute; reflexivity|] : typeclass_instances.


(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1 (..(cons tyn nil)..))) : lrust_type_scope.

Section incl.
  Context `{typeG Σ}.

   (* FIXME : do we need that anywhere?. *)
  Lemma ty_incl_emp ρ ty : ty_incl ρ ∅ ty.
  Proof.
  Admitted.

  Lemma ty_incl_sum ρ n tyl1 tyl2 (_ : LstTySize n tyl1) (_ : LstTySize n tyl2) :
    Duplicable ρ → Forall2 (ty_incl ρ) tyl1 tyl2 →
    ty_incl ρ (sum tyl1) (sum tyl2).
  Proof.
    iIntros (DUP FA tid) "#LFT #Hρ". rewrite /sum /=. iSplitR "".
    - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗
         (□ ∀ i vl, (nth i tyl1 ∅%T).(ty_own) tid vl
                  → (nth i tyl2 ∅%T).(ty_own) tid vl)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "_ _!>*!#". eauto.
        - iIntros "#LFT #Hρ". iMod (IH with "LFT Hρ") as "#IH".
          iMod (Hincl with "LFT Hρ") as "[#Hh _]".
          iIntros "!>*!#*Hown". destruct i as [|i]. by iApply "Hh". by iApply "IH". }
      iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H".
      iDestruct "H" as (i vl') "[% Hown]". subst. iExists _, _. iSplit. done.
        by iApply "Hincl".
    - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗
         (□ ∀ i κ E l, (nth i tyl1 ∅%T).(ty_shr) κ tid E l
                     → (nth i tyl2 ∅%T).(ty_shr) κ tid E l)).
      { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH].
        - iIntros "#LFT _!>*!#". eauto.
        - iIntros "#LFT #Hρ".
          iMod (IH with "LFT Hρ") as "#IH". iMod (Hincl with "LFT Hρ") as "[_ #Hh]".
          iIntros "!>*!#*Hown". destruct i as [|i]; last by iApply "IH".
          by iDestruct ("Hh" $! _ _ _ with "Hown") as "[$ _]". }
      iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H". iSplit; last done.
      iDestruct "H" as (i) "[??]". iExists _. iSplit. done. by iApply "Hincl".
  Qed.
End incl.
