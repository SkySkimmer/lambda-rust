From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl.

Section sum.
  Context `{typeG Σ}.

  Local Obligation Tactic := idtac.

  Program Definition emp : type := {| st_own tid vl := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Global Instance emp_empty : Empty type := emp.

  Definition list_max (l : list nat) := foldr max 0%nat l.

  Lemma split_sum_mt l tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                               ⌜length vl = S (list_max $ map ty_size $ tyl)⌝ ∗
                               ty_own (nth i tyl ∅) tid vl')%I
    ⊣⊢ ∃ (i : nat), l ↦{q} #i ∗ shift_loc l 1 ↦∗{q}: (nth i tyl ∅).(ty_own) tid ∗
                     shift_loc l (S $ (nth i tyl ∅).(ty_size)) ↦∗{q}: λ vl,
                       ⌜((nth i tyl ∅).(ty_size) + length vl)%nat = (list_max $ map ty_size $ tyl)⌝.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl' vl'') "(% & % & Hown)".
      subst. iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      (* TODO: I should not have to say '[#]' here, similar to iDestruct ... as %.... *)
      iAssert (⌜length vl' = (nth i tyl ∅).(ty_size)⌝%I) with "[#]" as %Hvl'.
      { iApply ty_size_eq. done. }
      iDestruct (heap_mapsto_vec_app with "Hmt") as "[Hmt Htail]". iSplitR "Htail".
      + iExists vl'. by iFrame.
      + iExists vl''. rewrite (shift_loc_assoc_nat _ 1) Hvl'. iFrame. iPureIntro.
        rewrite -Hvl'. simpl in *. rewrite -app_length. congruence.
    - iDestruct "H" as (i) "(Hmt1 & Hown & Htail)".
      iDestruct "Hown" as (vl') "[Hmt2 Hown]". iDestruct "Htail" as (vl'') "[Hmt3 %]".
      (* TODO: I should not have to say '[#]' here, similar to iDestruct ... as %.... *)
      iAssert (⌜length vl' = (nth i tyl ∅).(ty_size)⌝%I) with "[#]" as %Hvl'.
      { iApply ty_size_eq. done. } iExists (#i::vl'++vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Hvl'.
      iFrame. iExists i, vl', vl''. iSplit; first done. iFrame. iPureIntro.
      simpl. f_equal. by rewrite app_length Hvl'.
  Qed.

  Program Definition sum (tyl : list type) :=
    {| ty_size := S (list_max $ map ty_size $ tyl);
       ty_own tid vl :=
         (∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                                ⌜length vl = S (list_max $ map ty_size $ tyl)⌝ ∗
                                (nth i tyl ∅).(ty_own) tid vl')%I;
       ty_shr κ tid N l :=
         (∃ (i : nat), (&frac{κ} λ q, l ↦{q} #i) ∗
               (nth i tyl ∅).(ty_shr) κ tid N (shift_loc l 1) ∗
               (&frac{κ} λ q, shift_loc l (S $ (nth i tyl ∅).(ty_size)) ↦∗{q}: λ vl,
                       ⌜((nth i tyl ∅).(ty_size) + length vl)%nat = (list_max $ map ty_size $ tyl)⌝))%I
    |}.
  Next Obligation.
    iIntros (tyl tid vl) "Hown". iDestruct "Hown" as (i vl' vl'') "(%&%&_)".
    subst. done.
  Qed.
  Next Obligation.
    intros tyl E N κ l tid ??. iIntros "#LFT Hown". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Hown") as (i) "Hown". set_solver.
    iMod (bor_sep with "LFT Hown") as "[Hmt Hown]". solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hown Htail]". solve_ndisj.
    iMod ((nth i tyl ∅).(ty_share) with "LFT Hown") as "#Hshr"; try done.
    iMod (bor_fracture with "LFT [Htail]") as "H";[set_solver| |]; last first.
    - iMod (bor_fracture with "LFT [Hmt]") as "H'";[set_solver| |]; last eauto.
      by iFrame.
    - by iFrame.
  Qed.
  Next Obligation.
    intros tyl κ κ' tid E E' l ?. iIntros "#LFT #Hord H".
    iDestruct "H" as (i) "[Hown0 [Hown Htail]]". iExists i.
    iSplitL "Hown0"; last iSplitL "Hown".
    - by iApply (frac_bor_shorten with "Hord").
    - iApply ((nth i tyl ∅).(ty_shr_mono) with "LFT Hord"); last done. done.
    - by iApply (frac_bor_shorten with "Hord").
  Qed.

  (* TODO : Make the Forall parameter a typeclass *)
  (* TODO : This next step is suspuciously slow. *)
  Global Program Instance sum_copy tyl :
    Forall Copy tyl → Copy (sum tyl).
  Next Obligation.
    intros tyl HFA tid vl.
    cut (∀ i vl', PersistentP (ty_own (nth i tyl ∅) tid vl')). by apply _.
    intros. apply @copy_persistent. edestruct nth_in_or_default as [| ->];
      [by eapply List.Forall_forall| apply _].
  Qed.
  Next Obligation.
    intros tyl HFA κ tid E F l q ?.
    iIntros "#LFT #H[[Htok1 [Htok2 Htok3]] Htl]".
    setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 [Hshr Hshrtail]]".
    iMod (frac_bor_acc with "LFT Hshr0 Htok1") as (q'1) "[Hown Hclose]". set_solver.
    iMod (frac_bor_acc with "LFT Hshrtail Htok2") as (q'2) "[Htail Hclose']". set_solver.
    iMod (@copy_shr_acc _ _ (nth i tyl ∅) with "LFT Hshr [Htok3 $Htl]")
      as (q'3) "[Hownq Hclose'']"; try done.
    { edestruct nth_in_or_default as [| ->]; last by apply _.
        by eapply List.Forall_forall. }
    destruct (Qp_lower_bound q'1 q'2) as (q'0 & q'01 & q'02 & -> & ->).
    destruct (Qp_lower_bound q'0 q'3) as (q' & q'11 & q'12 & -> & ->).
    rewrite -(heap_mapsto_vec_prop_op _ q' q'12); last (by intros; apply ty_size_eq).
    rewrite -!Qp_plus_assoc.
    rewrite -(heap_mapsto_vec_prop_op _ q' (q'11 + q'02)
        (list_max (map ty_size tyl) - (ty_size (nth i tyl ∅)))%nat); last first.
    { intros. iIntros (<-). iPureIntro. by rewrite minus_plus. }
    iDestruct "Hownq" as "[Hownq1 Hownq2]". iDestruct "Hown" as "[Hown1 >Hown2]".
    iDestruct "Htail" as "[Htail1 Htail2]".
    iExists q'. iModIntro. iSplitL "Hown1 Hownq1 Htail1".
    - iNext. iExists i. by iFrame.
    - iIntros "H". iDestruct "H" as (i') "[>Hown1 [Hownq1 Htail1]]".
      iDestruct (heap_mapsto_agree with "[$Hown1 $Hown2]") as %[= ->%Z_of_nat_inj].
      iMod ("Hclose''" with "[$Hownq1 $Hownq2]"). iMod ("Hclose'" with "[$Htail1 $Htail2]").
      iMod ("Hclose" with "[$Hown1 $Hown2]") as "$". by iFrame.
  Qed.
End sum.

(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1 (..(cons tyn nil)..))) : lrust_type_scope.

Section incl.
  Context `{typeG Σ}.

  (* TODO *)
  (* Lemma ty_incl_sum ρ n tyl1 tyl2 (_ : LstTySize n tyl1) (_ : LstTySize n tyl2) : *)
  (*   Duplicable ρ → Forall2 (ty_incl ρ) tyl1 tyl2 → *)
  (*   ty_incl ρ (sum tyl1) (sum tyl2). *)
  (* Proof. *)
  (*   iIntros (DUP FA tid) "#LFT #Hρ". rewrite /sum /=. iSplitR "". *)
  (*   - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗ *)
  (*        (□ ∀ i vl, (nth i tyl1 ∅%T).(ty_own) tid vl *)
  (*                 → (nth i tyl2 ∅%T).(ty_own) tid vl)). *)
  (*     { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH]. *)
  (*       - iIntros "_ _!>*!#". eauto. *)
  (*       - iIntros "#LFT #Hρ". iMod (IH with "LFT Hρ") as "#IH". *)
  (*         iMod (Hincl with "LFT Hρ") as "[#Hh _]". *)
  (*         iIntros "!>*!#*Hown". destruct i as [|i]. by iApply "Hh". by iApply "IH". } *)
  (*     iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H". *)
  (*     iDestruct "H" as (i vl') "[% Hown]". subst. iExists _, _. iSplit. done. *)
  (*       by iApply "Hincl". *)
  (*   - assert (Hincl : lft_ctx -∗ ρ tid ={⊤}=∗ *)
  (*        (□ ∀ i κ E l, (nth i tyl1 ∅%T).(ty_shr) κ tid E l *)
  (*                    → (nth i tyl2 ∅%T).(ty_shr) κ tid E l)). *)
  (*     { clear -FA DUP. induction FA as [|ty1 ty2 tyl1 tyl2 Hincl _ IH]. *)
  (*       - iIntros "#LFT _!>*!#". eauto. *)
  (*       - iIntros "#LFT #Hρ". *)
  (*         iMod (IH with "LFT Hρ") as "#IH". iMod (Hincl with "LFT Hρ") as "[_ #Hh]". *)
  (*         iIntros "!>*!#*Hown". destruct i as [|i]; last by iApply "IH". *)
  (*         by iDestruct ("Hh" $! _ _ _ with "Hown") as "[$ _]". } *)
  (*     iMod (Hincl with "LFT Hρ") as "#Hincl". iIntros "!>!#*H". iSplit; last done. *)
  (*     iDestruct "H" as (i) "[??]". iExists _. iSplit. done. by iApply "Hincl". *)
  (* Qed. *)
End incl.
