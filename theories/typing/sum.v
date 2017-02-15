From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.base_logic Require Import fractional.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section sum.
  Context `{typeG Σ}.

  Local Obligation Tactic := idtac.

  Program Definition emp : type :=
    {| ty_size := 1%nat;
       ty_own tid vl := False%I;
       ty_shr κ tid l := False%I |}.
  Next Obligation. iIntros (tid vl) "[]". Qed.
  Next Obligation.
    iIntros (E κ l tid ??) "#LFT Hown Htok".
    iMod (bor_acc with "LFT Hown Htok") as "[>H _]"; first done.
    iDestruct "H" as (?) "[_ []]".
  Qed.
  Next Obligation. iIntros (κ κ' tid l) "#LFT #Hord []". Qed.

  Global Instance emp_empty : Empty type := emp.

  Global Instance emp_copy : Copy ∅.
  Proof. split; first by apply _. iIntros (????????) "? []". Qed.

  Global Instance emp_send : Send ∅.
  Proof. iIntros (???) "[]". Qed.

  Global Instance emp_sync : Sync ∅.
  Proof. iIntros (????) "[]". Qed.

  Definition list_max (l : list nat) := foldr max 0%nat l.

  Definition is_pad i tyl (vl : list val) : iProp Σ :=
    ⌜((nth i tyl ∅).(ty_size) + length vl)%nat = (list_max $ map ty_size tyl)⌝%I.

  Lemma split_sum_mt l tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                               ⌜length vl = S (list_max $ map ty_size tyl)⌝ ∗
                               ty_own (nth i tyl ∅) tid vl')%I
    ⊣⊢ ∃ (i : nat), (l ↦{q} #i ∗
                       shift_loc l (S $ (nth i tyl ∅).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
                              shift_loc l 1 ↦∗{q}: (nth i tyl ∅).(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl' vl'') "(% & % & Hown)".
      subst. iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iDestruct (heap_mapsto_vec_app with "Hmt") as "[Hmt Htail]". iSplitL "Htail".
      + iExists vl''. rewrite (shift_loc_assoc_nat _ 1) Hvl'. iFrame. iPureIntro.
        rewrite -Hvl'. simpl in *. rewrite -app_length. congruence.
      + iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[[Hmt1 Htail] Hown]".
      iDestruct "Hown" as (vl') "[Hmt2 Hown]". iDestruct "Htail" as (vl'') "[Hmt3 %]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iExists (#i::vl'++vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Hvl'.
      iFrame. iExists i, vl', vl''. iSplit; first done. iFrame. iPureIntro.
      simpl. f_equal. by rewrite app_length Hvl'.
  Qed.

  Program Definition sum (tyl : list type) :=
    {| ty_size := S (list_max $ map ty_size tyl);
       ty_own tid vl :=
         (∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                                ⌜length vl = S (list_max $ map ty_size tyl)⌝ ∗
                                (nth i tyl ∅).(ty_own) tid vl')%I;
       ty_shr κ tid l :=
         (∃ (i : nat),
             (&frac{κ} λ q, l ↦{q} #i ∗
                       shift_loc l (S $ (nth i tyl ∅).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
               (nth i tyl ∅).(ty_shr) κ tid (shift_loc l 1))%I
    |}.
  Next Obligation.
    iIntros (tyl tid vl) "Hown". iDestruct "Hown" as (i vl' vl'') "(%&%&_)".
    subst. done.
  Qed.
  Next Obligation.
    intros tyl E κ l tid. iIntros (??) "#LFT Hown Htok". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Hown") as (i) "Hown". set_solver.
    iMod (bor_sep with "LFT Hown") as "[Hmt Hown]". solve_ndisj.
    iMod ((nth i tyl ∅).(ty_share) with "LFT Hown Htok") as "[#Hshr $]"; try done.
    iMod (bor_fracture with "LFT [Hmt]") as "H'";[set_solver| |]; last eauto.
      by iFrame.
  Qed.
  Next Obligation.
    iIntros (tyl κ κ' tid l) "#LFT #Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i.
    iSplitL "Hown0".
    - by iApply (frac_bor_shorten with "Hord").
    - iApply ((nth i tyl ∅).(ty_shr_mono) with "LFT Hord"); done.
  Qed.

  Global Instance sum_ne n: Proper (dist n ==> dist n) sum.
  Proof.
    intros x y EQ.
    assert (EQmax : list_max (map ty_size x) = list_max (map ty_size y)).
    { induction EQ as [|???? EQ _ IH]=>//=.
      rewrite IH. f_equiv. apply EQ. }
    assert (EQnth :∀ i, nth i x ∅ ≡{n}≡ nth i y ∅).
    { clear EQmax. induction EQ as [|???? EQ _ IH]=>-[|i] //=. }
    split; [split|]; simpl.
    - by rewrite EQmax.
    - f_contractive=>tid vl. rewrite EQmax. by setoid_rewrite EQnth.
    - intros κ tid l. unfold is_pad. rewrite EQmax.
      assert (EQsz : ∀ i, (nth i x ∅).(ty_size) = (nth i y ∅).(ty_size))
        by (intros; apply EQnth).
      repeat (rewrite EQsz || f_equiv). apply EQnth.
  Qed.

  Global Instance sum_mono E L :
    Proper (Forall2 (subtype E L) ==> subtype E L) sum.
  Proof.
    iIntros (tyl1 tyl2 Htyl) "#LFT #? %".
    iAssert (⌜list_max (map ty_size tyl1) = list_max (map ty_size tyl2)⌝%I) with "[#]" as %Hleq.
    { iInduction Htyl as [|???? Hsub] "IH"; first done.
      iDestruct (Hsub with "LFT [] []") as "(% & _ & _)"; [done..|].
      iDestruct "IH" as %IH. iPureIntro. simpl. inversion_clear IH. by f_equal. }
    iAssert (∀ i, type_incl (nth i tyl1 ∅) (nth i tyl2 ∅))%I with "[#]" as "#Hty".
      { iIntros (i). edestruct (nth_lookup_or_length tyl1 i) as [Hl1|Hl]; last first.
        { rewrite nth_overflow // nth_overflow; first by iApply type_incl_refl.
          by erewrite <-Forall2_length. }
        edestruct @Forall2_lookup_l as (ty2 & Hl2 & Hty2); [done..|].
        rewrite (nth_lookup_Some tyl2 _ _ ty2) //.
        by iApply (Hty2 with "[] []"). }
    clear -Hleq. iSplit; last iSplit.
    - simpl. by rewrite Hleq.
    - iAlways. iIntros (tid vl) "H". iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
      iExists i, vl', vl''. iSplit; first done.
      iSplit; first by rewrite -Hleq.
      iDestruct ("Hty" $! i) as "(_ & #Htyi & _)". by iApply "Htyi".
    - iAlways. iIntros (κ tid l) "H". iDestruct "H" as (i) "(Hmt & Hshr)".
      iExists i. iSplitR "Hshr".
      + rewrite /is_pad -Hleq. iDestruct ("Hty" $! i) as "(Hlen & _)".
        iDestruct "Hlen" as %<-. done.
      + iDestruct ("Hty" $! i) as "(_ & _ & #Htyi)". by iApply "Htyi".
  Qed.
  Lemma sum_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_mono. Qed.
  Global Instance sum_proper E L :
    Proper (Forall2 (eqtype E L) ==> eqtype E L) sum.
  Proof.
    intros tyl1 tyl2 Heq; split; eapply sum_mono; [|rewrite -Forall2_flip];
      (eapply Forall2_impl; [done|by intros ?? []]).
  Qed.
  Lemma sum_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_proper. Qed.

  Lemma nth_empty {A : Type} i (d : A) :
    nth i [] d = d.
  Proof. by destruct i. Qed.

  Lemma emp_sum E L :
    eqtype E L emp (sum []).
  Proof.
    split; (iIntros; iSplit; first done; iSplit; iAlways).
    - iIntros (??) "[]".
    - iIntros (κ tid l) "[]".
    - iIntros (??) "H". iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
      by rewrite nth_empty.
    - iIntros (???) "H". iDestruct "H" as (i) "(_ & Hshr)". by rewrite nth_empty.
  Qed.

  Global Instance sum_copy tyl : LstCopy tyl → Copy (sum tyl).
  Proof.
    intros HFA. split.
    - intros tid vl.
      cut (∀ i vl', PersistentP (ty_own (nth i tyl ∅) tid vl')). by apply _.
      intros. apply @copy_persistent. edestruct nth_in_or_default as [| ->];
                                        [by eapply List.Forall_forall| apply _].
    - intros κ tid E F l q ? HF.
      iIntros "#LFT #H Htl [Htok1 Htok2]".
      setoid_rewrite split_sum_mt. iDestruct "H" as (i) "[Hshr0 Hshr]".
      iMod (frac_bor_acc with "LFT Hshr0 Htok1") as (q'1) "[>Hown Hclose]". set_solver.
      iAssert ((∃ vl, is_pad i tyl vl)%I) with "[#]" as %[vl Hpad].
      { iDestruct "Hown" as "[_ Hpad]". iDestruct "Hpad" as (vl) "[_ %]".
        eauto. }
      iMod (@copy_shr_acc _ _ (nth i tyl ∅) with "LFT Hshr Htl Htok2")
        as (q'2) "(Htl & HownC & Hclose')"; try done.
      { edestruct nth_in_or_default as [| ->]; last by apply _.
          by eapply List.Forall_forall. }
      { rewrite <-HF. simpl. rewrite <-union_subseteq_r.
        apply shr_locsE_subseteq. omega. }
      iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
      { (* Really, we don't even have a lemma for anti-monotonicity of difference...? *)
        cut (shr_locsE (shift_loc l 1) (ty_size (nth i tyl ∅)) ⊆
                  shr_locsE (shift_loc l 1) (list_max (map ty_size tyl))).
        - simpl. set_solver+.
        - apply shr_locsE_subseteq. omega. }
      destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
      rewrite -(heap_mapsto_pred_op _ q' q'02); last (by intros; apply ty_size_eq).
      rewrite (fractional (Φ := λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I).
      iDestruct "HownC" as "[HownC1 HownC2]". iDestruct "Hown" as "[Hown1 Hown2]".
      iExists q'. iModIntro. iSplitL "Hown1 HownC1".
      + iNext. iExists i. iFrame.
      + iIntros "Htl H". iDestruct "H" as (i') "[>Hown1 HownC1]".
        iDestruct ("Htlclose" with "Htl") as "Htl".
        iDestruct (heap_mapsto_agree with "[Hown1 Hown2]") as "#Heq".
        { iDestruct "Hown1" as "[$ _]". iDestruct "Hown2" as "[$ _]". }
        iDestruct "Heq" as %[= ->%Z_of_nat_inj].
        iMod ("Hclose'" with "Htl [$HownC1 $HownC2]") as "[$ ?]".
        iMod ("Hclose" with "[$Hown1 $Hown2]") as "$". by iFrame.
  Qed.

  Global Instance sum_send tyl : LstSend tyl → Send (sum tyl).
  Proof.
    iIntros (Hsend tid1 tid2 vl) "H". iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
    iExists _, _, _. iSplit; first done. iSplit; first done. iApply @send_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; last by apply _.
          by eapply List.Forall_forall.
  Qed.

  Global Instance sum_sync tyl : LstSync tyl → Sync (sum tyl).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (i) "[Hframe Hown]".
    iExists _. iFrame "Hframe". iApply @sync_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; last by apply _.
          by eapply List.Forall_forall.
  Qed.
End sum.

(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1%T (..(cons tyn%T nil)..))) : lrust_type_scope.

Hint Resolve sum_mono' sum_proper' : lrust_typing.
