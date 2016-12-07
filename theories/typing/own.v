From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_incl typing product.

Section own.
  Context `{iris_typeG Σ}.

  (* Even though it does not seem too natural to put this here, it is
     the only place where it is used. *)
  Program Definition uninit : type :=
    {| st_size := 1; st_own tid vl := ⌜length vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Program Definition own (q : Qp) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [ty_incl_own].

            Since this assertion is timeless, this should not cause
            problems. *)
         (∃ l:loc, ⌜vl = [ #l ]⌝ ∗ ▷ l ↦∗: ty.(ty_own) tid ∗ ▷ †{q}l…ty.(ty_size))%I;
       ty_shr κ tid E l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ (∀ q' F, ⌜E ∪ mgmtE ⊆ F⌝ →
                 q'.[κ] ={F,F∖E}▷=∗ ty.(ty_shr) κ tid E l' ∗ q'.[κ]))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    move=> q ty E N κ l tid q' ?? /=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (bor_exists with "LFT Hb2") as (l') "Hb2". set_solver.
    iMod (bor_sep with "LFT Hb2") as "[EQ Hb2]". set_solver.
    iMod (bor_persistent with "LFT EQ Htok") as "[>% $]". set_solver. subst.
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_sep with "LFT Hb2") as "[Hb2 _]". set_solver.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hbf". set_solver.
    rewrite bor_unfold_idx. iDestruct "Hb2" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc N _ (idx_bor_own 1 i ∨ ty_shr ty κ tid (↑N) l')%I
         with "[Hpbown]") as "#Hinv"; first by eauto.
    iExists l'. iIntros "!>{$Hbf}!#". iIntros (q'' F) "% Htok".
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later_tok with "LFT [Hbtok] Htok") as "H". set_solver.
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "H" as "[Hb Htok]".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#$ $]". done. set_solver.
      iApply "Hclose". auto.
    - iModIntro. iNext. iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid E E' l ?. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb #Hvs]".
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]"). iIntros "!#".
    iIntros (q' F) "% Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖E)). set_solver. set_solver.
    iMod (lft_incl_acc with "Hκ Htok") as (q'') "[Htok Hclose]". set_solver.
    iMod ("Hvs" with "* [%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      by iApply (ty.(ty_shr_mono) with "LFT Hκ").
  Qed.

  Lemma ty_incl_own ρ ty1 ty2 q :
    ty_incl ρ ty1 ty2 → ty_incl ρ (own q ty1) (own q ty2).
  Proof.
    iIntros (Hincl tid) "#LFT H/=". iMod (Hincl with "LFT H") as "[#Howni #Hshri]".
    iModIntro. iSplit; iIntros "!#*H".
    - iDestruct "H" as (l) "(%&Hmt&H†)". subst. iExists _. iSplit. done.
      iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct (ty_size_eq with "Hown") as %<-.
      iDestruct ("Howni" $! _ with "Hown") as "Hown".
      iDestruct (ty_size_eq with "Hown") as %<-. iFrame.
      iExists _. by iFrame.
    - iDestruct "H" as (l') "[Hfb #Hvs]". iSplit; last done. iExists l'. iFrame.
      iIntros "!#". iIntros (q' F) "% Hκ".
      iMod ("Hvs" with "* [%] Hκ") as "Hvs'". done. iModIntro. iNext.
      iMod "Hvs'" as "[Hshr $]". by iDestruct ("Hshri" with "* Hshr") as "[$ _]".
  Qed.

  Lemma typed_alloc ρ (n : nat):
    0 < n → typed_step_ty ρ (Alloc #n) (own 1 (Π(replicate n uninit))).
  Proof.
    iIntros (Hn tid) "!#(#HEAP&_&_&$)". wp_alloc l vl as "H↦" "H†". iIntros "!>".
    iExists _. iSplit. done. iNext. rewrite Nat2Z.id. iSplitR "H†".
    - iExists vl. iFrame.
      match goal with H : Z.of_nat n = Z.of_nat (length vl) |- _ => rename H into Hlen end.
      clear Hn. apply (inj Z.of_nat) in Hlen. subst.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - assert (ty_size (Π (replicate n uninit)) = n) as ->; last done.
      clear. simpl. induction n. done. rewrite /= IHn //.
  Qed.

  Lemma typed_free ty (ν : expr):
    typed_step (ν ◁ own 1 ty) (Free #ty.(ty_size) ν) (λ _, top).
  Proof.
    iIntros (tid) "!#(#HEAP&_&H◁&$)". wp_bind ν.
    iApply (has_type_wp with "[$H◁]"). iIntros (v) "_ H◁ !>".
    rewrite has_type_value.
    iDestruct "H◁" as (l) "(Hv & H↦∗: & >H†)". iDestruct "Hv" as %[=->].
    iDestruct "H↦∗:" as (vl) "[>H↦ Hown]".
    rewrite ty_size_eq. iDestruct "Hown" as ">%". wp_free; eauto.
  Qed.

  Lemma update_strong ty1 ty2 q:
    ty1.(ty_size) = ty2.(ty_size) →
    update ty1 (λ ν, ν ◁ own q ty2)%P (λ ν, ν ◁ own q ty1)%P.
  Proof.
    iIntros (Hsz ν tid Φ E ?) "_ H◁ HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    rewrite ty2.(ty_size_eq) -Hsz. iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%".
    iIntros (vl') "[H↦ Hown']!>". rewrite /has_type Hνv.
    iExists _. iSplit. done. iFrame. iExists _. iFrame.
  Qed.

  Lemma consumes_copy_own ty q:
    Copy ty → consumes ty (λ ν, ν ◁ own q ty)%P (λ ν, ν ◁ own q ty)%P.
  Proof.
    iIntros (? ν tid Φ E ?) "_ H◁ Htl HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦!>".
    rewrite /has_type Hνv. iExists _. iSplit. done. iFrame. iExists vl. eauto.
  Qed.

  Lemma consumes_move ty q:
    consumes ty (λ ν, ν ◁ own q ty)%P
             (λ ν, ν ◁ own q (Π(replicate ty.(ty_size) uninit)))%P.
  Proof.
    iIntros (ν tid Φ E ?) "_ H◁ Htl HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">Hlen".
      by rewrite ty.(ty_size_eq). iDestruct "Hlen" as %Hlen.
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦!>".
    rewrite /has_type Hνv. iExists _. iSplit. done. iSplitR "H†".
    - rewrite -Hlen. iExists vl. iIntros "{$H↦}!>". clear.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - assert (ty_size (Π (replicate (ty_size ty) uninit)) = ty_size ty) as ->; last by auto.
      clear. induction ty.(ty_size). done. by apply (f_equal S).
  Qed.
End own.