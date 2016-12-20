From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import borrow frac_borrow reborrow.
From lrust.lang Require Export new_delete.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import typing product perm uninit own uniq_bor shr_bor.

(** Typing rules for memory instructions. *)

Section typing.
  Context `{typeG Σ}.

  
  Lemma update_strong ty1 ty2 n:
    ty1.(ty_size) = ty2.(ty_size) →
    update ty1 (λ ν, ν ◁ own n ty2)%P (λ ν, ν ◁ own n ty1)%P.
  Proof.
    iIntros (Hsz ν tid Φ E ?) "_ H◁ HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    rewrite ty2.(ty_size_eq) -Hsz. iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%".
    iIntros (vl') "[H↦ Hown']!>". rewrite /has_type Hνv.
    iExists _. iSplit. done. iFrame. iExists _. iFrame.
  Qed.

  Lemma consumes_copy_own ty n:
    Copy ty → consumes ty (λ ν, ν ◁ own n ty)%P (λ ν, ν ◁ own n ty)%P.
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

  Lemma consumes_move ty n:
    consumes ty (λ ν, ν ◁ own n ty)%P (λ ν, ν ◁ own n (uninit ty.(ty_size)))%P.
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
    - rewrite uninit_sz; auto.
  Qed.


  Lemma consumes_copy_uniq_bor `(!Copy ty) κ κ' q:
    consumes ty (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l' P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv.
    iExists _, _. erewrite <-uPred.iff_refl. auto.
  Qed.

  Lemma update_weak ty q κ κ':
    update ty (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
              (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%#". iIntros (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[Hbor Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv.
    iExists _, _. erewrite <-uPred.iff_refl. auto.
  Qed.

  Lemma consumes_copy_shr_bor ty κ κ' q:
    Copy ty →
    consumes ty (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (? ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l') "[Heq #Hshr]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (copy_shr_acc with "LFT Hshr Htok Htl") as (q'') "(H↦ & Htl & Hclose')".
    { assert (↑shrN ⊆ (↑lrustN : coPset)) by solve_ndisj. set_solver. } (* FIXME: some tactic should solve this in one go. *)
    { done. }
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦] Htl") as "[Htok $]". iExists _; by iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma typed_new ρ (n : nat):
    0 ≤ n → typed_step_ty ρ (new [ #n]%E) (own n (uninit n)).
  Proof.
    iIntros (Hn tid) "!#(#HEAP&_&_&$)". iApply (wp_new with "HEAP"); try done.
    iIntros "!>*(% & H† & H↦)". iExists _. iSplit. done. iNext.
    rewrite Nat2Z.id. iSplitR "H†".
    - iExists vl. iFrame.
      match goal with H : Z.of_nat n = Z.of_nat (length vl) |- _ => rename H into Hlen end.
      clear Hn. apply (inj Z.of_nat) in Hlen. subst.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - by rewrite uninit_sz freeable_sz_full.
  Qed.

  Lemma typed_delete ty (ν : expr):
    typed_step (ν ◁ own ty.(ty_size) ty) (delete [ #ty.(ty_size); ν])%E (λ _, top).
  Proof.
    iIntros (tid) "!#(#HEAP&_&H◁&$)". wp_bind ν.
    iApply (has_type_wp with "[$H◁]"). iIntros (v) "_ H◁ !>".
    rewrite has_type_value.
    iDestruct "H◁" as (l) "(Hv & H↦∗: & >H†)". iDestruct "Hv" as %[=->].
    iDestruct "H↦∗:" as (vl) "[>H↦ Hown]".
    rewrite ty_size_eq. iDestruct "Hown" as ">Hown". iDestruct "Hown" as %<-.
    iApply (wp_delete with "[-]"); try by auto.
    rewrite freeable_sz_full. by iFrame.
  Qed.


  Lemma typed_deref_uniq_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &uniq{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_acc_cons with "LFT H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep _ _ _ (l' ↦∗: ty_own ty tid) with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "$". iFrame "#". iExists _, _.
      iFrame. iSplitR. done. by rewrite -uPred.iff_refl.
    - iFrame "H↦ H† Hown".
    - iIntros "!>(?&?&?)!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame.
  Qed.

  Lemma typed_deref_uniq_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &uniq{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &uniq{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l P) "[[Heq #HPiff] HP]".
    iDestruct "Heq" as %[=->].
    iMod (bor_iff with "LFT [] HP") as "H↦". set_solver. by eauto.
    iMod (lft_incl_acc with "H⊑1 Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_exists with "LFT H↦") as (vl) "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_exists with "LFT Hbor") as (P') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H Hbor]". done.
    iMod (bor_persistent_tok with "LFT H Htok") as "[[>% #HP'iff] Htok]". done. subst.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    rewrite heap_mapsto_vec_singleton.
    iApply (wp_fupd_step  _ (⊤∖↑lftN) with "[Hbor]"); try done.
      by iApply (bor_unnest with "LFT Hbor").
    wp_read. iIntros "!> Hbor". iFrame "#". iSplitL "Hbor".
    - iExists _, _. iSplitR. by auto.
      iApply (bor_shorten with "[] Hbor").
      iApply (lft_incl_glb with "H⊑2"). iApply lft_incl_refl.
    - iApply ("Hclose" with ">"). by iMod ("Hclose'" with "[$H↦]") as "[_ $]".
  Qed.

  Lemma typed_deref_shr_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &shr{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &shr{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & [Htok1 Htok2]) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok1") as (q'') "[Htok1 Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iMod (lft_incl_acc with "H⊑ Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[Hshr Htok2]{$H⊑}". iMod ("Hclose''" with "Htok2") as "$".
      iSplitL "Hshr"; first by iExists _; auto. iApply ("Hclose" with ">").
      iFrame. iApply "Hclose'". auto.
  Qed.

  Lemma typed_deref_shr_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &shr{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &shr{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & [Htok1 Htok2] & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (lft_incl_acc with "H⊑1 Htok1") as (q') "[Htok1 Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "[] Htok2") as (q2) "[Htok2 Hclose'']". solve_ndisj.
    { iApply (lft_incl_trans with "[]"); done. }
    iApply (wp_fupd_step _ (_∖_) with "[Hown Htok2]"); try done.
    - iApply ("Hown" with "* [%] Htok2"). set_solver+.
    - wp_read. iIntros "!>[#Hshr Htok2]{$H⊑1}".
      iMod ("Hclose''" with "Htok2") as "$". iSplitR.
      * iExists _. iSplitR. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
      * iApply ("Hclose" with ">"). iApply ("Hclose'" with "[$H↦]").
  Qed.

End typing.
