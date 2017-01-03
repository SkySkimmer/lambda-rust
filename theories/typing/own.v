From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lifetime Require Import borrow frac_borrow.
From lrust.lang Require Export new_delete.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.

Section own.
  Context `{typeG Σ}.

  Program Definition freeable_sz (n : nat) (sz : nat) (l : loc) : iProp Σ :=
    match sz, n return _ with
    | 0%nat, _ => True
    | _, 0%nat => False
    | sz, n => †{mk_Qp (sz / n) _}l…sz
    end%I.
  Next Obligation. intros _ _ _ sz0 ? n ?. by apply Qcmult_pos_pos. Qed.
  Arguments freeable_sz : simpl never.
  Global Instance freable_sz_timeless n sz l : TimelessP (freeable_sz n sz l).
  Proof. destruct sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ (†{1}l…n ∨ ⌜Z.of_nat n = 0⌝)%I.
  Proof.
    destruct n.
    - iSplit; iIntros "H /="; auto.
    - assert (Z.of_nat (S n) = 0 ↔ False) as -> by done. rewrite right_id.
      rewrite /freeable_sz (proj2 (Qp_eq (mk_Qp _ _) 1)) //= Qcmult_inv_r //.
  Qed.

  Lemma freeable_sz_split n sz1 sz2 l :
    freeable_sz n sz1 l ∗ freeable_sz n sz2 (shift_loc l sz1) ⊣⊢
                freeable_sz n (sz1 + sz2) l.
  Proof.
    destruct sz1; [|destruct sz2;[|rewrite /freeable_sz plus_Sn_m; destruct n]].
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit. by iIntros "[[]?]". by iIntros "[]".
    - rewrite heap_freeable_op_eq. f_equiv. apply Qp_eq.
      rewrite /= -Qcmult_plus_distr_l -Z2Qc_inj_add /Z.add. do 3 f_equal. lia.
  Qed.

  Program Definition own (n : nat) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [subtype_own].

            Since this assertion is timeless, this should not cause
            problems. *)
         (∃ l:loc, ⌜vl = [ #l ]⌝ ∗ ▷ l ↦∗: ty.(ty_own) tid ∗
                   ▷ freeable_sz n ty.(ty_size) l)%I;
       ty_shr κ tid l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ (∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ] ={F,F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) κ tid l' ∗ q.[κ]))%I
    |}.
  Next Obligation.
    iIntros (q ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.
  Next Obligation.
    move=>n ty N κ l tid ?? /=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    iMod (bor_exists with "LFT Hb2") as (l') "Hb2". set_solver. 
    iMod (bor_sep with "LFT Hb2") as "[EQ Hb2]". set_solver.
    iMod (bor_persistent_tok with "LFT EQ Htok") as "[>% $]". set_solver.
    iExists l'. subst. rewrite heap_mapsto_vec_singleton.
    iMod (bor_sep with "LFT Hb2") as "[Hb2 _]". set_solver.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$". set_solver.
    rewrite bor_unfold_idx. iDestruct "Hb2" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ tid l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later with "LFT [Hbtok]") as "Hb".
      { apply ndisj_subseteq_difference. solve_ndisj. set_solver. } (* FIXME: some tactic should solve this in one go. *)
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#$ $]".
      { apply ndisj_subseteq_difference. solve_ndisj. set_solver. } (* FIXME: some tactic should solve this in one go. *)
      iApply "Hclose". auto.
    - iMod fupd_intro_mask' as "Hclose'"; last iModIntro. set_solver.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid l. iIntros "#LFT #Hκ #H".
    iDestruct "H" as (l') "[Hfb #Hvs]".
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]"). iIntros "!# *% Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖↑shrN∖↑lftN)). set_solver. set_solver.
    iMod (lft_incl_acc with "Hκ Htok") as (q') "[Htok Hclose]"; first set_solver.
    iMod ("Hvs" with "* [%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty.(ty_shr_mono) with "LFT Hκ").
  Qed.

  Global Instance own_mono E L n :
    Proper (subtype E L ==> subtype E L) (own n).
  Proof.
    intros ty1 ty2 Hincl. iIntros. iSplit; first done.
    iDestruct (Hincl with "* [] [] []") as "(_ & #Ho & #Hs)"; [done..|clear Hincl].
    iSplit; iAlways.
    - iIntros (??) "H". iDestruct "H" as (l) "(%&Hmt&H†)". subst.
      iExists _. iSplit. done. iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct (ty_size_eq with "Hown") as %<-.
      iDestruct ("Ho" with "* Hown") as "Hown".
      iDestruct (ty_size_eq with "Hown") as %<-. iFrame.
      iExists _. by iFrame.
    - iIntros (???) "H". iDestruct "H" as (l') "[Hfb #Hvs]".
      iExists l'. iFrame. iIntros "!#". iIntros (F' q) "% Htok".
      iMod ("Hvs" with "* [%] Htok") as "Hvs'". done. iModIntro. iNext.
      iMod "Hvs'" as "[Hshr $]". iApply ("Hs" with "Hshr").
  Qed.
  Lemma own_mono' E L n ty1 ty2 :
    subtype E L ty1 ty2 → subtype E L (own n ty1) (own n ty2).
  Proof. apply own_mono. Qed.
  Global Instance own_proper E L n :
    Proper (eqtype E L ==> eqtype E L) (own n).
  Proof. intros ?? Heq. split; f_equiv; apply Heq. Qed.
  Lemma own_proper' E L n ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (own n ty1) (own n ty2).
  Proof. apply own_proper. Qed.

  Global Instance own_contractive n : Contractive (own n).
  Proof.
    intros m ?? EQ. split; [split|]; simpl.
    - done.
    - destruct m=>// tid vl /=. repeat (apply EQ || f_contractive || f_equiv).
    - intros κ tid l. repeat (apply EQ || f_contractive || f_equiv).
  Qed.
  Global Instance own_ne n m : Proper (dist m ==> dist m) (own n).
  Proof. apply contractive_ne, _. Qed.

  Global Instance own_send n ty :
    Send ty → Send (own n ty).
  Proof.
    iIntros (Hsend tid1 tid2 vl) "H". iDestruct "H" as (l) "[% [Hm H†]]". subst vl.
    iExists _. iSplit; first done. iFrame "H†". iNext.
    iApply (heap_mapsto_pred_wand with "Hm"). iIntros (vl) "?". by iApply Hsend.
  Qed.

  Global Instance own_sync n ty :
    Sync ty → Sync (own n ty).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists _. iFrame "Hm". iAlways. iIntros (F q) "% Htok".
    iMod ("Hshr" with "* [] Htok") as "Hfin"; first done. iModIntro. iNext.
    iClear "Hshr". (* FIXME: Using "{HShr} [HShr $]" for the intro pattern in the following line doesn't work. *)
    iMod "Hfin" as "[Hshr $]". by iApply Hsync.
  Qed.
End own.

Section typing.
  Context `{typeG Σ}.

  (** Typing *)
  Lemma write_own E L ty ty' n :
    ty.(ty_size) = ty'.(ty_size) → typed_write E L (own n ty') ty (own n ty).
  Proof.
    iIntros (Hsz p tid F qE qL ?) "_ $ $ Hown". iDestruct "Hown" as (l) "(Heq & H↦ & H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    rewrite ty'.(ty_size_eq). (* This turns out to be the fastest way to apply a lemma below ▷ -- at least if we're fine throwing away the premise even though the result is persistent, which in this case, we are. *)
    iDestruct "Hown" as ">%". iModIntro. iExists _, _. iFrame "H↦".
    iSplit; first by rewrite Hsz. iIntros "Hown !>".
    iExists _. iSplit; first done. rewrite Hsz. iFrame.
  Qed.

  Lemma read_own_copy E L ty n :
    Copy ty → typed_read E L (own n ty) ty (own n ty).
  Proof.
    iIntros (Hsz p tid F qE qL ?) "_ $ $ $ Hown". iDestruct "Hown" as (l) "(Heq & H↦ & H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ #Hown]". iModIntro.
    iExists l, _, _. iSplit; first done. iFrame "∗#". iIntros "Hl !>".
    iExists _. iSplit; first done. iFrame "H†". iExists _. by iFrame.
  Qed.

  Lemma read_own_move E L ty n :
    typed_read E L (own n ty) ty (own n $ uninit ty.(ty_size)).
  Proof.
    iIntros (p tid F qE qL ?) "_ $ $ $ Hown". iDestruct "Hown" as (l) "(Heq & H↦ & H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
    { by iApply ty_size_eq. }
    iModIntro. iExists l, vl, _. iSplit; first done. iFrame "∗#". iIntros "Hl !>".
    iExists _. iSplit; first done. rewrite uninit_sz. iFrame "H†". iExists _.
    iFrame. iApply uninit_own. auto.
  Qed.

  Lemma type_new E L (n : nat) :
    typed_instruction_ty E L [] (new [ #n ]%E) (own n (uninit n)).
  Proof.
    iIntros (tid eq) "#HEAP #LFT $ $ $ _".
    iApply (wp_new with "HEAP"); try done; first omega. iModIntro.
    iIntros (l vl) "(% & H† & Hlft)". rewrite tctx_interp_singleton tctx_hasty_val.
    iExists _. iSplit; first done. iNext. rewrite Nat2Z.id. iSplitR "H†".
    - iExists vl. iFrame.
      match goal with H : Z.of_nat n = Z.of_nat (length vl) |- _ => rename H into Hlen end.
      apply (inj Z.of_nat) in Hlen. subst.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - by rewrite uninit_sz freeable_sz_full.
  Qed.

  Lemma type_delete E L n ty p :
    n = ty.(ty_size) →
    typed_instruction E L [p ◁ own n ty] (delete [ #n; p])%E (λ _, []).
  Proof.
    iIntros (-> tid eq) "#HEAP #LFT $ $ $ Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "_ Hown".
    iDestruct "Hown" as (l) "(Hv & H↦∗: & >H†)". iDestruct "Hv" as %[=->].
    iDestruct "H↦∗:" as (vl) "[>H↦ Hown]". rewrite tctx_interp_nil.
    rewrite ty_size_eq. iDestruct "Hown" as ">Hown". iDestruct "Hown" as %<-.
    iApply (wp_delete with "[-]"); try (by auto); [].
    rewrite freeable_sz_full. by iFrame.
  Qed.
End typing.

Hint Resolve own_mono' own_proper' : lrust_typing.
