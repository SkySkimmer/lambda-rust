From Coq.QArith Require Import Qcanon.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import fractional.
From iris.algebra Require Import excl csum frac auth.
From lrust.lang Require Import lang proofmode notation new_delete.
Set Default Proof Using "Type".

(* TODO : get_mut, make_mut, try_unwrap *)

Definition clone_arc : val :=
  rec: "clone" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: CAS "l" "strong" ("strong" + #1) then #() else "clone" ["l"].

Definition clone_weak : val :=
  rec: "clone" ["l"] :=
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) then #() else "clone" ["l"].

Definition downgrade : val :=
  rec: "downgrade" ["l"] :=
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) then #() else "downgrade" ["l"].

Definition upgrade : val :=
  rec: "upgrade" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: "strong" = #0 then #false
    else
      if: CAS "l" "strong" ("strong" + #1) then #true
      else "upgrade" ["l"].

Definition drop_weak dealloc `{Closed [] dealloc} : val :=
  rec: "drop" ["l"] :=
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" - #1) then
      if: "weak" = #1 then dealloc else #()
    else "drop" ["l"].

Definition drop_arc drop dealloc `{Closed [] drop, Closed [] dealloc} : val :=
  rec: "drop" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: CAS "l" "strong" ("strong" - #1) then
      if: "strong" = #1 then
        drop;;
        drop_weak dealloc ["l"]
      else #()
    else "drop" ["l"].

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Definition arc_stR :=
  prodUR (optionUR (csumR (prodR fracR positiveR) (exclR unitC))) natUR.
Class arcG Σ :=
  RcG :> inG Σ (authR arc_stR).
Definition arcΣ : gFunctors := #[GFunctor (authR arc_stR)].
Instance subG_arcΣ {Σ} : subG arcΣ Σ → arcG Σ.
Proof. solve_inG. Qed.

Definition arc_tok q : authR arc_stR :=
  ◯ (Some $ Cinl (q, 1%positive), 0%nat).
Definition arc_dropping_tok : authR arc_stR :=
  ◯ (Some $ Cinr $ Excl (), 0%nat).
Definition weak_tok : authR arc_stR := ◯ (None, 1%nat).

Section arc.
  Context `{!lrustG Σ, !arcG Σ} (N : namespace) (P1 : Qp → iProp Σ)
          {HP1:Fractional P1} (P2 : iProp Σ).
  Set Default Proof Using "HP1".

  Instance P1_AsFractional q : AsFractional (P1 q) P1 q.
  Proof. done. Qed.

  Definition arc_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ st : arc_stR, own γ (● st) ∗
      match st with
      | (Some (Cinl (q, strong)), weak) => ∃ q',
        l ↦ #(Zpos strong) ∗ shift_loc l 1 ↦ #(S weak) ∗
          ⌜(q + q')%Qp = 1%Qp⌝ ∗ P1 q'
      | (Some (Cinr _), weak) =>
        l ↦ #0 ∗ shift_loc l 1 ↦ #(S weak)
      | (None, (S _) as weak) =>
        l ↦ #0 ∗ shift_loc l 1 ↦ #weak ∗ P2
      | _ => True
      end)%I.

  Definition is_arc (γ : gname) (l : loc) : iProp Σ :=
    inv N (arc_inv γ l).

  Definition arc_tok_acc (γ : gname) P E : iProp Σ :=
    (□ (P ={E,∅}=∗ ∃ q, own γ (arc_tok q) ∗ (own γ (arc_tok q) ={∅,E}=∗ P)))%I.

  Definition weak_tok_acc (γ : gname) P E : iProp Σ :=
    (□ (P ={E,∅}=∗ own γ weak_tok ∗ (own γ weak_tok ={∅,E}=∗ P)))%I.

  Definition dealloc_spec dealloc : iProp Σ :=
    ({{{ P2 }}} dealloc {{{ RET #() ; True }}})%I.

  Definition drop_spec drop : iProp Σ :=
    ({{{ P1 1 }}} drop {{{ RET #() ; P2 }}})%I.

  Lemma create_arc E l :
    l ↦ #1 -∗ shift_loc l 1 ↦ #1 -∗ P1 1 ={E}=∗
      ∃ γ q, is_arc γ l ∗ P1 q ∗ own γ (arc_tok q).
  Proof.
    iIntros "Hl1 Hl2 [HP1 HP1']".
    iMod (own_alloc ((● (Some $ Cinl ((1/2)%Qp, xH), O) ⋅
                      ◯ (Some $ Cinl ((1/2)%Qp, xH), O)))) as (γ) "[H● H◯]"; first done.
    iExists _, _. iFrame. iApply inv_alloc. iExists _. iFrame. iExists _. iFrame.
    rewrite Qp_div_2. auto.
  Qed.

  Lemma create_weak E l :
    l ↦ #0 -∗ shift_loc l 1 ↦ #1 -∗ P2 ={E}=∗ ∃ γ, is_arc γ l ∗ own γ weak_tok.
  Proof.
    iIntros "Hl1 Hl2 HP2".
    iMod (own_alloc ((● (None, 1%nat) ⋅ ◯ (None, 1%nat)))) as (γ) "[H● H◯]"; first done.
    iExists _. iFrame. iApply inv_alloc. iExists _. iFrame.
  Qed.

  Lemma arc_tok_auth_val st q :
    ✓ (● st ⋅ arc_tok q) →
    ∃ q' strong weak, st = (Some $ Cinl (q', strong), weak) ∧
                      if decide (strong = xH) then q = q'
                      else ∃ q'', (q' = q + q'')%Qp.
  Proof.
    move=>/auth_valid_discrete_2 [/prod_included [/option_included Hincl _] [Hval _]].
    destruct st, Hincl as [[=]|(?&?&[= <-]&?&[Hincl|Hincl%csum_included])];
      simpl in *; subst.
    - setoid_subst. eexists _, _, _. by split.
    - destruct Hincl as [->|[(?&[]&[=<-]&->&
             [[??]%frac_included%Qp_lt_sum  ?%pos_included]%prod_included)|
        (?&?&[=]&?)]]; first done.
      eexists _, _, _. split=>//. simpl in *. destruct decide; [subst;lia|eauto].
  Qed.

  Lemma clone_arc_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} clone_arc [ #l]
    {{{ q', RET #(); P ∗ own γ (arc_tok q') ∗ P1 q' }}}.
  Proof.
    iIntros "#INV #Hacc !# * HP HΦ". iLöb as "IH". wp_rec. wp_bind (!ˢᶜ_)%E.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (own_valid_2 with "H● Hown") as %(?& strong &?&[-> _])%arc_tok_auth_val.
    iDestruct "H" as (?) "[H H']". wp_read. iMod ("Hclose2" with "Hown") as "HP".
    iModIntro. iMod ("Hclose1" with "[H H' H●]") as "_".
    { iExists _. auto with iFrame. }
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _). iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (own_valid_2 with "H● Hown") as %(?&strong'&?&[-> _])%arc_tok_auth_val.
    iDestruct "H" as (q) "(Hl & Hl1 & >Heq & [HP1 HP1'])". iDestruct "Heq" as %Heq.
    destruct (decide (strong = strong')) as [->|?].
    - wp_apply (wp_cas_int_suc with "Hl"); first done. iIntros "Hl".
      iMod (own_update with "H●") as "[H● Hown']".
      { apply auth_update_alloc, prod_local_update_1,
         (op_local_update_discrete _ _ (Some (Cinl ((q/2)%Qp, 1%positive))))=>-[/= Hqa _].
        split; simpl; last done. apply frac_valid'. rewrite -Heq comm_L -{2}(Qp_div_2 q).
        apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (_ / _)%Qp).
        apply Qcplus_le_mono_r, Qp_ge_0. }
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[Hl Hl1 H● HP1']") as "_".
      { iExists _. iFrame. iExists _. rewrite /= [xH ⋅ _]comm_L. iFrame.
        rewrite [(q / 2)%Qp ⋅ _]comm frac_op' -[(_ + _)%Qp]assoc Qp_div_2. auto. }
      iModIntro. wp_apply (wp_if _ true). wp_value. iApply "HΦ". iFrame.
    - wp_apply (wp_cas_int_fail with "Hl"); [done|congruence|]. iIntros "Hl".
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[Hl Hl1 HP1 HP1' H●]") as "_".
      { iExists _. iFrame. iExists q. auto with iFrame. }
      iModIntro. wp_apply (wp_if _ false). iApply ("IH" with "HP HΦ").
  Qed.

  Lemma downgrade_arc_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} downgrade [ #l] {{{ RET #(); P ∗ own γ weak_tok }}}.
  Proof.
    iIntros "#INV #Hacc !# * HP HΦ". iLöb as "IH". wp_rec. wp_op. wp_bind (!ˢᶜ_)%E.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (own_valid_2 with "H● Hown") as %(?&?& weak &[-> _])%arc_tok_auth_val.
    iDestruct "H" as (?) "(H & H' & H'')". wp_read. iMod ("Hclose2" with "Hown") as "HP".
    iModIntro. iMod ("Hclose1" with "[H H' H'' H●]") as "_".
    { iExists _. auto with iFrame. }
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _). wp_op.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (own_valid_2 with "H● Hown") as %(?&?& weak' &[-> _])%arc_tok_auth_val.
    iDestruct "H" as (q) "(Hl & Hl1 & >Heq & HP1)". iDestruct "Heq" as %Heq.
    destruct (decide (weak = weak')) as [<-|Hw].
    - wp_apply (wp_cas_int_suc with "Hl1"); first done. iIntros "Hl1".
      iMod (own_update with "H●") as "[H● Hown']".
      { by apply auth_update_alloc, prod_local_update_2,
              (op_local_update_discrete _ _ (1%nat)). }
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[Hl Hl1 H● HP1]") as "_".
      { iExists _. iFrame. iExists _.
        rewrite Z.add_comm (Nat2Z.inj_add 1). auto with iFrame. }
      iModIntro. wp_apply (wp_if _ true). wp_value. iApply "HΦ". iFrame.
    - wp_apply (wp_cas_int_fail with "Hl1"); [done| |].
      { contradict Hw. apply SuccNat2Pos.inj. lia. }
      iMod ("Hclose2" with "Hown") as "HP". iIntros "Hl1 !>".
      iMod ("Hclose1" with "[Hl Hl1 HP1 H●]") as "_".
      { iExists _. auto with iFrame. }
      iModIntro. wp_apply (wp_if _ false). iApply ("IH" with "HP HΦ").
  Qed.

  Lemma weak_tok_auth_val st :
    ✓ (● st ⋅ weak_tok) → ∃ st' weak, st = (st', S weak) ∧ ✓ st'.
  Proof.
    move=>/auth_valid_discrete_2 [/prod_included
                [/option_included Hincl /nat_included Hincl'] [Hval _]].
    destruct st as [?[]], Hincl as [_|(?&?&[=]&?)]; simpl in *; try lia. eauto.
  Qed.

  Lemma clone_weak_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc γ l -∗ weak_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} clone_weak [ #l] {{{ RET #(); P ∗ own γ weak_tok }}}.
  Proof.
    iIntros "#INV #Hacc !# * HP HΦ". iLöb as "IH". wp_rec. wp_op. wp_bind (!ˢᶜ_)%E.
    iAssert (□ (P ={⊤,∅}=∗ ∃ w : Z, shift_loc l 1 ↦ #w ∗
              (shift_loc l 1 ↦ #(w + 1) ={∅,⊤}=∗ P ∗ own γ weak_tok) ∧
              (shift_loc l 1 ↦ #w ={∅,⊤}=∗ P)))%I as "#Hproto".
    { iIntros "!# HP". iInv N as (st) "[>H● H]" "Hclose1".
      iMod ("Hacc" with "HP") as "[Hown Hclose2]".
      iDestruct (own_valid_2 with "H● Hown") as %(st' & weak & -> & Hval)%weak_tok_auth_val.
      destruct st' as [[[]| |]|]; try done; iExists _.
      - iDestruct "H" as (?) "(? & >$ & ?)". iIntros "!>"; iSplit; iIntros "?";
        iMod ("Hclose2" with "Hown") as "HP".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame.
          iApply "Hclose1". iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame.
      - iDestruct "H" as "[? >$]". iIntros "!>"; iSplit; iIntros "?";
        iMod ("Hclose2" with "Hown") as "HP".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame. iApply "Hclose1".
          iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame.
      - iDestruct "H" as "(? & >$ & ?)". iIntros "!>"; iSplit; iIntros "?";
        iMod ("Hclose2" with "Hown") as "HP".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame. iApply "Hclose1".
          iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame. }
    iMod ("Hproto" with "HP") as (w) "[Hw [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hw") as "HP". iModIntro. wp_let. wp_op. wp_op.
    wp_bind (CAS _ _ _). iMod ("Hproto" with "HP") as (w') "[H↦ Hclose]".
    destruct (decide (w = w')) as [<-|].
    - wp_apply (wp_cas_int_suc with "H↦"); first done. iIntros "H↦".
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "H↦"). iModIntro.
      wp_apply (wp_if _ true). wp_value. by iApply "HΦ".
    - wp_apply (wp_cas_int_fail with "H↦"); try done. iIntros "H↦".
      iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "H↦") as "Hown".
      iModIntro. wp_apply (wp_if _ false). by iApply ("IH" with "Hown").
  Qed.

  Lemma upgrade_arc_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc γ l -∗ weak_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} upgrade [ #l]
    {{{ (b : bool) q, RET #b; P ∗ if b then own γ (arc_tok q) ∗ P1 q else True }}}.
  Proof.
    iIntros "#INV #Hacc !# * HP HΦ". iLöb as "IH". wp_rec. wp_bind (!ˢᶜ_)%E.
    iAssert (□ (P ={⊤,∅}=∗ ∃ s : Z, l ↦ #s ∗
              (⌜s ≠ 0⌝ -∗ l ↦ #(s + 1) ={∅,⊤}=∗ ∃ q, P ∗ own γ (arc_tok q) ∗ ▷ P1 q) ∧
              (l ↦ #s ={∅,⊤}=∗ P)))%I as "#Hproto".
    { iIntros "!# HP". iInv N as (st) "[>H● H]" "Hclose1".
      iMod ("Hacc" with "HP") as "[Hown Hclose2]".
      iDestruct (own_valid_2 with "H● Hown") as %(st' & weak & -> & Hval)%weak_tok_auth_val.
      destruct st' as [[[]| |]|]; try done; iExists _.
      - iDestruct "H" as (q) "(>$ & ? & >Heq & [HP1 HP1'])". iDestruct "Heq" as %Heq.
        iIntros "!>"; iSplit; iMod ("Hclose2" with "Hown") as "HP".
        + iIntros "_ Hl". iExists (q/2)%Qp. iMod (own_update with "H●") as "[H● $]".
          { apply auth_update_alloc. rewrite -[(_,0%nat)]right_id.
            apply op_local_update_discrete. constructor; last done. split; last done.
            apply frac_valid'. rewrite -Heq comm_L -{2}(Qp_div_2 q).
            apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (_ / _)%Qp).
            apply Qcplus_le_mono_r, Qp_ge_0. }
          iFrame. iApply "Hclose1". iExists _. iFrame. iExists _. iFrame.
          rewrite /= [xH ⋅ _]comm_L frac_op' [(_ + c)%Qp]comm -[(_ + _)%Qp]assoc
                  Qp_div_2. auto with iFrame.
        + iIntros "Hl". iFrame. iApply ("Hclose1" with "[-]"). iExists _. iFrame.
          iExists q. auto with iFrame.
      - iDestruct "H" as "[>$ ?]". iIntros "!>"; iSplit; first by auto with congruence.
        iIntros "Hl". iMod ("Hclose2" with "Hown") as "$". iApply "Hclose1".
        iExists _. auto with iFrame.
      - iDestruct "H" as "[>$ ?]". iIntros "!>"; iSplit; first by auto with congruence.
        iIntros "Hl". iMod ("Hclose2" with "Hown") as "$". iApply "Hclose1".
        iExists _. auto with iFrame. }
    iMod ("Hproto" with "HP") as (s) "[Hs [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hs") as "HP". iModIntro. wp_let. wp_op=>[->|?]; wp_if.
    - iApply ("HΦ" $! _ 1%Qp). auto.
    - wp_op. wp_bind (CAS _ _ _). iMod ("Hproto" with "HP") as (s') "[H↦ Hclose]".
      destruct (decide (s = s')) as [<-|].
      + wp_apply (wp_cas_int_suc with "H↦"); first done. iIntros "H↦".
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "[//] H↦") as (q) "(?&?&?)". iModIntro.
        wp_apply (wp_if _ true). wp_value. iApply "HΦ". iFrame.
      + wp_apply (wp_cas_int_fail with "H↦"); try done. iIntros "H↦".
        iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "H↦") as "Hown".
        iModIntro. wp_apply (wp_if _ false). by iApply ("IH" with "Hown").
  Qed.

  Lemma drop_weak_spec dealloc `{Closed [] dealloc} (γ : gname) (l : loc) :
    is_arc γ l -∗ dealloc_spec dealloc -∗
    {{{ own γ weak_tok }}} drop_weak dealloc [ #l] {{{ RET #() ; True }}}.
  Proof.
    iIntros "#INV #Hdealloc !# * Hown HΦ". iLöb as "IH". wp_rec. wp_op.
    wp_bind (!ˢᶜ_)%E.
    iAssert (□ (own γ weak_tok ={⊤,⊤ ∖ ↑N}=∗ ∃ w : Z, shift_loc l 1 ↦ #w ∗
              (shift_loc l 1 ↦ #(w - 1) ={⊤ ∖ ↑N,⊤}=∗ ⌜w ≠ 1⌝ ∨ ▷ P2) ∧
              (shift_loc l 1 ↦ #w ={⊤ ∖ ↑N,⊤}=∗ own γ weak_tok)))%I as "#Hproto".
    { iIntros "!# Hown". iInv N as (st) "[>H● H]" "Hclose1".
      iDestruct (own_valid_2 with "H● Hown") as %(st' & weak & -> & Hval)%weak_tok_auth_val.
      destruct st' as [[[]| |]|]; try done; iExists _.
      - iDestruct "H" as (q) "(? & >$ & >Heq & HP1)". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
          iExists _. iMod (own_update_2 with "H● Hown") as "$".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_empty 1%nat), _. }
          iExists _. iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame.
      - iDestruct "H" as "[? >$]". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
          iExists _. iMod (own_update_2 with "H● Hown") as "$".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_empty 1%nat), _. }
          iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame.
      - iDestruct "H" as "(? & >$ & HP2)". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod (own_update_2 with "H● Hown") as "H●".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_empty 1%nat), _. }
          destruct weak as [|weak].
          * iMod ("Hclose1" with "[-HP2]") as "_"; last by auto. iExists _. iFrame.
          * iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
            iExists _. iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame. }
    iMod ("Hproto" with "Hown") as (w) "[Hw [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hw") as "Hown". iModIntro. wp_let. wp_op. wp_op.
    wp_bind (CAS _ _ _).
    iMod ("Hproto" with "Hown") as (w') "[Hw Hclose]". destruct (decide (w = w')) as [<-|?].
    - wp_apply (wp_cas_int_suc with "Hw"); first done. iIntros "Hw".
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "Hw") as "HP2". iModIntro.
      wp_apply (wp_if _ true). wp_op=>[->|?]; wp_if; last by iApply "HΦ".
      iDestruct "HP2" as "[%|HP2]"; first done. by iApply ("Hdealloc" with "HP2").
    - wp_apply (wp_cas_int_fail with "Hw"); try done. iIntros "Hw".
      iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hw") as "Hown". iModIntro.
      wp_apply (wp_if _ false). by iApply ("IH" with "Hown").
  Qed.

  Lemma drop_arc_spec drop dealloc `{Closed [] drop, Closed [] dealloc}
        (γ : gname) (q: Qp) (l : loc) :
    is_arc γ l -∗ drop_spec drop -∗ dealloc_spec dealloc -∗
    {{{ own γ (arc_tok q) ∗ P1 q }}} drop_arc drop dealloc [ #l]
    {{{ RET #() ; True }}}.
  Proof.
    iIntros "#INV #Hdrop #Hdealloc !# * [Hown HP1] HΦ". iLöb as "IH". wp_rec.
    wp_bind (!ˢᶜ_)%E. iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (own_valid_2 with "H● Hown") as %(?& s &?&[-> _])%arc_tok_auth_val.
    iDestruct "H" as (?) "[H H']". wp_read. iMod ("Hclose" with "[H H' H●]") as "_".
    { iExists _. auto with iFrame. }
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _).
    iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (own_valid_2 with "H● Hown") as %(q' & s' & w &[-> Hqq'])%arc_tok_auth_val.
    iDestruct "H" as (q'') "(Hs & Hw & >Hq'' & HP1')". iDestruct "Hq''" as %Hq''.
    destruct (decide (s = s')) as [<-|?].
    - wp_apply (wp_cas_int_suc with "Hs"); first done. iIntros "Hs".
      destruct decide as [->|?].
      + revert Hq''. rewrite -Hqq' // => Hq''.
        iMod (own_update_2 with "H● Hown") as "[H● H◯]".
        { apply auth_update, prod_local_update_1.
          rewrite -[x in (x, _)]right_id.
          etrans; first apply cancel_local_update_empty, _.
          by apply (op_local_update _ _ (Some (Cinr (Excl ())))). }
        iMod ("Hclose" with "[H● Hs Hw]") as "_"; first by iExists _; do 2 iFrame.
        iModIntro. wp_apply (wp_if _ true). wp_op=>[_|//]; wp_if.
        rewrite -Hq''. wp_apply ("Hdrop" with "[$HP1 $HP1']"). iIntros "HP2". wp_seq.
        iApply (drop_weak_spec with "INV Hdealloc [> H◯ HP2] HΦ").
        iInv N as ([st ?]) "[>H● H]" "Hclose".
        iDestruct (own_valid_2 with "H● H◯")
          as %[[[[=]|Hincl]%option_included _]%prod_included [? _]]%auth_valid_discrete_2.
        simpl in Hincl. destruct Hincl as (?&?&[=<-]&->&[?|[]%exclusive_included]);
          try done; try apply _. setoid_subst.
        iMod (own_update_2 with "H● H◯") as "[H● $]".
        { apply auth_update, prod_local_update'.
          - apply delete_option_local_update, _.
          - by apply (op_local_update _ _ 1%nat). }
        iApply "Hclose". iExists _. by iFrame.
      + destruct Hqq' as [? ->].
        rewrite -[in (_, _)](Pos.succ_pred s) // -Pos.add_1_l -pair_op -Cinl_op Some_op.
        iMod (own_update_2 _ _ _ _ with "H● Hown") as "H●".
        { apply auth_update_dealloc, prod_local_update_1, @cancel_local_update_empty, _. }
        iMod ("Hclose" with "[- HΦ]") as "_".
        { iExists _. iFrame. iExists (q + q'')%Qp. iFrame. iSplit; first by destruct s.
          iIntros "!> !%". rewrite assoc -Hq''. f_equal. apply comm, _. }
        iModIntro. wp_apply (wp_if _ true). wp_op. by intros [=->]. intros _.
        wp_if. by iApply "HΦ".
    - wp_apply (wp_cas_int_fail with "Hs"); [done|congruence|]. iIntros "Hs".
      iMod ("Hclose" with "[Hs Hw HP1' H●]") as "_"; first by iExists _; auto with iFrame.
      iModIntro. wp_apply (wp_if _ false). by iApply ("IH" with "Hown HP1 HΦ").
  Qed.
End arc.