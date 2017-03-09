From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition rc_stR :=
  optionUR (prodR fracR positiveR).
Class rcG Σ :=
  RcG :> inG Σ (authR rc_stR).
Definition rcΣ : gFunctors := #[GFunctor (authR rc_stR)].
Instance subG_rcΣ {Σ} : subG rcΣ Σ → rcG Σ.
Proof. solve_inG. Qed.

Definition rcN := lrustN .@ "rc".
Definition rc_invN := rcN .@ "inv".
Definition rc_shrN := rcN .@ "shr".

Section rc.
  Context `{!typeG Σ, !rcG Σ}.

  Definition rc_inv tid ν (γ : gname) (l : loc) (ty : type) : iProp Σ :=
    (∃ st, own γ (● st) ∗
      match st with
      | Some (q, c) => ∃ q',
       l ↦ #(Zpos c) ∗ †{1%Qp}l…(S ty.(ty_size)) ∗
         ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν] ∗
         (1.[ν] ={↑lftN,∅}▷=∗ ▷ shift_loc l 1 ↦∗: ty.(ty_own) tid)
      | None => True
      end)%I.

  Program Definition rc (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           (l ↦ #1 ∗ †{1%Qp}l…(S ty.(ty_size)) ∗ ▷ shift_loc l 1 ↦∗: ty.(ty_own) tid) ∨
           (∃ γ ν q, na_inv tid rc_invN (rc_inv tid ν γ l ty) ∗
                     own γ (◯ Some (q, 1%positive)) ∗ q.[ν] ∗
                     ty.(ty_shr) ν tid (shift_loc l 1))
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ]
             ={F, F∖↑shrN}▷=∗ q.[κ] ∗ ∃ γ ν q',
                na_inv tid rc_invN (rc_inv tid ν γ l' ty) ∗
                &na{κ, tid, rc_invN}(own γ (◯ Some (q', 1%positive))) ∗
                ty.(ty_shr) κ tid (shift_loc l' 1)
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _ _, _ ∗ &na{_,_,_} _ ∗ _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I
          with "[Hpbown]") as "#Hinv"; first by iLeft.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]"; first set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose2]"; first solve_ndisj.
      set (X := (∃ _ _ _, _)%I).
      iModIntro. iNext. iAssert (|={F ∖ ↑shrN}=> X )%I with "[HP]" as ">HX".
      { iDestruct "HP" as "[[Hl' [H† Hown]]|$]"; last done.
        iMod (lft_create with "LFT") as (ν) "[[Hν1 Hν2] #Hν†]"; first solve_ndisj.
        (* TODO: We should consider changing the statement of bor_create to dis-entangle the two masks such that this is no longer necessary. *)
        iApply (fupd_mask_mono (↑lftN)); first solve_ndisj.
        iMod (bor_create with "LFT Hown") as "[HP HPend]"; first solve_ndisj.
        iMod (own_alloc (● Some ((1/2)%Qp, 1%positive) ⋅ ◯ Some ((1/2)%Qp, 1%positive))) as (γ) "[Ha Hf]".
        { apply auth_valid_discrete_2. done. }
        iMod (na_inv_alloc tid _ _ (rc_inv tid ν γ l' ty) with "[Ha Hν2 Hl' H† HPend]").
        { rewrite /rc_inv. iExists (Some (_, _)). iFrame. iExists _. iFrame.
          iNext. iSplit; first by rewrite Qp_div_2. iIntros "Hν".
          iMod ("Hν†" with "Hν") as "Hfin". iModIntro. iNext. iMod "Hfin".
          iMod ("HPend" with "Hfin"). done. }
        iMod (ty_share with "LFT HP Hν1") as "[??]"; first solve_ndisj.
        iExists _, _, _. iFrame. done. }
      iDestruct "HX" as (γ ν q') "(#Hinv & Hrc & Htok & #Hshr)".
      iMod ("Hclose2" with "[] [Hrc Htok]") as "[HX Htok]".
      { iNext. iIntros "HX". iModIntro. (* FIXME: iNext here doesn't strip of the next from in front of the evar. *)
        iRight. iExists γ, ν, q'. iExact "HX". }
      { iNext. by iFrame "#∗". }
      iAssert (|={F ∖ ↑shrN}=> C)%I with "[HX]" as ">#HC".
      { iExists _, _, _. iFrame "Hinv".
        iMod (bor_sep with "LFT HX") as "[_ HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[Hrc HX]"; first solve_ndisj.
        iMod (bor_sep with "LFT HX") as "[Hlft _]"; first solve_ndisj.
        iDestruct (frac_bor_lft_incl with "LFT >[Hlft]") as "#Hlft".
        { iApply (bor_fracture with "LFT"); first solve_ndisj. by rewrite Qp_mult_1_r. }
        iMod (bor_na with "Hrc") as "$"; first solve_ndisj.
        iApply ty_shr_mono; done. }
      iMod ("Hclose" with "[]") as "_"; first by auto.
      by iFrame "#∗".
    - iMod ("Hclose" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. iNext. by iFrame.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iAlways. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (???) "(? & ? & ?)".
    iExists _, _, _. iModIntro. iFrame. iSplit.
    - by iApply na_bor_shorten.
    - by iApply ty_shr_mono.
  Qed.
End rc.

Section code.
  Context `{!typeG Σ, !rcG Σ}.

  Definition rc_new ty : val :=
    funrec: <> ["x"] :=
      let: "rcbox" := new [ #(S ty.(ty_size))] in
      let: "rc" := new [ #1 ] in
      "rcbox" +ₗ #0 <- #1;;
      "rcbox" +ₗ #1 <-{ty.(ty_size)} !"x";;
      "rc" +ₗ #0 <- "rcbox";;
      delete [ #ty.(ty_size) ; "x"];; "return" ["rc"].

  Lemma rc_new_type ty :
    typed_val (rc_new ty) (fn([]; ty) → rc ty).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (_ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (rcbox); simpl_subst.
    iApply type_new; [solve_typing..|]; iIntros (rc); simpl_subst.
    iIntros (tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite (Nat2Z.id (S ty.(ty_size))) 2!tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hrc [Hrcbox Hx]]". destruct x as [[|lx|]|]; try done.
    iDestruct "Hx" as "[Hx Hx†]". iDestruct "Hx" as (vl) "[Hx↦ Hx]".
    destruct rcbox as [[|lrcbox|]|]; try done. iDestruct "Hrcbox" as "[Hrcbox Hrcbox†]".
    iDestruct "Hrcbox" as (vl') "Hrcbox". rewrite uninit_own.
    iDestruct "Hrcbox" as "[>Hrcbox↦ >SZ]". destruct vl' as [|]; iDestruct "SZ" as %[=].
    rewrite heap_mapsto_vec_cons. iDestruct "Hrcbox↦" as "[Hrcbox↦0 Hrcbox↦1]".
    destruct rc as [[|lrc|]|]; try done. iDestruct "Hrc" as "[Hrc Hrc†]".
    iDestruct "Hrc" as (vl'') "Hrc". rewrite uninit_own.
    iDestruct "Hrc" as "[>Hrc↦ >SZ]". destruct vl'' as [|]; iDestruct "SZ" as %[=].
    destruct vl'' as [|]; last done. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hrcbox↦1 $Hx↦]"); [done||lia..|].
    iIntros "[Hrcbox↦1 Hx↦]". wp_seq. wp_op. rewrite shift_loc_0. wp_write.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lrc ◁ box (rc ty)]%TC
        with "[] LFT Hna HE HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      { iExists _. rewrite uninit_own. auto. }
      iNext. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. iFrame. iLeft.
      rewrite freeable_sz_full_S. iFrame. iExists _. iFrame.  }
    iApply type_delete; [solve_typing..|].
    iApply (type_jump [ #_]); solve_typing.
  Qed.
End code.
