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

  Definition rc_inv tid (γ : gname) (l : loc) (ν : lft) (ty : type) : iProp Σ :=
    (own γ (● None) ∨
     ∃ q q' c, l ↦ #(Zpos c) ∗ own γ (● Some (q, c)) ∗ †{1%Qp}l…(S ty.(ty_size)) ∗
            ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν] ∗ ty.(ty_shr) ν tid (shift_loc l 1))%I.

  Program Definition rc (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => ∃ γ ν q,
           na_inv tid rc_invN (rc_inv tid γ l ν ty) ∗ own γ (◯ Some (q, 1%positive)) ∗ q.[ν]
         | _ => False end;
       ty_shr κ tid l :=
         ∃ γ ν q (l' : loc), κ ⊑ ν ∗ &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
                     ▷ na_inv tid rc_invN (rc_inv tid γ l' ν ty) ∗
                     &na{κ, tid, rc_invN}(own γ (◯ Some (q, 1%positive)))
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (ν) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]"; first done.
    iMod (bor_persistent_tok with "LFT Hinv Htok") as "[#Hinv Htok]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hrc Hlft]"; first done.
    iDestruct (frac_bor_lft_incl with "LFT >[Hlft]") as "#Hlft".
    { iApply bor_fracture; try done. by rewrite Qp_mult_1_r. }
    iMod (bor_na with "Hrc") as "#Hrc"; first done.
    eauto 20.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (????) "#H".
    do 4 iExists _. iDestruct "H" as "(? & ? & $ & ?)".
    iSplit; last iSplit.
    - by iApply lft_incl_trans.
    - by iApply frac_bor_shorten.
    - by iApply na_bor_shorten.
  Qed.
End rc.
