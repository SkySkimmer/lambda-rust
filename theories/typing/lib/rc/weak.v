From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
From lrust.typing.lib Require Export rc.
Set Default Proof Using "Type".

Section weak.
  Context `{!typeG Σ, !rcG Σ}.

  Program Definition weak (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => ∃ γ ν, rc_persist tid ν γ l ty ∗ own γ weak_tok
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦{q} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ]
             ={F, F∖↑shrN}▷=∗ q.[κ] ∗ ∃ γ ν, rc_persist tid ν γ l' ty ∗
                &na{κ, tid, rc_shrN}(own γ weak_tok)
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    (* Ideally, we'd change ty_shr to say "l ↦{q} #l" in the fractured borrow,
       but that would be additional work here... *)
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _, _ ∗ &na{_,_,_} _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I with "[Hpbown]") as "#Hinv";
      first by iLeft.
    iIntros "!> !# * % Htok".
    iMod (inv_open with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose2]"; first solve_ndisj.
      iDestruct "HP" as (γ ν) "(#Hpersist & Hweak)".
      iModIntro. iNext. iMod ("Hclose2" with "[] Hweak") as "[Hb $]"; first by auto 10.
      iAssert C with "[>Hb]" as "#HC".
      { iExists _, _. iFrame "Hpersist". iApply (bor_na with "Hb"). solve_ndisj. }
      iMod ("Hclose1" with "[]") as "_"; by auto.
    - iMod ("Hclose1" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. auto.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iAlways. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (? ν) "(? & ?)".
    iExists _, _. iFrame. by iApply na_bor_shorten.
  Qed.

  Global Instance weak_wf ty `{!TyWf ty} : TyWf (weak ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Global Instance weak_type_contractive : TypeContractive weak.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || exact: type_dist2_dist ||
                                       f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance weak_ne : NonExpansive weak.
  Proof. apply type_contractive_ne, _. Qed.

  Lemma weak_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (weak ty1) (weak ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(Hsz & #Hoincl & #Hsincl)".
    iSplit; first done. iSplit; iAlways.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as (γ ν) "(#Hpersist & Htok)".
      iExists _, _. iFrame "Htok". by iApply rc_persist_type_incl.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iIntros "{$Hfrac} !# * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[$ H]". iDestruct "H" as (γ ν) "(Hpersist & Hshr)".
      iExists _, _. iFrame "Hshr". by iApply rc_persist_type_incl.
  Qed.

  Global Instance weak_mono E L :
    Proper (subtype E L ==> subtype E L) weak.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!# #HE". iApply weak_subtype. iApply "Hsub"; done.
  Qed.
  Global Instance weak_proper E L :
    Proper (eqtype E L ==> eqtype E L) weak.
  Proof. intros ??[]. by split; apply weak_mono. Qed.
End weak.

Section code.

End code.
