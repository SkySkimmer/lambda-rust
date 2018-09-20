From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition refcell_stR :=
  optionUR (prodR (prodR
             (agreeR (prodC lftC boolC))
             fracR)
             positiveR).
Class refcellG Σ :=
  RefCellG :> inG Σ (authR refcell_stR).
Definition refcellΣ : gFunctors := #[GFunctor (authR refcell_stR)].
Instance subG_refcellΣ {Σ} : subG refcellΣ Σ → refcellG Σ.
Proof. solve_inG. Qed.

Definition refcell_st := option ((lft * Datatypes.bool) * frac * positive).
Definition refcell_st_to_R (st : refcell_st) : refcell_stR :=
  match st with
  | None => None
  | Some (x, q, n) => Some (to_agree x, q, n)
  end.
Coercion refcell_st_to_R : refcell_st >-> ucmra_car.

Definition Z_of_refcell_st (st : refcell_st) : Z :=
  match st with
  | None => 0
  | Some (_, false, _, n) => Zpos n (* Immutably borrowed *)
  | Some (_, true, _, n) => Zneg n  (* Mutably borrowed *)
  end.

Definition reading_stR (q : frac) (ν : lft) : refcell_stR :=
  refcell_st_to_R $ Some (ν, false, q, xH).
Definition writing_stR (q : frac) (ν : lft) : refcell_stR :=
  refcell_st_to_R $ Some (ν, true, q, xH).

Definition refcellN := lrustN .@ "refcell".
Definition refcell_invN := refcellN .@ "inv".

Section refcell_inv.
  Context `{typeG Σ, refcellG Σ}.

  Definition refcell_inv tid (l : loc) (γ : gname) (α : lft) ty : iProp Σ :=
    (∃ st, l ↦ #(Z_of_refcell_st st) ∗ own γ (● (refcell_st_to_R st)) ∗
      match st return _ with
      | None =>
        (* Not borrowed. *)
        &{α}((l +ₗ 1) ↦∗: ty.(ty_own) tid)
      | Some (ν, rw, q, _) =>
        (1.[ν] ={↑lftN,∅}▷=∗ &{α}((l +ₗ 1) ↦∗: ty.(ty_own) tid)) ∗
        (∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν]) ∗
        if rw then (* Mutably borrowed. *) True
        else       (* Immutably borrowed. *) ty.(ty_shr) (α ⊓ ν) tid (l +ₗ 1)
      end)%I.

  Global Instance refcell_inv_type_ne n tid l γ α :
    Proper (type_dist2 n ==> dist n) (refcell_inv tid l γ α).
  Proof.
    solve_proper_core
      ltac:(fun _ => exact: type_dist2_S || f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance refcell_inv_ne tid l γ α : NonExpansive (refcell_inv tid l γ α).
  Proof.
    intros n ???. (* TODO: f_equiv takes forever here, what is going on? *)
    eapply refcell_inv_type_ne, type_dist_dist2. done.
  Qed.

  Lemma refcell_inv_proper E L ty1 ty2 q :
    eqtype E L ty1 ty2 →
    llctx_interp L q -∗ ∀ tid l γ α, □ (elctx_interp E -∗
    refcell_inv tid l γ α ty1 -∗ refcell_inv tid l γ α ty2).
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic. *)
    (*             It would easily gain from some automation. *)
    rewrite eqtype_unfold. iIntros (Hty) "HL".
    iDestruct (Hty with "HL") as "#Hty". iIntros "* !# #HE H".
    iDestruct ("Hty" with "HE") as "(% & #Hown & #Hshr)".
    iAssert (□ (&{α}((l +ₗ 1) ↦∗: ty_own ty1 tid) -∗
                &{α}((l +ₗ 1) ↦∗: ty_own ty2 tid)))%I as "#Hb".
    { iIntros "!# H". iApply bor_iff; last done.
      iNext; iAlways; iSplit; iIntros "H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl;
      iFrame; by iApply "Hown". }
    iDestruct "H" as (st) "H"; iExists st;
      iDestruct "H" as "($&$&H)"; destruct st as [[[[ν rw] q' ] n]|]; try done;
      last by iApply "Hb".
    iDestruct "H" as "(Hh & $ & H)". iSplitL "Hh".
    { iIntros "Hν". iMod ("Hh" with "Hν") as "Hh". iModIntro. iNext.
      iMod "Hh". by iApply "Hb". }
    destruct rw; try done. by iApply "Hshr".
  Qed.
End refcell_inv.

Section refcell.
  Context `{typeG Σ, refcellG Σ}.

  (* Original Rust type:
     pub struct RefCell<T: ?Sized> {
       borrow: Cell<BorrowFlag>,
       value: UnsafeCell<T>,
     }
  *)

  Program Definition refcell (ty : type) :=
    {| ty_size := S ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' => ty.(ty_own) tid vl'
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ α γ, κ ⊑ α ∗ &na{α, tid, refcell_invN}(refcell_inv tid l γ α ty))%I |}.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq /=. by iIntros (->).
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H Hclose]". done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    iDestruct "H" as "Hown".
    iMod ("Hclose" $! ((∃ n:Z, l ↦ #n) ∗
            (l +ₗ 1) ↦∗: ty.(ty_own) tid) with "[] [-]")%I as "[H [Htok Htok']]".
    { iIntros "!> [Hn Hvl] !>". iDestruct "Hn" as (n') "Hn".
      iDestruct "Hvl" as (vl') "[H↦ Hvl]".
      iExists (#n'::vl'). rewrite heap_mapsto_vec_cons. iFrame. }
    { iNext. rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[Hn Hvl]".
      iSplitL "Hn"; eauto with iFrame. }
    iMod (bor_sep with "LFT H") as "[Hn Hvl]". done.
    iMod (bor_acc_cons with "LFT Hn Htok") as "[H Hclose]". done.
    iAssert ((q / 2).[κ] ∗ ▷ ∃ γ, refcell_inv tid l γ κ ty)%I with "[> -Hclose]"
      as "[$ HQ]"; last first.
    { iMod ("Hclose" with "[] HQ") as "[Hb $]".
      - iIntros "!> H !>". iNext. iDestruct "H" as (γ st) "(H & _ & _)". eauto.
      - iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
        iExists κ, γ. iSplitR. by iApply lft_incl_refl. by iApply bor_na. }
    clear dependent n. iDestruct "H" as ([|n|n]) "Hn"; try lia.
    - iFrame. iMod (own_alloc (● None)) as (γ) "Hst". done. iExists γ, None. by iFrame.
    - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
      iMod (own_alloc (● (refcell_st_to_R $ Some (ν, false, (1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iApply (fupd_mask_mono (↑lftN)); first done.
      iMod (rebor _ _ (κ ⊓ ν) with "LFT [] Hvl") as "[Hvl Hh]". done.
      { iApply lft_intersect_incl_l. }
      iDestruct (lft_intersect_acc with "Htok' Htok1") as (q') "[Htok Hclose]".
      iMod (ty_share with "LFT Hvl Htok") as "[Hshr Htok]". done.
      iDestruct ("Hclose" with "Htok") as "[$ Htok]".
      iExists γ, _. iFrame "Hst Hn Hshr".
      iSplitR "Htok2"; last by iExists _; iFrame; rewrite Qp_div_2.
      iIntros "!> !> Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro. iNext. iMod "Hν".
      iApply fupd_mask_mono; last iApply "Hh". done. rewrite -lft_dead_or. auto.
    - iMod (own_alloc (● (refcell_st_to_R $ Some (static, true, (1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iFrame "Htok'". iExists γ, _. iFrame. iSplitR.
      { rewrite -step_fupd_intro. auto. set_solver+. }
      iSplitR; [|done]. iExists (1/2)%Qp. rewrite Qp_div_2. iSplitR; [done|].
      iApply lft_tok_static.
  Qed.
  Next Obligation.
    iIntros (?????) "#Hκ H". iDestruct "H" as (α γ) "[#??]".
    iExists _, _. iFrame. iApply lft_incl_trans; auto.
  Qed.

  Global Instance refcell_wf ty `{!TyWf ty} : TyWf (refcell ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

  Global Instance refcell_type_ne : TypeNonExpansive refcell.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || (eapply refcell_inv_type_ne; try reflexivity) ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance refcell_ne : NonExpansive refcell.
  Proof.
    constructor; solve_proper_core ltac:(fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance refcell_mono E L : Proper (eqtype E L ==> subtype E L) refcell.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (ty1 ty2 EQ qL) "HL". generalize EQ. rewrite eqtype_unfold=>EQ'.
    iDestruct (EQ' with "HL") as "#EQ'".
    iDestruct (refcell_inv_proper with "HL") as "#Hty1ty2"; first done.
    iDestruct (refcell_inv_proper with "HL") as "#Hty2ty1"; first by symmetry.
    iIntros "!# #HE". iDestruct ("EQ'" with "HE") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit; iIntros "!# * H"].
    - iPureIntro. simpl. congruence.
    - destruct vl as [|[[]|]]; try done. by iApply "Hown".
    - iDestruct "H" as (a γ) "[Ha H]". iExists a, γ. iFrame.
      iApply na_bor_iff; last done. iNext; iAlways; iSplit; iIntros "H".
      by iApply "Hty1ty2". by iApply "Hty2ty1".
  Qed.
  Lemma refcell_mono' E L ty1 ty2 :
    eqtype E L ty1 ty2 → subtype E L (refcell ty1) (refcell ty2).
  Proof. eapply refcell_mono. Qed.
  Global Instance refcell_proper E L : Proper (eqtype E L ==> eqtype E L) refcell.
  Proof. by split; apply refcell_mono. Qed.
  Lemma refcell_proper' E L ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (refcell ty1) (refcell ty2).
  Proof. eapply refcell_proper. Qed.

  Global Instance refcell_send :
    Send ty → Send (refcell ty).
  Proof. move=>????[|[[]|]]//=. Qed.
End refcell.

Hint Resolve refcell_mono' refcell_proper' : lrust_typing.
