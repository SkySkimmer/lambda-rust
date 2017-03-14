From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition refcell_stR :=
  optionUR (prodR (agreeR lftC) (csumR (exclR unitC) (prodR fracR positiveR))).
Class refcellG Σ :=
  RefCellG :> inG Σ (authR refcell_stR).
Definition refcellΣ : gFunctors := #[GFunctor (authR refcell_stR)].
Instance subG_refcellΣ {Σ} : subG refcellΣ Σ → refcellG Σ.
Proof. solve_inG. Qed.

Definition Z_of_refcell_st (st : refcell_stR) : Z :=
  match st with
  | None => 0
  | Some (_, Cinr (_, n)) => Zpos n
  | Some _ => -1
  end.

Definition reading_st (q : frac) (ν : lft) : refcell_stR :=
  Some (to_agree ν, Cinr (q, xH)).
Definition writing_st (ν : lft) : refcell_stR :=
  Some (to_agree ν, Cinl (Excl ())).

Definition refcellN := lrustN .@ "refcell".
Definition refcell_invN := refcellN .@ "inv".

Section refcell_inv.
  Context `{typeG Σ, refcellG Σ}.

  Definition refcell_inv tid (l : loc) (γ : gname) (α : lft) ty : iProp Σ :=
    (∃ st, l ↦ #(Z_of_refcell_st st) ∗ own γ (● st) ∗
      match st return _ with
      | None =>
        (* Not borrowed. *)
        &{α}(shift_loc l 1 ↦∗: ty.(ty_own) tid)
      | Some (agν, st) =>
        ∃ ν, agν ≡ to_agree ν ∗
             (1.[ν] ={↑lftN,∅}▷=∗ &{α}(shift_loc l 1 ↦∗: ty.(ty_own) tid)) ∗
             match st with
             | Cinr (q, n) =>
               (* Immutably borrowed. *)
               ty.(ty_shr) (α ⊓ ν) tid (shift_loc l 1) ∗
               ∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν]
             | _ => (* Mutably borrowed. *) True
             end
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

  Lemma refcell_inv_proper E L tid l γ α ty1 ty2 :
    eqtype E L ty1 ty2 →
    elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
    refcell_inv tid l γ α ty1 -∗ refcell_inv tid l γ α ty2.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (Hty%eqtype_unfold) "#HE #HL H". unfold refcell_inv.
    iDestruct (Hty with "HE HL") as "(% & Hown & Hshr)".
    iAssert (□ (&{α} shift_loc l 1 ↦∗: ty_own ty1 tid -∗
                &{α} shift_loc l 1 ↦∗: ty_own ty2 tid))%I with "[]" as "#Hb".
    { iIntros "!# H". iApply bor_iff; last done.
      iSplit; iIntros "!>!#H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl;
      iFrame; by iApply "Hown". }
    iDestruct "H" as (st) "H"; iExists st;
      iDestruct "H" as "($&$&H)"; destruct st as [[agν st]|]; try done;
      last by iApply "Hb".
    iDestruct "H" as (ν) "(Hag & Hh & H)". iExists ν. iFrame. iSplitL "Hh".
    { iIntros "Hν". iMod ("Hh" with "Hν") as "Hh". iModIntro. iNext.
      iMod "Hh". by iApply "Hb". }
    destruct st as [|[]|]; try done. iDestruct "H" as "[H $]". by iApply "Hshr".
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
         | #(LitInt z) :: vl' => ⌜-1 ≤ z⌝ ∗ ty.(ty_own) tid vl'
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ α γ, κ ⊑ α ∗ &na{α, tid, refcell_invN}(refcell_inv tid l γ α ty))%I |}.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %] !% /=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H Hclose]". done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    iDestruct "H" as "[>% Hown]".
    iMod ("Hclose" $! ((∃ n:Z, l ↦ #n ∗ ⌜-1 ≤ n⌝) ∗
            shift_loc l 1 ↦∗: ty.(ty_own) tid) with "[] [-]")%I as "[H [Htok Htok']]".
    { iIntros "!> [Hn Hvl] !>". iDestruct "Hn" as (n') "[Hn >%]".
      iDestruct "Hvl" as (vl') "[H↦ Hvl]".
      iExists (#n'::vl'). rewrite heap_mapsto_vec_cons. iFrame "∗%". }
    { iNext. rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[Hn Hvl]".
      iSplitL "Hn"; [eauto|iExists _; iFrame]. }
    iMod (bor_sep with "LFT H") as "[Hn Hvl]". done.
    iMod (bor_acc_cons with "LFT Hn Htok") as "[H Hclose]". done.
    iAssert ((q / 2).[κ] ∗ ▷ ∃ γ, refcell_inv tid l γ κ ty)%I with "[> -Hclose]"
      as "[$ HQ]"; last first.
    { iMod ("Hclose" with "[] HQ") as "[Hb $]".
      - iIntros "!> H !>". iNext. iDestruct "H" as (γ st) "(? & _ & _)".
        iExists _. iIntros "{$H}!%". destruct st as [[?[|[]|]]|]; simpl; lia.
      - iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
        iExists κ, γ. iSplitR. by iApply lft_incl_refl. by iApply bor_na. }
    clear dependent n. iDestruct "H" as ([|n|[]]) "[Hn >%]"; try lia.
    - iFrame. iMod (own_alloc (● None)) as (γ) "Hst". done. iExists γ, None. by iFrame.
    - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
      iMod (own_alloc (● Some (to_agree ν, Cinr ((1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iApply (fupd_mask_mono (↑lftN)); first done.
      iMod (rebor _ _ (κ ⊓ ν) with "LFT [] Hvl") as "[Hvl Hh]". done.
      { iApply lft_intersect_incl_l. }
      iDestruct (lft_intersect_acc with "Htok' Htok1") as (q') "[Htok Hclose]".
      iMod (ty_share with "LFT Hvl Htok") as "[Hshr Htok]". done.
      iDestruct ("Hclose" with "Htok") as "[$ Htok]".
      iExists γ, _. iFrame "Hst Hn". iExists _. iIntros "{$Hshr}".
      iSplitR; first by auto. iSplitR "Htok2"; last first.
      { iExists _. iFrame. rewrite Qp_div_2. auto. }
      iIntros "!> !> Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro. iNext. iMod "Hν".
      iApply fupd_mask_mono; last iApply "Hh". done. rewrite -lft_dead_or. auto.
    - iMod (own_alloc (● writing_st static)) as (γ) "Hst". { by apply auth_auth_valid. }
      iFrame. iExists _, _. iFrame. iExists _. iSplitR; first by auto.
      iIntros "!>!> _". iApply step_fupd_intro; [set_solver|auto].
  Qed.
  Next Obligation.
    iIntros (?????) "#Hκ H". iDestruct "H" as (α γ) "[#??]".
    iExists _, _. iFrame. iApply lft_incl_trans; auto.
  Qed.

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
    iIntros (ty1 ty2 EQ) "#HE #HL". pose proof EQ as EQ'%eqtype_unfold.
    iDestruct (EQ' with "HE HL") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit; iIntros "!# * H"].
    - iPureIntro. simpl. congruence.
    - destruct vl as [|[[]|]]; try done. iDestruct "H" as "[$ H]". by iApply "Hown".
    - iDestruct "H" as (a γ) "[Ha H]". iExists a, γ. iFrame.
      iApply na_bor_iff; last done.
      iSplit; iIntros "!>!# H"; by iApply refcell_inv_proper.
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
  Proof. move=>????[|[[]|]]//=??. iIntros "[$?]". by iApply send_change_tid. Qed.
End refcell.

Hint Resolve refcell_mono' refcell_proper' : lrust_typing.
