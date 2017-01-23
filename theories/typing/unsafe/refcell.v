From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition refcell_stR :=
  optionUR (csumR (exclR unitC) (prodR (prodR (agreeR (leibnizC lft)) fracR) posR)).
Class refcellG Σ :=
  RefCellG :> inG Σ (authR refcell_stR).

Definition Z_of_refcell_st (st : refcell_stR) : Z :=
  match st with
  | None => 0
  | Some (Cinr (_, _, n)) => Zpos n
  | Some _ => -1
  end.

Definition reading_st (q : frac) (κ : lft) : refcell_stR :=
  Some (Cinr (to_agree (κ : leibnizC lft), q, xH)).
Definition writing_st (q : frac) : refcell_stR := Some (Cinl (Excl ())).

Section refcell.
  Context `{typeG Σ, refcellG Σ}.

  Definition refcell_inv (l : loc) ty tid (a : lft) (γ : gname) : iProp Σ :=
    (∃ st, l ↦ #(Z_of_refcell_st st) ∗ own γ (● st) ∗
      match st return _ with
      | None => &{a}(shift_loc l 1 ↦∗: ty.(ty_own) tid)
      | Some (Cinr ({|agree_car := v|}, q, n)) =>
        ∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[v] ∗
              ty.(ty_shr) (a ∪ v) tid (shift_loc l 1) ∗
              ([†v] ={lftE}=∗ &{a}(shift_loc l 1 ↦∗: ty.(ty_own) tid))
      | Some _ => True
      end)%I.

  Program Definition refcell (ty : type) :=
    {| ty_size := S ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' => ⌜-1 ≤ z⌝ ∗ ty.(ty_own) tid vl'
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ a γ, κ ⊑ a ∗ &na{a, tid, lrustN}(refcell_inv l ty tid a γ))%I |}.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %]!%/=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H Hclose]". done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    iDestruct "H" as "[>% Hown]".
    iMod ("Hclose" $! ((∃ n:Z, l ↦ #n ∗ ⌜-1 ≤ n⌝) ∗
            shift_loc l 1 ↦∗: ty.(ty_own) tid) with "[-] []")%I as "[H [Htok Htok']]".
    { iNext. rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[Hn Hvl]".
      iSplitL "Hn"; [eauto|iExists _; iFrame]. }
    { iIntros "!> [Hn Hvl] !>". iDestruct "Hn" as (n') "[Hn >%]".
      iDestruct "Hvl" as (vl') "[H↦ Hvl]".
      iExists (#n'::vl'). rewrite heap_mapsto_vec_cons. iFrame "∗%". }
    iMod (bor_sep with "LFT H") as "[Hn Hvl]". done.
    iMod (bor_acc_cons with "LFT Hn Htok") as "[H Hclose]". done.
    iAssert ((q / 2).[κ] ∗ ▷ ∃ γ, refcell_inv l ty tid κ γ)%I with ">[-Hclose]"
      as "[$ HQ]"; last first.
    { iMod ("Hclose" with "* HQ []") as "[Hb $]".
      - iIntros "!> H !>". iNext. iDestruct "H" as (γ st) "(? & _ & _)".
        iExists _. iIntros "{$H}!%". destruct st as [[|[[]?]|]|]; simpl; lia.
      - iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
        iExists κ, γ. iSplitR. by iApply lft_incl_refl. by iApply bor_na. }
    clear dependent n. iDestruct "H" as ([|n|[]]) "[Hn >%]"; try lia.
    - iFrame. iMod (own_alloc (● None)) as (γ) "Hst". done. iExists γ, None. by iFrame.
    - iMod (lft_create with "LFT") as (v) "[[Htok1 Htok2] _]". done.
      iMod (own_alloc
         (● Some (Cinr (to_agree (v : leibnizC _), (1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      destruct (Qp_lower_bound (1/2) (q/2)) as (q' & q1 & q2 & H12 & ->). rewrite H12.
      iDestruct "Htok'" as "[Htok' $]". iDestruct "Htok1" as "[Htok1 Htok1']".
      iApply (fupd_mask_mono lftE). done.
      iMod (rebor _ _ (κ∪v) with "LFT [] Hvl") as "[Hvl Hh]". done.
      { iApply lft_le_incl. apply gmultiset_union_subseteq_l. }
      iMod (ty_share _ _ (κ∪v) _ _ q' with "LFT Hvl [Htok' Htok1]")
        as "[Hshr Htok]". done.
      { rewrite -lft_tok_sep. iFrame. }
      rewrite -lft_tok_sep. iDestruct "Htok" as "[$ Htok]".
      iExists γ, _. iFrame "Hst Hn". iExists _. iIntros "{$Htok2 $Hshr}!>!>".
      rewrite -H12 Qp_div_2. iSplit; first done. iIntros "H†". iApply "Hh".
      rewrite -lft_dead_or. auto.
    - iMod (own_alloc (● Some (Cinl (Excl ())))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iFrame. iExists _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "LFT #Hκ H". iDestruct "H" as (a γ) "[#??]".
    iExists _, _. iFrame. iApply lft_incl_trans; auto.
  Qed.

  Global Instance refcell_ne n : Proper (dist n ==> dist n) refcell.
  Proof.
    move=>??[[]]/=Hsz Hown Hshr. split; [split|]; simpl. congruence.
    - f_contractive=>tid vl. repeat f_equiv. apply Hown.
    - intros κ tid l. unfold refcell_inv.
      repeat (f_contractive || f_equiv); apply dist_S.
      apply Hshr. apply Hown. apply Hown.
  Qed.

  Global Instance refcell_mono E L : Proper (eqtype E L ==> subtype E L) refcell.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (ty1 ty2 EQ%eqtype_unfold) "#LFT #HE #HL".
    iDestruct (EQ with "LFT HE HL") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit; iIntros "!# * H"].
    - iPureIntro. simpl. congruence.
    - destruct vl as [|[[]|]]; try done. iDestruct "H" as "[$ H]". by iApply "Hown".
    - iDestruct "H" as (a γ) "[Ha H]". iExists a, γ. iFrame.
      iApply (na_bor_iff_proper with "[] H"). iNext. iAlways.
      iAssert (□ (&{a} shift_loc l 1 ↦∗: ty_own ty1 tid ↔
                  &{a} shift_loc l 1 ↦∗: ty_own ty2 tid))%I as "#Hbiff".
      { iSplit; iIntros "!#H"; iApply (bor_iff_proper with "[] H"); iIntros "!>!#"; 
        iSplit; iIntros "H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl; iFrame;
          by iApply "Hown". }
      iSplit; iIntros "H"; iDestruct "H" as (st) "H"; iExists st;
        iDestruct "H" as "($&$&H)"; destruct st as [[|[[[]]]|]|]; try done;
        (try by iApply "Hbiff");
      iDestruct "H" as (q') "(Heq & Htok & Hs & H†)"; iExists q'; iFrame;
      (iSplitL "Hs"; [by iApply "Hshr"| iIntros "?"; iApply "Hbiff"; by iApply "H†"]).
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
