From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import fractional.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export base.
From lrust.lifetime Require Import frac_borrow.
Set Default Proof Using "Type".

Definition elctx_elt : Type := lft * lft.
Notation elctx := (list elctx_elt).

Delimit Scope lrust_elctx_scope with EL.
(* We need to define [elctx] and [llctx] as notations to make eauto
   work. But then, Coq is not able to bind them to their
   notations, so we have to use [Arguments] everywhere. *)
Bind Scope lrust_elctx_scope with elctx_elt.

Notation "κ1 ⊑ κ2" := (@pair lft lft κ1 κ2) (at level 70) : lrust_elctx_scope.

Notation "a :: b" := (@cons elctx_elt a%EL b%EL)
  (at level 60, right associativity) : lrust_elctx_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons elctx_elt x1%EL (@cons elctx_elt x2%EL
        (..(@cons elctx_elt xn%EL (@nil elctx_elt))..))) : lrust_elctx_scope.
Notation "[ x ]" := (@cons elctx_elt x%EL (@nil elctx_elt)) : lrust_elctx_scope.

Definition llctx_elt : Type := lft * list lft.
Notation llctx := (list llctx_elt).

Delimit Scope lrust_llctx_scope with LL.
Bind Scope lrust_llctx_scope with llctx_elt.

Notation "κ ⊑ κl" := (@pair lft (list lft) κ κl) (at level 70) : lrust_llctx_scope.

Notation "a :: b" := (@cons llctx_elt a%LL b%LL)
  (at level 60, right associativity) : lrust_llctx_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons llctx_elt x1%LL (@cons llctx_elt x2%LL
        (..(@cons llctx_elt xn%LL (@nil llctx_elt))..))) : lrust_llctx_scope.
Notation "[ x ]" := (@cons llctx_elt x%LL (@nil llctx_elt)) : lrust_llctx_scope.

Section lft_contexts.
  Context `{invG Σ, lftG Σ}.
  Implicit Type (κ : lft).

  (* External lifetime contexts. *)
  Definition elctx_elt_interp (x : elctx_elt) : iProp Σ :=
    (x.1 ⊑ x.2)%I.

  Definition elctx_interp (E : elctx) : iProp Σ :=
    ([∗ list] x ∈ E, elctx_elt_interp x)%I.
  Global Arguments elctx_interp _%EL.
  Global Instance elctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Global Instance elctx_interp_persistent E :
    PersistentP (elctx_interp E).
  Proof. apply _. Qed.

  (* Local lifetime contexts. *)
  Definition llctx_elt_interp (x : llctx_elt) (q : Qp) : iProp Σ :=
    let κ' := lft_intersect_list (x.2) in
    (∃ κ0, ⌜x.1 = κ' ⊓ κ0⌝ ∗ q.[κ0] ∗ □ (1.[κ0] ={↑lftN,∅}▷=∗ [†κ0]))%I.
  Global Instance llctx_elt_interp_fractional x :
    Fractional (llctx_elt_interp x).
  Proof.
    destruct x as [κ κs]. iIntros (q q'). iSplit; iIntros "H".
    - iDestruct "H" as (κ0) "(% & [Hq Hq'] & #?)".
      iSplitL "Hq"; iExists _; by iFrame "∗%".
    - iDestruct "H" as "[Hq Hq']".
      iDestruct "Hq" as (κ0) "(% & Hq & #?)".
      iDestruct "Hq'" as (κ0') "(% & Hq' & #?)". simpl in *.
      rewrite (inj (lft_intersect (foldr lft_intersect static κs)) κ0' κ0); last congruence.
      iExists κ0. by iFrame "∗%".
  Qed.

  Definition llctx_interp (L : llctx) (q : Qp) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp x q)%I.
  Global Arguments llctx_interp _%LL _%Qp.
  Global Instance llctx_interp_fractional L :
    Fractional (llctx_interp L).
  Proof. intros ??. rewrite -big_sepL_sepL. by setoid_rewrite <-fractional. Qed.
  Global Instance llctx_interp_as_fractional L q :
    AsFractional (llctx_interp L q) (llctx_interp L) q.
  Proof. split. done. apply _. Qed.
  Global Instance llctx_interp_permut :
    Proper ((≡ₚ) ==> eq ==> (⊣⊢)) llctx_interp.
  Proof. intros ????? ->. by apply big_opL_permutation. Qed.

  Lemma lctx_equalize_lft qL κ1 κ2 `{!frac_borG Σ} :
    lft_ctx -∗ llctx_elt_interp (κ1 ⊑ [κ2]%list) qL ={⊤}=∗
      elctx_elt_interp (κ1 ⊑ κ2) ∗ elctx_elt_interp (κ2 ⊑ κ1).
  Proof.
    iIntros "#LFT Hκ". rewrite /llctx_elt_interp /=. (* TODO: Why is this unfold necessary? *)
    iDestruct "Hκ" as (κ) "(% & Hκ & _)".
    iMod (bor_create _ κ2 (qL).[κ] with "LFT [Hκ]") as "[Hκ _]";
      first done; first by iFrame.
    iMod (bor_fracture (λ q, (qL * q).[_])%I with "LFT [Hκ]") as "#Hκ"; first done.
    { rewrite Qp_mult_1_r. done. }
    iModIntro. subst κ1. iSplit.
    - iApply lft_incl_trans; iApply lft_intersect_incl_l.
    - iApply (lft_incl_glb with "[]"); first iApply (lft_incl_glb with "[]").
      + iApply lft_incl_refl.
      + iApply lft_incl_static.
      + iApply (frac_bor_lft_incl with "LFT"). done.
  Qed.

  Context (E : elctx) (L : llctx).

  (* Lifetime inclusion *)
  Definition lctx_lft_incl κ κ' : Prop :=
    ∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ κ ⊑ κ').

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_incl κ κ' : lctx_lft_incl κ κ' → lctx_lft_incl κ κ'.
  Proof. done. Qed.

  Lemma lctx_lft_incl_relf κ : lctx_lft_incl κ κ.
  Proof. iIntros (qL) "_ !# _". iApply lft_incl_refl. Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_relf.
    iIntros (??? H1 H2 ?) "HL".
    iDestruct (H1 with "HL") as "#H1".
    iDestruct (H2 with "HL") as "#H2".
    iClear "∗". iIntros "!# #HE". iApply lft_incl_trans.
    by iApply "H1". by iApply "H2".
  Qed.

  Global Instance lctx_lft_incl_proper :
    Proper (lctx_lft_eq ==> lctx_lft_eq ==> iff) lctx_lft_incl.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance lctx_lft_eq_equivalence : Equivalence lctx_lft_eq.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma lctx_lft_incl_static κ : lctx_lft_incl κ static.
  Proof. iIntros (qL) "_ !# _". iApply lft_incl_static. Qed.

  Lemma lctx_lft_incl_local κ κ' κs :
    (κ ⊑ κs)%LL ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    iIntros (? Hκ'κs qL) "H".
    iDestruct (big_sepL_elem_of with "H") as "H"; first done.
    iDestruct "H" as (κ'') "[EQ _]". iDestruct "EQ" as %EQ.
    simpl in EQ; subst. iIntros "!# #HE".
    iApply lft_incl_trans; first iApply lft_intersect_incl_l.
    by iApply lft_intersect_list_elem_of_incl.
  Qed.

  Lemma lctx_lft_incl_local' κ κ' κ'' κs :
    (κ ⊑ κs)%LL ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local. Qed.

  Lemma lctx_lft_incl_external κ κ' : (κ ⊑ κ')%EL ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (??) "_ !# #HE".
    rewrite /elctx_interp /elctx_elt_interp big_sepL_elem_of //. done.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    (κ ⊑ κ')%EL ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_external. Qed.

  (* Lifetime aliveness *)

  Definition lctx_lft_alive (κ : lft) : Prop :=
    ∀ F qL, ↑lftN ⊆ F → elctx_interp E -∗ llctx_interp L qL ={F}=∗
          ∃ q', q'.[κ] ∗ (q'.[κ] ={F}=∗ llctx_interp L qL).

  Lemma lctx_lft_alive_tok κ F q :
    ↑lftN ⊆ F →
    lctx_lft_alive κ → elctx_interp E -∗ llctx_interp L q ={F}=∗
      ∃ q', q'.[κ] ∗ llctx_interp L q' ∗
                   (q'.[κ] -∗ llctx_interp L q' ={F}=∗ llctx_interp L q).
  Proof.
    iIntros (? Hal) "#HE [HL1 HL2]".
    iMod (Hal with "HE HL1") as (q') "[Htok Hclose]"; first done.
    destruct (Qp_lower_bound (q/2) q') as (qq & q0  & q'0 & Hq & ->). rewrite Hq.
    iExists qq. iDestruct "HL2" as "[$ HL]". iDestruct "Htok" as "[$ Htok]".
    iIntros "!> Htok' HL'". iCombine "HL'" "HL" as "HL". rewrite -Hq. iFrame.
    iApply "Hclose". iFrame.
  Qed.

  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof.
    iIntros (F qL ?) "_ $". iExists 1%Qp. iSplitL. by iApply lft_tok_static. auto.
  Qed.

  Lemma lctx_lft_alive_local κ κs:
    (κ ⊑ κs)%LL ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs F qL ?) "#HE HL".
    iDestruct "HL" as "[HL1 HL2]". rewrite {2}/llctx_interp /llctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HL2") as "[Hκ Hclose]". done.
    iDestruct "Hκ" as (κ0) "(EQ & Htok & #Hend)". simpl. iDestruct "EQ" as %->.
    iAssert (∃ q', q'.[foldr lft_intersect static κs] ∗
      (q'.[foldr lft_intersect static κs] ={F}=∗ llctx_interp L (qL / 2)))%I
      with "[> HE HL1]" as "H".
    { move:(qL/2)%Qp=>qL'. clear HL. iClear "Hend".
      iInduction Hκs as [|κ κs Hκ ?] "IH" forall (qL').
      - iExists 1%Qp. iFrame. iSplitR; last by auto. iApply lft_tok_static.
      - iDestruct "HL1" as "[HL1 HL2]".
        iMod (Hκ with "HE HL1") as (q') "[Htok' Hclose]". done.
        iMod ("IH" with "HL2") as (q'') "[Htok'' Hclose']".
        destruct (Qp_lower_bound q' q'') as (q0 & q'2 & q''2 & -> & ->).
        iExists q0. rewrite -lft_tok_sep. iDestruct "Htok'" as "[$ Hr']".
        iDestruct "Htok''" as "[$ Hr'']". iIntros "!>[Hκ Hfold]".
        iMod ("Hclose" with "[$Hκ $Hr']") as "$". iApply "Hclose'". iFrame. }
    iDestruct "H" as (q') "[Htok' Hclose']". rewrite -{5}(Qp_div_2 qL).
    destruct (Qp_lower_bound q' (qL/2)) as (q0 & q'2 & q''2 & -> & ->).
    iExists q0. rewrite -(lft_tok_sep q0). iDestruct "Htok" as "[$ Htok]".
    iDestruct "Htok'" as "[$ Htok']". iIntros "!>[Hfold Hκ0]".
    iMod ("Hclose'" with "[$Hfold $Htok']") as "$".
    rewrite /llctx_interp /llctx_elt_interp. iApply "Hclose". iExists κ0. iFrame. auto.
  Qed.

  Lemma lctx_lft_alive_incl κ κ':
    lctx_lft_alive κ → lctx_lft_incl κ κ' → lctx_lft_alive κ'.
  Proof.
    iIntros (Hal Hinc F qL ?) "#HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl". iApply (Hinc with "HL HE").
    iMod (Hal with "HE HL") as (q') "[Htok Hclose]". done.
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']". done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hclose" with "[> -]").
    by iApply "Hclose'".
  Qed.

  Lemma lctx_lft_alive_external κ κ':
    (κ ⊑ κ')%EL ∈ E → lctx_lft_alive κ → lctx_lft_alive κ'.
  Proof.
    intros. by eapply lctx_lft_alive_incl, lctx_lft_incl_external.
  Qed.

  Lemma lctx_lft_alive_list κs ϝ `{!frac_borG Σ} :
    Forall lctx_lft_alive κs →
    ∀ (F : coPset) (qL : Qp),
      ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗
         llctx_interp L qL ={F}=∗ elctx_interp ((λ κ, ϝ ⊑ κ) <$> κs)%EL ∗
                                   ([†ϝ] ={F}=∗ llctx_interp L qL).
  Proof.
    iIntros (Hκs F qL ?) "#LFT #HE". iInduction κs as [|κ κs] "IH" forall (qL Hκs).
    { iIntros "$ !>". rewrite /elctx_interp big_sepL_nil. auto. }
    iIntros "[HL1 HL2]". inversion Hκs as [|?? Hκ Hκs']. clear Hκs. subst.
    iMod ("IH" with "[% //] HL2") as "[#Hκs Hclose1] {IH}".
    iMod (Hκ with "HE HL1") as (q) "[Hκ Hclose2]"; first done.
    iMod (bor_create with "LFT [Hκ]") as "[Hκ H†]"; first done. iApply "Hκ".
    iDestruct (frac_bor_lft_incl _ _ q with "LFT [> Hκ]") as "#Hincl".
    { iApply (bor_fracture with "LFT [>-]"); first done. simpl.
      rewrite Qp_mult_1_r. done. (* FIXME: right_id? *) }
    iModIntro. iFrame "#". iIntros "#Hϝ†".
    iMod ("H†" with "Hϝ†") as ">Hκ". iMod ("Hclose2" with "Hκ") as "$".
    by iApply "Hclose1".
  Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    ∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ elctx_interp E').

  Lemma elctx_sat_nil : elctx_sat [].
  Proof.
    iIntros (?) "_ !# _". rewrite /elctx_interp big_sepL_nil. auto.
  Qed.

  Lemma elctx_sat_lft_incl E' κ κ' :
    lctx_lft_incl κ κ' → elctx_sat E' → elctx_sat ((κ ⊑ κ') :: E')%EL.
  Proof.
    iIntros (Hκκ' HE' qL) "HL".
    iDestruct (Hκκ' with "HL") as "#Hincl".
    iDestruct (HE' with "HL") as "#HE'".
    iClear "∗". iIntros "!# #HE".
    (* FIXME: Why does iSplit fail here?  The goal is persistent. *)
    iSplitL.
    - by iApply "Hincl".
    - by iApply "HE'".
  Qed.

  Lemma elctx_sat_app E1 E2 :
    elctx_sat E1 → elctx_sat E2 → elctx_sat (E1 ++ E2).
  Proof.
    iIntros (HE1 HE2 ?) "HL".
    iDestruct (HE1 with "HL") as "#HE1".
    iDestruct (HE2 with "HL") as "#HE2".
    iClear "∗". iIntros "!# #HE".
    iDestruct ("HE1" with "HE") as "#$".
    iApply ("HE2" with "HE").
  Qed.

  Lemma elctx_sat_refl : elctx_sat E.
  Proof. iIntros (?) "_ !# ?". done. Qed.
End lft_contexts.

Arguments lctx_lft_incl {_ _ _} _%EL _%LL _ _.
Arguments lctx_lft_eq {_ _ _} _%EL _%LL _ _.
Arguments lctx_lft_alive {_ _ _} _%EL _%LL _.
Arguments elctx_sat {_ _ _} _%EL _%LL _%EL.
Arguments lctx_lft_incl_incl {_ _ _ _%EL _%LL} _ _.
Arguments lctx_lft_alive_tok {_ _ _ _%EL _%LL} _ _ _.

Lemma elctx_sat_submseteq `{invG Σ, lftG Σ} E E' L :
  E' ⊆+ E → elctx_sat E L E'.
Proof. iIntros (HE' ?) "_ !# H". by iApply big_sepL_submseteq. Qed.

Hint Constructors Forall Forall2 elem_of_list : lrust_typing.
Hint Resolve of_val_unlock : lrust_typing.
Hint Resolve
     lctx_lft_incl_relf lctx_lft_incl_static lctx_lft_incl_local'
     lctx_lft_incl_external'
     lctx_lft_alive_static lctx_lft_alive_local lctx_lft_alive_external
     elctx_sat_nil elctx_sat_lft_incl elctx_sat_app elctx_sat_refl
     submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : lrust_typing.

Hint Resolve elctx_sat_submseteq | 100 : lrust_typing.

(* FIXME : I would prefer using a [Hint Resolve <-] for this, but
   unfortunately, this is not preserved across modules. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5189
   This should be fixed in the next version of Coq. *)
Hint Extern 1 (_ ∈ _ ++ _) => apply <- @elem_of_app : lrust_typing.

Hint Opaque elctx_sat lctx_lft_alive lctx_lft_incl : lrust_typing.
