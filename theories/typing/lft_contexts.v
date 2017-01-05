From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import fractional.
From lrust.lifetime Require Import derived borrow frac_borrow.

Inductive elctx_elt : Type :=
| ELCtx_Alive (κ : lft)
| ELCtx_Incl (κ κ' : lft).
Definition elctx := list elctx_elt.

Delimit Scope lrust_elctx_scope with EL.
Bind Scope lrust_elctx_scope with elctx elctx_elt.

Notation "☀ κ" := (ELCtx_Alive κ) (at level 70) : lrust_elctx_scope.
Infix "⊑" := ELCtx_Incl (at level 70) : lrust_elctx_scope.

Notation "a :: b" := (@cons elctx_elt a%EL b%EL)
  (at level 60, right associativity) : lrust_elctx_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons elctx_elt x1%EL (@cons elctx_elt x2%EL
        (..(@cons elctx_elt xn%EL (@nil elctx_elt))..))) : lrust_elctx_scope.
Notation "[ x ]" := (@cons elctx_elt x%EL (@nil elctx_elt)) : lrust_elctx_scope.

Definition llctx_elt : Type := lft * list lft.
Definition llctx := list llctx_elt.

Delimit Scope lrust_llctx_scope with LL.
Bind Scope lrust_llctx_scope with llctx llctx_elt.

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
  Definition elctx_elt_interp (x : elctx_elt) (q : Qp) : iProp Σ :=
    match x with
    | ☀ κ => q.[κ]%I
    | κ ⊑ κ' => (κ ⊑ κ')%I
    end%EL.
  Global Instance elctx_elt_interp_fractional x:
    Fractional (elctx_elt_interp x).
  Proof. destruct x; unfold elctx_elt_interp; apply _. Qed.
  Typeclasses Opaque elctx_elt_interp.
  Definition elctx_elt_interp_0 (x : elctx_elt) : iProp Σ :=
    match x with
    | ☀ κ => True%I
    | κ ⊑ κ' => (κ ⊑ κ')%I
    end%EL.
  Global Instance elctx_elt_interp_0_persistent x:
    PersistentP (elctx_elt_interp_0 x).
  Proof. destruct x; apply _. Qed.
  Typeclasses Opaque elctx_elt_interp_0.

  Lemma elctx_elt_interp_persist x q :
    elctx_elt_interp x q -∗ elctx_elt_interp_0 x.
  Proof. destruct x; by iIntros "?/=". Qed.

  Definition elctx_interp (E : elctx) (q : Qp) : iProp Σ :=
    ([∗ list] x ∈ E, elctx_elt_interp x q)%I.
  Global Instance elctx_interp_fractional E:
    Fractional (elctx_interp E).
  Proof. intros ??. rewrite -big_sepL_sepL. by setoid_rewrite <-fractional. Qed.
  Global Instance elctx_interp_as_fractional E q:
    AsFractional (elctx_interp E q) (elctx_interp E) q.
  Proof. split. done. apply _. Qed.
  Global Instance elctx_interp_permut:
    Proper ((≡ₚ) ==> eq ==> (⊣⊢)) elctx_interp.
  Proof. intros ????? ->. by apply big_opL_permutation. Qed.
  Typeclasses Opaque elctx_interp.

  Definition elctx_interp_0 (E : elctx) : iProp Σ :=
    ([∗ list] x ∈ E, elctx_elt_interp_0 x)%I.
  Global Instance elctx_interp_0_persistent E:
    PersistentP (elctx_interp_0 E).
  Proof. apply _. Qed.
  Global Instance elctx_interp_0_permut:
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp_0.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Typeclasses Opaque elctx_interp_0.

  Lemma elctx_interp_persist x q :
    elctx_interp x q -∗ elctx_interp_0 x.
  Proof.
    unfold elctx_interp, elctx_interp_0. f_equiv. intros _ ?.
    apply elctx_elt_interp_persist.
  Qed.

  (* Local lifetime contexts. *)

  Definition llctx_elt_interp (x : llctx_elt) (q : Qp) : iProp Σ :=
    let κ' := foldr (∪) static (x.2) in
    (∃ κ0, ⌜x.1 = κ' ∪ κ0⌝ ∗ q.[κ0] ∗ □ (1.[κ0] ={⊤,⊤∖↑lftN}▷=∗ [†κ0]))%I.
  Global Instance llctx_elt_interp_fractional x :
    Fractional (llctx_elt_interp x).
  Proof.
    destruct x as [κ κs]. iIntros (q q'). iSplit; iIntros "H".
    - iDestruct "H" as (κ0) "(% & [Hq Hq'] & #?)".
      iSplitL "Hq"; iExists _; by iFrame "∗%".
    - iDestruct "H" as "[Hq Hq']".
      iDestruct "Hq" as (κ0) "(% & Hq & #?)".
      iDestruct "Hq'" as (κ0') "(% & Hq' & #?)". simpl in *.
      rewrite (inj (union (foldr (∪) static κs)) κ0' κ0); last congruence.
      iExists κ0. by iFrame "∗%".
  Qed.
  Typeclasses Opaque llctx_elt_interp.

  Definition llctx_elt_interp_0 (x : llctx_elt) : Prop :=
    let κ' := foldr (∪) static (x.2) in (∃ κ0, x.1 = κ' ∪ κ0).
  Lemma llctx_elt_interp_persist x q :
    llctx_elt_interp x q -∗ ⌜llctx_elt_interp_0 x⌝.
  Proof.
    iIntros "H". unfold llctx_elt_interp.
    iDestruct "H" as (κ0) "[% _]". by iExists κ0.
  Qed.

  Definition llctx_interp (L : llctx) (q : Qp) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp x q)%I.
  Global Instance llctx_interp_fractional L:
    Fractional (llctx_interp L).
  Proof. intros ??. rewrite -big_sepL_sepL. by setoid_rewrite <-fractional. Qed.
  Global Instance llctx_interp_as_fractional L q:
    AsFractional (llctx_interp L q) (llctx_interp L) q.
  Proof. split. done. apply _. Qed.
  Global Instance llctx_interp_permut:
    Proper ((≡ₚ) ==> eq ==> (⊣⊢)) llctx_interp.
  Proof. intros ????? ->. by apply big_opL_permutation. Qed.
  Typeclasses Opaque llctx_interp.

  Definition llctx_interp_0 (L : llctx) : Prop :=
    ∀ x, x ∈ L → llctx_elt_interp_0 x.
  Lemma llctx_interp_persist L q :
    llctx_interp L q -∗ ⌜llctx_interp_0 L⌝.
  Proof.
    iIntros "H". iIntros (x ?). iApply llctx_elt_interp_persist.
    unfold llctx_interp. by iApply (big_sepL_elem_of with "H").
  Qed.

  Lemma lctx_equalize_lft qE qL κ1 κ2 `{!frac_borG Σ} :
    lft_ctx -∗ llctx_elt_interp (κ1 ⊑ [κ2]%list) qL ={⊤}=∗
      elctx_elt_interp (κ1 ⊑ κ2) qE ∗ elctx_elt_interp (κ2 ⊑ κ1) qE.
  Proof.
    iIntros "#LFT Hκ". rewrite /llctx_elt_interp /=. (* TODO: Why is this unfold necessary? *)
    iDestruct "Hκ" as (κ) "(% & Hκ & _)".
    iMod (bor_create _ κ2 with "LFT [Hκ]") as "[Hκ _]"; first done; first by iFrame.
    iMod (bor_fracture (λ q, (qL * q).[_])%I with "LFT [Hκ]") as "#Hκ"; first done.
    { rewrite Qp_mult_1_r. done. }
    iModIntro. subst κ1. iSplit.
    - iApply lft_le_incl.
      rewrite <-!gmultiset_union_subseteq_l. done.
    - iApply (lft_incl_glb with "[]"); first iApply (lft_incl_glb with "[]").
      + iApply lft_incl_refl.
      + iApply lft_incl_static.
      + iApply (frac_bor_lft_incl with "LFT"). done.
  Qed.

  Context (E : elctx) (L : llctx).

  (* Lifetime inclusion *)

  Definition lctx_lft_incl κ κ' : Prop :=
    elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗ κ ⊑ κ'.

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_relf κ : lctx_lft_incl κ κ.
  Proof. iIntros "_ _". iApply lft_incl_refl. Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_relf.
    iIntros (??? H1 H2) "#HE #HL". iApply (lft_incl_trans with "[#] [#]").
    iApply (H1 with "HE HL"). iApply (H2 with "HE HL").
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
  Proof. iIntros "_ _". iApply lft_incl_static. Qed.

  Lemma lctx_lft_incl_local κ κ' κs :
    (κ ⊑ κs)%LL ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    iIntros (? Hκ'κs) "_ H". iDestruct "H" as %HL.
    edestruct HL as [κ0 EQ]. done. simpl in EQ; subst.
    iApply lft_le_incl. etrans; last by apply gmultiset_union_subseteq_l.
    clear -Hκ'κs. induction Hκ'κs.
    - apply gmultiset_union_subseteq_l.
    - etrans. done. apply gmultiset_union_subseteq_r.
  Qed.

  Lemma lctx_lft_incl_local' κ κ' κ'' κs :
    (κ ⊑ κs)%LL ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local. Qed.

  Lemma lctx_lft_incl_external κ κ' : (κ ⊑ κ')%EL ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (?) "H _".
    rewrite /elctx_interp_0 /elctx_elt_interp_0 big_sepL_elem_of //. done.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    (κ ⊑ κ')%EL ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_external. Qed.

  (* Lifetime aliveness *)

  Definition lctx_lft_alive (κ : lft) : Prop :=
    ∀ F qE qL, ↑lftN ⊆ F → elctx_interp E qE -∗ llctx_interp L qL ={F}=∗
          ∃ q', q'.[κ] ∗ (q'.[κ] ={F}=∗ elctx_interp E qE ∗ llctx_interp L qL).

  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof.
    iIntros (F qE qL ?) "$$". iExists 1%Qp. iSplitL. by iApply lft_tok_static. auto.
  Qed.

  Lemma lctx_lft_alive_local κ κs:
    (κ ⊑ κs)%LL ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs F qE qL ?) "HE HL".
    iDestruct "HL" as "[HL1 HL2]". rewrite {2}/llctx_interp /llctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HL2") as "[Hκ Hclose]". done.
    iDestruct "Hκ" as (κ0) "(EQ & Htok & #Hend)". simpl. iDestruct "EQ" as %->.
    iAssert (∃ q', q'.[foldr union static κs] ∗
      (q'.[foldr union static κs] ={F}=∗ elctx_interp E qE ∗ llctx_interp L (qL / 2)))%I
      with ">[HE HL1]" as "H".
    { move:(qL/2)%Qp=>qL'. clear HL. iClear "Hend".
      iInduction Hκs as [|κ κs Hκ ?] "IH" forall (qE qL').
      - iExists 1%Qp. iFrame. iSplitR; last by auto. iApply lft_tok_static.
      - iDestruct "HL1" as "[HL1 HL2]". iDestruct "HE" as "[HE1 HE2]".
        iMod (Hκ with "* HE1 HL1") as (q') "[Htok' Hclose]". done.
        iMod ("IH" with "* HE2 HL2") as (q'') "[Htok'' Hclose']".
        destruct (Qp_lower_bound q' q'') as (q0 & q'2 & q''2 & -> & ->).
        iExists q0. rewrite -lft_tok_sep. iDestruct "Htok'" as "[$ Hr']".
        iDestruct "Htok''" as "[$ Hr'']". iIntros "!>[Hκ Hfold]".
        iMod ("Hclose" with "[$Hκ $Hr']") as "[$$]". iApply "Hclose'". iFrame. }
    iDestruct "H" as (q') "[Htok' Hclose']". rewrite -{5}(Qp_div_2 qL).
    destruct (Qp_lower_bound q' (qL/2)) as (q0 & q'2 & q''2 & -> & ->).
    iExists q0. rewrite -(lft_tok_sep q0). iDestruct "Htok" as "[$ Htok]".
    iDestruct "Htok'" as "[$ Htok']". iIntros "!>[Hfold Hκ0]".
    iMod ("Hclose'" with "[$Hfold $Htok']") as "[$$]".
    rewrite /llctx_interp /llctx_elt_interp. iApply "Hclose". iExists κ0. iFrame. auto.
  Qed.

  Lemma lctx_lft_alive_external κ: (☀κ)%EL ∈ E → lctx_lft_alive κ.
  Proof.
    iIntros ([i HE]%elem_of_list_lookup_1 F qE qL ?) "HE $ !>".
    rewrite /elctx_interp /elctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HE") as "[Hκ Hclose]". done.
    iExists qE. iFrame. iIntros "?!>". by iApply "Hclose".
  Qed.

  Lemma lctx_lft_alive_incl κ κ':
    lctx_lft_alive κ → lctx_lft_incl κ κ' → lctx_lft_alive κ'.
  Proof.
    iIntros (Hal Hinc F qE qL ?) "HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl". iApply (Hinc with "[HE] [HL]").
      by iApply elctx_interp_persist. by iApply llctx_interp_persist.
    iMod (Hal with "HE HL") as (q') "[Htok Hclose]". done.
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']". done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hclose" with ">").
    by iApply "Hclose'".
  Qed.

  Lemma lctx_lft_alive_external' κ κ':
    (☀κ)%EL ∈ E → (κ ⊑ κ')%EL ∈ E → lctx_lft_alive κ'.
  Proof.
    intros. eapply lctx_lft_alive_incl, lctx_lft_incl_external; last done.
    by apply lctx_lft_alive_external.
  Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    ∀ qE qL F, ↑lftN ⊆ F → elctx_interp E qE -∗ llctx_interp L qL ={F}=∗
      ∃ qE', elctx_interp E' qE' ∗
       (elctx_interp E' qE' ={F}=∗ elctx_interp E qE ∗ llctx_interp L qL).

  Lemma elctx_sat_nil : elctx_sat [].
  Proof.
    iIntros (qE qL F ?) "$$". iExists 1%Qp. rewrite /elctx_interp big_sepL_nil. auto.
  Qed.

  Lemma elctx_sat_alive E' κ :
    lctx_lft_alive κ → elctx_sat E' → elctx_sat ((☀κ) :: E').
  Proof.
    iIntros (Hκ HE' qE qL F ?) "[HE1 HE2] [HL1 HL2]".
    iMod (Hκ with "HE1 HL1") as (q) "[Htok Hclose]". done.
    iMod (HE' with "HE2 HL2") as (q') "[HE' Hclose']". done.
    destruct (Qp_lower_bound q q') as (q0 & q2 & q'2 & -> & ->). iExists q0.
    rewrite {5 6}/elctx_interp big_sepL_cons /=.
    iDestruct "Htok" as "[$ Htok]". iDestruct "HE'" as "[Hf HE']".
    iSplitL "Hf". by rewrite /elctx_interp.
    iIntros "!>[Htok' ?]". iMod ("Hclose" with "[$Htok $Htok']") as "[$$]".
    iApply "Hclose'". iFrame. by rewrite /elctx_interp.
  Qed.

  Lemma elctx_sat_lft_incl E' κ κ' :
    lctx_lft_incl κ κ' → elctx_sat E' → elctx_sat ((κ ⊑ κ') :: E').
  Proof.
    iIntros (Hκκ' HE' qE qL F ?) "HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl". iApply (Hκκ' with "[HE] [HL]").
      by iApply elctx_interp_persist. by iApply llctx_interp_persist.
    iMod (HE' with "HE HL") as (q) "[HE' Hclose']". done.
    iExists q. rewrite {1 2 4 5}/elctx_interp big_sepL_cons /=.
    iIntros "{$Hincl $HE'}!>[_ ?]". by iApply "Hclose'".
  Qed.
End lft_contexts.


Section elctx_incl.
  (* External lifetime context inclusion, in a persistent context.
     (Used for function types subtyping).
     On paper, this corresponds to using only the inclusions from E, L
     to show E1; [] |- E2.
  *)

  Context `{invG Σ, lftG Σ} (E : elctx) (L : llctx).

  Definition elctx_incl E1 E2 : Prop :=
    ∀ F, ↑lftN ⊆ F → elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
    ∀ qE1, elctx_interp E1 qE1 ={F}=∗ ∃ qE2, elctx_interp E2 qE2 ∗
       (elctx_interp E2 qE2 ={F}=∗ elctx_interp E1 qE1).
  Global Instance : RewriteRelation elctx_incl.

  Global Instance elctx_incl_preorder : PreOrder elctx_incl.
  Proof.
    split.
    - iIntros (???) "_ _ * ?". iExists _. iFrame. eauto.
    - iIntros (x y z Hxy Hyz ??) "#HE #HL * HE1".
      iMod (Hxy with "HE HL * HE1") as (qy) "[HE1 Hclose1]"; first done.
      iMod (Hyz with "HE HL * HE1") as (qz) "[HE1 Hclose2]"; first done.
      iModIntro. iExists qz. iFrame "HE1". iIntros "HE1".
      iApply ("Hclose1" with ">"). iApply "Hclose2". done.
  Qed.

  Lemma elctx_incl_refl E' : elctx_incl E' E'.
  Proof. reflexivity. Qed.

  Lemma elctx_incl_nil E' : elctx_incl E' [].
  Proof.
    iIntros (??) "_ _ * $". iExists 1%Qp.
    rewrite /elctx_interp big_sepL_nil. auto.
  Qed.

  Global Instance elctx_incl_app_proper :
    Proper (elctx_incl ==> elctx_incl ==> elctx_incl) app.
  Proof.
    iIntros (?? HE1 ?? HE2 ??) "#HE #HL *". rewrite {1}/elctx_interp big_sepL_app.
    iIntros "[HE1 HE2]".
    iMod (HE1 with "HE HL * HE1") as (q1) "[HE1 Hclose1]"; first done.
    iMod (HE2 with "HE HL * HE2") as (q2) "[HE2 Hclose2]"; first done.
    destruct (Qp_lower_bound q1 q2) as (q & ? & ? & -> & ->).
    iModIntro. iExists q. rewrite /elctx_interp !big_sepL_app.
    iDestruct "HE1" as "[$ HE1]". iDestruct "HE2" as "[$ HE2]".
    iIntros "[HE1' HE2']".
    iMod ("Hclose1" with "[$HE1 $HE1']") as "$".
    iMod ("Hclose2" with "[$HE2 $HE2']") as "$".
    done.
  Qed.
  Global Instance elctx_incl_cons_proper x :
    Proper (elctx_incl ==> elctx_incl) (cons x).
  Proof. by apply (elctx_incl_app_proper [_] [_]). Qed.

  Lemma elctx_incl_dup E1 :
    elctx_incl E1 (E1 ++ E1).
  Proof.
    iIntros (??) "#HE #HL * [HE1 HE1']".
    iModIntro. iExists (qE1 / 2)%Qp.
    rewrite /elctx_interp !big_sepL_app. iFrame.
    iIntros "[HE1 HE1']". by iFrame.
  Qed.

  Lemma elctx_sat_incl E1 E2 :
    elctx_sat E1 [] E2 → elctx_incl E1 E2.
   Proof.
    iIntros (H12 ??) "#HE #HL * HE1".
    iMod (H12 _ 1%Qp with "HE1 []") as (qE2) "[HE2 Hclose]". done.
    { by rewrite /llctx_interp big_sepL_nil. }
    iExists qE2. iFrame. iIntros "!> HE2".
    by iMod ("Hclose" with "HE2") as "[$ _]".
   Qed.

  Lemma elctx_incl_lft_alive E1 E2 κ :
    lctx_lft_alive E1 [] κ → elctx_incl E1 E2 → elctx_incl E1 ((☀κ) :: E2).
  Proof.
    intros Hκ HE2. rewrite (elctx_incl_dup E1).
    apply (elctx_incl_app_proper _ [_]); last done.
    apply elctx_sat_incl. apply elctx_sat_alive, elctx_sat_nil; first done.
  Qed.

  Lemma elctx_incl_lft_incl E1 E2 κ κ' :
    lctx_lft_incl (E ++ E1) L κ κ' → elctx_incl E1 E2 →
    elctx_incl E1 ((κ ⊑ κ') :: E2).
  Proof.
    iIntros (Hκκ' HE2 ??) "#HE #HL * HE1".
    iDestruct (elctx_interp_persist with "HE1") as "#HE1'".
    iDestruct (Hκκ' with "[HE HE1'] HL") as "#Hκκ'".
    { rewrite /elctx_interp_0 big_sepL_app. auto. }
    iMod (HE2 with "HE HL * HE1") as (qE2) "[HE2 Hclose']". done.
    iExists qE2. rewrite /elctx_interp big_sepL_cons /=. iFrame "∗#".
    iIntros "!> [_ HE2']". by iApply "Hclose'".
  Qed.
End elctx_incl.

Ltac solve_typing := by eauto 100 with lrust_typing.

Hint Constructors Forall Forall2 : lrust_typing.
Hint Resolve
     lctx_lft_incl_relf lctx_lft_incl_static lctx_lft_incl_local'
     lctx_lft_incl_external'
     lctx_lft_alive_static lctx_lft_alive_local lctx_lft_alive_external
     elctx_sat_nil elctx_sat_alive elctx_sat_lft_incl
     elctx_incl_refl elctx_incl_nil elctx_incl_lft_alive elctx_incl_lft_incl
  : lrust_typing.

(* We declare these as hint extern, so that the [B] parameter of elem_of does
   not have to be [list _] and can be an alias of this. *)
Hint Extern 0 (@elem_of _ _ (@elem_of_list _) _ (_ :: _)) =>
  eapply @elem_of_list_here : lrust_typing.
Hint Extern 1 (@elem_of _ _ (@elem_of_list _) _ (_ :: _)) =>
  eapply @elem_of_list_further : lrust_typing.

Hint Resolve lctx_lft_alive_external' | 100 : lrust_typing.

Lemma elctx_incl_lft_incl_alive `{invG Σ, lftG Σ} E L E1 E2 κ κ' :
  lctx_lft_incl (E ++ E1) L κ κ' → elctx_incl E L E1 E2 →
  elctx_incl E L ((☀κ) :: E1) ((☀κ') :: E2).
Proof.
  move=> ? /elctx_incl_lft_incl -> //.
  apply (elctx_incl_app_proper _ _ [_; _] [_]); solve_typing.
Qed.
