From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import fractional.
From lrust.lifetime Require Export derived.

Section lft_contexts.
  Context `{invG Σ, lftG Σ}.
  Implicit Type (κ : lft).

  (* External lifetime contexts. *)

  Inductive elctx_elt : Type :=
  | ELCtx_Alive κ
  | ELCtx_Incl κ κ'.
  Definition elctx := list elctx_elt.

  Definition elctx_elt_interp (x : elctx_elt) (q : Qp) : iProp Σ :=
    match x with
    | ELCtx_Alive κ => q.[κ]
    | ELCtx_Incl κ κ' => κ ⊑ κ'
    end%I.
  Global Instance elctx_elt_interp_fractional x:
    Fractional (elctx_elt_interp x).
  Proof. destruct x; unfold elctx_elt_interp; apply _. Qed.
  Typeclasses Opaque elctx_elt_interp.
  Definition elctx_elt_interp_0 (x : elctx_elt) : iProp Σ :=
    match x with
    | ELCtx_Alive κ => True
    | ELCtx_Incl κ κ' => κ ⊑ κ'
    end%I.
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

  Definition llctx_elt : Type := lft * list lft.
  Definition llctx := list llctx_elt.

  Definition llctx_elt_interp (x : llctx_elt) (q : Qp) : iProp Σ :=
    let κ' := foldr (∪) static (x.2) in
    (∃ κ0, ⌜x.1 = κ' ∪ κ0⌝ ∗ q.[κ0] ∗ □ (1.[x.1] ={⊤,⊤∖↑lftN}▷=∗ [†x.1]))%I.
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

  Context (E : elctx) (L : llctx).

  (* Lifetime inclusion *)

  (* There does not seem to be a need in the type system for
     "equivalence" of lifetimes. If so, TODO : add it, and the
     corresponding [Proper] instances for the relevent types. *)
  Definition incl κ κ' : Prop :=
    elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗ κ ⊑ κ'.

  Global Instance incl_preorder : PreOrder incl.
  Proof.
    split.
    - iIntros (?) "_ _". iApply lft_incl_refl.
    - iIntros (??? H1 H2) "#HE #HL". iApply (lft_incl_trans with "[#] [#]").
      iApply (H1 with "HE HL"). iApply (H2 with "HE HL").
  Qed.

  Lemma incl_static κ : incl κ static.
  Proof. iIntros "_ _". iApply lft_incl_static. Qed.

  Lemma incl_local κ κ' κs : (κ, κs) ∈ L → κ' ∈ κs → incl κ κ'.
  Proof.
    iIntros (? Hκ'κs) "_ H". iDestruct "H" as %HL.
    edestruct HL as [κ0 EQ]. done. simpl in EQ; subst.
    iApply lft_le_incl. etrans; last by apply gmultiset_union_subseteq_l.
    clear -Hκ'κs. induction Hκ'κs.
    - apply gmultiset_union_subseteq_l.
    - etrans. done. apply gmultiset_union_subseteq_r.
  Qed.

  Lemma incl_external κ κ' : ELCtx_Incl κ κ' ∈ E → incl κ κ'.
  Proof.
    iIntros (?) "H _".
    rewrite /elctx_interp_0 /elctx_elt_interp_0 big_sepL_elem_of //. done.
  Qed.

  (* Lifetime aliveness *)

  Definition alive (κ : lft) : Prop :=
    ∀ F qE qL, ⌜↑lftN ⊆ F⌝ -∗ elctx_interp E qE -∗ llctx_interp L qL ={F}=∗
          ∃ q', q'.[κ] ∗ (q'.[κ] ={F}=∗ elctx_interp E qE ∗ llctx_interp L qL).

  Lemma alive_static : alive static.
  Proof.
    iIntros (F qE qL) "%$$". iExists 1%Qp. iSplitL. by iApply lft_tok_static. auto.
  Qed.

  Lemma alive_llctx κ κs: (κ, κs) ∈ L → Forall alive κs → alive κ.
  Proof.
    iIntros ([i HL]%elem_of_list_lookup_1 Hκs F qE qL) "% HE HL".
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
        iMod (Hκ with "* [%] HE1 HL1") as (q') "[Htok' Hclose]". done.
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

  Lemma alive_elctx κ: ELCtx_Alive κ ∈ E → alive κ.
  Proof.
    iIntros ([i HE]%elem_of_list_lookup_1 F qE qL) "% HE $ !>".
    rewrite /elctx_interp /elctx_elt_interp.
    iDestruct (big_sepL_lookup_acc with "HE") as "[Hκ Hclose]". done.
    iExists qE. iFrame. iIntros "?!>". by iApply "Hclose".
  Qed.

  Lemma alive_incl κ κ': alive κ → incl κ κ' → alive κ'.
  Proof.
    iIntros (Hal Hinc F qE qL) "% HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl". iApply (Hinc with "[HE] [HL]").
      by iApply elctx_interp_persist. by iApply llctx_interp_persist.
    iMod (Hal with "[%] HE HL") as (q') "[Htok Hclose]". done.
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose']". done.
    iExists q''. iIntros "{$Htok}!>Htok". iApply ("Hclose" with ">").
    by iApply "Hclose'".
  Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    ∀ qE qL F, ⌜↑lftN ⊆ F⌝ -∗ elctx_interp E qE -∗ llctx_interp L qL ={F}=∗
      ∃ qE', elctx_interp E' qE' ∗
       (elctx_interp E' qE' ={F}=∗ elctx_interp E qE ∗ llctx_interp L qL).

  Lemma elctx_sat_nil : elctx_sat [].
  Proof.
    iIntros (qE qL F) "%$$". iExists 1%Qp. rewrite /elctx_interp big_sepL_nil. auto.
  Qed.

  Lemma elctx_sat_alive E' κ :
    alive κ → elctx_sat E' → elctx_sat (ELCtx_Alive κ :: E').
  Proof.
    iIntros (Hκ HE' qE qL F) "% [HE1 HE2] [HL1 HL2]".
    iMod (Hκ with "[%] HE1 HL1") as (q) "[Htok Hclose]". done.
    iMod (HE' with "[%] HE2 HL2") as (q') "[HE' Hclose']". done.
    destruct (Qp_lower_bound q q') as (q0 & q2 & q'2 & -> & ->). iExists q0.
    rewrite {5 6}/elctx_interp big_sepL_cons /=.
    iDestruct "Htok" as "[$ Htok]". iDestruct "HE'" as "[Hf HE']".
    iSplitL "Hf". by rewrite /elctx_interp.
    iIntros "!>[Htok' ?]". iMod ("Hclose" with "[$Htok $Htok']") as "[$$]".
    iApply "Hclose'". iFrame. by rewrite /elctx_interp.
  Qed.

  Lemma elctx_sat_incl E' κ κ' :
    incl κ κ' → elctx_sat E' → elctx_sat (ELCtx_Incl κ κ' :: E').
  Proof.
    iIntros (Hκκ' HE' qE qL F) "% HE HL".
    iAssert (κ ⊑ κ')%I with "[#]" as "#Hincl". iApply (Hκκ' with "[HE] [HL]").
      by iApply elctx_interp_persist. by iApply llctx_interp_persist.
    iMod (HE' with "[%] HE HL") as (q) "[HE' Hclose']". done.
    iExists q. rewrite {1 2 4 5}/elctx_interp big_sepL_cons /=.
    iIntros "{$Hincl $HE'}!>[_ ?]". by iApply "Hclose'".
  Qed.
End lft_contexts.