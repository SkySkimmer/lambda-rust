From iris.base_logic.lib Require Export na_invariants.
From lrust.lang Require Import heap.
From lrust.lifetime Require Import borrow frac_borrow reborrow.
From lrust.typing Require Import lft_contexts.

Class typeG Σ := TypeG {
  type_heapG :> heapG Σ;
  type_lftG :> lftG Σ;
  type_na_invG :> na_invG Σ;
  type_frac_borrowG Σ :> frac_borG Σ
}.

Definition mgmtE := ↑lftN.
Definition lrustN := nroot .@ "lrust".

Section type.
  Context `{typeG Σ}.

  Definition thread_id := na_inv_pool_name.

  Record type :=
    { ty_size : nat;
      ty_own : thread_id → list val → iProp Σ;
      ty_shr : lft → thread_id → coPset → loc → iProp Σ;

      ty_shr_persistent κ tid E l : PersistentP (ty_shr κ tid E l);

      ty_size_eq tid vl : ty_own tid vl -∗ ⌜length vl = ty_size⌝;
      (* The mask for starting the sharing does /not/ include the
         namespace N, for allowing more flexibility for the user of
         this type (typically for the [own] type). AFAIK, there is no
         fundamental reason for this.

         This should not be harmful, since sharing typically creates
         invariants, which does not need the mask.  Moreover, it is
         more consistent with thread-local tokens, which we do not
         give any. *)
      ty_share E N κ l tid : mgmtE ⊥ ↑N → mgmtE ⊆ E →
        lft_ctx -∗ &{κ} (l ↦∗: ty_own tid) ={E}=∗ ty_shr κ tid (↑N) l;
      ty_shr_mono κ κ' tid E E' l : E ⊆ E' →
        lft_ctx -∗ κ' ⊑ κ -∗ ty_shr κ tid E l -∗ ty_shr κ' tid E' l
    }.
  Global Existing Instances ty_shr_persistent.

  Class Copy (t : type) := {
    copy_persistent tid vl : PersistentP (t.(ty_own) tid vl);
    copy_shr_acc κ tid E F l q :
      mgmtE ∪ F ⊆ E →
      lft_ctx -∗ t.(ty_shr) κ tid F l -∗
        q.[κ] ∗ na_own tid F ={E}=∗ ∃ q', ▷l ↦∗{q'}: t.(ty_own) tid ∗
          (▷l ↦∗{q'}: t.(ty_own) tid ={E}=∗ q.[κ] ∗ na_own tid F)
  }.
  Global Existing Instances copy_persistent.

  (* We are repeating the typeclass parameter here jsut to make sure
     that simple_type does depend on it. Otherwise, the coercion defined
     bellow will not be acceptable by Coq. *)
  Record simple_type `{typeG Σ} :=
    { st_size : nat;
      st_own : thread_id → list val → iProp Σ;

      st_size_eq tid vl : st_own tid vl -∗ ⌜length vl = st_size⌝;
      st_own_persistent tid vl : PersistentP (st_own tid vl) }.

  Global Existing Instance st_own_persistent.

  Program Definition ty_of_st (st : simple_type) : type :=
    {| ty_size := st.(st_size); ty_own := st.(st_own);

       (* [st.(st_own) tid vl] needs to be outside of the fractured
          borrow, otherwise I do not know how to prove the shr part of
          [subtype_shr_mono]. *)
       ty_shr := λ κ tid _ l,
                 (∃ vl, (&frac{κ} λ q, l ↦∗{q} vl) ∗
                        (▷ st.(st_own) tid vl ∨ □|={↑lftN}=>[†κ]))%I
    |}.
  Next Obligation. intros. apply st_size_eq. Qed.
  Next Obligation.
    intros st E N κ l tid ? ?. iIntros "#LFT Hmt".
    iMod (bor_exists with "LFT Hmt") as (vl) "Hmt". set_solver.
    iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]". set_solver.
    iMod (bor_persistent with "LFT Hown") as "[Hown|#H†]". set_solver.
    - iMod (bor_fracture with "LFT [Hmt]") as "Hfrac"; last first.
      { iExists vl. iFrame. auto. }
      done. set_solver.
    - iExists []. iSplitL; last by auto. iApply (frac_bor_fake with "LFT"); auto.
  Qed.
  Next Obligation.
    intros st κ κ' tid E E' l ?. iIntros "#LFT #Hord H".
    iDestruct "H" as (vl) "[#Hf #Hown]".
    iExists vl. iSplit. by iApply (frac_bor_shorten with "Hord").
    iDestruct "Hown" as "[Hown|#H†]". auto. iRight. iIntros "!#".
    by iApply (lft_incl_dead with "Hord >").
  Qed.

  Global Program Instance ty_of_st_copy st : Copy (ty_of_st st).
  Next Obligation.
    intros st κ tid E F l q ?. iIntros "#LFT #Hshr[Hlft $]".
    iDestruct "Hshr" as (vl) "[Hf [Hown|#H†]]".
    - iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first set_solver.
      iModIntro. iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
      + iNext. iExists _. by iFrame.
      + iIntros "Hmt1". iDestruct "Hmt1" as (vl') "[Hmt1 #Hown']".
        iAssert (▷ ⌜length vl = length vl'⌝)%I as ">%".
        { iNext. iDestruct (st_size_eq with "Hown") as %->.
          iDestruct (st_size_eq with "Hown'") as %->. done. }
        iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op // Qp_div_2.
        iDestruct "Hmt" as "[>% Hmt]". subst. by iApply "Hclose".
    - iApply fupd_mask_mono; last iMod "H†". set_solver.
      iDestruct (lft_tok_dead with "Hlft H†") as "[]".
  Qed.
End type.

Coercion ty_of_st : simple_type >-> type.

Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

Section subtyping.
  Context `{typeG Σ} (E : lectx) (L : llctx).

  Record subtype (ty1 ty2 : type) : Prop :=
    { subtype_sz : ty1.(ty_size) = ty2.(ty_size);
      subtype_own qE qL :
        lft_ctx -∗ lectx_interp E qE -∗ llctx_interp L qL -∗
          □ ∀ tid vl, ty1.(ty_own) tid vl -∗ ty2.(ty_own) tid vl;
      subtype_shr qE qL :
        lft_ctx -∗ lectx_interp E qE -∗ llctx_interp L qL -∗
          □ ∀ κ tid F l, ty1.(ty_shr) κ tid F l -∗ ty2.(ty_shr) κ tid F l }.

  Global Instance subtype_preorder : PreOrder subtype.
  Proof.
    split.
    - intros ty. split; [done| |]; iIntros (? ?) "_ _ _ !# * $".
    - intros ty1 ty2 ty3 H1 H2. split.
      + etrans. eapply H1. eapply H2.
      + iIntros (? ?) "#LFT HE HL".
        iDestruct (subtype_own _ _ H1 with "LFT HE HL") as "#H1".
        iDestruct (subtype_own _ _ H2 with "LFT HE HL") as "#H2".
        iIntros "{HE HL} !# * ?". iApply "H2". by iApply "H1".
      + iIntros (? ?) "#LFT HE HL".
        iDestruct (subtype_shr _ _ H1 with "LFT HE HL") as "#H1".
        iDestruct (subtype_shr _ _ H2 with "LFT HE HL") as "#H2".
        iIntros "{HE HL} !# * ?". iApply "H2". by iApply "H1".
  Qed.

  Definition eqtype (ty1 ty2 : type) : Prop :=
    subtype ty1 ty2 ∧ subtype ty2 ty1.

  Global Instance subtype_equivalence : Equivalence eqtype.
  Proof.
    split.
    - split; done.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.
End subtyping.
