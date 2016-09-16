From Coq Require Import Qcanon.
From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm.

Import Perm Types.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Definitions *)
  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, ρ1 tid ={⊤}=> ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

End defs.

Infix "⇒" := perm_incl (at level 95, no associativity) : C_scope.
Notation "(⇒)" := perm_incl (only parsing) : C_scope.

Notation "ρ1 ⇔ ρ2" := (equiv (A:=perm) ρ1%P ρ2%P)
   (at level 95, no associativity) : C_scope.
Notation "(⇔)" := (equiv (A:=perm)) (only parsing) : C_scope.

Section props.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Properties *)
  Global Instance perm_incl_preorder : PreOrder (⇒).
  Proof.
    split.
    - iIntros (? tid) "H". eauto.
    - iIntros (??? H12 H23 tid) "H". iVs (H12 with "H") as "H". by iApply H23.
  Qed.

  Global Instance perm_equiv_equiv : Equivalence (⇔).
  Proof.
    split.
    - by split.
    - by intros x y []; split.
    - intros x y z [] []. split; by transitivity y.
  Qed.

  Global Instance perm_incl_proper :
    Proper ((⇔) ==> (⇔) ==> iff) (⇒).
  Proof. intros ??[??]??[??]; split; intros ?; by simplify_order. Qed.

  Global Instance perm_sep_proper :
    Proper ((⇔) ==> (⇔) ==> (⇔)) (sep).
  Proof.
    intros ??[A B]??[C D]; split; iIntros (tid) "[A B]".
    iVs (A with "A") as "$". iApply (C with "B").
    iVs (B with "A") as "$". iApply (D with "B").
  Qed.

  Lemma uPred_equiv_perm_equiv ρ θ : (∀ tid, ρ tid ⊣⊢ θ tid) → (ρ ⇔ θ).
  Proof. intros Heq. split=>tid; rewrite Heq; by iIntros. Qed.

  Lemma perm_incl_top ρ : ρ ⇒ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 : ρ1 ⇒ ρ2 → ρ ★ ρ1 ⇒ ρ ★ ρ2.
  Proof. iIntros (Hρ tid) "[$?]". by iApply Hρ. Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    ρ1 ⇒ ρ2 → ρ1 ★ ρ ⇒ ρ2 ★ ρ.
  Proof. iIntros (Hρ tid) "[?$]". by iApply Hρ. Qed.

  Lemma perm_incl_exists_intro {A} P x : P x ⇒ ∃ x : A, P x.
  Proof. iIntros (tid) "H!==>". by iExists x. Qed.

  Global Instance perm_sep_assoc : Assoc (⇔) sep.
  Proof. intros ???; split. by iIntros (tid) "[$[$$]]". by iIntros (tid) "[[$$]$]". Qed.

  Global Instance perm_sep_comm : Comm (⇔) sep.
  Proof. intros ??; split; by iIntros (tid) "[$$]". Qed.

  Global Instance perm_top_right_id : RightId (⇔) ⊤ sep.
  Proof. intros ρ; split. by iIntros (tid) "[? _]". by iIntros (tid) "$". Qed.

  Global Instance perm_top_left_id : LeftId (⇔) ⊤ sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

  Lemma perm_incl_duplicable ρ (_ : Duplicable ρ) : ρ ⇒ ρ ★ ρ.
  Proof. iIntros (tid) "#H!==>". by iSplit. Qed.

  Lemma perm_tok_plus κ q1 q2 :
    tok κ q1 ★ tok κ q2 ⇔ tok κ (q1 + q2).
  Proof.
    rewrite /tok /sep /=; split; intros tid; rewrite -lft_own_op;
      iIntros "[[$$]H]!==>". by iDestruct "H" as "[$?]". by auto.
  Qed.

  Lemma perm_lftincl_refl κ : ⊤ ⇒ κ ⊑ κ.
  Proof. iIntros (tid) "_!==>". iApply lft_incl_refl. Qed.

  Lemma perm_lftincl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 ★ κ2 ⊑ κ3 ⇒ κ1 ⊑ κ3.
  Proof. iIntros (tid) "[#?#?]!==>". iApply lft_incl_trans. auto. Qed.

  Lemma perm_incl_share v κ ty :
    v ◁ &uniq{κ} ty ⇒ v ◁ &shr{κ} ty.
  Proof.
    iIntros (tid) "Huniq". destruct v; last done.
    iDestruct "Huniq" as (l) "[% Hown]".
    (* FIXME : we need some tokens here. *)
    iAssert (∃ q, [κ]{q})%I as "Htok". admit.
    iDestruct "Htok" as (q) "Htok".
    iVs (ty.(ty_share) _ lrustN with "Hown Htok") as "[Hown _]".
    apply disjoint_union_l; solve_ndisj. set_solver. iVsIntro.
    iExists _. iSplit. done. done.
  Admitted.

  Lemma split_own_prod tyl (q0: Qp) (ql : list Qp) (l : loc) tid :
    length tyl = length ql →
      (own (foldr Qp_plus q0 ql) (product tyl)).(ty_own) tid [ #l] ⊣⊢
    ▷ †{q0}(shift_loc l (0 + (product tyl).(ty_size))%nat)…0 ★
    [★ list] qtyoffs ∈ (combine ql (combine_offs tyl 0)),
         (own (qtyoffs.1) (qtyoffs.2.1)).(ty_own)
              tid [ #(shift_loc l (qtyoffs.2.2))].
  Proof.
    intros Hlen.
    assert (REW: ∀ (l : loc) (Φ : loc → iProp Σ),
               Φ l ⊣⊢ (∃ l0:loc, [ #l] = [ #l0] ★ Φ l0)).
    { intros l0 Φ. iSplit; iIntros "H". eauto.
      iDestruct "H" as (l') "[Heq H]". iDestruct "Heq" as %[=]. subst. done. }
    setoid_rewrite <-REW. clear REW.
    rewrite big_sepL_sepL assoc split_prod_mt big_sepL_later. apply uPred.sep_proper.
    - rewrite -{1}(shift_loc_0_nat l). generalize 0%nat at -3. revert ql Hlen.
      induction tyl as [|ty tyl IH]; intros [|q ql] [=] offs.
      + by rewrite big_sepL_nil !right_id.
      + rewrite -heap_freeable_op_eq uPred.later_sep shift_loc_assoc_nat IH //
                Nat.add_assoc big_sepL_cons.
        iSplit; by iIntros "($&$&$)".
    - generalize 0%nat. revert ql Hlen.
      induction tyl as [|ty tyl IH]; intros [|q ql] [=] offs. done.
      rewrite !big_sepL_cons IH //.
  Qed.

  Lemma perm_split_own_prod tyl (q : Qp) (ql : list Qp) v :
    length tyl = length ql →
    foldr (λ (q : Qp) acc, q + acc)%Qc 0%Qc ql = q →
    v ◁ own q (product tyl) ⇔
      foldr (λ qtyoffs acc,
             proj_valuable (Z.of_nat (qtyoffs.2.2)) v ◁
                           own (qtyoffs.1) (qtyoffs.2.1) ★ acc)
            ⊤ (combine ql (combine_offs tyl 0)).
  Proof.
    intros Hlen Hq.
    assert (DEC : Decision (∃ (l : loc), v = Some #l)).
    { destruct v as [[[]|]|]; try by right; intros [l [=]]. left; eauto. }
    destruct DEC as [[l ->]|Hv]; last first.
    { destruct tyl as [|ty0 tyl], ql as [|q0 ql]; try done.
      { destruct q as [q ?]. simpl in *. by subst. }
      destruct v as [[[|l|]|]|];
        try by split; iIntros (tid) "H";
          [iDestruct "H" as (l) "[% _]" || iDestruct "H" as "[]" |
           iDestruct "H" as "[[]_]"].
      naive_solver. }
    destruct (@exists_last _ ql) as (ql'&q0&->).
    { destruct ql as [|q0 ql]; last done. destruct q. simpl in *. by subst. }
    assert (foldr Qp_plus (q0/2) (ql' ++ [q0/2]) = q)%Qp as <-.
    { destruct q as [q Hqpos]. apply Qp_eq. simpl in *. subst. clear. induction ql'.
      - by rewrite /fold_right /app Qp_div_2 Qcplus_0_r.
      - by rewrite /= IHql'. }
    revert Hlen. assert (length (ql' ++ [q0]) = length (ql' ++ [q0/2]%Qp)) as ->. 
    { rewrite !app_length /=. lia. }
    intros Hlen. apply uPred_equiv_perm_equiv=>tid.
    rewrite /has_type /from_option split_own_prod //.
    clear -Hlen. revert ql' Hlen. generalize 0%nat at -2.
    induction tyl as [|ty tyl IH]; destruct ql' as [|q ql']=>Hlen; try done.
    - destruct tyl; last done. clear IH Hlen.
      rewrite big_sepL_singleton /= /sep !right_id comm uPred.sep_exist_r.
      apply uPred.exist_proper=>l0.
      rewrite -{3}(Qp_div_2 q0) -{3}(right_id O plus ty.(ty_size))
              -heap_freeable_op_eq uPred.later_sep -!assoc.
      iSplit; iIntros "[#Eq [? [? ?]]]"; iFrame "# ★";
        iDestruct "Eq" as %[=]; subst; rewrite shift_loc_assoc_nat //.
    - simpl in *. rewrite big_sepL_cons /sep -IH; last by congruence. clear IH.
      rewrite !uPred.sep_exist_r !uPred.sep_exist_l. apply uPred.exist_proper=>l0.
      rewrite -!assoc /=. by iSplit; iIntros "[$[$[$[$$]]]]".
  Qed.

End props.
