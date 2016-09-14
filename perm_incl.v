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

  Lemma perm_split_own_prod tyl (q : Qp) (ql : list Qp) v :
    length tyl = length ql →
    foldr (λ (q : Qp) acc, q + acc)%Qc 0%Qc ql = q →
    v ◁ own q (product tyl) ⇔
      foldr (λ qtysz acc,
             proj_valuable (Z.of_nat (qtysz.2.2)) v ◁
                           own (qtysz.1) (qtysz.2.1) ★ acc)
            ⊤ (combine ql (combine_offs tyl 0)).
  Proof.
    destruct tyl as [|ty0 tyl], ql as [|q0 ql]; try done.
    { simpl. intros _?. destruct q as [q ?]. simpl in *. by subst. }
    destruct v as [[[|l|]|]|];
      try by split; iIntros (tid) "H";
        [iDestruct "H" as (l) "[% _]" || iDestruct "H" as "[]" |
         iDestruct "H" as "[[]_]"].
    intros [= EQ]. revert EQ.
    rewrite -{1}(shift_loc_0 l). change 0 with (Z.of_nat 0). generalize O at 2 3.
    revert q ty0 q0 ql. induction tyl as [|ty1 tyl IH]=>q ty0 q0 ql offs Hlen Hq;
      destruct ql as [|q1 ql]; try done.
    - simpl in Hq. rewrite ->Qcplus_0_r, <-Qp_eq in Hq. subst q.
      rewrite /= right_id. split; iIntros (tid) "H!==>/="; rewrite Nat.add_0_r.
      + iDestruct "H" as (l') "(%&?&H)". iExists l'. iSplit. done. iFrame. iNext.
        iDestruct "H" as (vl) "[Hvl H]".
        iDestruct "H" as ([|?[|??]]) "(%&%&?)"; try done.
        iExists _. subst. rewrite /= app_nil_r big_sepL_singleton. by iFrame.
      + iDestruct "H" as (l') "(%&?&Hown)". iExists l'. iSplit. done. iFrame. iNext.
        iDestruct "Hown" as (vl) "[Hmt Hown]". iExists vl. iFrame.
        iExists [vl]. rewrite /= app_nil_r big_sepL_singleton. iFrame. by iSplit.
    - assert (Hq' : (0 < q1 + foldr (λ (q : Qp) acc, q + acc) 0 ql)%Qc).
      { apply Qcplus_pos_nonneg. done. clear. induction ql. done.
        apply Qcplus_nonneg_nonneg; last done. by apply Qclt_le_weak. }
      pose (q' := mk_Qp _ Hq').
      assert (q = q0 + q')%Qp as -> by rewrite Qp_eq -Hq //. clear Hq.
      injection Hlen. clear Hlen. intro Hlen.
      simpl in IH|-*. rewrite -(IH q') //. clear IH. split; iIntros (tid) "H".
      + iDestruct "H" as (l') "(Hl'&Hf&H)". iDestruct "Hl'" as %[= Hl']. subst.
        iDestruct "H" as (vl) "[Hvl H]".
        iDestruct "H" as ([|vl0[|vl1 vll]]) "(>%&>%&Hown)"; try done. subst.
        rewrite big_sepL_cons heap_mapsto_vec_app -heap_freeable_op_eq.
        iDestruct "Hf" as "[Hf0 Hfq]". iDestruct "Hvl" as "[Hvl0 Hvll]".
        iDestruct "Hown" as "[Hown0 Hown]".
        iAssert (▷ (length vl0 = ty_size ty0))%I with "[#]" as "#>Hlenvl0".
        { iNext. iApply (ty_size_eq with "Hown0"). }
        iDestruct "Hlenvl0" as %Hlenvl0. iVsIntro. iSplitL "Hf0 Hvl0 Hown0".
        * iExists _. iSplit. done. iFrame. iNext. iExists vl0. by iFrame.
        * iExists _. iSplit. done. rewrite !shift_loc_assoc -!Nat2Z.inj_add Hlenvl0.
          iFrame. iNext. iExists (concat (vl1 :: vll)). iFrame. iExists (_ :: _).
          iSplit. done. iFrame. iPureIntro. simpl in *. congruence.
      + iDestruct "H" as "[H0 H]".
        iDestruct "H0" as (vl0) "(Heq&Hf0&Hmt0)". iDestruct "Heq" as %[= ?]. subst vl0.
        iDestruct "H" as (vl) "(Heq&Hf&Hmt)". iDestruct "Heq" as %[= ?]. subst vl.
        iVsIntro. iExists (shift_loc l offs). iSplit. done. iNext.
        iSplitL "Hf Hf0".
        * rewrite -heap_freeable_op_eq shift_loc_assoc Nat2Z.inj_add. by iFrame.
        * iDestruct "Hmt0" as (vl0) "[Hmt0 Hown0]". iDestruct "Hmt" as (vl) "[Hmt Hown]".
          iDestruct (ty_size_eq with "Hown0") as %<-.
          iExists (vl0 ++ vl). iSplitL "Hmt Hmt0".
          { rewrite heap_mapsto_vec_app shift_loc_assoc Nat2Z.inj_add. by iFrame. }
          iDestruct "Hown" as (vll) "(%&%&Hown)". subst.
          iExists (_ :: _). iSplit. done. iSplit. iPureIntro; simpl in *; congruence.
          rewrite big_sepL_cons. by iFrame.
  Qed.

End props.
