From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm.

Import Perm.

Section defs.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* Definitions *)
  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, ρ1 tid ={⊤}=> ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Class Duplicable (ρ : @perm Σ) :=
    perm_incl_duplicable : perm_incl ρ (ρ ★ ρ).

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
    iIntros (tid) "Huniq". iDestruct "Huniq" as (l) "[% Hown]".
    (* FIXME : we nee some tokens here. *)
    iAssert (∃ q, [κ]{q})%I as "Htok". admit.
    iDestruct "Htok" as (q) "Htok".
    iVs (ty.(ty_share) _ lrustN with "Hown Htok") as "[Hown _]".
    admit. set_solver. iVsIntro. iExists _. iSplit. done. done.
  Admitted.

  Lemma has_type_dup v ty : ty.(ty_dup) → Duplicable (v ◁ ty).
  Proof. iIntros (Hdup tid) "H". by iApply ty_dup_dup. Qed.

  Global Instance lft_incl_dup κ κ' : Duplicable (κ ⊑ κ').
  Proof. iIntros (tid) "#H!==>". by iSplit. Qed.

  Global Instance sep_dup P Q :
    Duplicable P → Duplicable Q → Duplicable (P ★ Q).
  Proof.
    iIntros (HP HQ tid) "[HP HQ]".
    iVs (HP with "HP") as "[$$]". by iApply HQ.
  Qed.

  Global Instance top_dup : Duplicable ⊤.
  Proof. iIntros (tid) "_!==>". by iSplit. Qed.

End props.

Hint Extern 0 (Duplicable (_ ◁ _)) => apply has_type_dup; exact I.
