From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import thread_local.
From lrust Require Export type perm.

Section perm_incl.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, ρ1 tid ={⊤}=> ρ2 tid.

  Lemma perm_incl_top ρ : perm_incl ρ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Global Instance perm_incl_refl : Reflexive perm_incl.
  Proof. iIntros (? tid) "H". eauto. Qed.

  Global Instance perm_incl_trans : Transitive perm_incl.
  Proof.
    iIntros (??? H12 H23 tid) "H". iVs (H12 with "H") as "H". by iApply H23.
  Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 :
    perm_incl ρ1 ρ2 → perm_incl (ρ ★ ρ1) (ρ ★ ρ2).
  Proof. iIntros (Hρ tid) "[$?]". by iApply Hρ. Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    perm_incl ρ1 ρ2 → perm_incl (ρ1 ★ ρ) (ρ2 ★ ρ).
  Proof. iIntros (Hρ tid) "[?$]". by iApply Hρ. Qed.

End perm_incl.

Section duplicable.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Class Duplicable (ρ : perm) :=
    perm_incl_duplicable : perm_incl ρ (ρ ★ ρ).

  Lemma has_type_dup v ty : ty.(ty_dup) → Duplicable (v ◁ ty).
  Proof. iIntros (Hdup tid) "H!==>". by iApply ty_dup_dup. Qed.

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

End duplicable.

Hint Extern 0 (Duplicable (_ ◁ _)) => apply has_type_dup; exact I.

Section perm_equiv.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  Definition perm_equiv ρ1 ρ2 := perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Global Instance perm_equiv_refl : Reflexive perm_equiv.
  Proof. by split. Qed.

  Global Instance perm_equiv_trans : Transitive perm_equiv.
  Proof. intros x y z [] []. split; by transitivity y. Qed.

  Global Instance perm_equiv_sym : Symmetric perm_equiv.
  Proof. by intros x y []; split. Qed.

  Global Instance perm_incl_proper :
    Proper (perm_equiv ==> perm_equiv ==> iff) perm_incl.
  Proof. intros ??[??]??[??]; split; eauto using perm_incl_trans. Qed.

  Global Instance sep_assoc : Assoc perm_equiv Perm.sep.
  Proof. intros ???; split. by iIntros (tid) "[$[$$]]". by iIntros (tid) "[[$$]$]". Qed.

  Global Instance sep_comm : Comm perm_equiv Perm.sep.
  Proof. intros ??; split; by iIntros (tid) "[$$]". Qed.

  Global Instance top_right_id : RightId perm_equiv ⊤ Perm.sep.
  Proof. intros ρ; split. by iIntros (tid) "[? _]". by iIntros (tid) "$". Qed.

  Global Instance top_left_id : LeftId perm_equiv ⊤ Perm.sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

End perm_equiv.