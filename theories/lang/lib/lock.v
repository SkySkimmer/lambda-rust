From iris.program_logic Require Import weakestpre.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From lrust.lang Require Import proofmode notation.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

Definition newlock : val := λ: [], let: "l" := Alloc #1 in "l" <- #false ;; "l".
Definition try_acquire : val := λ: ["l"], CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" ["l"] := if: try_acquire ["l"] then #() else "acquire" ["l"].
Definition release : val := λ: ["l"], "l" <-ˢᶜ #false.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!lrustG Σ, !lockG Σ} (N : namespace).

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname): iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne l : NonExpansive (is_lock γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : PersistentP (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma newlock_inplace (E : coPset) (R : iProp Σ) l :
    ▷ R -∗ l ↦ #false ={E}=∗ ∃ γ, is_lock γ l R.
  Proof.
    iIntros "HR Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-]") as "#?".
    { iNext. iExists false. by iFrame. }
    eauto.
  Qed.
    

  Lemma newlock_spec (R : iProp Σ) :
    {{{ ▷ R }}} newlock [] {{{ l γ, RET #l; is_lock γ l R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite -wp_fupd /newlock /=.
    wp_seq. wp_alloc l vl as "Hl" "H†". inv_vec vl=>x.
    (* FIXME: Something is wrong with the printing of the expression here *)
    rewrite heap_mapsto_vec_singleton. (* FIXME shouldn't this also compute now, like bigops do? *)
    wp_let. wp_write.
    iMod (newlock_inplace with "[HR] Hl") as (γ) "?".
    { (* FIXME: Can we make it so that we can just say "HR" instead of "[HR]", and the
         later does not matter? Or at least, "$HR" should work.  Why can't we frame
         below later? *)
      done. }
    iApply "HΦ". done.
  Qed.

  Lemma try_acquire_spec γ l R :
    {{{ is_lock γ l R }}} try_acquire [ #l ]
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    wp_rec. iInv N as ([]) "[Hl HR]" "Hclose".
    - wp_apply (wp_cas_int_fail with "Hl"); [done..|]. iIntros "Hl".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iApply ("HΦ" $! false). done.
    - wp_apply (wp_cas_int_suc with "Hl"); [done..|]. iIntros "Hl".
      iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. rewrite /locked. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.

  Lemma acquire_spec γ l R :
    {{{ is_lock γ l R }}} acquire [ #l ] {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec γ l R :
    {{{ is_lock γ l R ∗ locked γ ∗ R }}} release [ #l ] {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hlocked & HR) HΦ".
    rewrite /release /=. wp_let. iInv N as (b) "[Hl _]" "Hclose".
    wp_write. iApply "HΦ". iApply "Hclose". iNext. iExists false. by iFrame.
  Qed.
End proof.

Typeclasses Opaque is_lock locked.
