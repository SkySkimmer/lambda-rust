From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From lrust.lang Require Import lang proofmode notation.
Set Default Proof Using "Type".

Definition mklock_unlocked : val := λ: ["l"], "l" <- #false.
Definition mklock_locked : val := λ: ["l"], "l" <- #true.
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
  Context `{!lrustG Σ, !lockG Σ}.

  Definition lock_proto (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition locked (γ : gname): iProp Σ := own γ (Excl ()).

  Global Instance lock_proto_ne γ l : NonExpansive (lock_proto γ l).
  Proof. solve_proper. Qed.

  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Lemma lock_proto_iff γ l R R' :
    □ (R ↔ R') -∗ lock_proto γ l R -∗ lock_proto γ l R'.
  Proof.
    iIntros "#HRR' Hlck". iDestruct "Hlck" as (b) "[Hl HR]". iExists b.
    iFrame "Hl". destruct b; first done. iDestruct "HR" as "[$ HR]".
    by iApply "HRR'".
  Qed.

  (** The main proofs. *)
  Lemma lock_proto_create (R : iProp Σ) l (b : bool) :
    l ↦ #b -∗ (if b then True else ▷ R) ==∗ ∃ γ, ▷ lock_proto γ l R.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iExists _, _. iFrame "Hl". destruct b; first done. by iFrame.
  Qed.

  Lemma lock_proto_destroy γ l R :
    lock_proto γ l R -∗ ∃ (b : bool), l ↦ #b ∗ if b then True else R.
  Proof.
    iIntros "Hlck". iDestruct "Hlck" as (b) "[Hl HR]".
    iExists b. iFrame "Hl". destruct b; first done.
    iDestruct "HR" as "[_ $]".
  Qed.

  Lemma mklock_unlocked_spec (R : iProp Σ) (l : loc) v :
    {{{ l ↦ v ∗ ▷ R }}} mklock_unlocked [ #l ] {{{ γ, RET #(); ▷ lock_proto γ l R }}}.
  Proof.
    iIntros (Φ) "[Hl HR] HΦ". wp_lam. rewrite -wp_fupd. wp_write.
    iMod (lock_proto_create with "Hl HR") as (γ) "Hproto".
    iApply "HΦ". by iFrame.
  Qed.

  Lemma mklock_locked_spec (R : iProp Σ) (l : loc) v :
    {{{ l ↦ v }}} mklock_locked [ #l ] {{{ γ, RET #(); ▷ lock_proto γ l R }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_lam. rewrite -wp_fupd. wp_write.
    iMod (lock_proto_create with "Hl [//]") as (γ) "Hproto".
    iApply "HΦ". by iFrame.
  Qed.

  (* At this point, it'd be really nice to have some sugar for symmetric
     accessors. *)
  Lemma try_acquire_spec E γ l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto γ l R ∗ (▷ lock_proto γ l R ={∅,E}=∗ P)) -∗
    {{{ P }}} try_acquire [ #l ] @ E
    {{{ b, RET #b; (if b is true then locked γ ∗ ▷ R else True) ∗ P }}}.
  Proof.
    iIntros "#Hproto !# * HP HΦ".
    wp_rec. iMod ("Hproto" with "HP") as "(Hinv & Hclose)".
    iDestruct "Hinv" as ([]) "[Hl HR]".
    - wp_apply (wp_cas_int_fail with "Hl"); [done..|]. iIntros "Hl".
      iMod ("Hclose" with "[Hl]"); first (iExists true; by eauto).
      iModIntro. iApply ("HΦ" $! false). auto.
    - wp_apply (wp_cas_int_suc with "Hl"); [done..|]. iIntros "Hl".
      iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]") as "HP"; first (iExists true; by eauto).
      iModIntro. rewrite /locked. iApply ("HΦ" $! true with "[$Hγ $HR $HP]").
  Qed.

  Lemma acquire_spec E γ l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto γ l R ∗ (▷ lock_proto γ l R ={∅,E}=∗ P)) -∗
    {{{ P }}} acquire [ #l ] @ E {{{ RET #(); locked γ ∗ ▷ R ∗ P }}}.
  Proof.
    iIntros "#Hproto !# * HP HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hproto HP"). iIntros ([]).
    - iIntros "[[Hlked HR] Hown]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "[_ Hown]". wp_if. iApply ("IH" with "Hown HΦ").
  Qed.

  Lemma release_spec E γ l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto γ l R ∗ (▷ lock_proto γ l R ={∅,E}=∗ P)) -∗
    {{{ locked γ ∗ R ∗ P }}} release [ #l ] @ E {{{ RET #(); P }}}.
  Proof.
    iIntros "#Hproto !# * (Hlocked & HR & HP) HΦ". wp_let.
    iMod ("Hproto" with "HP") as "(Hinv & Hclose)".
    iDestruct "Hinv" as (b) "[? _]". wp_write. iApply "HΦ".
    iApply "Hclose". iExists false. by iFrame.
  Qed.
End proof.

Typeclasses Opaque lock_proto locked.
