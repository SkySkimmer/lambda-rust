From iris.program_logic Require Import weakestpre.
From iris.base_logic.lib Require Import cancelable_invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From lrust.lang Require Import lang proofmode notation.
Set Default Proof Using "Type".

Definition newlock : val := λ: [], let: "l" := Alloc #1 in "l" <- #false ;; "l".
Definition try_acquire : val := λ: ["l"], CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" ["l"] := if: try_acquire ["l"] then #() else "acquire" ["l"].
Definition release : val := λ: ["l"], "l" <-ˢᶜ #false.

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC); lock_cinvG :> cinvG Σ }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC); cinvΣ].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!lrustG Σ, !lockG Σ} (N : namespace).

  Definition lockname := (gname * gname)%type.

  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : lockname) (l : loc) (R : iProp Σ) : iProp Σ :=
    cinv N (γ.1) (lock_inv (γ.2) l R).

  Definition own_lock (γ : lockname) : frac → iProp Σ :=
    cinv_own (γ.1).

  Definition locked (γ : lockname): iProp Σ := own (γ.2) (Excl ()).

  Global Instance lock_inv_ne γ l : NonExpansive (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_contractive γ l : Contractive (is_lock γ l).
  Proof. solve_contractive. Qed.
  Global Instance is_lock_ne γ l : NonExpansive (is_lock γ l).
  Proof. exact: contractive_ne. Qed.

  Global Instance is_lock_persistent γ l R : PersistentP (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ : lockname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Lemma is_lock_iff γ l R R' :
    □ ▷ (R ↔ R') -∗ is_lock γ l R -∗ is_lock γ l R'.
  Proof.
    iIntros "#HRR' Hlck". iApply cinv_iff; last done. iNext. iAlways.
    iSplit; iIntros "Hinv"; iDestruct "Hinv" as (b) "[Hl HR]"; iExists b;
      iFrame "Hl"; (destruct b; first done); iDestruct "HR" as "[$ HR]";
      by iApply "HRR'".
  Qed.

  (** The main proofs. *)
  Lemma newlock_inplace (E : coPset) (R : iProp Σ) l (b : bool) :
    l ↦ #b -∗ (if b then True else ▷ R) ={E}=∗ ∃ γ, is_lock γ l R ∗ own_lock γ 1%Qp.
  Proof.
    iIntros "Hl HR".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (cinv_alloc _ N (lock_inv γ l R) with "[-]") as (γ') "Hlock".
    { iExists b. destruct b; by iFrame. }
    iModIntro. iExists (_, _). eauto.
  Qed.

  Lemma newlock_spec (R : iProp Σ) :
    {{{ ▷ R }}} newlock [] {{{ l γ, RET #l; is_lock γ l R ∗ own_lock γ 1%Qp }}}.
  Proof.
    iIntros (Φ) "HR HΦ". iApply wp_fupd.
    wp_seq. wp_alloc l vl as "Hl" "H†". inv_vec vl=>x.
    rewrite heap_mapsto_vec_singleton. (* FIXME shouldn't this also compute now, like bigops do? *)
    wp_let. wp_write. iMod (newlock_inplace with "Hl HR") as (γ) "?".
    by iApply "HΦ".
  Qed.

  Lemma destroy_lock E γ l R :
    ↑N ⊆ E → 
    is_lock γ l R -∗ own_lock γ 1%Qp ={E}=∗ ∃ (b : bool), l ↦ #b ∗ if b then True else ▷ R.
  Proof.
    iIntros (?) "#Hinv Hown".
    iMod (cinv_cancel with "Hinv Hown") as (b) "[>Hl HR]"; first done.
    iExists b. destruct b; first by eauto.
    iDestruct "HR" as "[_ $]". done.
  Qed.

  Lemma try_acquire_spec γ l R q :
    {{{ is_lock γ l R ∗ own_lock γ q }}} try_acquire [ #l ]
    {{{ b, RET #b; (if b is true then locked γ ∗ R else True) ∗ own_lock γ q }}}.
  Proof.
    iIntros (Φ) "[Hinv Hown] HΦ".
    wp_rec. iMod (cinv_open with "Hinv Hown") as "(Hinv & Hown & Hclose)"; first done.
    iDestruct "Hinv" as ([]) "[Hl HR]".
    - wp_apply (wp_cas_int_fail with "Hl"); [done..|]. iIntros "Hl".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iApply ("HΦ" $! false). auto.
    - wp_apply (wp_cas_int_suc with "Hl"); [done..|]. iIntros "Hl".
      iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. rewrite /locked. iApply ("HΦ" $! true with "[$Hγ $HR $Hown]").
  Qed.

  Lemma acquire_spec γ l R q :
    {{{ is_lock γ l R ∗ own_lock γ q }}} acquire [ #l ]
    {{{ RET #(); locked γ ∗ R ∗ own_lock γ q }}}.
  Proof.
    iIntros (Φ) "[#Hinv Hown] HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "[$Hinv $Hown]"). iIntros ([]).
    - iIntros "[[Hlked HR] Hown]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "[_ Hown]". wp_if. iApply ("IH" with "Hown [HΦ]"). auto.
  Qed.

  Lemma release_spec γ l R q :
    {{{ is_lock γ l R ∗ locked γ ∗ R ∗ own_lock γ q }}} release [ #l ]
    {{{ RET #(); own_lock γ q }}}.
  Proof.
    iIntros (Φ) "(Hinv & Hlocked & HR & Hown) HΦ".
    rewrite /release /=. wp_let.
    iMod (cinv_open with "Hinv Hown") as "(Hinv & Hown & Hclose)"; first done.
    iDestruct "Hinv" as (b) "[? _]". wp_write. iApply "HΦ". iFrame "Hown".
    iApply "Hclose". iNext. iExists false. by iFrame.
  Qed.
End proof.

Typeclasses Opaque is_lock locked.
