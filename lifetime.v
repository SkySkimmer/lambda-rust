From iris.program_logic Require Export viewshifts pviewshifts.
From iris.program_logic Require Import invariants namespaces.
From iris.prelude Require Import strings.
From iris.proofmode Require Import invariants.

Definition lftN := nroot .@ "lft".

Definition lifetime := positive.

Axiom lifetimeG : ∀ (Λ:language) (Σ:gFunctors), Set.
Existing Class lifetimeG.
Axiom lifetimeG_iris_inG : ∀ Λ Σ, lifetimeG Λ Σ → irisG Λ Σ.
Existing Instance lifetimeG_iris_inG.

(*** Definitions  *)

Parameter lft : ∀ `{lifetimeG Λ Σ} (κ : lifetime), iProp Σ.
Parameter lft_own : ∀ `{lifetimeG Λ Σ} (κ : lifetime) (q: Qp), iProp Σ.
Parameter lft_dead : ∀ `{lifetimeG Λ Σ} (κ : lifetime), iProp Σ.
Parameter lft_incl : ∀ `{lifetimeG Λ Σ} (κ κ' : lifetime), iProp Σ.
Parameter lft_extract :
  ∀ `{lifetimeG Λ Σ} (κ : lifetime) (P : iProp Σ), iProp Σ.
Parameter lft_borrow : ∀ `{lifetimeG Λ Σ} (κ : lifetime) (P : iProp Σ), iProp Σ.
Parameter lft_open_borrow :
  ∀ `{lifetimeG Λ Σ} (κ : lifetime) (q:Qp) (P : iProp Σ), iProp Σ.
Parameter lft_frac_borrow :
  ∀ `{lifetimeG Λ Σ} (κ : lifetime) (P : Qp → iProp Σ), iProp Σ.
Parameter lft_pers_borrow :
  ∀ `{lifetimeG Λ Σ} (κ : lifetime) (i : gname) (P : iProp Σ), iProp Σ.
Parameter lft_pers_borrow_own :
  ∀ `{lifetimeG Λ Σ} (i : gname) (κ : lifetime), iProp Σ.

(*** Notations  *)

Notation "[ κ ]{ q }" := (lft_own κ q) : uPred_scope.
Notation "[† κ ]" := (lft_dead κ) : uPred_scope.
Infix "⊑" := lft_incl (at level 70) : uPred_scope.
Notation "κ ∋ P" := (lft_extract κ P)
  (at level 75, right associativity) : uPred_scope.
Notation "&{ κ } P" := (lft_borrow κ P)
  (at level 20, right associativity) : uPred_scope.
Notation "&frac{ κ } P" := (lft_frac_borrow κ P)
  (at level 20, right associativity) : uPred_scope.

Section instances.
  Context `{lifetimeG Λ Σ}.

  (*** PersitentP and TimelessP instances. *)

  Axiom lft_persistent : ∀ κ, PersistentP (lft κ).
  Global Existing Instance lft_persistent.

  Axiom lft_own_timeless : ∀ κ q, TimelessP [κ]{q}.
  Global Existing Instance lft_own_timeless.

  Axiom lft_dead_persistent : ∀ κ, PersistentP [†κ].
  Axiom lft_dead_timeless : ∀ κ, TimelessP [†κ].
  Global Existing Instances lft_dead_persistent lft_dead_timeless.

  Axiom lft_incl_persistent : ∀ κ κ', PersistentP (κ ⊑ κ').
  Global Existing Instance lft_incl_persistent.

  Axiom lft_frac_borrow_persistent : ∀ κ P, PersistentP (lft_frac_borrow κ P).
  Global Existing Instance lft_frac_borrow_persistent.

  Axiom lft_pers_borrow_persistent :
    ∀ κ i P, PersistentP (lft_pers_borrow κ i P).
  Global Existing Instance lft_pers_borrow_persistent.

  Axiom lft_pers_borrow_own_timeless :
    ∀ i κ, TimelessP (lft_pers_borrow_own i κ).
  Global Existing Instance lft_pers_borrow_own_timeless.
End instances.

Section lft.

  Context `{lifetimeG Λ Σ}.

  (** Basic rules about lifetimes. *)
  Axiom lft_begin :  ∀ `(nclose lftN ⊆ E), True ={E}=> ∃ κ, [κ]{1} ★ lft κ.
  (* TODO : Do we really need a full mask here ? *)
  Axiom lft_end : ∀ κ, lft κ ⊢ [κ]{1} ={⊤,∅}=★ ▷ |={∅,⊤}=> [†κ].
  Axiom lft_own_op : ∀ κ q1 q2, [κ]{q1} ★ [κ]{q2} ⊣⊢ [κ]{q1+q2}.

  (** Creating borrows and using them. *)
  Axiom lft_borrow_create :
    ∀ `(nclose lftN ⊆ E) κ P, lft κ ⊢ ▷ P ={E}=> &{κ}P ★ κ ∋ P.
  Axiom lft_borrow_split :
    ∀ `(nclose lftN ⊆ E) κ P Q, &{κ} (P ★ Q) ={E}=> &{κ}P ★ &{κ}Q.
  Axiom lft_borrow_combine :
    ∀ `(nclose lftN ⊆ E) κ P Q, &{κ}P ★ &{κ}Q ={E}=> &{κ}(P ★ Q).
  Axiom lft_borrow_open :
    ∀ `(nclose lftN ⊆ E) κ P q,
      &{κ}P ★ [κ]{q} ={E}=> ▷ P ★ lft_open_borrow κ q P.
  Axiom lft_borrow_close :
    ∀ `(nclose lftN ⊆ E) κ P q,
      ▷ P ★ lft_open_borrow κ q P ={E}=> &{κ}P ★ [κ]{q}.
  Axiom lft_open_borrow_contravar :
    ∀ `(nclose lftN ⊆ E) κ P Q q,
      ▷ (▷Q ={⊤ ∖ nclose lftN}=★ ▷P) ★ lft_open_borrow κ q P
      ={E}=> lft_open_borrow κ q Q.
  Axiom lft_reborrow :
    ∀ `(nclose lftN ⊆ E) κ κ' P, κ' ⊑ κ ⊢ &{κ}P ={E}=> &{κ'}P ★ κ' ∋ &{κ}P.
  Axiom lft_borrow_unnest :
    ∀ `(nclose lftN ⊆ E) κ κ' P q',
      κ' ⊑ κ ⊢ &{κ}P ★ lft_open_borrow κ' q' (&{κ}P) ={E}=> [κ']{q'} ★ &{κ'}P.

  (** Lifetime inclusion. *)
  Axiom lft_mkincl :
    ∀ `(nclose lftN ⊆ E) κ κ' q, lft κ ⊢ &{κ'} [κ]{q} ={E}=> κ' ⊑ κ.
  Axiom lft_incl_refl : ∀ κ, True ⊢ κ ⊑ κ.
  Axiom lft_incl_trans : ∀ κ κ' κ'', κ ⊑ κ' ∧ κ' ⊑ κ'' ⊢ κ ⊑ κ''.
  Axiom lft_incl_trade : ∀ `(nclose lftN ⊆ E)κ κ' q, κ ⊑ κ' ⊢
      [κ]{q} ={E}=> ∃ q', [κ']{q'} ★ ([κ']{q'} ={E}=★ [κ]{q}).
  Axiom lft_borrow_incl : ∀ κ κ' P, κ' ⊑ κ ⊢ &{κ}P → &{κ'}P.

  (** Extraction. *)
  (* Axiom lft_extract_split : ∀ κ P Q, κ ∋ (P ★ Q) ={E}=> κ ∋ P ★ κ ∋ Q .*)
  Axiom lft_extract_combine :
    ∀ `(nclose lftN ⊆ E) κ P Q, κ ∋ P ★ κ ∋ Q ={E}=> κ ∋ (P ★ Q).
  Axiom lft_extract_out : ∀ `(nclose lftN ⊆ E) κ P, [†κ] ⊢ κ ∋ P ={E}=> ▷ P.


  (** Fractured borrows. *)
  (* TODO : I think an arbitrary mask is ok here. Not sure. *)
  Axiom lft_borrow_fracture : ∀ E κ φ, &{κ}(φ 1%Qp) ={E}=> &frac{κ}φ.
  Axiom lft_frac_borrow_open : ∀ `(nclose lftN ⊆ E) κ φ q,
      □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ★ φ q2) ★ &frac{κ}φ ⊢
     [κ]{q} ={E}=> ∃ q', ▷ φ q' ★ (▷ φ q' ={E}=★ [κ]{q}).
  Axiom lft_frac_borrow_incl : ∀ κ κ' φ, κ' ⊑ κ ⊢ &frac{κ}φ → &frac{κ'}φ.

  (** Persistent borrows.  *)
  (* TODO : Build all the other borrows from them. *)
  Axiom lft_borrow_persist :
    ∀ κ P, &{κ}P ⊣⊢ ∃ κ' i, κ ⊑ κ' ★ lft_pers_borrow κ' i P ★
                                     lft_pers_borrow_own i κ'.
  Axiom lft_pers_borrow_open :
    ∀ `(nclose lftN ⊆ E) κ i P q,
      lft_pers_borrow κ i P ⊢ lft_pers_borrow_own i κ ★ [κ]{q} ={E}=> ▷ P ★
                                 (▷ P ={E}=★ lft_pers_borrow_own i κ ★ [κ]{q}).

End lft.

(*** Derived notions. *)

(** Shared borrows. *)
Definition lft_shr_borrow `{lifetimeG Λ Σ} (κ : lifetime)
                          (N : namespace) (P : iProp Σ) :=
  (∃ κ' i, κ ⊑ κ' ★ lftN ⊥ N ★ lft_pers_borrow κ' i P
                  ★ inv N (lft_pers_borrow_own i κ'))%I.
Instance lft_shr_borrow_persistent `{lifetimeG Λ Σ} κ N P :
  PersistentP (lft_shr_borrow κ N P) := _.

Notation "&shr{ κ | N } P" := (lft_shr_borrow κ N P)
  (at level 20, right associativity) : uPred_scope.

Lemma lft_borrow_share `{lifetimeG Λ Σ} E κ P N :
  lftN ⊥ N → &{κ}P ={E}=> &shr{κ|N}P.
Proof.
  iIntros (?) "HP".
  iDestruct (lft_borrow_persist with "HP") as (κ' i) "(#?&#?&Hown)".
  iExists κ', i. iVs (inv_alloc N E with "[Hown]").
  by iIntros "!>"; iApply "Hown". by auto.
Qed.

Lemma lft_shr_borrow_open `{lifetimeG Λ Σ} E κ P q N :
  nclose N ⊆ E → nclose lftN ⊆ E →
  &shr{κ|N}P ⊢ [κ]{q} ={E,E∖N}=> ▷P ★ (▷P ={E∖N,E}=★ [κ]{q}).
Proof.
  iIntros (??) "#HP!#Hκ".
  iDestruct "HP" as (κ' i) "(#Hord&%&#Hpers&#Hinv)". iInv N as ">Hown" "Hclose".
  iVs (lft_incl_trade with "Hord Hκ") as (q') "(Hκ'&Hclose')".
    by auto using ndisj_subseteq_difference.
  iVs (lft_pers_borrow_open with "Hpers [Hown Hκ']") as "[? Hclose'']".
    by auto using ndisj_subseteq_difference. by iFrame.
  iFrame. iIntros "!==>HP". iVs ("Hclose''" with "HP") as "[Hown Hκ]".
  iVs ("Hclose'" with "Hκ"). iFrame. iApply "Hclose". auto.
Qed.

Lemma lft_shr_borrow_incl `{lifetimeG Λ Σ} κ κ' P N :
  κ' ⊑ κ ⊢ &shr{κ|N}P → &shr{κ'|N}P.
Proof.
  iIntros "#Hord #HP". iDestruct "HP" as (κ0 i) "(#Hord'&%&#Hpers&#Hinv)".
  iExists κ0, i. iSplit; last by eauto. iApply lft_incl_trans; eauto.
Qed.

Typeclasses Opaque lft_shr_borrow.
