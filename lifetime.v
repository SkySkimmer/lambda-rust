From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Export viewshifts pviewshifts.
From iris.program_logic Require Import invariants namespaces thread_local.
From iris.prelude Require Import strings.
From iris.proofmode Require Import invariants.

Definition lftN := nroot .@ "lft".

Definition lifetime := positive.

Axiom lifetimeG : ∀ (Σ:gFunctors), Set.
Existing Class lifetimeG.

(*** Definitions  *)

Parameter lft : ∀ `{lifetimeG Σ} (κ : lifetime), iProp Σ.
Parameter lft_own : ∀ `{lifetimeG Σ} (κ : lifetime) (q: Qp), iProp Σ.
Parameter lft_dead : ∀ `{lifetimeG Σ} (κ : lifetime), iProp Σ.
Parameter lft_incl : ∀ `{lifetimeG Σ} (κ κ' : lifetime), iProp Σ.
Parameter lft_extract :
  ∀ `{lifetimeG Σ} (κ : lifetime) (P : iProp Σ), iProp Σ.
Parameter lft_borrow : ∀ `{lifetimeG Σ} (κ : lifetime) (P : iProp Σ), iProp Σ.
Parameter lft_open_borrow :
  ∀ `{lifetimeG Σ} (κ : lifetime) (q:Qp) (P : iProp Σ), iProp Σ.
Parameter lft_frac_borrow :
  ∀ `{lifetimeG Σ} (κ : lifetime) (P : Qp → iProp Σ), iProp Σ.
Parameter lft_pers_borrow :
  ∀ `{lifetimeG Σ} (κ : lifetime) (i : gname) (P : iProp Σ), iProp Σ.
Parameter lft_pers_borrow_own :
  ∀ `{lifetimeG Σ} (i : gname) (κ : lifetime), iProp Σ.

(*** Notations  *)

Notation "[ κ ]{ q }" := (lft_own κ q)
  (format "[ κ ]{ q }"): uPred_scope.
Notation "[† κ ]" := (lft_dead κ)
  (format "[† κ ]"): uPred_scope.
Infix "⊑" := lft_incl (at level 70) : uPred_scope.
Notation "κ ∋ P" := (lft_extract κ P)
  (at level 75, right associativity) : uPred_scope.
Notation "&{ κ } P" := (lft_borrow κ P)
  (format "&{ κ } P", at level 20, right associativity) : uPred_scope.
Notation "&frac{ κ } P" := (lft_frac_borrow κ P)
  (format "&frac{ κ } P", at level 20, right associativity) : uPred_scope.

Section lft.
  Context `{irisG Λ Σ, lifetimeG Σ}.

  (*** PersitentP and TimelessP instances  *)

  Axiom lft_persistent : ∀ κ, PersistentP (lft κ).
  Global Existing Instance lft_persistent.

  Axiom lft_own_timeless : ∀ κ q, TimelessP [κ]{q}.
  Global Existing Instance lft_own_timeless.

  Axiom lft_dead_persistent : ∀ κ, PersistentP [†κ].
  Axiom lft_dead_timeless : ∀ κ, TimelessP [†κ].
  Global Existing Instances lft_dead_persistent lft_dead_timeless.

  Axiom lft_incl_persistent : ∀ κ κ', PersistentP (κ ⊑ κ').
  Global Existing Instance lft_incl_persistent.

  Axiom lft_extract_proper : ∀ κ, Proper ((⊣⊢) ==> (⊣⊢)) (lft_extract κ).
  Global Existing Instance lft_extract_proper.

  Axiom lft_borrow_proper : ∀ κ, Proper ((⊣⊢) ==> (⊣⊢)) (lft_borrow κ).
  Global Existing Instance lft_borrow_proper.

  Axiom lft_open_borrow_proper :
    ∀ κ q, Proper ((⊣⊢) ==> (⊣⊢)) (lft_open_borrow κ q).
  Global Existing Instance lft_open_borrow_proper.

  Axiom lft_frac_borrow_persistent : ∀ κ P, PersistentP (lft_frac_borrow κ P).
  Global Existing Instance lft_frac_borrow_persistent.

  Axiom lft_pers_borrow_persistent :
    ∀ κ i P, PersistentP (lft_pers_borrow κ i P).
  Global Existing Instance lft_pers_borrow_persistent.
  Axiom lft_pers_borrow_proper :
    ∀ κ i, Proper ((⊣⊢) ==> (⊣⊢)) (lft_pers_borrow κ i).
  Global Existing Instance lft_pers_borrow_proper.

  Axiom lft_pers_borrow_own_timeless :
    ∀ i κ, TimelessP (lft_pers_borrow_own i κ).
  Global Existing Instance lft_pers_borrow_own_timeless.

  (** Basic rules about lifetimes  *)
  Axiom lft_begin : ∀ `(nclose lftN ⊆ E), True ={E}=> ∃ κ, [κ]{1} ★ lft κ.
  (* TODO : Do we really need a full mask here ? *)
  Axiom lft_end : ∀ κ, lft κ ⊢ [κ]{1} ={⊤,∅}=★ ▷ |={∅,⊤}=> [†κ].
  Axiom lft_own_op : ∀ κ q1 q2, [κ]{q1} ★ [κ]{q2} ⊣⊢ [κ]{q1+q2}.

  (** Creating borrows and using them  *)
  Axiom lft_borrow_create :
    ∀ `(nclose lftN ⊆ E) κ P, lft κ ⊢ ▷ P ={E}=> &{κ} P ★ κ ∋ P.
  Axiom lft_borrow_split :
    ∀ `(nclose lftN ⊆ E) κ P Q, &{κ}(P ★ Q) ={E}=> &{κ}P ★ &{κ}Q.
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
      lft_open_borrow κ q P ★ ▷ (▷Q ={⊤ ∖ nclose lftN}=★ ▷P)
      ={E}=> lft_open_borrow κ q Q.
  Axiom lft_reborrow :
    ∀ `(nclose lftN ⊆ E) κ κ' P, κ' ⊑ κ ⊢ &{κ}P ={E}=> &{κ'}P ★ κ' ∋ &{κ}P.
  Axiom lft_borrow_unnest :
    ∀ `(nclose lftN ⊆ E) κ κ' P q',
      κ' ⊑ κ ⊢ &{κ}P ★ lft_open_borrow κ' q' (&{κ}P) ={E}=> [κ']{q'} ★ &{κ'}P.

  (** Lifetime inclusion  *)
  Axiom lft_mkincl :
    ∀ `(nclose lftN ⊆ E) κ κ' q, lft κ ⊢ &{κ'} [κ]{q} ={E}=> κ' ⊑ κ.
  Axiom lft_incl_refl : ∀ κ, True ⊢ κ ⊑ κ.
  Axiom lft_incl_trans : ∀ κ κ' κ'', κ ⊑ κ' ∧ κ' ⊑ κ'' ⊢ κ ⊑ κ''.
  Axiom lft_incl_trade : ∀ `(nclose lftN ⊆ E) κ κ' q,
      κ ⊑ κ' ⊢ [κ]{q} ={E}=> ∃ q', [κ']{q'} ★ ([κ']{q'} ={E}=★ [κ]{q}).
  Axiom lft_borrow_incl : ∀ κ κ' P, κ' ⊑ κ ⊢ &{κ}P → &{κ'}P.
  Axiom lft_incl_lft_l : ∀ κ κ', κ ⊑ κ' ⊢ lft κ.
  Axiom lft_incl_lft_r : ∀ κ κ', κ ⊑ κ' ⊢ lft κ'.

  (** Extraction  *)
  (* Axiom lft_extract_split : ∀ κ P Q, κ ∋ (P ★ Q) ={E}=> κ ∋ P ★ κ ∋ Q .*)
  Axiom lft_extract_combine :
    ∀ `(nclose lftN ⊆ E) κ P Q, κ ∋ P ★ κ ∋ Q ={E}=> κ ∋ (P ★ Q).
  Axiom lft_extract_out : ∀ `(nclose lftN ⊆ E) κ P, [†κ] ⊢ κ ∋ P ={E}=> ▷ P.
  Axiom lft_extract_lft : ∀ κ P, κ ∋ P ⊢ lft κ.

  (** Fractured borrows  *)
  (* TODO : I think an arbitrary mask is ok here. Not sure. *)
  Axiom lft_borrow_fracture : ∀ E κ φ, &{κ}(φ 1%Qp) ={E}=> &frac{κ}φ.
  Axiom lft_frac_borrow_open : ∀ `(nclose lftN ⊆ E) κ φ q,
      □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ★ φ q2) ★ &frac{κ}φ ⊢
     [κ]{q} ={E}=> ∃ q', ▷ φ q' ★ (▷ φ q' ={E}=★ [κ]{q}).
  Axiom lft_frac_borrow_incl : ∀ κ κ' φ, κ' ⊑ κ ⊢ &frac{κ}φ → &frac{κ'}φ.
  Axiom lft_frac_borrow_lft : ∀ κ φ, &frac{κ}φ ⊢ lft κ.

  (** Persistent borrows  *)
  Axiom lft_borrow_persist :
    ∀ κ P, &{κ}P ⊣⊢ ∃ κ' i, κ ⊑ κ' ★ lft_pers_borrow κ' i P ★
                                     lft_pers_borrow_own i κ'.
  Axiom lft_pers_borrow_open :
    ∀ `(nclose lftN ⊆ E) κ i P q,
      lft_pers_borrow κ i P ⊢ lft_pers_borrow_own i κ ★ [κ]{q} ={E}=> ▷ P ★
                                 (▷ P ={E}=★ lft_pers_borrow_own i κ ★ [κ]{q}).
  Axiom lft_pers_borrow_lft : ∀ κ i P, lft_pers_borrow κ i P ⊢ lft κ.

  (*** Derived lemmas  *)

  Lemma lft_own_split κ q : [κ]{q} ⊣⊢ ([κ]{q/2} ★ [κ]{q/2}).
  Proof. by rewrite lft_own_op Qp_div_2. Qed.

  Global Instance into_and_lft_own κ q :
    IntoAnd false ([κ]{q}) ([κ]{q/2}) ([κ]{q/2}).
  Proof. by rewrite /IntoAnd lft_own_split. Qed.

  Lemma lft_borrow_open' E κ P q :
    nclose lftN ⊆ E →
      &{κ}P ★ [κ]{q} ={E}=> ▷ P ★ (▷ P ={E}=★ &{κ}P ★ [κ]{q}).
  Proof.
    iIntros (?) "H". iVs (lft_borrow_open with "H") as "[HP Hopen]". done.
    iIntros "!==> {$HP} HP". iVs (lft_borrow_close with "[HP Hopen]").
      done. by iFrame "HP". done.
  Qed.

  Lemma lft_mkincl' E κ κ' q :
    nclose lftN ⊆ E →
    lft κ ★ lft κ' ⊢ [κ]{q} ={E}=> κ' ⊑ κ ★ κ' ∋ [κ]{q}.
  Proof.
    iIntros (?) "[#Hκ#Hκ']!#?".
    iVs (lft_borrow_create with "Hκ' [-]") as "[??]". done. by iFrame.
    iFrame. by iApply (lft_mkincl with "Hκ [-]").
  Qed.

  Lemma lft_borrow_close_stronger `(nclose lftN ⊆ E) κ P Q q :
    ▷ Q ★ lft_open_borrow κ q P ★ ▷ (▷Q ={⊤ ∖ nclose lftN}=★ ▷P)
      ={E}=> &{κ}Q ★ [κ]{q}.
  Proof.
    iIntros "[HP Hvsob]".
    iVs (lft_open_borrow_contravar with "Hvsob"). set_solver.
    iApply (lft_borrow_close with "[-]"). set_solver. by iSplitL "HP".
  Qed.

  Lemma lft_borrow_big_sepL_split `(nclose lftN ⊆ E) {A} κ Φ (l : list A) :
    &{κ}([★ list] k↦y ∈ l, Φ k y) ={E}=> [★ list] k↦y ∈ l, &{κ}(Φ k y).
  Proof.
    revert Φ. induction l=>Φ; iIntros. by rewrite !big_sepL_nil.
    rewrite !big_sepL_cons.
    iVs (lft_borrow_split with "[-]") as "[??]"; try done.
    iFrame. by iVs (IHl with "[-]").
  Qed.

End lft.

(*** Derived notions  *)

(** Shared borrows  *)
Definition lft_shr_borrow `{irisG Λ Σ, lifetimeG Σ} (κ : lifetime)
                           (N : namespace) (P : iProp Σ) :=
  (∃ κ' i, κ ⊑ κ' ★ lftN ⊥ N ★ lft_pers_borrow κ' i P
                  ★ inv N (lft_pers_borrow_own i κ'))%I.

Notation "&shr{ κ | N } P" := (lft_shr_borrow κ N P)
  (format "&shr{ κ | N } P", at level 20, right associativity) : uPred_scope.

Section shared_borrows.
  Context `{irisG Λ Σ, lifetimeG Σ}
          (κ : lifetime) (N : namespace) (P : iProp Σ).

  Global Instance lft_shr_borrow_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (lft_shr_borrow κ N).
  Proof. solve_proper. Qed.
  Global Instance lft_shr_borrow_persistent : PersistentP (&shr{κ | N} P) := _.

  Lemma lft_borrow_share E :
    lftN ⊥ N → &{κ}P ={E}=> &shr{κ|N}P.
  Proof.
    iIntros (?) "HP".
    iDestruct (lft_borrow_persist with "HP") as (κ' i) "(#?&#?&Hown)".
    iExists κ', i. iVs (inv_alloc N E with "[Hown]").
    by iIntros "!>"; iApply "Hown". by auto.
  Qed.

  Lemma lft_shr_borrow_open E q :
    nclose N ⊆ E → nclose lftN ⊆ E →
    &shr{κ|N}P ⊢ [κ]{q} ={E,E∖N}=> ▷P ★ (▷P ={E∖N,E}=★ [κ]{q}).
  Proof.
    iIntros (??) "#HP!#Hκ".
    iDestruct "HP" as (κ' i) "(#Hord&%&#Hpers&#Hinv)". iInv N as ">Hown" "Hclose".
    iVs (lft_incl_trade with "Hord Hκ") as (q') "(Hκ'&Hclose')". solve_ndisj.
    iVs (lft_pers_borrow_open with "Hpers [Hown Hκ']") as "[HP Hclose'']".
      solve_ndisj. by iFrame.
    iIntros "{$HP}!==>HP". iVs ("Hclose''" with "HP") as "[Hown Hκ]".
    iVs ("Hclose'" with "Hκ"). iFrame. iApply "Hclose". auto.
  Qed.

  Lemma lft_shr_borrow_incl κ' :
    κ' ⊑ κ ⊢ &shr{κ|N}P → &shr{κ'|N}P.
  Proof.
    iIntros "#Hord #HP". iDestruct "HP" as (κ0 i) "(#Hord'&%&#Hpers&#Hinv)".
    iExists κ0, i. iSplit; last by eauto. iApply lft_incl_trans; eauto.
  Qed.

  Lemma lft_shr_borrow_lft : &shr{κ|N}P ⊢ lft κ.
  Proof.
    iIntros "#HP". iDestruct "HP" as (κ' i) "[H _]". by iApply lft_incl_lft_l.
  Qed.

End shared_borrows.

Typeclasses Opaque lft_shr_borrow.

(** Thread local borrows  *)

Definition lft_tl_borrow `{irisG Λ Σ, lifetimeG Σ, thread_localG Σ}
           (κ : lifetime) (tid : thread_id) (N : namespace) (P : iProp Σ) :=
  (∃ κ' i, κ ⊑ κ' ★ lftN ⊥ N ★ lft_pers_borrow κ' i P
                  ★ tl_inv tid N (lft_pers_borrow_own i κ'))%I.

Notation "&tl{ κ | tid | N } P" := (lft_tl_borrow κ tid N P)
  (format "&tl{ κ | tid | N } P", at level 20, right associativity) : uPred_scope.

Section tl_borrows.
  Context `{irisG Λ Σ, lifetimeG Σ, thread_localG Σ}
          (κ : lifetime) (tid : thread_id) (N : namespace) (P : iProp Σ).

  Global Instance lft_tl_borrow_persistent : PersistentP (&tl{κ|tid|N} P) := _.
  Global Instance lft_tl_borrow_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (lft_tl_borrow κ tid N).
  Proof.
    intros P1 P2 EQ. apply uPred.exist_proper. intros κ'.
    apply uPred.exist_proper. intros i. by rewrite EQ.
  Qed.

  Lemma lft_borrow_share_tl E :
    lftN ⊥ N → &{κ}P ={E}=> &tl{κ|tid|N}P.
  Proof.
    iIntros (?) "HP".
    iDestruct (lft_borrow_persist with "HP") as (κ' i) "(#?&#?&Hown)".
    iExists κ', i. iVs (tl_inv_alloc tid E N with "[Hown]").
      by iIntros "!>"; iApply "Hown". by auto.
  Qed.

  Lemma lft_tl_borrow_open E F q :
    nclose lftN ⊆ E → nclose tlN ⊆ E → nclose N ⊆ F →
    &tl{κ|tid|N}P ⊢ [κ]{q} ★ tl_own tid F ={E}=> ▷P ★ tl_own tid (F ∖ N) ★
                     (▷P ★ tl_own tid (F ∖ N) ={E}=★ [κ]{q} ★ tl_own tid F).
  Proof.
    iIntros (???) "#HP!#[Hκ Htlown]".
    iDestruct "HP" as (κ' i) "(#Hord&%&#Hpers&#Hinv)".
    iVs (tl_inv_open with "Hinv Htlown") as "(>Hown&Htlown&Hclose)"; try done.
    iVs (lft_incl_trade with "Hord Hκ") as (q') "(Hκ'&Hclose')". done.
    iVs (lft_pers_borrow_open with "Hpers [Hown Hκ']") as "[HP Hclose'']".
      done. by iFrame.
    iIntros "{$HP $Htlown}!==>[HP Htlown]".
    iVs ("Hclose''" with "HP") as "[Hown Hκ]". iVs ("Hclose'" with "Hκ").
    iFrame. iApply "Hclose". by iFrame.
  Qed.

  Lemma lft_tl_borrow_incl κ' :
    κ' ⊑ κ ⊢ &tl{κ|tid|N}P → &tl{κ'|tid|N}P.
  Proof.
    iIntros "#Hord #HP". iDestruct "HP" as (κ0 i) "(#Hord'&%&#Hpers&#Hinv)".
    iExists κ0, i. iSplit; last by eauto. iApply lft_incl_trans; eauto.
  Qed.

  Lemma lft_tl_borrow_lft : &tl{κ|tid|N}P ⊢ lft κ.
  Proof.
    iIntros "#HP". iDestruct "HP" as (κ' i) "[H _]". by iApply lft_incl_lft_l.
  Qed.

End tl_borrows.

Typeclasses Opaque lft_tl_borrow.
