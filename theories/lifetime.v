From iris.algebra Require Import csum auth frac.
From iris.base_logic.lib Require Export fancy_updates invariants namespaces.
From iris.base_logic.lib Require Import thread_local.
From iris.proofmode Require Import tactics.
From Coq Require Import Qcanon.

Definition lftN := nroot .@ "lft".

Definition atomic_lft := positive.

Definition lft_tokUR : ucmraT :=
  authUR (gmapUR atomic_lft (csumR fracR unitR)).

(* FIXME : this is not the actual definitions. *)
Definition borrow_idx := positive.
Definition borrow_tokUR : ucmraT :=
  authUR (gmapUR borrow_idx fracR).

Class lifetimeG Σ := LifetimeG {
  lft_tok_inG :> inG Σ lft_tokUR;
  borrow_tok_inG :> inG Σ borrow_tokUR;
  frac_inG :> inG Σ fracR;
  lft_toks_name : gname;
  borrow_tok_name : gname
}.

Section defs.

  (*** Definitions  *)

  Context `{lifetimeG Σ}.

  Definition lifetime := gmap atomic_lft nat.

  Definition static : lifetime := ∅.

  Definition Qp_nat_mul  (q : Qp) (n : nat) : option Qp :=
    match n with
    | O => None
    | S n' => Some (Nat.iter n' (λ acc, q ⋅ acc)%Qp q)
    end.

  Definition lft_own (q : Qp) (κ : lifetime) : iProp Σ :=
    own lft_toks_name (◯ (Cinl <$> omap (Qp_nat_mul q) κ)).

  Definition lft_dead (κ : lifetime) : iProp Σ :=
    (∃ Λ, ■ (∃ n, κ !! Λ = Some (S n)) ∗
            own lft_toks_name (◯ {[ Λ := Cinr () ]}))%I.

  Definition idx_borrow_own (q : Qp) (i : borrow_idx) :=
    own borrow_tok_name (◯ {[ i := q ]}).

End defs.

Typeclasses Opaque lft_own lft_dead .

Parameter idx_borrow:
  ∀ `{lifetimeG Σ} (κ : lifetime) (i : borrow_idx) (P : iProp Σ), iProp Σ.

Definition borrow `{lifetimeG Σ} (κ : lifetime) (P : iProp Σ) : iProp Σ :=
  (∃ i, idx_borrow κ i P ∗ idx_borrow_own 1 i)%I.

(*** Notations  *)

Notation "q .[ κ ]" := (lft_own q κ)
    (format "q .[ κ ]", at level 0): uPred_scope.
Notation "[† κ ]" := (lft_dead κ) (format "[† κ ]"): uPred_scope.
Notation "&{ κ } P" := (borrow κ P)
  (format "&{ κ } P", at level 20, right associativity) : uPred_scope.
Hint Unfold lifetime : typeclass_instances.

Section lft.
  Context `{invG Σ, lifetimeG Σ}.

  (*** PersitentP, TimelessP and Proper instances  *)

  Global Instance lft_own_timeless q κ : TimelessP q.[κ].
  Proof. unfold lft_own. apply _. Qed.

  Global Instance lft_dead_persistent κ : PersistentP [†κ].
  Proof. unfold lft_dead. apply _. Qed.
  Global Instance lft_dead_timeless κ : PersistentP [†κ].
  Proof. unfold lft_dead. apply _. Qed.

  Axiom idx_borrow_persistent :
    ∀ κ i P, PersistentP (idx_borrow κ i P).
  Global Existing Instance idx_borrow_persistent.
  Axiom idx_borrow_proper :
    ∀ κ i, Proper ((⊣⊢) ==> (⊣⊢)) (idx_borrow κ i).
  Global Existing Instance idx_borrow_proper.

  Axiom idx_borrow_own_timeless :
    ∀ q i, TimelessP (idx_borrow_own q i).
  Global Existing Instance idx_borrow_own_timeless.

  Global Instance borrow_proper κ: Proper ((⊣⊢) ==> (⊣⊢)) (borrow κ).
  Proof. solve_proper. Qed.

  (** Basic rules about lifetimes  *)
  Lemma lft_own_op q κ1 κ2 : q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ⋅ κ2].
  Proof.
    rewrite /lft_own -own_op. f_equiv. constructor. done. move=>Λ /=.
    rewrite lookup_op !lookup_fmap !lookup_omap lookup_op.
    case: (κ1 !! Λ)=>[[|a1]|]; case: (κ2 !! Λ)=>[[|a2]|]/=; rewrite ?right_id ?left_id //.
    apply reflexive_eq. apply (f_equal (Some ∘ Cinl)).
    induction a1. done. rewrite /= -assoc. by f_equal.
  Qed.

  Lemma lft_dead_or κ1 κ2 : [†κ1] ∨ [†κ2] ⊣⊢ [† κ1⋅κ2].
  Proof.
    unfold lft_dead. setoid_rewrite lookup_op. iSplit.
    - iIntros "[H|H]"; iDestruct "H" as (Λ) "[H?]";
        iDestruct "H" as %[n Hn]; iExists _; iFrame; iPureIntro; rewrite Hn.
      + case: (κ2 !! Λ); eauto.
      + case: (κ1 !! Λ)=>[n'|]; eauto. exists (n' + n)%nat. by apply (f_equal Some).
    - iIntros "H". iDestruct "H" as (Λ) "[H Hown]"; eauto. iDestruct "H" as %[n Hn].
      case K1: (κ1 !! Λ) Hn=>[[|a1]|]; case K2: (κ2 !! Λ)=>[[|a2]|]; intros [=<-];
      (iRight + iLeft); iExists Λ; iIntros "{$Hown}!%"; by eauto.
  Qed.

  Lemma lft_own_frac_op κ q q':
       (q + q').[κ] ⊣⊢ q.[κ] ∗ q'.[κ].
  Proof.
    rewrite /lft_own -own_op -auth_frag_op. f_equiv. constructor. done. simpl.
    intros Λ. rewrite lookup_op !lookup_fmap !lookup_omap. apply reflexive_eq.
    case: (κ !! Λ)=>[[|a]|]//=. rewrite -Some_op Cinl_op. repeat f_equal.
    induction a as [|a IH]. done.
    rewrite /= IH /op /cmra_op /= /frac_op !assoc. f_equal.
    rewrite -!assoc. f_equal. apply (comm _).
  Qed.

  Axiom lft_create :
    ∀ `(nclose lftN ⊆ E), True ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={⊤,∅}▷=∗ [†κ]).

  Axiom idx_borrow_acc :
    ∀ `(nclose lftN ⊆ E) q κ i P,
      idx_borrow κ i P ⊢ idx_borrow_own 1 i ∗ q.[κ] ={E}=∗ ▷ P ∗
                                 (▷ P ={E}=∗ idx_borrow_own 1 i ∗ q.[κ]).
  Axiom idx_borrow_atomic_acc :
    ∀ `(nclose lftN ⊆ E) q κ i P,
      idx_borrow κ i P ⊢ idx_borrow_own q i
         ={E,E∖lftN}=∗
            ▷ P ∗ (▷ P ={E∖lftN,E}=∗ idx_borrow_own q i) ∨
            [†κ] ∗ (|={E∖lftN,E}=> idx_borrow_own q i).

  (** Basic borrows  *)
  Axiom borrow_create :
    ∀ `(nclose lftN ⊆ E) κ P, ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
  Axiom borrow_split :
    ∀ `(nclose lftN ⊆ E) κ P Q, &{κ}(P ∗ Q) ={E}=∗ &{κ}P ∗ &{κ}Q.
  Axiom borrow_combine :
    ∀ `(nclose lftN ⊆ E) κ P Q, &{κ}P ∗ &{κ}Q ={E}=∗ &{κ}(P ∗ Q).
  Axiom borrow_acc_strong :
    ∀ `(nclose lftN ⊆ E) q κ P,
      &{κ}P ⊢ q.[κ] ={E}=∗ ▷ P ∗
      ∀ Q, ▷ Q ∗ ▷([†κ] ∗ ▷Q ={⊤ ∖ nclose lftN}=∗ ▷ P) ={E}=∗ &{κ}Q ∗ q.[κ].
  Axiom borrow_acc_atomic_strong :
    ∀ `(nclose lftN ⊆ E) κ P,
      &{κ}P ={E,E∖lftN}=∗
        (▷ P ∗ ∀ Q, ▷ Q ∗ ▷([†κ] ∗ ▷Q ={⊤ ∖ nclose lftN}=∗ ▷ P) ={E∖lftN,E}=∗ &{κ}Q) ∨
        [†κ] ∗ ∀ Q, |={E∖lftN,E}=> &{κ}Q.
  Axiom borrow_reborrow' :
    ∀ `(nclose lftN ⊆ E) κ κ' P, κ ≼ κ' →
      &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗ &{κ}P).
  Axiom borrow_unnest :
    ∀ `(nclose lftN ⊆ E) κ κ' P, &{κ'}&{κ}P ⊢ |={E}▷=> &{κ ⋅ κ'}P.

  (*** Derived lemmas  *)

  Lemma lft_own_dead q κ : q.[κ] ∗ [† κ] ⊢ False.
  Proof.
    rewrite /lft_own /lft_dead.
    iIntros "[Hl Hr]". iDestruct "Hr" as (Λ) "[HΛ Hr]".
    iDestruct "HΛ" as %[n HΛ].
    iDestruct (own_valid_2 with "[$Hl $Hr]") as %Hval. iPureIntro.
    generalize (Hval Λ).
    by rewrite lookup_op lookup_singleton lookup_fmap lookup_omap HΛ.
  Qed.

  Lemma lft_own_static q : True ==∗ q.[static].
  Proof.
    rewrite /lft_own /static omap_empty fmap_empty.
    apply (own_empty (A:=lft_tokUR) lft_toks_name).
  Qed.

  Lemma lft_not_dead_static : [† static] ⊢ False.
  Proof.
    rewrite /lft_dead /static. setoid_rewrite lookup_empty.
    iIntros "HΛ". iDestruct "HΛ" as (Λ) "[% _]". naive_solver.
  Qed.

  Lemma lft_own_split κ q : q.[κ] ⊣⊢ (q/2).[κ] ∗ (q/2).[κ].
  Proof. by rewrite -lft_own_frac_op Qp_div_2. Qed.

  Global Instance into_and_lft_own_half κ q :
    IntoAnd false q.[κ] (q/2).[κ] (q/2).[κ] | 100.
  Proof. by rewrite /IntoAnd lft_own_split. Qed.

  Global Instance from_sep_lft_own_half κ q :
    FromSep q.[κ] (q/2).[κ] (q/2).[κ] | 100.
  Proof. by rewrite /FromSep -lft_own_split. Qed.

  Global Instance frame_lft_own_half κ q :
    Frame (q/2).[κ] q.[κ] (q/2).[κ] | 100.
  Proof. by rewrite /Frame -lft_own_split. Qed.

  Global Instance into_and_lft_own_frac κ q1 q2 :
    IntoAnd false (q1+q2).[κ] q1.[κ] q2.[κ].
  Proof. by rewrite /IntoAnd lft_own_frac_op. Qed.

  Global Instance from_sep_lft_own_frac κ q1 q2 :
    FromSep (q1+q2).[κ] q1.[κ] q2.[κ].
  Proof. by rewrite /FromSep -lft_own_frac_op. Qed.

  Global Instance into_and_lft_own κ1 κ2 q :
    IntoAnd false q.[κ1⋅κ2] q.[κ1] q.[κ2].
  Proof. by rewrite /IntoAnd lft_own_op. Qed.

  Global Instance from_sep_lft_own κ1 κ2 q :
    FromSep q.[κ1⋅κ2] q.[κ1] q.[κ2].
  Proof. by rewrite /FromSep lft_own_op. Qed.

  Lemma borrow_acc E q κ P : nclose lftN ⊆ E →
      &{κ}P ⊢ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
  Proof.
    iIntros (?) "HP Htok".
    iMod (borrow_acc_strong with "HP Htok") as "[HP Hclose]". done.
    iIntros "!> {$HP} HP". iApply "Hclose". by iIntros "{$HP}!>[_$]".
  Qed.

  Lemma borrow_exists {A} `(nclose lftN ⊆ E) κ (Φ : A → iProp Σ) {_:Inhabited A}:
    &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
  Proof.
    iIntros "Hb". iMod (borrow_acc_atomic_strong with "Hb") as "[[HΦ Hclose]|[H† Hclose]]". done.
    - iDestruct "HΦ" as (x) "HΦ". iExists x. iApply "Hclose". iIntros "{$HΦ}!>[_?]". eauto.
    - iExists inhabitant. iApply "Hclose".
  Qed.

  Lemma borrow_or `(nclose lftN ⊆ E) κ P Q:
    &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
  Proof.
    iIntros "H". rewrite uPred.or_alt.
    iMod (borrow_exists with "H") as ([]) "H"; auto.
  Qed.

  Lemma borrow_persistent `(nclose lftN ⊆ E) `{PersistentP _ P} κ q:
    &{κ}P ⊢ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
  Proof.
    iIntros "Hb Htok".
    iMod (borrow_acc with "Hb Htok") as "[#HP Hob]". done.
    by iMod ("Hob" with "HP") as "[_$]".
  Qed.

End lft.

Typeclasses Opaque borrow.

(*** Inclusion and shortening. *)

Definition lft_incl `{invG Σ, lifetimeG Σ} κ κ' : iProp Σ :=
  (□((∀ q, q.[κ] ={lftN}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={lftN}=∗ q.[κ])) ∗
     ([†κ'] ={lftN}=∗ [†κ])))%I.

Infix "⊑" := lft_incl (at level 60) : C_scope.

Section incl.
  Context `{invG Σ, lifetimeG Σ}.

  Global Instance lft_incl_persistent κ κ': PersistentP (κ ⊑ κ') := _.

  Lemma lft_incl_acc `(nclose lftN ⊆ E) κ κ' q:
    κ ⊑ κ' ⊢ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
  Proof.
    iIntros "#[H _] Hq". iApply fupd_mask_mono. eassumption.
    iMod ("H" with "*Hq") as (q') "[Hq' Hclose]". iExists q'.
    iIntros "{$Hq'}!>Hq". iApply fupd_mask_mono. eassumption. by iApply "Hclose".
  Qed.

  Lemma lft_incl_dead `(nclose lftN ⊆ E) κ κ': κ ⊑ κ' ⊢ [†κ'] ={E}=∗ [†κ].
  Proof.
    iIntros "#[_ H] Hq". iApply fupd_mask_mono. eassumption. by iApply "H".
  Qed.

  Lemma lft_le_incl κ κ': κ' ≼ κ → True ⊢ κ ⊑ κ'.
  Proof.
    iIntros ([κ0 ->%leibniz_equiv]) "!#". iSplitR.
    - iIntros (q) "[Hκ' Hκ0]". iExists q. iIntros "!>{$Hκ'}Hκ'!>". by iSplitR "Hκ0".
    - iIntros "?!>". iApply lft_dead_or. auto.
  Qed.

  Lemma lft_incl_refl κ : True ⊢ κ ⊑ κ.
  Proof. by apply lft_le_incl. Qed.

  Lemma lft_incl_trans κ κ' κ'': κ ⊑ κ' ∗ κ' ⊑ κ'' ⊢ κ ⊑ κ''.
  Proof.
    unfold lft_incl. iIntros "[#[H1 H1†] #[H2 H2†]]!#". iSplitR.
    - iIntros (q) "Hκ".
      iMod ("H1" with "*Hκ") as (q') "[Hκ' Hclose]".
      iMod ("H2" with "*Hκ'") as (q'') "[Hκ'' Hclose']".
      iExists q''. iIntros "{$Hκ''}!>Hκ''". iMod ("Hclose'" with "Hκ''") as "Hκ'".
        by iApply "Hclose".
    - iIntros "H†". iMod ("H2†" with "H†"). by iApply "H1†".
  Qed.

  Axiom idx_borrow_shorten :
    ∀ κ κ' i P, κ ⊑ κ' ⊢ idx_borrow κ' i P -∗ idx_borrow κ i P.

  Lemma borrow_shorten κ κ' P: κ ⊑ κ' ⊢ &{κ'}P -∗ &{κ}P.
  Proof.
    iIntros "H⊑ H". unfold borrow. iDestruct "H" as (i) "[??]".
    iExists i. iFrame. by iApply (idx_borrow_shorten with "H⊑").
  Qed.

  Lemma lft_incl_lb κ κ' κ'' : κ ⊑ κ' ∗ κ ⊑ κ'' ⊢ κ ⊑ κ' ⋅ κ''.
  Proof.
    iIntros "[#[H1 H1†] #[H2 H2†]]!#". iSplitR.
    - iIntros (q) "[Hκ'1 Hκ'2]".
      iMod ("H1" with "*Hκ'1") as (q') "[Hκ' Hclose']".
      iMod ("H2" with "*Hκ'2") as (q'') "[Hκ'' Hclose'']".
      destruct (Qp_lower_bound q' q'') as (qq & q'0 & q''0 & -> & ->).
      iExists qq. rewrite -lft_own_op !lft_own_frac_op.
      iDestruct "Hκ'" as "[$ Hκ']". iDestruct "Hκ''" as "[$ Hκ'']".
      iIntros "!>[Hκ'0 Hκ''0]".
      iMod ("Hclose'" with "[$Hκ' $Hκ'0]") as "$".
      by iMod ("Hclose''" with "[$Hκ'' $Hκ''0]") as "$".
    - rewrite -lft_dead_or. iIntros "[H†|H†]". by iApply "H1†". by iApply "H2†".
  Qed.

  Lemma lft_incl_static κ : True ⊢ κ ⊑ static.
  Proof.
    iIntros "!#". iSplitR.
    - iIntros (q) "?". iExists 1%Qp. iSplitR. by iApply lft_own_static. auto.
    - iIntros "?". by iDestruct (lft_not_dead_static with "[-]") as "[]".
  Qed.

  Lemma reborrow `(nclose lftN ⊆ E) P κ κ':
    κ' ⊑ κ ⊢ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗  &{κ}P).
  Proof.
    iIntros "#H⊑ HP". iMod (borrow_reborrow' with "HP") as "[Hκ' H∋]".
      done. by exists κ'.
    iDestruct (borrow_shorten with "[H⊑] Hκ'") as "$".
    { iApply lft_incl_lb. iSplit. done. iApply lft_incl_refl. }
    iIntros "!>Hκ'". iApply ("H∋" with "[Hκ']"). iApply lft_dead_or. auto.
  Qed.

End incl.

Typeclasses Opaque lft_incl.

(*** Derived notions  *)

(** Shared borrows  *)
Definition shr_borrow `{invG Σ, lifetimeG Σ} κ (P : iProp Σ) :=
  (∃ i, idx_borrow κ i P ∗ inv lftN (∃ q, idx_borrow_own q i))%I.
Notation "&shr{ κ } P" := (shr_borrow κ P)
  (format "&shr{ κ } P", at level 20, right associativity) : uPred_scope.

Section shared_borrows.
  Context `{invG Σ, lifetimeG Σ} (P : iProp Σ).

  Global Instance shr_borrow_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (shr_borrow κ).
  Proof. solve_proper. Qed.
  Global Instance shr_borrow_persistent : PersistentP (&shr{κ} P) := _.

  Lemma borrow_share `(nclose lftN ⊆ E) κ : &{κ}P ={E}=∗ &shr{κ}P.
  Proof.
    iIntros "HP". unfold borrow. iDestruct "HP" as (i) "(#?&Hown)".
    iExists i. iFrame "#". iApply inv_alloc. auto.
  Qed.

  Lemma shr_borrow_acc `(nclose lftN ⊆ E) κ :
    &shr{κ}P ={E,E∖lftN}=∗ ▷P ∗ (▷P ={E∖lftN,E}=∗ True) ∨
                          [†κ] ∗ |={E∖lftN,E}=> True.
  Proof.
    iIntros "#HP". iDestruct "HP" as (i) "(#Hidx&#Hinv)".
    iInv lftN as (q') ">Hq'" "Hclose".
    rewrite -(Qp_div_2 q') /idx_borrow_own -op_singleton auth_frag_op own_op.
    iDestruct "Hq'" as "[Hq'0 Hq'1]". iMod ("Hclose" with "[Hq'1]") as "_". by eauto.
    iMod (idx_borrow_atomic_acc with "Hidx Hq'0") as "[[HP Hclose]|[H† Hclose]]". done.
    - iLeft. iFrame. iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iRight. iFrame. iIntros "!>". by iMod "Hclose".
  Qed.

  Lemma shr_borrow_acc_tok `(nclose lftN ⊆ E) q κ :
    &shr{κ}P ⊢ q.[κ] ={E,E∖lftN}=∗ ▷P ∗ (▷P ={E∖lftN,E}=∗ q.[κ]).
  Proof.
    iIntros "#Hshr Hκ". iMod (shr_borrow_acc with "Hshr") as "[[$ Hclose]|[H† _]]". done.
    - iIntros "!>HP". by iMod ("Hclose" with "HP").
    - iDestruct (lft_own_dead with "[-]") as "[]". by iFrame.
  Qed.

  Lemma shr_borrow_shorten κ κ': κ ⊑ κ' ⊢ &shr{κ'}P -∗ &shr{κ}P.
  Proof.
    iIntros "#H⊑ H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
      by iApply (idx_borrow_shorten with "H⊑").
  Qed.

End shared_borrows.

Typeclasses Opaque shr_borrow.

(** Fractured borrows  *)
Definition frac_borrow `{invG Σ, lifetimeG Σ} κ (Φ : Qp → iProp Σ) :=
  (∃ γ κ', κ ⊑ κ' ∗ &shr{κ'} ∃ q, Φ q ∗ own γ q ∗
                       (q = 1%Qp ∨ ∃ q', (q + q')%Qp = 1%Qp ∗ q'.[κ']))%I.
Notation "&frac{ κ } P" := (frac_borrow κ P)
  (format "&frac{ κ } P", at level 20, right associativity) : uPred_scope.

Section frac_borrow.

  Context `{invG Σ, lifetimeG Σ}.

  Global Instance frac_borrow_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (frac_borrow κ).
  Proof. solve_proper. Qed.
  Global Instance frac_borrow_persistent : PersistentP (&frac{κ}φ) := _.

  Lemma borrow_fracture φ `(nclose lftN ⊆ E) κ:
    &{κ}(φ 1%Qp) ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros "Hφ". iMod (own_alloc 1%Qp) as (γ) "?". done.
    iMod (borrow_acc_atomic_strong with "Hφ") as "[[Hφ Hclose]|[H† Hclose]]". done.
    - iMod ("Hclose" with "*[-]") as "Hφ"; last first.
      { iExists γ, κ. iSplitR; last by iApply (borrow_share with "Hφ").
        iApply lft_incl_refl. }
      iSplitL. by iExists 1%Qp; iFrame; auto.
      iIntros "!>[H† Hφ]!>". iNext. iDestruct "Hφ" as (q') "(Hφ & _ & [%|Hκ])". by subst.
      iDestruct "Hκ" as (q'') "[_ Hκ]".
      iDestruct (lft_own_dead with "[$Hκ $H†]") as "[]".
    - iMod ("Hclose" with "*") as "Hφ"; last first.
      iExists γ, κ. iSplitR; last by iApply (borrow_share with "Hφ"). iApply lft_incl_refl.
  Qed.

  Lemma frac_borrow_atomic_acc `(nclose lftN ⊆ E) κ φ:
    &frac{κ}φ ={E,E∖lftN}=∗ (∃ q, ▷ φ q ∗ (▷ φ q ={E∖lftN,E}=∗ True))
                          ∨ [†κ] ∗ |={E∖lftN,E}=> True.
  Proof.
    iIntros "#Hφ". iDestruct "Hφ" as (γ κ') "[Hκκ' Hshr]".
    iMod (shr_borrow_acc with "Hshr") as "[[Hφ Hclose]|[H† Hclose]]". done.
    - iLeft. iDestruct "Hφ" as (q) "(Hφ & Hγ & H)". iExists q. iFrame.
      iIntros "!>Hφ". iApply "Hclose". iExists q. iFrame.
    - iRight. iMod "Hclose" as "_". iMod (lft_incl_dead with "Hκκ' H†") as "$". done.
      iApply fupd_intro_mask. set_solver. done.
  Qed.

  Lemma frac_borrow_acc `(nclose lftN ⊆ E) q κ φ:
    □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) ⊢
    &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros "#Hφ Hfrac Hκ". unfold frac_borrow.
    iDestruct "Hfrac" as (γ κ') "#[#Hκκ' Hshr]".
    iMod (lft_incl_acc with "Hκκ' Hκ") as (qκ') "[[Hκ1 Hκ2] Hclose]". done.
    iMod (shr_borrow_acc_tok with "Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & Hq)".
    destruct (Qp_lower_bound (qκ'/2) (qφ/2)) as (qq & qκ'0 & qφ0 & Hqκ' & Hqφ).
    iExists qq.
    iAssert (▷ φ qq ∗ ▷ φ (qφ0 + qφ / 2))%Qp%I with "[Hφqφ]" as "[$ Hqφ]".
    { iNext. rewrite -{1}(Qp_div_2 qφ) {1}Hqφ. iApply "Hφ". by rewrite assoc. }
    rewrite -{1}(Qp_div_2 qφ) {1}Hqφ -assoc {1}Hqκ'.
    iDestruct "Hκ2" as "[Hκq Hκqκ0]". iDestruct "Hown" as "[Hownq Hown]".
    iMod ("Hclose'" with "[Hqφ Hq Hown Hκq]") as "Hκ1".
    { iNext. iExists _. iFrame. iRight. iDestruct "Hq" as "[%|Hq]".
      - subst. iExists qq. iIntros "{$Hκq}!%".
        by rewrite (comm _ qφ0) -assoc (comm _ qφ0) -Hqφ Qp_div_2.
      - iDestruct "Hq" as (q') "[% Hq'κ]". iExists (qq + q')%Qp.
        rewrite lft_own_frac_op. iIntros "{$Hκq $Hq'κ}!%".
        by rewrite assoc (comm _ _ qq) assoc -Hqφ Qp_div_2. }
    clear Hqφ qφ qφ0. iIntros "!>Hqφ".
    iMod (shr_borrow_acc_tok with "Hshr Hκ1") as "[H Hclose']". done.
    iDestruct "H" as (qφ) "(Hφqφ & >Hown & >[%|Hq])".
    { subst. iCombine "Hown" "Hownq" as "Hown".
      by iDestruct (own_valid with "Hown") as %Hval%Qp_not_plus_q_ge_1. }
    iDestruct "Hq" as (q') "[Hqφq' Hq'κ]". iCombine "Hown" "Hownq" as "Hown".
    iDestruct (own_valid with "Hown") as %Hval. iDestruct "Hqφq'" as %Hqφq'.
    assert (0 < q'-qq ∨ qq = q')%Qc as [Hq'q|<-].
    { change (qφ + qq ≤ 1)%Qc in Hval. apply Qp_eq in Hqφq'. simpl in Hval, Hqφq'.
      rewrite <-Hqφq', <-Qcplus_le_mono_l in Hval. apply Qcle_lt_or_eq in Hval.
      destruct Hval as [Hval|Hval].
      by left; apply ->Qclt_minus_iff. by right; apply Qp_eq, Qc_is_canon. }
    - assert (q' = mk_Qp _ Hq'q + qq)%Qp as ->. { apply Qp_eq. simpl. ring. }
      iDestruct "Hq'κ" as "[Hq'qκ Hqκ]".
      iMod ("Hclose'" with "[Hqφ Hφqφ Hown Hq'qκ]") as "Hqκ2".
      { iNext. iExists (qφ + qq)%Qp. iFrame. iSplitR "Hq'qκ". by iApply "Hφ"; iFrame.
        iRight. iExists _. iIntros "{$Hq'qκ}!%".
        revert Hqφq'. rewrite !Qp_eq. move=>/=<-. ring. }
      iApply "Hclose". iFrame. rewrite Hqκ' !lft_own_frac_op. by iFrame.
    - iMod ("Hclose'" with "[Hqφ Hφqφ Hown]") as "Hqκ2".
      { iNext. iExists (qφ ⋅ qq)%Qp. iFrame. iSplitL. by iApply "Hφ"; iFrame. auto. }
      iApply "Hclose". rewrite -{2}(Qp_div_2 qκ') {2}Hqκ' !lft_own_frac_op. by iFrame.
  Qed.

  Lemma frac_borrow_shorten κ κ' φ: κ ⊑ κ' ⊢ &frac{κ'}φ -∗ &frac{κ}φ.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (γ κ0) "[H⊑?]". iExists γ, κ0. iFrame.
    iApply lft_incl_trans. iFrame.
  Qed.

  Lemma frac_borrow_incl κ κ' q:
    &frac{κ}(λ q', (q * q').[κ']) ⊢ κ ⊑ κ'.
  Proof.
    iIntros "#Hbor!#". iSplitR.
    - iIntros (q') "Hκ'".
      iMod (frac_borrow_acc with "[] Hbor Hκ'") as (q'') "[>? Hclose]". done.
      + iIntros "/=!#*". rewrite Qp_mult_plus_distr_r lft_own_frac_op. iSplit; auto.
      + iExists _. iFrame. iIntros "!>Hκ'". iApply "Hclose". auto.
    - iIntros "H†'".
      iMod (frac_borrow_atomic_acc with "Hbor") as "[H|[$ $]]". done.
      iDestruct "H" as (q') "[>Hκ' _]".
      iDestruct (lft_own_dead with "[$H†' $Hκ']") as "[]".
  Qed.

End frac_borrow.

Typeclasses Opaque frac_borrow.

(** Thread local borrows  *)

Definition tl_borrow `{invG Σ, lifetimeG Σ, thread_localG Σ}
           (κ : lifetime) (tid : thread_id) (N : namespace) (P : iProp Σ) :=
  (∃ i, idx_borrow κ i P ∗ tl_inv tid N (idx_borrow_own 1 i))%I.

Notation "&tl{ κ | tid | N } P" := (tl_borrow κ tid N P)
  (format "&tl{ κ | tid | N } P", at level 20, right associativity) : uPred_scope.

Section tl_borrow.
  Context `{invG Σ, lifetimeG Σ, thread_localG Σ}
          (tid : thread_id) (N : namespace) (P : iProp Σ).

  Global Instance tl_borrow_persistent κ : PersistentP (&tl{κ|tid|N} P) := _.
  Global Instance tl_borrow_proper κ :
    Proper ((⊣⊢) ==> (⊣⊢)) (tl_borrow κ tid N).
  Proof.
    intros P1 P2 EQ. apply uPred.exist_proper. intros i. by rewrite EQ.
  Qed.

  Lemma borrow_tl κ `(nclose lftN ⊆ E): &{κ}P ={E}=∗ &tl{κ|tid|N}P.
  Proof.
    iIntros "HP". unfold borrow. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (tl_inv_alloc tid E N with "[Hown]"). auto.
  Qed.

  Lemma tl_borrow_acc q κ E F :
    nclose lftN ⊆ E → nclose tlN ⊆ E → nclose N ⊆ F →
    &tl{κ|tid|N}P ⊢ q.[κ] ∗ tl_own tid F ={E}=∗ ▷P ∗ tl_own tid (F ∖ N) ∗
                     (▷P ∗ tl_own tid (F ∖ N) ={E}=∗ q.[κ] ∗ tl_own tid F).
  Proof.
    iIntros (???) "#HP[Hκ Htlown]".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (tl_inv_open with "Hinv Htlown") as "(>Hown&Htlown&Hclose)"; try done.
    iMod (idx_borrow_acc with "Hpers [$Hown $Hκ]") as "[HP Hclose']". done.
    iIntros "{$HP $Htlown}!>[HP Htlown]".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma tl_borrow_shorten κ κ': κ ⊑ κ' ⊢ &tl{κ'|tid|N}P -∗ &tl{κ|tid|N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
    iApply (idx_borrow_shorten with "Hκκ' H").
  Qed.

End tl_borrow.

Typeclasses Opaque tl_borrow.
