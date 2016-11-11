From iris.algebra Require Import csum auth frac gmap.
From iris.base_logic.lib Require Export fancy_updates invariants namespaces.
From iris.proofmode Require Import tactics.

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
  lft_toks_name : gname;
  borrow_tok_name : gname
}.

Parameter lft_ctx : ∀ `{lifetimeG Σ}, iProp Σ.

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

  Parameter idx_borrow:
    ∀ `{lifetimeG Σ} (κ : lifetime) (i : borrow_idx) (P : iProp Σ), iProp Σ.

  Definition borrow (κ : lifetime) (P : iProp Σ) : iProp Σ :=
    (∃ i, idx_borrow κ i P ∗ idx_borrow_own 1 i)%I.

End defs.

Typeclasses Opaque lft_own lft_dead borrow.

(*** Notations  *)

Notation "q .[ κ ]" := (lft_own q κ)
    (format "q .[ κ ]", at level 0): uPred_scope.
Notation "[† κ ]" := (lft_dead κ) (format "[† κ ]"): uPred_scope.
Notation "&{ κ } P" := (borrow κ P)
  (format "&{ κ } P", at level 20, right associativity) : uPred_scope.
Hint Unfold lifetime : typeclass_instances.

Section lft.
  Context `{invG Σ, lifetimeG Σ}.

  Axiom lft_ctx_alloc : True ={∅}=∗ lft_ctx.

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

  Axiom lft_ctx_persistent : PersistentP lft_ctx.

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
    ∀ `(nclose lftN ⊆ E),
      lft_ctx ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={⊤,⊤∖nclose lftN}▷=∗ [†κ]).

  Axiom idx_borrow_acc :
    ∀ `(nclose lftN ⊆ E) q κ i P,
      lft_ctx ⊢ idx_borrow κ i P -∗ idx_borrow_own 1 i
              -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ idx_borrow_own 1 i ∗ q.[κ]).
  Axiom idx_borrow_atomic_acc :
    ∀ `(nclose lftN ⊆ E) q κ i P,
      lft_ctx ⊢ idx_borrow κ i P -∗ idx_borrow_own q i
         ={E,E∖lftN}=∗
            ▷ P ∗ (▷ P ={E∖lftN,E}=∗ idx_borrow_own q i) ∨
            [†κ] ∗ (|={E∖lftN,E}=> idx_borrow_own q i).

  (** Basic borrows  *)
  Axiom borrow_create :
    ∀ `(nclose lftN ⊆ E) κ P, lft_ctx ⊢ ▷ P ={E}=∗ &{κ} P ∗ ([†κ] ={E}=∗ ▷ P).
  Axiom borrow_fake : ∀ `(nclose lftN ⊆ E) κ P, lft_ctx ⊢ [†κ] ={E}=∗ &{κ}P.
  Axiom borrow_split :
    ∀ `(nclose lftN ⊆ E) κ P Q, lft_ctx ⊢ &{κ}(P ∗ Q) ={E}=∗ &{κ}P ∗ &{κ}Q.
  Axiom borrow_combine :
    ∀ `(nclose lftN ⊆ E) κ P Q, lft_ctx ⊢ &{κ}P -∗ &{κ}Q ={E}=∗ &{κ}(P ∗ Q).
  Axiom borrow_acc_strong :
    ∀ `(nclose lftN ⊆ E) q κ P,
      lft_ctx ⊢ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗
      ∀ Q, ▷ Q ∗ ▷([†κ] -∗ ▷Q ={⊤ ∖ nclose lftN}=∗ ▷ P) ={E}=∗ &{κ}Q ∗ q.[κ].
  Axiom borrow_acc_atomic_strong :
    ∀ `(nclose lftN ⊆ E) κ P,
      lft_ctx ⊢ &{κ}P ={E,E∖lftN}=∗
        (▷ P ∗ ∀ Q, ▷ Q ∗ ▷([†κ] -∗ ▷Q ={⊤ ∖ nclose lftN}=∗ ▷ P) ={E∖lftN,E}=∗ &{κ}Q) ∨
        [†κ] ∗ |={E∖lftN,E}=> True.
  Axiom borrow_reborrow' :
    ∀ `(nclose lftN ⊆ E) κ κ' P, κ ≼ κ' →
      lft_ctx ⊢ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗ &{κ}P).
  Axiom borrow_unnest :
    ∀ `(nclose lftN ⊆ E) κ κ' P, lft_ctx ⊢ &{κ'}&{κ}P ={E}▷=∗ &{κ ⋅ κ'}P.

  (*** Derived lemmas  *)

  Lemma lft_own_dead q κ : q.[κ] ⊢ [† κ] -∗ False.
  Proof.
    rewrite /lft_own /lft_dead.
    iIntros "Hl Hr". iDestruct "Hr" as (Λ) "[HΛ Hr]".
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
      lft_ctx ⊢ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ (▷ P ={E}=∗ &{κ}P ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT HP Htok".
    iMod (borrow_acc_strong with "LFT HP Htok") as "[HP Hclose]". done.
    iIntros "!> {$HP} HP". iApply "Hclose". by iIntros "{$HP}!>_$".
  Qed.

  Lemma borrow_exists {A} `(nclose lftN ⊆ E) κ (Φ : A → iProp Σ) {_:Inhabited A}:
    lft_ctx ⊢ &{κ}(∃ x, Φ x) ={E}=∗ ∃ x, &{κ}Φ x.
  Proof.
    iIntros "#LFT Hb".
    iMod (borrow_acc_atomic_strong with "LFT Hb") as "[[HΦ Hclose]|[H† Hclose]]". done.
    - iDestruct "HΦ" as (x) "HΦ". iExists x. iApply "Hclose". iIntros "{$HΦ}!>_?". eauto.
    - iMod "Hclose" as "_". iExists inhabitant. by iApply (borrow_fake with "LFT").
  Qed.

  Lemma borrow_or `(nclose lftN ⊆ E) κ P Q:
    lft_ctx ⊢ &{κ}(P ∨ Q) ={E}=∗ (&{κ}P ∨ &{κ}Q).
  Proof.
    iIntros "#LFT H". rewrite uPred.or_alt.
    iMod (borrow_exists with "LFT H") as ([]) "H"; auto.
  Qed.

  Lemma borrow_persistent `(nclose lftN ⊆ E) `{PersistentP _ P} κ q:
    lft_ctx ⊢ &{κ}P -∗ q.[κ] ={E}=∗ ▷ P ∗ q.[κ].
  Proof.
    iIntros "#LFT Hb Htok".
    iMod (borrow_acc with "LFT Hb Htok") as "[#HP Hob]". done.
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
    lft_ctx ⊢ κ' ⊑ κ -∗ &{κ}P ={E}=∗ &{κ'}P ∗ ([†κ'] ={E}=∗  &{κ}P).
  Proof.
    iIntros "#LFT #H⊑ HP". iMod (borrow_reborrow' with "LFT HP") as "[Hκ' H∋]".
      done. by exists κ'.
    iDestruct (borrow_shorten with "[H⊑] Hκ'") as "$".
    { iApply lft_incl_lb. iSplit. done. iApply lft_incl_refl. }
    iIntros "!>Hκ'". iApply ("H∋" with "[Hκ']"). iApply lft_dead_or. auto.
  Qed.

End incl.

Typeclasses Opaque lft_incl.
