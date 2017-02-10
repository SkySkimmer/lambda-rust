From iris.program_logic Require Import weakestpre.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From lrust.lang Require Import proofmode notation.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

Definition spawn : val :=
  λ: ["f"],
    let: "c" := Alloc #2 in
    "c" <- #0;; (* Initialize "sent" field to 0 (non-atomically). *)
    Fork ("f" ["c"]);;
    "c".
Definition finish : val :=
  λ: ["c"; "v"],
    "c" +ₗ #1 <- "v";; (* Store data (non-atomically). *)
    "c" <-ˢᶜ #1;; (* Signal that we finished (atomically!) *)
    #().
Definition join : val :=
  rec: "join" ["c"] :=
    if: !ˢᶜ"c" then
      let: "v" := !("c" +ₗ #1) in (* The thread finished, we can non-atomically load the data. *)
      Free #2 "c";;
      "v"
    else
      "join" ["c"].

(** The CMRA & functor we need. *)
Class spawnG Σ := SpawnG { spawn_tokG :> inG Σ (exclR unitC) }.
Definition spawnΣ : gFunctors := #[GFunctor (exclR unitC)].

Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!lrustG Σ, !spawnG Σ} (N : namespace).

Definition spawn_inv (γf γj : gname) (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (own γf (Excl ()) ∗ own γj (Excl ()) ∨
   ∃ b, c ↦ #(lit_of_bool b) ∗ 
        match b with false => True%I 
                   | true => ∃ v, shift_loc c 1 ↦ v ∗ Ψ v ∗ own γf (Excl ())
        end)%I.

Definition finish_handle (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (∃ γf γj v, own γf (Excl ()) ∗ shift_loc c 1 ↦ v ∗ inv N (spawn_inv γf γj c Ψ))%I.

Definition join_handle (c : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  (∃ γf γj, own γj (Excl ()) ∗ † c … 2 ∗ inv N (spawn_inv γf γj c Ψ))%I.

Global Instance spawn_inv_ne n γf γj c :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γf γj c).
Proof. solve_proper. Qed.
Global Instance finish_handle_ne n c :
  Proper (pointwise_relation val (dist n) ==> dist n) (finish_handle c).
Proof. solve_proper. Qed.
Global Instance join_handle_ne n c :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle c).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec (Ψ : val → iProp Σ) e (f : val) :
  to_val e = Some f →
  {{{ ∀ c, finish_handle c Ψ -∗ WP f [ #c] {{ _, True }} }}}
    spawn [e] {{{ c, RET #c; join_handle c Ψ }}}.
Proof.
  iIntros (<-%of_to_val Φ) "Hf HΦ". rewrite /spawn /=.
  wp_let. wp_alloc l vl as "Hl" "H†". wp_let.
  iMod (own_alloc (Excl ())) as (γf) "Hγf"; first done.
  iMod (own_alloc (Excl ())) as (γj) "Hγj"; first done.
  (* TODO: maybe we should get vl as a vector here instead of a separate hypothesis for the length? *)
  assert (2 = length vl)%nat as Hvl.
  { apply Nat2Z.inj. done. }
  destruct vl as [|v0 vl]; first done. destruct vl as [|v1 vl]; first done.
  destruct vl; last done. clear H Hvl.
  rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
  iDestruct "Hl" as "[Hc Hd]". wp_write. clear v0.
  iMod (inv_alloc N _ (spawn_inv γf γj l Ψ) with "[Hc]") as "#?".
  { iNext. iRight. iExists false. auto. }
  (* TODO: Cannot use wp_apply due to curried lemma. *)
  wp_bind (Fork _). iApply (wp_fork with "[Hγf Hf Hd]").
  - iNext. iApply "Hf". iExists _, _, _. iFrame. auto.
  - iIntros "!> _". wp_seq. iApply "HΦ". iExists _, _.
    iFrame. auto.
Qed.

Lemma finish_spec (Ψ : val → iProp Σ) c v :
  {{{ finish_handle c Ψ ∗ Ψ v }}} finish [ #c; v] {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[Hfin HΨ] HΦ". iDestruct "Hfin" as (γf γj v0) "(Hf & Hd & #?)".
  wp_lam. wp_op. wp_write.
  wp_bind (_ <-ˢᶜ _)%E. iInv N as "[[>Hf' _]|Hinv]" "Hclose".
  { iExFalso. iCombine "Hf" "Hf'" as "Hf". iDestruct (own_valid with "Hf") as "%".
    auto. }
  iDestruct "Hinv" as (b) "[>Hc _]". wp_write.
  iMod ("Hclose" with "[-HΦ]").
  - iNext. iRight. iExists true. iFrame. iExists _. iFrame.
  - iModIntro. wp_seq. by iApply "HΦ".
Qed.

Lemma join_spec (Ψ : val → iProp Σ) c :
  {{{ join_handle c Ψ }}} join [ #c] {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "H HΦ". iDestruct "H" as (γf γj) "(Hj & H† & #?)".
  iLöb as "IH". wp_rec.
  wp_bind (!ˢᶜ _)%E. iInv N as "[[_ >Hj']|Hinv]" "Hclose".
  { iExFalso. iCombine "Hj" "Hj'" as "Hj". iDestruct (own_valid with "Hj") as "%".
    auto. }
  iDestruct "Hinv" as (b) "[>Hc Ho]". wp_read. destruct b; last first.
  { iMod ("Hclose" with "[Hc]").
    - iNext. iRight. iExists _. iFrame.
    - iModIntro. iApply wp_if. iNext. iApply ("IH" with "Hj H†").
      auto. }
  iDestruct "Ho" as (v) "(Hd & HΨ & Hf)".
  iMod ("Hclose" with "[Hj Hf]").
  { iNext. iLeft. iFrame. }
  iModIntro. iApply wp_if. iNext. wp_op. wp_read. wp_let.
  iAssert (c ↦∗ [ #true; v])%I with "[Hc Hd]" as "Hc".
  { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
  wp_free; first done. iApply "HΦ". done.
Qed.
End proof.

Typeclasses Opaque finish_handle join_handle.
