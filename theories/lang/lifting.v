From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Export lang heap.
From lrust.lang Require Import tactics.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.
Local Hint Extern 0 (head_reducible _ _) => do_head_step eauto 2.
Hint Constructors lit_neq lit_eq.

Class lrustG Σ := LRustG {
  lrustG_invG : invG Σ;
  lrustG_gen_heapG :> heapG Σ
}.

Instance lrustG_irisG `{lrustG Σ} : irisG lrust_lang Σ := {
  iris_invG := lrustG_invG;
  state_interp := heap_ctx
}.
Global Opaque iris_invG.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_eq/=
  | H : lit_neq _ ?x ?y |- _ => inversion H; clear H; simplify_eq/=
  end.

Section lifting.
Context `{lrustG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types ef : option expr.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {E e} K Φ :
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} -∗ WP fill K e @ E {{ Φ }}.
Proof. exact: wp_ectx_bind. Qed.

Lemma wp_bindi {E e} Ki Φ :
  WP e @ E {{ v, WP fill_item Ki (of_val v) @ E {{ Φ }} }} -∗
     WP fill_item Ki e @ E {{ Φ }}.
Proof. exact: weakestpre.wp_bind. Qed.

(** Heap *)
Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l sz (vl : vec val sz), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…(Z.to_nat n) ∗ l ↦∗ vl }}}.
Proof.
  iIntros (? Φ) "HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (heap_alloc with "Hσ") as "[Hσ Hl]"; [done..|].
  iModIntro; iSplit=> //. iFrame.
  iApply ("HΦ" $! _ _ (list_to_vec init)).
  rewrite vec_to_list_of_list. auto.
Qed.

Lemma wp_free E (n:Z) l vl :
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc E l q v :
  {{{ ▷ l ↦{q} v }}} Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (?) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[n ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. rewrite to_of_val. iFrame. by iApply "HΦ".
Qed.

Lemma wp_read_na E l q v :
  {{{ ▷ l ↦{q} v }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hv HΦ". iApply wp_lift_head_step; auto. iIntros (σ1) "Hσ".
  iMod (heap_read_na with "Hσ Hv") as (n) "(% & Hσ & Hσclose)".
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1 n.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iMod ("Hσclose" with "Hσ") as (n) "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step. rewrite to_of_val /=.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_write_sc E l e v v' :
  to_val e = Some v →
  {{{ ▷ l ↦ v' }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iMod (heap_write _ _ _  v with "Hσ Hv") as "[Hσ Hv]".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_write_na E l e v v' :
  to_val e = Some v →
  {{{ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ".
  iApply wp_lift_head_step; auto. iIntros (σ1) "Hσ".
  iMod (heap_write_na with "Hσ Hv") as "(% & Hσ & Hσclose)".
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iMod ("Hσclose" with "Hσ") as "(% & Hσ & Hv)".
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "!>"; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. by iApply "HΦ".
Qed.

Lemma wp_cas_int_fail E l q z1 e2 lit2 zl :
  to_val e2 = Some (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦{q} LitV (LitInt zl) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 0; l ↦{q} LitV (LitInt zl) }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hv") as %[n ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc E l lit1 e2 lit2 :
  to_val e2 = Some (LitV lit2) → lit1 ≠ LitUnit →
  {{{ ▷ l ↦ LitV lit1 }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct lit1; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; [inv_lit|].
  iMod (heap_write with "Hσ Hv") as "[$ Hv]".
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_int_suc E l z1 e2 lit2 :
  to_val e2 = Some (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_suc E l l1 e2 lit2 :
  to_val e2 = Some (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof. intros ?. by apply wp_cas_suc. Qed.

Lemma wp_cas_loc_fail E l q q' q1 l1 v1' e2 lit2 l' vl' :
  to_val e2 = Some (LitV lit2) → l1 ≠ l' →
  {{{ ▷ l ↦{q} LitV (LitLoc l') ∗ ▷ l' ↦{q'} vl' ∗ ▷ l1 ↦{q1} v1' }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 0);
      l ↦{q} LitV (LitLoc l') ∗ l' ↦{q'} vl' ∗ l1 ↦{q1} v1' }}}.
Proof.
  iIntros (<-%of_to_val ? Φ) "(>Hl & >Hl' & >Hl1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read with "Hσ Hl") as %[nl ?].
  iDestruct (heap_read with "Hσ Hl'") as %[nl' ?].
  iDestruct (heap_read with "Hσ Hl1") as %[nl1 ?].
  iModIntro; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; inv_lit.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; iFrame.
Qed.

Lemma wp_cas_loc_nondet E l l1 e2 l2 ll :
  to_val e2 = Some (LitV $ LitLoc l2) →
  {{{ ▷ l ↦ LitV (LitLoc ll) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ b, RET LitV (lit_of_bool b);
      if b is true then l ↦ LitV (LitLoc l2)
      else ⌜l1 ≠ ll⌝ ∗ l ↦ LitV (LitLoc ll) }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hv HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1) "Hσ". iDestruct (heap_read_1 with "Hσ Hv") as %?.
  iModIntro; iSplit; first (destruct (decide (ll = l1)) as [->|]; by eauto).
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step; last lia.
  - inv_lit. iModIntro; iSplit; [done|]; iFrame "Hσ".
    iApply "HΦ"; simpl; auto.
  - iMod (heap_write with "Hσ Hv") as "[$ Hv]".
    iModIntro; iSplit; [done|]. iApply "HΦ"; iFrame.
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  {{{ ▷ WP e {{ _, True }} }}} Fork e @ E {{{ RET LitV LitUnit; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_pure_det_head_step; eauto.
  by intros; inv_head_step; eauto. iApply step_fupd_intro; first done. iNext.
  rewrite big_sepL_singleton. iFrame. iApply wp_value. done. by iApply "HΦ".
Qed.

Lemma wp_rec_step_fupd E E' e f xl erec erec' el Φ :
  e = Rec f xl erec →
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (f :b: xl +b+ []) erec →
  subst_l (f::xl) (e::el) erec = Some erec' →
  (|={E,E'}▷=> WP erec' @ E {{ Φ }}) -∗ WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "H". iApply wp_lift_pure_det_head_step_no_fork; subst; eauto.
  by intros; inv_head_step; eauto.
Qed.

Lemma wp_rec E e f xl erec erec' el Φ :
  e = Rec f xl erec →
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (f :b: xl +b+ []) erec →
  subst_l (f::xl) (e::el) erec = Some erec' →
  ▷ WP erec' @ E {{ Φ }} -∗ WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "?". iApply wp_rec_step_fupd; [done..|].
  iApply step_fupd_intro; done.
Qed.

Lemma wp_bin_op_pure E op l1 l2 l' :
  (∀ σ, bin_op_eval σ op l1 l2 l') →
  {{{ True }}} BinOp op (Lit l1) (Lit l2) @ E
  {{{ l'' σ, RET LitV l''; ⌜bin_op_eval σ op l1 l2 l''⌝ }}}.
Proof.
  iIntros (? Φ) "HΦ". iApply wp_lift_pure_head_step; eauto.
  { intros. by inv_head_step. }
  iApply step_fupd_intro; first done. iNext. iIntros (e2 efs σ Hs).
  inv_head_step; rewrite right_id.
  rewrite -wp_value //. iApply "HΦ". eauto.
Qed.

Lemma wp_le E (n1 n2 : Z) P Φ :
  (n1 ≤ n2 → P -∗ ▷ Φ (LitV $  true)) →
  (n2 < n1 → P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hg) "HP".
  destruct (bool_decide_reflect (n1 ≤ n2)); [rewrite Hl //|rewrite Hg; last omega];
    clear Hl Hg; (iApply wp_bin_op_pure; first by econstructor); iNext; iIntros (?? Heval);
    inversion_clear Heval; [rewrite bool_decide_true //|rewrite bool_decide_false //].
Qed.

Lemma wp_eq_int E (n1 n2 : Z) P Φ :
  (n1 = n2 → P -∗ ▷ Φ (LitV true)) →
  (n1 ≠ n2 → P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2)) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hg) "HP".
  destruct (bool_decide_reflect (n1 = n2)); [rewrite Hl //|rewrite Hg //];
    clear Hl Hg; iApply wp_bin_op_pure; subst.
  - intros. apply BinOpEqTrue. constructor.
  - iNext; iIntros (?? Heval). by inversion_clear Heval; inv_lit.
  - intros. apply BinOpEqFalse. by constructor.
  - iNext; iIntros (?? Heval). by inversion_clear Heval; inv_lit.
Qed.

Lemma wp_eq_loc_0_r E (l : loc) P Φ :
  (P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0)) @ E {{ Φ }}.
Proof.
  iIntros (HΦ) "HP". iApply wp_bin_op_pure. by intros; do 2 constructor.
  rewrite HΦ. iNext. iIntros (?? Heval). by inversion_clear Heval; inv_lit.
Qed.

Lemma wp_eq_loc_0_l E (l : loc) P Φ :
  (P -∗ ▷ Φ (LitV false)) →
  P -∗ WP BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l)) @ E {{ Φ }}.
Proof.
  iIntros (HΦ) "HP". iApply wp_bin_op_pure. by intros; do 2 constructor.
  rewrite HΦ. iNext. iIntros (?? Heval). by inversion_clear Heval; inv_lit.
Qed.

(* TODO: wp_eq for locations, if needed. *)

Lemma wp_offset E l z Φ :
  ▷ Φ (LitV $ LitLoc $ shift_loc l z) -∗
    WP BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_plus E z1 z2 Φ :
  ▷ Φ (LitV $ LitInt $ z1 + z2) -∗
    WP BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_minus E z1 z2 Φ :
  ▷ Φ (LitV $ LitInt $ z1 - z2) -∗
    WP BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E {{ Φ }}.
Proof.
  iIntros "HP". iApply wp_bin_op_pure; first by econstructor.
  iNext. iIntros (?? Heval). inversion_clear Heval. done.
Qed.

Lemma wp_case E i e el Φ :
  0 ≤ i →
  el !! (Z.to_nat i) = Some e →
  ▷ WP e @ E {{ Φ }} -∗ WP Case (Lit $ LitInt i) el @ E {{ Φ }}.
Proof.
  iIntros (??) "?". iApply wp_lift_pure_det_head_step_no_fork'; eauto.
  by intros; inv_head_step; eauto.
Qed.

Lemma wp_if E (b : bool) e1 e2 Φ :
  (if b then ▷ WP e1 @ E {{ Φ }} else ▷ WP e2 @ E {{ Φ }})%I -∗
  WP If (Lit b) e1 e2 @ E {{ Φ }}.
Proof. iIntros "?". by destruct b; iApply wp_case. Qed.


(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ:
  is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf Hf]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    assert (App f ((of_val <$> vs) ++ e :: el) = fill_item (AppRCtx vf vs el) e)
      as -> by rewrite /= (of_to_val f) //.
    iApply wp_bindi. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]) (of_to_val f) //.
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → is_Some (to_val f) →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_of_list Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"); first done. iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite vec_to_list_length.
Qed.


(** Proof rules for the lam-related sugar *)
Lemma wp_lam E xl e eb e' el Φ :
  e = Lam xl eb →
  Forall (λ ei, is_Some (to_val ei)) el →
  Closed (xl +b+ []) eb →
  subst_l xl el eb = Some e' →
  ▷ WP e' @ E {{ Φ }} -∗ WP App e el @ E {{ Φ }}.
Proof.
  iIntros (-> ???) "?". iApply (wp_rec _ _ BAnon)=>//.
    by rewrite /= option_fmap_id.
Qed.

Lemma wp_let E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x e1 e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. eauto using wp_lam. Qed.

Lemma wp_let' E x e1 e2 v Φ :
  to_val e1 = Some v →
  Closed (x :b: []) e2 →
  ▷ WP subst' x (of_val v) e2 @ E {{ Φ }} -∗ WP Let x e1 e2 @ E {{ Φ }}.
Proof. intros ?. rewrite (of_to_val e1) //. eauto using wp_let. Qed.

Lemma wp_seq E e1 e2 v Φ :
  to_val e1 = Some v →
  Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} -∗ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros (??) "?". by iApply (wp_let _ BAnon). Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) -∗ WP Skip @ E {{ Φ }}.
Proof. iIntros. iApply wp_seq. done. iNext. by iApply wp_value. Qed.

End lifting.
