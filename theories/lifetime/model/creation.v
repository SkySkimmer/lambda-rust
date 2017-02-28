From lrust.lifetime Require Export primitive.
From lrust.lifetime Require Import faking.
From iris.algebra Require Import csum auth frac gmap agree gset.
From iris.base_logic Require Import big_op.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section creation.
Context `{invG Σ, lftG Σ}.
Implicit Types κ : lft.

Lemma lft_kill (I : gmap lft lft_names) (K K' : gset lft) (κ : lft) :
  let Iinv := (
    own_ilft_auth I ∗
    ([∗ set] κ' ∈ K, lft_inv_alive κ') ∗
    ([∗ set] κ' ∈ K', lft_inv_dead κ'))%I in
  (∀ κ', is_Some (I !! κ') → κ' ⊂ κ → κ' ∈ K) →
  (∀ κ', is_Some (I !! κ') → κ ⊂ κ' → κ' ∈ K') →
  Iinv -∗ lft_inv_alive κ -∗ [†κ] ={↑borN ∪ ↑inhN}=∗ Iinv ∗ lft_inv_dead κ.
Proof.
  iIntros (Iinv HK HK') "(HI & Halive & Hdead) Hlalive Hκ".
  rewrite lft_inv_alive_unfold;
    iDestruct "Hlalive" as (P Q) "(Hbor & Hvs & Hinh)".
  rewrite /lft_bor_alive; iDestruct "Hbor" as (B) "(Hbox & Hbor & HB)".
  iAssert ⌜∀ i s, B !! i = Some s → s = Bor_in⌝%I with "[#]" as %HB.
  { iIntros (i s HBI).
    iDestruct (big_sepM_lookup _ B with "HB") as "HB"=> //.
    destruct s as [|q|κ']; rewrite /bor_cnt //.
    { iDestruct (lft_tok_dead with "HB Hκ") as "[]". }
    iDestruct "HB" as "[% Hcnt]".
    iDestruct (own_cnt_auth with "HI Hcnt") as %?.
    iDestruct (@big_sepS_elem_of with "Hdead") as "Hdead"; first by eauto.
    rewrite /lft_inv_dead; iDestruct "Hdead" as (R) "(_ & Hcnt' & _)".
    iDestruct (own_cnt_valid_2 with "Hcnt' Hcnt")
      as %[?%nat_included _]%auth_valid_discrete_2; omega. }
  iMod (box_empty with "Hbox") as "[HP Hbox]"=>//; first set_solver.
  { intros i s. by rewrite lookup_fmap fmap_Some=> -[? [/HB -> ->]]. }
  rewrite lft_vs_unfold; iDestruct "Hvs" as (n) "[Hcnt Hvs]".
  iDestruct (big_sepS_filter_acc (⊂ κ) _ _ (dom _ I) with "Halive")
    as "[Halive Halive']".
  { intros κ'. rewrite elem_of_dom. eauto. }
  iApply fupd_trans. iApply fupd_mask_mono; first by apply union_subseteq_l.
  iMod ("Hvs" $! I with "[HI Halive Hbox Hbor] HP Hκ") as "(Hinv & HQ & Hcnt')".
  { rewrite lft_vs_inv_unfold. iFrame. rewrite /lft_bor_dead.
    iExists (dom _ B), P. rewrite !to_gmap_dom -map_fmap_compose.
    rewrite (map_fmap_ext _ ((1%Qp,) ∘ to_agree) B); last naive_solver.
    iFrame. }
  rewrite lft_vs_inv_unfold; iDestruct "Hinv" as "(?&HI&Halive)".
  iSpecialize ("Halive'" with "Halive").
  iMod (own_cnt_update_2 with "Hcnt Hcnt'") as "?".
  { apply auth_update_dealloc, (nat_local_update _ _ 0 0); omega. }
  rewrite /Iinv. iFrame "Hdead Halive' HI".
  iModIntro. iMod (lft_inh_kill with "[$Hinh $HQ]"); first set_solver+.
  iModIntro. rewrite /lft_inv_dead. iExists Q. by iFrame.
Qed.

Lemma lfts_kill A (I : gmap lft lft_names) (K K' : gset lft) :
  let Iinv K' := (own_ilft_auth I ∗ [∗ set] κ' ∈ K', lft_inv_alive κ')%I in
  (∀ κ κ', κ ∈ K → is_Some (I !! κ') → κ ⊆ κ' → κ' ∈ K) →
  (∀ κ κ', κ ∈ K → lft_alive_in A κ → is_Some (I !! κ') →
    κ' ∉ K → κ' ⊂ κ → κ' ∈ K') →
  Iinv K' -∗ ([∗ set] κ ∈ K, lft_inv A κ ∗ [†κ])
    ={↑borN ∪ ↑inhN}=∗ Iinv K' ∗ [∗ set] κ ∈ K, lft_inv_dead κ.
Proof.
  intros Iinv. revert K'.
  induction (collection_wf K) as [K _ IH]=> K' HK HK'.
  iIntros "[HI Halive] HK".
  pose (Kalive := filter (lft_alive_in A) K).
  destruct (decide (Kalive = ∅)) as [HKalive|].
  { iModIntro. rewrite /Iinv. iFrame.
    iApply (@big_sepS_impl with "[$HK]"); iAlways.
    rewrite /lft_inv. iIntros (κ Hκ) "[[[_ %]|[$ _]] _]". set_solver. }
  destruct (minimal_exists_L (⊂) Kalive)
    as (κ & [Hκalive HκK]%elem_of_filter & Hκmin); first done.
  iDestruct (@big_sepS_delete with "HK") as "[[Hκinv Hκ] HK]"; first done.
  iDestruct (lft_inv_alive_in with "Hκinv") as "Hκalive"; first done.
  iAssert ⌜κ ∉ K'⌝%I with "[#]" as %HκK'.
  { iIntros (Hκ). iApply (lft_inv_alive_twice κ with "Hκalive").
    by iApply (@big_sepS_elem_of with "Halive"). }
  specialize (IH (K ∖ {[ κ ]})). feed specialize IH; [set_solver +HκK|].
  iMod (IH ({[ κ ]} ∪ K') with "[HI Halive Hκalive] HK") as "[[HI Halive] Hdead]".
  { intros κ' κ''.
    rewrite !elem_of_difference !elem_of_singleton=> -[? Hneq] ??.
    split; [by eauto|]; intros ->.
    eapply (minimal_strict_1 _ _ κ' Hκmin), strict_spec_alt; eauto.
    apply elem_of_filter; eauto using lft_alive_in_subseteq. }
  { intros κ' κ'' Hκ' ? [γs'' ?].
    destruct (decide (κ'' = κ)) as [->|]; [set_solver +|].
    move: Hκ'; rewrite not_elem_of_difference elem_of_difference
       elem_of_union not_elem_of_singleton elem_of_singleton.
    intros [??] [?|?]; eauto. }
  { rewrite /Iinv big_sepS_insert //. iFrame. }
  iDestruct (@big_sepS_insert with "Halive") as "[Hκalive Halive]"; first done.
  iMod (lft_kill with "[$HI $Halive $Hdead] Hκalive Hκ")
    as "[(HI&Halive&Hdead) Hκdead]".
  { intros κ' ??. eapply (HK' κ); eauto.
    intros ?. eapply (minimal_strict_1 _ _ _ Hκmin); eauto.
    apply elem_of_filter; split; last done.
    eapply lft_alive_in_subseteq, gmultiset_subset_subseteq; eauto. }
  { intros κ' ? [??]%strict_spec_alt.
    rewrite elem_of_difference elem_of_singleton; eauto. }
  iModIntro. rewrite /Iinv (big_sepS_delete _ K) //. iFrame.
Qed.

Definition kill_set (I : gmap lft lft_names) (Λ : atomic_lft) : gset lft :=
  filter (Λ ∈) (dom (gset lft) I).

Lemma elem_of_kill_set I Λ κ : κ ∈ kill_set I Λ ↔ Λ ∈ κ ∧ is_Some (I !! κ).
Proof. by rewrite /kill_set elem_of_filter elem_of_dom. Qed.
Lemma kill_set_subseteq I Λ : kill_set I Λ ⊆ dom (gset lft) I.
Proof. intros κ [??]%elem_of_kill_set. by apply elem_of_dom. Qed.

Definition down_close (A : gmap atomic_lft bool)
    (I : gmap lft lft_names) (K : gset lft) : gset lft :=
  filter (λ κ, κ ∉ K ∧
    set_Exists (λ κ', κ ⊂ κ' ∧ lft_alive_in A κ') K) (dom (gset lft) I).
Lemma elem_of_down_close A I K κ :
  κ ∈ down_close A I K ↔
    is_Some (I !! κ) ∧ κ ∉ K ∧ ∃ κ', κ' ∈ K ∧ κ ⊂ κ' ∧ lft_alive_in A κ'.
Proof. rewrite /down_close elem_of_filter elem_of_dom /set_Exists. tauto. Qed.

Lemma down_close_lft_alive_in A I K κ : κ ∈ down_close A I K → lft_alive_in A κ.
Proof.
  rewrite elem_of_down_close; intros (?&?&?&?&?&?).
  eapply lft_alive_in_subseteq, gmultiset_subset_subseteq; eauto.
Qed.
Lemma down_close_disjoint A I K : K ⊥ down_close A I K.
Proof. intros κ. rewrite elem_of_down_close. naive_solver. Qed.
Lemma down_close_subseteq A I K :
  down_close A I K ⊆ dom (gset lft) I.
Proof. intros κ [??]%elem_of_down_close. by apply elem_of_dom. Qed.

Lemma lft_create E :
  ↑lftN ⊆ E →
  lft_ctx ={E}=∗ ∃ κ, 1.[κ] ∗ □ (1.[κ] ={↑lftN,∅}▷=∗ [†κ]).
Proof.
  iIntros (?) "#LFT".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  destruct (exist_fresh (dom (gset _) A)) as [Λ HΛ%not_elem_of_dom].
  iMod (own_update with "HA") as "[HA HΛ]".
  { apply auth_update_alloc, (alloc_singleton_local_update _ Λ (Cinl 1%Qp))=>//.
    by rewrite lookup_fmap HΛ. }
  iMod ("Hclose" with "[HA HI Hinv]") as "_".
  { iNext. rewrite /lfts_inv /own_alft_auth.
    iExists (<[Λ:=true]>A), I. rewrite /to_alftUR fmap_insert; iFrame.
    iApply (@big_sepS_impl with "[$Hinv]").
    iAlways. rewrite /lft_inv. iIntros (κ ?) "[[Hκ %]|[Hκ %]]".
    - iLeft. iFrame "Hκ". iPureIntro. by apply lft_alive_in_insert.
    - iRight. iFrame "Hκ". iPureIntro. by apply lft_dead_in_insert. }
  iModIntro; iExists {[ Λ ]}.
  rewrite {1}/lft_tok big_sepMS_singleton. iFrame "HΛ".
  clear I A HΛ. iIntros "!# HΛ".
  iApply (step_fupd_mask_mono (↑lftN) _ _ (↑lftN∖↑mgmtN));  [set_solver..|].
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  rewrite /lft_tok big_sepMS_singleton.
  iDestruct (own_valid_2 with "HA HΛ")
    as %[[s [?%leibniz_equiv ?]]%singleton_included _]%auth_valid_discrete_2.
  iMod (own_update_2 with "HA HΛ") as "[HA HΛ]".
  { by eapply auth_update, singleton_local_update,
      (exclusive_local_update _ (Cinr ())). }
  iDestruct "HΛ" as "#HΛ". iModIntro; iNext.
  pose (K := kill_set I Λ); pose (K' := down_close A I K).
  assert (K ⊥ K') by (by apply down_close_disjoint).
  destruct (proj1 (subseteq_disjoint_union_L (K ∪ K')
    (dom (gset lft) I))) as (K''&HI&?).
  { apply union_least. apply kill_set_subseteq. apply down_close_subseteq. }
  rewrite HI !big_sepS_union //. iDestruct "Hinv" as "[[HinvK HinvD] Hinv]".
  iAssert ([∗ set] κ ∈ K', lft_inv_alive κ)%I with "[HinvD]" as "HinvD".
  { iApply (@big_sepS_impl with "[$HinvD]"); iIntros "!#".
    iIntros (κ Hκ) "?". iApply lft_inv_alive_in; last done.
    eauto using down_close_lft_alive_in. }
  iAssert ([∗ set] κ ∈ K, lft_inv A κ ∗ [† κ])%I with "[HinvK]" as "HinvK".
  { iApply (@big_sepS_impl with "[$HinvK]"); iIntros "!#".
    iIntros (κ [? _]%elem_of_kill_set) "$". rewrite /lft_dead. eauto. }
  iApply fupd_trans. iApply (fupd_mask_mono (↑borN ∪ ↑inhN));
                       first by apply union_least; solve_ndisj.
  iMod (lfts_kill A I K K' with "[$HI $HinvD] HinvK") as "[[HI HinvD] HinvK]".
  { intros κ κ' [??]%elem_of_kill_set ??. apply elem_of_kill_set.
    split; last done. by eapply gmultiset_elem_of_subseteq. }
  { intros κ κ' ?????. apply elem_of_down_close; eauto 10. }
  iModIntro. iMod ("Hclose" with "[-]") as "_"; last first.
  { iModIntro. rewrite /lft_dead. iExists Λ.
    rewrite elem_of_singleton. auto. }
  iNext. iExists (<[Λ:=false]>A), I.
  rewrite /own_alft_auth /to_alftUR fmap_insert. iFrame "HA HI".
  rewrite HI !big_sepS_union //.
  iSplitL "HinvK HinvD"; first iSplitL "HinvK".
  - iApply (@big_sepS_impl with "[$HinvK]"); iIntros "!#".
    iIntros (κ [? _]%elem_of_kill_set) "Hdead". rewrite /lft_inv.
    iRight. iFrame. iPureIntro. by apply lft_dead_in_insert_false'.
  - iApply (@big_sepS_impl with "[$HinvD]"); iIntros "!#".
    iIntros (κ Hκ) "Halive". rewrite /lft_inv.
    iLeft. iFrame "Halive". iPureIntro.
    assert (lft_alive_in A κ) as Halive by (by eapply down_close_lft_alive_in).
    apply lft_alive_in_insert_false; last done.
    apply elem_of_down_close in Hκ as (?&HFOO&_).
    move: HFOO. rewrite elem_of_kill_set. tauto.
  - iApply (@big_sepS_impl with "[$Hinv]"); iIntros "!#".
    rewrite /lft_inv. iIntros (κ Hκ) "[[? %]|[? %]]".
    + iLeft. iFrame. iPureIntro.
      apply lft_alive_in_insert_false; last done.
      assert (κ ∉ K). intros ?. eapply H5. 2: eauto. rewrite elem_of_union. eauto.
      move: H7. rewrite elem_of_kill_set not_and_l. intros [?|?]. done.
      contradict H7. apply elem_of_dom. set_solver +HI Hκ.
    + iRight. iFrame. iPureIntro. by apply lft_dead_in_insert_false.
Qed.
End creation.
