From iris.program_logic Require Import hoare.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation memcpy.
From lrust.typing Require Export type perm.
From lrust Require Import typing.perm_incl lang.proofmode.
From lrust.lifetime Require Import frac_borrow.

Import Types Perm.

Section typing.

  Context `{iris_typeG Σ}.

  (* TODO : good notations for [typed_step] and [typed_step_ty] ? *)
  Definition typed_step (ρ : perm) e (θ : val → perm) :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ tl_own tid ⊤ }} e
           {{ v, θ v tid ∗ tl_own tid ⊤ }}.

  Definition typed_step_ty (ρ : perm) e ty :=
    typed_step ρ e (λ ν, ν ◁ ty)%P.

  Definition typed_program (ρ : perm) e :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ tl_own tid ⊤ }} e {{ _, False }}.

  Lemma typed_frame ρ e θ ξ:
    typed_step ρ e θ → typed_step (ρ ∗ ξ) e (λ ν, θ ν ∗ ξ)%P.
  Proof.
    iIntros (Hwt tid) "!#(#HEAP&#LFT&[?$]&?)". iApply Hwt. iFrame "∗#".
  Qed.

  Lemma typed_step_exists {A} ρ θ e ξ:
    (∀ x:A, typed_step (ρ ∗ θ x) e ξ) →
    typed_step (ρ ∗ ∃ x, θ x) e ξ.
  Proof.
    iIntros (Hwt tid) "!#(#HEAP&#LFT&[Hρ Hθ]&?)". iDestruct "Hθ" as (x) "Hθ".
    iApply Hwt. iFrame "∗#".
  Qed.

  Lemma typed_bool ρ (b:Datatypes.bool): typed_step_ty ρ #b bool.
  Proof. iIntros (tid) "!#(_&_&_&$)". wp_value. by iExists _. Qed.

  Lemma typed_int ρ (z:Datatypes.nat) :
    typed_step_ty ρ #z int.
  Proof. iIntros (tid) "!#(_&_&_&$)". wp_value. by iExists _. Qed.

  Lemma typed_fn {A n} `{Duplicable _ ρ, Closed (f :b: xl +b+ []) e} θ :
    length xl = n →
    (∀ (a : A) (vl : vec val n) (fv : val) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (fv ◁ fn θ ∗ (θ a vl) ∗ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (fn θ).
  Proof.
    iIntros (Hn He tid) "!#(#HEAP&#LFT&#Hρ&$)".
    assert (Rec f xl e = RecV f xl e) as -> by done. iApply wp_value'.
    rewrite has_type_value.
    iLöb as "IH". iExists _. iSplit. done. iIntros (a vl) "!#[Hθ?]".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply He. done. iFrame "∗#". by rewrite has_type_value.
  Qed.

  Lemma typed_cont {n} `{Closed (f :b: xl +b+ []) e} ρ θ :
    length xl = n →
    (∀ (fv : val) (vl : vec val n) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (fv ◁ cont (λ vl, ρ ∗ θ vl)%P ∗ (θ vl) ∗ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (cont θ).
  Proof.
    iIntros (Hn He tid) "!#(#HEAP&#LFT&Hρ&$)". specialize (He (RecV f xl e)).
    assert (Rec f xl e = RecV f xl e) as -> by done. iApply wp_value'.
    rewrite has_type_value.
    iLöb as "IH". iExists _. iSplit. done. iIntros (vl) "Hθ ?".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply He. done. iFrame "∗#". rewrite has_type_value.
    iExists _. iSplit. done. iIntros (vl') "[Hρ Hθ] Htl".
    iDestruct ("IH" with "Hρ") as (f') "[Hf' IH']".
    iDestruct "Hf'" as %[=<-]. iApply ("IH'" with "Hθ Htl").
  Qed.

  Lemma typed_valuable (ν : expr) ty:
    typed_step_ty (ν ◁ ty) ν ty.
  Proof.
    iIntros (tid) "!#(_&_&H&$)". iApply (has_type_wp with "[$H]"). by iIntros (v) "_ $".
  Qed.

  Lemma typed_plus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 + e2) int.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#ĽFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. by iExists _.
  Qed.

  Lemma typed_minus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 - e2) int.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#LFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. by iExists _.
  Qed.

  Lemma typed_le e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ∗ ρ2) (e1 ≤ e2) bool.
  Proof.
    unfold typed_step_ty, typed_step. setoid_rewrite has_type_value.
    iIntros (He1 He2 tid) "!#(#HEAP&#LFT&[H1 H2]&?)".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply He1; iFrame "∗#".
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply He2; iFrame "∗#".
    iIntros (v2) "[Hv2$]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op; intros _; by iExists _.
  Qed.

  Lemma typed_newlft ρ:
    typed_step ρ Newlft (λ _, ∃ α, 1.[α] ∗ α ∋ top)%P.
  Proof.
    iIntros (tid) "!#(_&#LFT&_&$)". wp_value.
    iMod (lft_create with "LFT") as (α) "[?#?]". done.
    iExists α. iFrame. iIntros "!>_!>". done.
  Qed.

  Lemma typed_endlft κ ρ:
    typed_step (κ ∋ ρ ∗ 1.[κ] ∗ †κ) Endlft (λ _, ρ)%P.
  Proof.
    iIntros (tid) "!#(_&_&(Hextr&Htok&Hend)&$)".
    iApply wp_fupd. iApply (wp_wand_r _ _ (λ _, _ ∗ True)%I). iSplitR "Hextr".
    iApply (wp_frame_step_l _ (⊤ ∖ ↑lftN) with "[-]"); try done.
    iDestruct ("Hend" with "Htok") as "$". by wp_seq.
    iIntros (v) "[#Hκ _]". by iApply fupd_mask_mono; last iApply "Hextr".
  Qed.

  Lemma typed_alloc ρ (n : nat):
    0 < n → typed_step_ty ρ (Alloc #n) (own 1 (Π(replicate n uninit))).
  Proof.
    iIntros (Hn tid) "!#(#HEAP&_&_&$)". wp_alloc l vl as "H↦" "H†". iIntros "!>".
    iExists _. iSplit. done. iNext. rewrite Nat2Z.id. iSplitR "H†".
    - iExists vl. iFrame.
      match goal with H : Z.of_nat n = Z.of_nat (length vl) |- _ => rename H into Hlen end.
      clear Hn. apply (inj Z.of_nat) in Hlen. subst.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - assert (ty_size (Π (replicate n uninit)) = n) as ->; last done.
      clear. simpl. induction n. done. rewrite /= IHn //.
  Qed.

  Lemma typed_free ty (ν : expr):
    typed_step (ν ◁ own 1 ty) (Free #ty.(ty_size) ν) (λ _, top).
  Proof.
    iIntros (tid) "!#(#HEAP&_&H◁&$)". wp_bind ν.
    iApply (has_type_wp with "[$H◁]"). iIntros (v) "_ H◁ !>".
    rewrite has_type_value.
    iDestruct "H◁" as (l) "(Hv & H↦∗: & >H†)". iDestruct "Hv" as %[=->].
    iDestruct "H↦∗:" as (vl) "[>H↦ Hown]".
    rewrite ty_size_eq. iDestruct "Hown" as ">%". wp_free; eauto.
  Qed.

  Definition consumes (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, mgmtE ∪ ↑lrustN ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗ tl_own tid ⊤ -∗
      (∀ (l:loc) vl q,
        (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗{q} vl ∗
         |={E}▷=> (ty.(ty_own) tid vl ∗ (l ↦∗{q} vl ={E}=∗ ρ2 ν tid ∗ tl_own tid ⊤)))
       -∗ Φ #l)
      -∗ WP ν @ E {{ Φ }}.

  Lemma consumes_copy_own ty q:
    ty.(ty_dup) → consumes ty (λ ν, ν ◁ own q ty)%P (λ ν, ν ◁ own q ty)%P.
  Proof.
    iIntros (? ν tid Φ E ?) "_ H◁ Htl HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦!>".
    rewrite /has_type Hνv. iExists _. iSplit. done. iFrame. iExists vl. eauto.
  Qed.

  Lemma consumes_move ty q:
    consumes ty (λ ν, ν ◁ own q ty)%P
             (λ ν, ν ◁ own q (Π(replicate ty.(ty_size) uninit)))%P.
  Proof.
    iIntros (ν tid Φ E ?) "_ H◁ Htl HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">Hlen".
      by rewrite ty.(ty_size_eq). iDestruct "Hlen" as %Hlen.
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦!>".
    rewrite /has_type Hνv. iExists _. iSplit. done. iSplitR "H†".
    - rewrite -Hlen. iExists vl. iIntros "{$H↦}!>". clear.
      iInduction vl as [|v vl] "IH". done.
      iExists [v], vl. iSplit. done. by iSplit.
    - assert (ty_size (Π (replicate (ty_size ty) uninit)) = ty_size ty) as ->; last by auto.
      clear. induction ty.(ty_size). done. by apply (f_equal S).
  Qed.

  Lemma consumes_copy_uniq_bor ty κ κ' q:
    ty.(ty_dup) →
    consumes ty (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &uniq{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (? ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l') "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[H↦ Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma consumes_copy_shr_bor ty κ κ' q:
    ty.(ty_dup) →
    consumes ty (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
                (λ ν, ν ◁ &shr{κ}ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (? ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) Htl HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l') "[Heq #Hshr]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    rewrite (union_difference_L (↑lrustN) ⊤); last done.
    setoid_rewrite ->tl_own_union; try set_solver. iDestruct "Htl" as "[Htl ?]".
    iMod (ty_shr_acc with "LFT Hshr [$Htok $Htl]") as (q'') "[H↦ Hclose']"; try set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iApply "HΦ". iFrame "∗#%". iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[Htok $]". iExists _; by iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma typed_deref ty ρ1 ρ2 (ν:expr) :
    ty.(ty_size) = 1%nat → consumes ty ρ1 ρ2 →
    typed_step (ρ1 ν) (!ν) (λ v, v ◁ ty ∗ ρ2 ν)%P.
  Proof.
    iIntros (Hsz Hconsumes tid) "!#(#HEAP & #LFT & Hρ1 & Htl)". wp_bind ν.
    iApply (Hconsumes with "LFT Hρ1 Htl"). done. iFrame. iIntros (l vl q) "(%&%&H↦&>Hupd)".
    rewrite ->Hsz in *. destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_read. rewrite /sep has_type_value.
    iMod "Hupd" as "[$ Hclose]". by iApply "Hclose".
  Qed.

  Lemma typed_deref_uniq_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &uniq{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_acc_strong with "LFT H↦ Htok") as (κ0) "(#Hκκ0 & H↦ & Hclose')". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & Hown & H†)".
    subst. rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose'" with "*[H↦ Hown H†][]") as "[Hbor Htok]"; last 1 first.
    - iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod (bor_sep with "LFT Hbor") as "[_ Hbor]". done.
      iMod ("Hclose" with "Htok") as "$". iFrame "#". iExists _.
      iIntros "!>". iSplit. done. iApply (bor_shorten with "Hκκ0 Hbor").
    - iFrame "H↦ H† Hown".
    - iIntros "!>(?&?&?)_!>". iNext. iExists _.
      rewrite -heap_mapsto_vec_singleton. iFrame. iExists _. by iFrame.
  Qed.

  Lemma typed_deref_shr_bor_own ty ν κ κ' q q':
    typed_step (ν ◁ &shr{κ} own q' ty ∗ κ' ⊑ κ ∗ q.[κ'])
               (!ν)
               (λ v, v ◁ &shr{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑ & Htok) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q'') "[[Htok1 Htok2] Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iSpecialize ("Hown" $! _ with "Htok2").
    iApply wp_strong_mono. reflexivity. iSplitL "Hclose Hclose'"; last first.
    - iApply (wp_frame_step_l _ (↑heapN) _ (λ v, l ↦{q'''} v ∗ ⌜v = #vl⌝)%I); try done.
      iSplitL "Hown"; last by wp_read; eauto.
      iApply step_fupd_mask_mono; last iApply (step_fupd_mask_frame_r _ _ (↑heapN));
        last iApply "Hown"; (set_solver || rewrite !disjoint_union_l; solve_ndisj).
    - iIntros (v) "([#Hshr Htok] & H↦ & %)". subst.
      iMod ("Hclose'" with "[$H↦]") as "Htok'".
      iMod ("Hclose" with "[$Htok $Htok']") as "$".
      iFrame "#". iExists _. eauto.
  Qed.

  Lemma typed_deref_uniq_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &uniq{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &uniq{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑1 Htok") as (q'') "[Htok Hclose]". done.
    iMod (bor_exists with "LFT H↦") as (vl) "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[Heq Hbor]". done.
    iMod (bor_persistent with "LFT Heq Htok") as "[>% Htok]". done. subst.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    rewrite heap_mapsto_vec_singleton.
    iApply (wp_strong_mono ⊤ ⊤ _ (λ v, _ ∗ ⌜v = #l'⌝ ∗ l ↦#l')%I). done.
    iSplitR "Hbor H↦"; last first.
    - iApply (wp_frame_step_l _ (⊤ ∖ ↑lftN) with "[-]"); try done; last first.
      iSplitL "Hbor". by iApply (bor_unnest with "LFT Hbor"). wp_read. auto.
    - iIntros (v) "(Hbor & % & H↦)". subst.
      iMod ("Hclose'" with "[$H↦]") as "[H↦ Htok]".
      iMod ("Hclose" with "Htok") as "$". iFrame "#".
      iExists _. iSplitR. done. iApply (bor_shorten with "[] Hbor").
      iApply (lft_incl_glb with "H⊑2"). iApply lft_incl_refl.
  Qed.

  Lemma typed_deref_shr_bor_bor ty ν κ κ' κ'' q:
    typed_step (ν ◁ &shr{κ'} &uniq{κ''} ty ∗ κ ⊑ κ' ∗ q.[κ] ∗ κ' ⊑ κ'')
               (!ν)
               (λ v, v ◁ &shr{κ'} ty ∗ κ ⊑ κ' ∗ q.[κ])%P.
  Proof.
    iIntros (tid) "!#(#HEAP & #LFT & (H◁ & #H⊑1 & Htok & #H⊑2) & $)". wp_bind ν.
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁!>". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "[Heq Hshr]".
    iDestruct "Heq" as %[=->]. iDestruct "Hshr" as (l') "[H↦ Hown]".
    iMod (lft_incl_acc with "H⊑1 Htok") as (q') "[[Htok1 Htok2] Hclose]". done.
    iMod (frac_bor_acc with "LFT H↦ Htok1") as (q'') "[>H↦ Hclose']". done.
    iAssert (κ' ⊑ κ'' ∪ κ')%I as "#H⊑3".
    { iApply (lft_incl_glb with "H⊑2 []"). iApply lft_incl_refl. }
    iMod (lft_incl_acc with "H⊑3 Htok2") as (q''') "[Htok Hclose'']". done.
    iSpecialize ("Hown" $! _ with "Htok").
    iApply wp_strong_mono. reflexivity. iSplitL "Hclose Hclose' Hclose''"; last first.
    - iApply (wp_frame_step_l _ (↑heapN) _ (λ v, l ↦{q''} v ∗ ⌜v = #l'⌝)%I); try done.
      iSplitL "Hown"; last by wp_read; eauto.
      iApply step_fupd_mask_mono; last iApply (step_fupd_mask_frame_r _ _ (↑heapN));
        last iApply "Hown"; (set_solver || rewrite ?disjoint_union_l; solve_ndisj).
    - iIntros (v) "([#Hshr Htok] & H↦ & %)". subst.
      iMod ("Hclose''" with "Htok") as "Htok".
      iMod ("Hclose'" with "[$H↦]") as "Htok'".
      iMod ("Hclose" with "[$Htok $Htok']") as "$". iFrame "#". iExists _.
      iSplitL. done. by iApply (ty_shr_mono with "LFT H⊑3 Hshr").
  Qed.

  Definition update (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, mgmtE ∪ (↑lrustN) ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗
      (∀ (l:loc) vl,
         (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗ vl ∗
           ∀ vl', l ↦∗ vl' ∗ ▷ (ty.(ty_own) tid vl') ={E}=∗ ρ2 ν tid) -∗ Φ #l) -∗
      WP ν @ E {{ Φ }}.

  Lemma update_strong ty1 ty2 q:
    ty1.(ty_size) = ty2.(ty_size) →
    update ty1 (λ ν, ν ◁ own q ty2)%P (λ ν, ν ◁ own q ty1)%P.
  Proof.
    iIntros (Hsz ν tid Φ E ?) "_ H◁ HΦ". iApply (has_type_wp with "H◁").
    iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦ & >H†)".
    iDestruct "Heq" as %[= ->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    rewrite ty2.(ty_size_eq) -Hsz. iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%".
    iIntros (vl') "[H↦ Hown']!>". rewrite /has_type Hνv.
    iExists _. iSplit. done. iFrame. iExists _. iFrame.
  Qed.

  Lemma update_weak ty q κ κ':
    update ty (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P
              (λ ν, ν ◁ &uniq{κ} ty ∗ κ' ⊑ κ ∗ q.[κ'])%P.
  Proof.
    iIntros (ν tid Φ E ?) "#LFT (H◁ & #H⊑ & Htok) HΦ".
    iApply (has_type_wp with "H◁"). iIntros (v) "Hνv H◁". iDestruct "Hνv" as %Hνv.
    rewrite has_type_value. iDestruct "H◁" as (l) "(Heq & H↦)". iDestruct "Heq" as %[=->].
    iMod (lft_incl_acc with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (bor_acc with "LFT H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iApply "HΦ". iFrame "∗%#". iIntros (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[Hbor Htok]". by iExists _; iFrame.
    iMod ("Hclose" with "Htok") as "$". rewrite /has_type Hνv. iExists _. eauto.
  Qed.

  Lemma typed_assign ρ1 ρ2 ty ν1 ν2:
    ty.(ty_size) = 1%nat → update ty ρ1 ρ2 →
    typed_step (ρ1 ν1 ∗ ν2 ◁ ty) (ν1 <- ν2) (λ _, ρ2 ν1).
  Proof.
    iIntros (Hsz Hupd tid) "!#(#HEAP & #LFT & [Hρ1 H◁] & $)". wp_bind ν1.
    iApply (Hupd with "LFT Hρ1"). done. iFrame. iIntros (l vl) "(%&%&H↦&Hupd)".
    rewrite ->Hsz in *. destruct vl as [|v[|]]; try done.
    wp_bind ν2. iApply (has_type_wp with "H◁"). iIntros (v') "% H◁!>".
    rewrite heap_mapsto_vec_singleton. wp_write.
    rewrite -heap_mapsto_vec_singleton has_type_value. iApply "Hupd". by iFrame.
  Qed.

  Lemma typed_memcpy ρ1 ρ1' ρ2 ρ2' ty ν1 ν2:
    update ty ρ1' ρ1 → consumes ty ρ2' ρ2 →
    typed_step (ρ1' ν1 ∗ ρ2' ν2) (ν1 <-{ty.(ty_size)} !ν2) (λ _, ρ1 ν1 ∗ ρ2 ν2)%P.
  Proof.
    iIntros (Hupd Hcons tid) "!#(#HEAP & #LFT & [H1 H2] & Htl)". wp_bind ν1.
    iApply (Hupd with "LFT H1"). done.
    iIntros (l vl) "(% & % & H↦ & Hupd)". wp_bind ν2.
    iApply (Hcons with "LFT H2 Htl"). done.
    iIntros (l' vl' q) "(% & % & H↦' & Hcons)". iApply wp_fupd.
    iMod "Hcons". iApply (wp_memcpy with "[$HEAP $H↦' $H↦]"); try done. iNext.
    iIntros "[H↦ H↦']". iMod "Hcons" as "[Hown' Hcons]".
    iMod ("Hcons" with "H↦'") as "[$$]". iApply "Hupd". by iFrame.
  Qed.

  Lemma typed_weaken ρ1 ρ2 e:
    typed_program ρ2 e → (ρ1 ⇒ ρ2) → typed_program ρ1 e.
  Proof.
    iIntros (Hρ2 Hρ12 tid) "!#(#HEAP & #LFT & Hρ1 & Htl)".
    iMod (Hρ12 with "LFT Hρ1"). iApply Hρ2. iFrame "∗#".
  Qed.

  Lemma typed_program_exists {A} ρ θ e:
    (∀ x:A, typed_program (ρ ∗ θ x) e) →
    typed_program (ρ ∗ ∃ x, θ x) e.
  Proof.
    iIntros (Hwt tid) "!#(#HEAP & #LFT & [Hρ Hθ] & ?)". iDestruct "Hθ" as (x) "Hθ".
    iApply Hwt. iFrame "∗#".
  Qed.

  Lemma typed_step_program ρ θ e K:
    typed_step ρ e θ →
    (∀ v, typed_program (θ v) (fill K (of_val v))) →
    typed_program ρ (fill K e).
  Proof.
    iIntros (He HK tid) "!#(#HEAP & #LFT & Hρ & Htl)".
    iApply wp_bind. iApply wp_wand_r. iSplitL. iApply He; iFrame "∗#".
    iIntros (v) "[Hθ Htl]". iApply HK. iFrame "∗#".
  Qed.

  Lemma typed_if ρ e1 e2 ν:
    typed_program ρ e1 → typed_program ρ e2 →
    typed_program (ρ ∗ ν ◁ bool) (if: ν then e1 else e2).
  Proof.
    iIntros (He1 He2 tid) "!#(#HEAP & #LFT & [Hρ H◁] & Htl)".
    wp_bind ν. iApply (has_type_wp with "H◁"). iIntros (v) "% H◁!>".
    rewrite has_type_value. iDestruct "H◁" as (b) "Heq". iDestruct "Heq" as %[= ->].
    wp_if. destruct b; iNext. iApply He1; iFrame "∗#". iApply He2; iFrame "∗#".
  Qed.

End typing.
