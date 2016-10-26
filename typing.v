From iris.program_logic Require Import thread_local hoare.
From lrust Require Export type perm notation.
From lrust Require Import type_incl perm_incl proofmode.

Import Types Perm.

Section typing.

  Context `{heapG Σ, lifetimeG Σ, thread_localG Σ}.

  (* TODO : good notations for [typed_step] and [typed_step_ty] ? *)
  Definition typed_step (ρ : perm) e (θ : Valuable.t → perm) :=
    ∀ tid,
      heap_ctx ⊢ {{ ρ tid ★ tl_own tid ⊤ }} e {{ v, θ (Some v) tid ★ tl_own tid ⊤ }}.

  (* FIXME : why isn't the notation context on the last parameter not
     taken into account? *)
  Arguments typed_step _%P _%E _%P.

  Definition typed_step_ty (ρ : perm) e ty :=
    typed_step ρ e (λ ν, ν ◁ ty)%P.

  Definition typed_program (ρ : perm) e :=
    ∀ tid, heap_ctx ⊢  {{ ρ tid ★ tl_own tid ⊤ }} e {{ v, False }}.

  Lemma typed_step_frame ρ e θ ξ:
    typed_step ρ e θ → typed_step (ρ ★ ξ) e (λ ν, θ ν ★ ξ)%P.
  Proof.
    iIntros (Hwt tid) "#HEAP!#[[?$]?]". iApply (Hwt with "HEAP"). by iFrame.
  Qed.

  Lemma typed_step_exists {A} ρ θ e ξ:
    (∀ x:A, typed_step (ρ ★ θ x) e ξ) →
    typed_step (ρ ★ ∃ x, θ x) e ξ.
  Proof.
    iIntros (Hwt tid) "#HEAP!#[[Hρ Hθ]?]". iDestruct "Hθ" as (x) "Hθ".
    iApply (Hwt with "HEAP"). by iFrame.
  Qed.

  Lemma typed_step_bool ρ (b:Datatypes.bool) :
    typed_step_ty ρ #b bool.
  Proof. iIntros (tid) "_!#[_$]". wp_value. simpl. eauto. Qed.

  Lemma typed_step_int ρ (z:Datatypes.nat) :
    typed_step_ty ρ #z int.
  Proof. iIntros (tid) "_!#[_$]". wp_value. simpl. eauto. Qed.

  Lemma typed_step_fn {A n} `{Duplicable _ ρ, Closed (f :b: xl +b+ []) e} θ :
    length xl = n →
    (∀ (a : A) (vl : vec val n) (fv : val) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (Some fv ◁ fn θ ★ (θ a vl) ★ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (fn θ).
  Proof.
    iIntros (Hn He tid) "#HEAP !# [#Hρ $]". iApply (wp_value _ _ _ (RecV f xl e)).
    { simpl. destruct decide as [CL|?]. repeat f_equal. apply proof_irrel. done. }
    iLöb as "IH". iExists _. iSplit. done. iIntros (a vl) "!#[Hθ?]".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply (He with "HEAP"). done. by iFrame "★#".
  Qed.

  Lemma typed_step_cont {n} `{Closed (f :b: xl +b+ []) e} ρ θ :
    length xl = n →
    (∀ (vl : vec val n) (fv : val) e',
        subst_l xl (map of_val vl) e = Some e' →
        typed_program (Some fv ◁ cont (λ vl, ρ ★ θ vl)%P ★ (θ vl) ★ ρ) (subst' f fv e')) →
    typed_step_ty ρ (Rec f xl e) (cont θ).
  Proof.
    iIntros (Hn He tid) "#HEAP !# [Hρ $]". iApply (wp_value _ _ _ (RecV f xl e)).
    { simpl. destruct decide as [CL|?]. repeat f_equal. apply proof_irrel. done. }
    iLöb as "IH". iExists _. iSplit. done. iIntros (vl) "Hθ ?".
    assert (is_Some (subst_l xl (map of_val vl) e)) as [e' He'].
    { clear -Hn. revert xl Hn e. induction vl=>-[|x xl] //=. by eauto.
      intros ? e. edestruct IHvl as [e' ->]. congruence. eauto. }
    iApply wp_rec; try done.
    { apply List.Forall_forall=>?. rewrite in_map_iff=>-[?[<- _]].
      rewrite to_of_val. eauto. }
    iNext. iApply (He with "HEAP"). done. iFrame. simpl.
    iExists _. iSplit. done. iIntros (vl') "[Hρ Hθ] Htl".
    iDestruct ("IH" with "Hρ") as (f') "[Hf' IH']".
    iDestruct "Hf'" as %[=<-]. iApply ("IH'" with "Hθ Htl").
  Qed.

  Lemma typed_step_valuable e ty:
    typed_step_ty (Valuable.of_expr e ◁ ty) e ty.
  Proof.
    iIntros (tid) "_!#[H$]".
    destruct (Valuable.of_expr e) as [v|] eqn:Hv. 2:by iDestruct "H" as "[]".
    by iApply Valuable.of_expr_wp.
  Qed.

  Lemma typed_step_plus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ★ ρ2) (BinOp PlusOp e1 e2) int.
  Proof.
    iIntros (He1 He2 tid) "#HEAP!#[[H1 H2]?]".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply (He1 with "HEAP"); by iFrame.
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply (He2 with "HEAP"); by iFrame.
    iIntros (v2) "[Hv2?]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. iFrame. by iExists _.
  Qed.

  Lemma typed_step_minus e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ★ ρ2) (BinOp MinusOp e1 e2) int.
  Proof.
    iIntros (He1 He2 tid) "#HEAP!#[[H1 H2]?]".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply (He1 with "HEAP"); by iFrame.
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply (He2 with "HEAP"); by iFrame.
    iIntros (v2) "[Hv2?]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    wp_op. iFrame. by iExists _.
  Qed.

  Lemma typed_step_le e1 e2 ρ1 ρ2:
    typed_step_ty ρ1 e1 int → typed_step_ty ρ2 e2 int →
    typed_step_ty (ρ1 ★ ρ2) (BinOp LeOp e1 e2) bool.
  Proof.
    iIntros (He1 He2 tid) "#HEAP!#[[H1 H2]?]".
    wp_bind e1. iApply wp_wand_r. iSplitR "H2". iApply (He1 with "HEAP"); by iFrame.
    iIntros (v1) "[Hv1?]". iDestruct "Hv1" as (z1) "Hz1". iDestruct "Hz1" as %[=->].
    wp_bind e2. iApply wp_wand_r. iSplitL. iApply (He2 with "HEAP"); by iFrame.
    iIntros (v2) "[Hv2?]". iDestruct "Hv2" as (z2) "Hz2". iDestruct "Hz2" as %[=->].
    iFrame. wp_op; intros _; by iExists _.
  Qed.

  Lemma typed_step_newlft ρ:
    typed_step ρ Newlft (λ _, ∃ α, [α]{1} ★ α ∋ top)%P.
  Proof.
    iIntros (tid) "_!#[_$]". wp_value. iMod lft_begin as (α) "[?#?]". done.
    iMod (lft_borrow_create with "[][]") as "[_?]". done. done.
    2:by iModIntro; iExists α; iFrame. eauto.
  Qed.

  Lemma typed_step_endlft κ ρ:
    typed_step (κ ∋ ρ ★ [κ]{1}) Endlft (λ _, ρ)%P.
  Proof.
    iIntros (tid) "_!#[[Hextr [Htok #Hlft]]$]".
    wp_bind (#() ;; #())%E.
    iApply (wp_wand_r _ _ (λ _, _ ★ True)%I). iSplitR "Hextr".
    iApply (wp_frame_step_l with "[-]"); try done.
    iDestruct (lft_end with "Hlft Htok") as "$". by wp_seq.
    iIntros (v) "[#Hκ _]". iMod (lft_extract_out with "Hκ Hextr"). done.
    by wp_seq.
  Qed.

  Lemma typed_step_alloc ρ (n : nat):
    0 < n → typed_step_ty ρ (Alloc #n) (own 1 (uninit n)).
  Proof.
    iIntros (? tid) "#HEAP!#[_$]". wp_alloc l vl as "H↦" "H†". iIntros "!>".
    iExists _. iSplit. done. iNext. rewrite Nat2Z.id. iFrame.
    apply (inj Z.of_nat) in H3. iExists _. iFrame. eauto.
  Qed.

  Lemma typed_step_free ty e:
    typed_step (Valuable.of_expr e ◁ own 1 ty) (Free #ty.(ty_size) e) (λ _, top).
  Proof.
    iIntros (tid) "#HEAP!#[Hown$]".
    destruct (Valuable.of_expr e) as [v|] eqn:EQv; last by iDestruct "Hown" as "[]".
    wp_bind e. iApply Valuable.of_expr_wp. done.
    iDestruct "Hown" as (l) "(Hv & >H† & H↦★:)". iDestruct "Hv" as %[=->].
    iDestruct "H↦★:" as (vl) "[>H↦ Hown]".
    rewrite ty_size_eq. iDestruct "Hown" as ">%". wp_free; eauto.
  Qed.

  Definition consumes (ty : type) (ρ1 ρ2 : Valuable.t → perm) : Prop :=
    ∀ v tid, ρ1 v tid ★ tl_own tid ⊤ ={mgmtE ∪ lrustN}=★
      ∃ (l : loc) vl q, v = Some #l ★ length vl = ty.(ty_size) ★ l ↦★{q} vl ★
        |={mgmtE ∪ lrustN}▷=> (ty.(ty_own) tid vl ★
           (l ↦★{q} vl ={mgmtE ∪ lrustN}=★ ρ2 v tid ★ tl_own tid ⊤)).
  (* FIXME : why isn't the notation context on the two last parameters not
     taken into account? *)
  Arguments consumes _%T _%P _%P.

  Lemma consumes_copy_own ty q:
    ty.(ty_dup) → consumes ty (λ ν, ν ◁ own q ty)%P (λ ν, ν ◁ own q ty)%P.
  Proof.
    iIntros (? [v|] tid) "[Hown Htl]"; last by iDestruct "Hown" as "[]".
    iDestruct "Hown" as (l) "[Heq [>H† H↦]]".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ (length vl = ty_size ty))%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iExists _, _, _. iFrame "★#%". iSplit. done. iIntros "!>!>!>H↦!>".
    iExists _. iSplit. done. iFrame. iExists vl. eauto.
  Qed.

  Lemma consumes_move ty q:
    consumes ty (λ ν, ν ◁ own q ty)%P (λ ν, ν ◁ own q (uninit ty.(ty_size)))%P.
  Proof.
    iIntros ([v|] tid) "[Hown Htl]"; last by iDestruct "Hown" as "[]".
    iDestruct "Hown" as (l) "[Heq [>H† H↦]]".
    iDestruct "Heq" as %[=->]. iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iAssert (▷ (length vl = ty_size ty))%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iExists _, _, _. iFrame "★#%". iSplit. done. iIntros "!>!>!>H↦!>".
    iExists _. iSplit. done. iFrame. iExists vl. eauto.
  Qed.

  Lemma consumes_copy_uniq_borrow ty κ κ' q:
    ty.(ty_dup) →
    consumes ty (λ ν, ν ◁ &uniq{κ}ty ★ κ' ⊑ κ ★ [κ']{q})%P
                (λ ν, ν ◁ &uniq{κ}ty ★ κ' ⊑ κ ★ [κ']{q})%P.
  Proof.
    iIntros (? [v|] tid) "[(H◁ & #H⊑ & [Htok #Hκ']) Htl]"; last by iDestruct "H◁" as "[]".
    iDestruct "H◁" as (l') "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_trade with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    iMod (lft_borrow_open with "H↦ Htok") as "[H↦ Hclose']". set_solver.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ (length vl = ty_size ty))%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iExists _, _, _. iFrame "★#%". iSplit. done. iIntros "!>!>!>H↦".
    iMod (lft_borrow_close with "[H↦] Hclose'") as "[H↦ Htok]". set_solver.
    { iExists _. by iFrame. }
    iMod ("Hclose" with "Htok") as "$". iExists _. eauto.
  Qed.

  Lemma consumes_copy_shr_borrow ty κ κ' q:
    ty.(ty_dup) →
    consumes ty (λ ν, ν ◁ &shr{κ}ty ★ κ' ⊑ κ ★ [κ']{q})%P
                (λ ν, ν ◁ &shr{κ}ty ★ κ' ⊑ κ ★ [κ']{q})%P.
  Proof.
    iIntros (? [v|] tid) "[(H◁ & #H⊑ & [Htok #Hκ']) Htl]"; last by iDestruct "H◁" as "[]".
    iDestruct "H◁" as (l') "[Heq #Hshr]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_trade with "H⊑ Htok") as (q') "[Htok Hclose]". set_solver.
    rewrite (union_difference_L (nclose lrustN) ⊤); last done.
    setoid_rewrite ->tl_own_union; try set_solver.
    iDestruct "Htl" as "[Htl $]".
    iMod (ty_shr_acc with "Hshr [Htok Htl]") as (q'') "[H↦ Hclose']";
      try set_solver. by iFrame.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iAssert (▷ (length vl = ty_size ty))%I with "[#]" as ">%".
      by rewrite ty.(ty_size_eq).
    iModIntro. iExists _, _, _. iFrame "★#%". iSplit. done. iIntros "!>!>!>H↦".
    iMod ("Hclose'" with "[H↦]") as "[Htok $]".
    { iExists _. by iFrame. }
    iMod ("Hclose" with "Htok") as "$". iExists _. eauto.
  Qed.

  Lemma typed_step_deref ty ρ1 ρ2 e:
    ty.(ty_size) = 1%nat → consumes ty ρ1 ρ2 →
    typed_step (ρ1 (Valuable.of_expr e)) ( *e) (λ v, v ◁ ty ★ ρ2 (Valuable.of_expr e))%P.
  Proof.
    (* FIXME : I need to use [fupd_mask_mono], but I do not expect so. *)
    iIntros (Hsz Hconsumes tid) "#HEAP!#H". iApply fupd_wp. iApply fupd_mask_mono.
    2:iMod (Hconsumes with "H") as (l vl q) "(%&%&H↦&Hupd)". done.
    iMod "Hupd". iModIntro. wp_bind e. iApply Valuable.of_expr_wp. done.
    rewrite ->Hsz in *. destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_read.
    iApply fupd_mask_mono. 2:iMod "Hupd" as "[$ Hclose]". done.
    by iApply "Hclose".
  Qed.

  Lemma typed_step_deref_uniq_borrow_own ty e κ κ' q q':
    typed_step (Valuable.of_expr e ◁ &uniq{κ} own q' ty ★ κ' ⊑ κ ★ [κ']{q})
               ( *e)
               (λ v, v ◁ &uniq{κ} ty ★ κ' ⊑ κ ★ [κ']{q})%P.
  Proof.
    iIntros (tid) "#HEAP !# [(H◁ & #H⊑ & Htok & #Hκ') Htl]".
    destruct (Valuable.of_expr e) eqn:He; last by iDestruct "H◁" as "[]".
    iDestruct "H◁" as (l) "[Heq H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_trade with "H⊑ Htok") as (q'') "[Htok Hclose]". done.
    iMod (lft_borrow_open with "H↦ Htok") as "[H↦ Hclose']". done.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". iDestruct "Hown" as (l') "(>% & H† & Hown)".
    subst. rewrite heap_mapsto_vec_singleton.
    wp_bind e. iApply Valuable.of_expr_wp. done. wp_read.
    iMod (lft_borrow_close_stronger with "[H↦ H† Hown] Hclose' []") as "[Hbor Htok]". done.
    { iCombine "H†" "Hown" as "H". iCombine "H↦" "H" as "H". iNext. iExact "H". }
    { iIntros "!>(?&?&?)!>". iNext. rewrite -heap_mapsto_vec_singleton. iExists _.
      iFrame. iExists _. iSplit. done. by iFrame. }
    iMod (lft_borrow_split with "Hbor") as "[_ Hbor]". done.
    iMod (lft_borrow_split with "Hbor") as "[_ Hbor]". done.
    iMod ("Hclose" with "Htok"). iFrame "#★". iIntros "!>". iExists _. eauto.
  Qed.

  Lemma typed_step_deref_shr_borrow_own ty e κ κ' q q':
    typed_step (Valuable.of_expr e ◁ &shr{κ} own q' ty ★ κ' ⊑ κ ★ [κ']{q})
               ( *e)
               (λ v, v ◁ &shr{κ} ty ★ κ' ⊑ κ ★ [κ']{q})%P.
  Proof.
    iIntros (tid) "#HEAP !# [(H◁ & #H⊑ & Htok & #Hκ') Htl]".
    destruct (Valuable.of_expr e) eqn:He; last by iDestruct "H◁" as "[]".
    iDestruct "H◁" as (l) "[Heq #H↦]". iDestruct "Heq" as %[=->].
    iMod (lft_incl_trade with "H⊑ Htok") as (q'') "[[Htok1 Htok2] Hclose]". done.
    iDestruct "H↦" as (vl) "[H↦b Hown]".
    iMod (lft_frac_borrow_open with "[] H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    { iIntros "!#". iIntros (q1 q2). rewrite heap_mapsto_op_eq. iSplit; auto. }
    wp_bind e. iApply Valuable.of_expr_wp. done.
    iSpecialize ("Hown" $! _ with "Htok2").
    iApply wp_strong_mono. reflexivity. iSplitL "Htl Hclose Hclose'"; last first.
    - iApply (wp_frame_step_l _ heapN _ (λ v, l ↦{q'''} v ★ v = #vl)%I); try done.
      iSplitL "Hown"; last by wp_read; eauto.
      (* TODO : solving this goal is way too complicated compared
         to what actually happens. *)
      iAssert (|={mgmtE ∪ ⊤ ∖ (mgmtE ∪ lrustN), heapN}▷=> True)%I as "H".
      { iApply fupd_mono. iIntros "H!>"; iExact "H".
        iApply fupd_intro_mask; last done.
        assert (Hdisj:nclose heapN ⊥ (mgmtE ∪ lrustN)) by (rewrite !disjoint_union_r; solve_ndisj).
        set_solver. }
      rewrite {3 4}(union_difference_L (mgmtE ∪ lrustN) ⊤); last done.
      iApply fupd_trans. iApply fupd_mask_frame_r. set_solver.
      iMod "Hown". iModIntro. iMod "H". iModIntro. iNext.
      iMod "H". iApply fupd_mask_frame_r. set_solver. done.
    - iFrame "★#". iIntros (v) "[[#Hshr Htok][H↦ %]]". subst.
      iMod ("Hclose'" with "[H↦]") as "Htok'". by eauto.
      iCombine "Htok" "Htok'" as "Htok". iMod ("Hclose" with "Htok") as "$".
      iModIntro. iExists _. eauto.
  Qed.

End typing.
