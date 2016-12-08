From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.lang Require Export proofmode notation.
From lrust.lifetime Require Import borrow frac_borrow.

Section perm.
  Context `{iris_typeG Σ}.

  Definition perm {Σ} := na_inv_pool_name → iProp Σ.

  Fixpoint eval_expr (ν : expr) : option val :=
    match ν with
    | BinOp OffsetOp e (Lit (LitInt n)) =>
      match eval_expr e with
      | Some (#(LitLoc l)) => Some (#(shift_loc l n))
      | _ => None
      end
    | e => to_val e
    end.

  Definition has_type (ν : expr) (ty : type) : perm := λ tid,
    from_option (λ v, ty.(ty_own) tid [v]) False%I (eval_expr ν).

  Definition extract (κ : lft) (ρ : perm) : perm :=
    λ tid, ([†κ] ={↑lftN}=∗ ρ tid)%I.

  Definition tok (κ : lft) (q : Qp) : perm :=
    λ _, q.[κ]%I.


  Definition killable (κ : lft) : perm :=
    λ _, (□ (1.[κ] ={⊤,⊤∖↑lftN}▷=∗ [†κ]))%I.

  Definition incl (κ κ' : lft) : perm :=
    λ _, (κ ⊑ κ')%I.

  Definition exist {A : Type} (P : A -> perm) : @perm Σ :=
    λ tid, (∃ x, P x tid)%I.

  Definition sep (ρ1 ρ2 : perm) : @perm Σ :=
    λ tid, (ρ1 tid ∗ ρ2 tid)%I.

  Global Instance top : Top (@perm Σ) :=
    λ _, True%I.

  Definition perm_incl (ρ1 ρ2 : perm) :=
    ∀ tid, lft_ctx -∗ ρ1 tid ={⊤}=∗ ρ2 tid.

  Global Instance perm_equiv : Equiv perm :=
    λ ρ1 ρ2, perm_incl ρ1 ρ2 ∧ perm_incl ρ2 ρ1.

  Definition borrowing κ (ρ ρ1 ρ2 : perm) :=
    ∀ tid, lft_ctx -∗ ρ tid -∗ ρ1 tid ={⊤}=∗ ρ2 tid ∗ extract κ ρ1 tid.
End perm.

Delimit Scope perm_scope with P.
Bind Scope perm_scope with perm.

Notation "ν ◁ ty" := (has_type ν%E ty)
  (at level 75, right associativity) : perm_scope.

Notation "κ ∋ ρ" := (extract κ ρ)
  (at level 75, right associativity) : perm_scope.

Notation "q .[ κ ]" := (tok κ q) (format "q .[ κ ]", at level 0) : perm_scope.

Notation "† κ" := (killable κ) (format "† κ", at level 75).

Infix "⊑" := incl (at level 70) : perm_scope.

Notation "∃ x .. y , P" :=
  (exist (λ x, .. (exist (λ y, P)) ..)) : perm_scope.

Infix "∗" := sep (at level 80, right associativity) : perm_scope.

Infix "⇒" := perm_incl (at level 95, no associativity) : C_scope.
Notation "(⇒)" := perm_incl (only parsing) : C_scope.

Notation "ρ1 ⇔ ρ2" := (equiv (A:=perm) ρ1%P ρ2%P)
   (at level 95, no associativity) : C_scope.
Notation "(⇔)" := (equiv (A:=perm)) (only parsing) : C_scope.

Section duplicable.
  Context `{iris_typeG Σ}.

  Class Duplicable (ρ : @perm Σ) :=
    duplicable_persistent tid : PersistentP (ρ tid).
  Global Existing Instance duplicable_persistent.

  Global Instance has_type_dup v ty : Copy ty → Duplicable (v ◁ ty).
  Proof. intros Hdup tid. apply _. Qed.

  Global Instance lft_incl_dup κ κ' : Duplicable (κ ⊑ κ').
  Proof. intros tid. apply _. Qed.

  Global Instance sep_dup P Q :
    Duplicable P → Duplicable Q → Duplicable (P ∗ Q).
  Proof. intros HP HQ tid. apply _. Qed.

  Global Instance top_dup : Duplicable ⊤.
  Proof. intros tid. apply _. Qed.
End duplicable.

Section has_type.
  Context `{iris_typeG Σ}.

  Lemma has_type_value (v : val) ty tid :
    (v ◁ ty)%P tid ⊣⊢ ty.(ty_own) tid [v].
  Proof.
    destruct v as [|f xl e ?]. done.
    unfold has_type, eval_expr, of_val.
    assert (Rec f xl e = RecV f xl e) as -> by done. by rewrite to_of_val.
  Qed.

  Lemma has_type_wp E (ν : expr) ty tid (Φ : val -> iProp _) :
    (ν ◁ ty)%P tid -∗
    (∀ (v : val), ⌜eval_expr ν = Some v⌝ -∗ (v ◁ ty)%P tid ={E}=∗ Φ v) -∗
    WP ν @ E {{ Φ }}.
  Proof.
    iIntros "H◁ HΦ". setoid_rewrite has_type_value. unfold has_type.
    destruct (eval_expr ν) eqn:EQν; last by iDestruct "H◁" as "[]". simpl.
    iMod ("HΦ" $! v with "[] H◁") as "HΦ". done.
    iInduction ν as [| | |[] e ? [|[]| | | | | | | | | |] _| | | | | | | |] "IH"
      forall (Φ v EQν); try done.
    - inversion EQν. subst. wp_value. auto.
    - wp_value. auto.
    - wp_bind e. simpl in EQν. destruct (eval_expr e) as [[[|l|]|]|]; try done.
      iApply ("IH" with "[] [HΦ]"). done. simpl. wp_op. inversion EQν. eauto.
  Qed.
End has_type.

Section perm_incl.
  Context `{iris_typeG Σ}.

  (* Properties *)
  Global Instance perm_incl_preorder : PreOrder (⇒).
  Proof.
    split.
    - iIntros (? tid) "H". eauto.
    - iIntros (??? H12 H23 tid) "#LFT H". iApply (H23 with "LFT >").
      by iApply (H12 with "LFT").
  Qed.

  Global Instance perm_equiv_equiv : Equivalence (⇔).
  Proof.
    split.
    - by split.
    - by intros x y []; split.
    - intros x y z [] []. split; by transitivity y.
  Qed.

  Global Instance perm_incl_proper :
    Proper ((⇔) ==> (⇔) ==> iff) (⇒).
  Proof. intros ??[??]??[??]; split; intros ?; by simplify_order. Qed.

  Global Instance perm_sep_proper :
    Proper ((⇔) ==> (⇔) ==> (⇔)) (sep).
  Proof.
    intros ??[A B]??[C D]; split; iIntros (tid) "#LFT [A B]".
    iMod (A with "LFT A") as "$". iApply (C with "LFT B").
    iMod (B with "LFT A") as "$". iApply (D with "LFT B").
  Qed.

  Lemma uPred_equiv_perm_equiv ρ θ : (∀ tid, ρ tid ⊣⊢ θ tid) → (ρ ⇔ θ).
  Proof. intros Heq. split=>tid; rewrite Heq; by iIntros. Qed.

  Lemma perm_incl_top ρ : ρ ⇒ ⊤.
  Proof. iIntros (tid) "H". eauto. Qed.

  Lemma perm_incl_frame_l ρ ρ1 ρ2 : ρ1 ⇒ ρ2 → ρ ∗ ρ1 ⇒ ρ ∗ ρ2.
  Proof. iIntros (Hρ tid) "#LFT [$?]". by iApply (Hρ with "LFT"). Qed.

  Lemma perm_incl_frame_r ρ ρ1 ρ2 :
    ρ1 ⇒ ρ2 → ρ1 ∗ ρ ⇒ ρ2 ∗ ρ.
  Proof. iIntros (Hρ tid) "#LFT [?$]". by iApply (Hρ with "LFT"). Qed.

  Lemma perm_incl_exists_intro {A} P x : P x ⇒ ∃ x : A, P x.
  Proof. iIntros (tid) "_ H!>". by iExists x. Qed.

  Global Instance perm_sep_assoc : Assoc (⇔) sep.
  Proof. intros ???; split. by iIntros (tid) "_ [$[$$]]". by iIntros (tid) "_ [[$$]$]". Qed.

  Global Instance perm_sep_comm : Comm (⇔) sep.
  Proof. intros ??; split; by iIntros (tid) "_ [$$]". Qed.

  Global Instance perm_top_right_id : RightId (⇔) ⊤ sep.
  Proof. intros ρ; split. by iIntros (tid) "_ [? _]". by iIntros (tid) "_ $". Qed.

  Global Instance perm_top_left_id : LeftId (⇔) ⊤ sep.
  Proof. intros ρ. by rewrite comm right_id. Qed.

  Lemma perm_incl_duplicable ρ (_ : Duplicable ρ) : ρ ⇒ ρ ∗ ρ.
  Proof. iIntros (tid) "_ #H!>". by iSplit. Qed.

  Lemma perm_tok_plus κ q1 q2 :
    tok κ q1 ∗ tok κ q2 ⇔ tok κ (q1 + q2).
  Proof. rewrite /tok /sep /=; split; by iIntros (tid) "_ [$$]". Qed.

  Lemma perm_lftincl_refl κ : ⊤ ⇒ κ ⊑ κ.
  Proof. iIntros (tid) "_ _!>". iApply lft_incl_refl. Qed.

  Lemma perm_lftincl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 ∗ κ2 ⊑ κ3 ⇒ κ1 ⊑ κ3.
  Proof. iIntros (tid) "_ [#?#?]!>". iApply (lft_incl_trans with "[] []"); auto. Qed.

  Lemma borrowing_perm_incl κ ρ ρ1 ρ2 θ :
    borrowing κ ρ ρ1 ρ2 → ρ ∗ κ ∋ θ ∗ ρ1 ⇒ ρ2 ∗ κ ∋ (θ ∗ ρ1).
  Proof.
    iIntros (Hbor tid) "LFT (Hρ&Hθ&Hρ1)". iMod (Hbor with "LFT Hρ Hρ1") as "[$ Hρ1]".
    iIntros "!>#H†". iSplitL "Hθ". by iApply "Hθ". by iApply "Hρ1".
  Qed.

  Lemma lftincl_borrowing κ κ' q : borrowing κ ⊤ q.[κ'] (κ ⊑ κ').
  Proof.
    iIntros (tid) "#LFT _ Htok". iApply (fupd_mask_mono (↑lftN)). done.
    iMod (bor_create with "LFT [$Htok]") as "[Hbor Hclose]". done.
    iMod (bor_fracture (λ q', (q * q').[κ'])%I with "LFT [Hbor]") as "Hbor". done.
    { by rewrite Qp_mult_1_r. }
    iSplitL "Hbor". iApply (frac_bor_incl with "LFT Hbor").
    iIntros "!>H". by iMod ("Hclose" with "H") as ">$".
  Qed.
End perm_incl.
