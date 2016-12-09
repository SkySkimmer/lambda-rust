From iris.program_logic Require Import hoare.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import perm.
From lrust.lang Require Import proofmode.
From lrust.lifetime Require Import frac_borrow reborrow borrow creation.

Section typing.
  Context `{iris_typeG Σ}.

  (* TODO : good notations for [typed_step] and [typed_step_ty] ? *)
  Definition typed_step (ρ : perm) e (θ : val → perm) :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ na_own tid ⊤ }} e
           {{ v, θ v tid ∗ na_own tid ⊤ }}.

  Definition typed_step_ty (ρ : perm) e ty :=
    typed_step ρ e (λ ν, ν ◁ ty)%P.

  Definition typed_program (ρ : perm) e :=
    ∀ tid, {{ heap_ctx ∗ lft_ctx ∗ ρ tid ∗ na_own tid ⊤ }} e {{ _, False }}.

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

  Lemma typed_valuable (ν : expr) ty:
    typed_step_ty (ν ◁ ty) ν ty.
  Proof.
    iIntros (tid) "!#(_&_&H&$)". iApply (has_type_wp with "[$H]"). by iIntros (v) "_ $".
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
    rewrite /killable /extract. iIntros (tid) "!#(_&_&(Hextr&Htok&Hend)&$)".
    iDestruct ("Hend" with "Htok") as "Hend".
    iApply (wp_fupd_step with "Hend"); try done. wp_seq.
    iIntros "!>H†". by iApply fupd_mask_mono; last iApply "Hextr".
  Qed.

  Definition consumes (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, mgmtE ∪ ↑lrustN ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗ na_own tid ⊤ -∗
      (∀ (l:loc) vl q,
        (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗{q} vl ∗
         |={E}▷=> (ty.(ty_own) tid vl ∗ (l ↦∗{q} vl ={E}=∗ ρ2 ν tid ∗ na_own tid ⊤)))
       -∗ Φ #l)
      -∗ WP ν @ E {{ Φ }}.

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

  Definition update (ty : type) (ρ1 ρ2 : expr → perm) : Prop :=
    ∀ ν tid Φ E, mgmtE ∪ (↑lrustN) ⊆ E →
      lft_ctx -∗ ρ1 ν tid -∗
      (∀ (l:loc) vl,
         (⌜length vl = ty.(ty_size)⌝ ∗ ⌜eval_expr ν = Some #l⌝ ∗ l ↦∗ vl ∗
           ∀ vl', l ↦∗ vl' ∗ ▷ (ty.(ty_own) tid vl') ={E}=∗ ρ2 ν tid) -∗ Φ #l) -∗
      WP ν @ E {{ Φ }}.

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
    iApply (Hρ2 with ">"). iFrame "∗#". iApply (Hρ12 with "LFT Hρ1").
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
End typing.
