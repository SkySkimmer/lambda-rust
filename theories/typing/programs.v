From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation.
From lrust.lang Require Import proofmode.
From lrust.lifetime Require Import frac_borrow reborrow borrow creation.
From lrust.typing Require Export type lft_contexts type_context cont_context.

Section typing.
  Context `{typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body (E : elctx) (L : llctx) (C : cctx) (T : tctx)
                        (e : expr) : iProp Σ :=
    (∀ tid qE, heap_ctx -∗ lft_ctx -∗ na_own tid ⊤ -∗ elctx_interp E qE -∗ llctx_interp L 1 -∗
               (elctx_interp E qE -∗ cctx_interp tid C) -∗ tctx_interp tid T -∗
               WP e {{ _, cont_postcondition }})%I.
  Global Arguments typed_body _ _ _ _ _%E.

  Instance typed_body_llctx_permut E :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> (⊢)) (typed_body E).
  Proof.
    intros L1 L2 HL C ? <- T ? <- e ? <-. rewrite /typed_body. by setoid_rewrite HL.
  Qed.

  Instance typed_body_elctx_permut :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> eq ==> (⊢)) typed_body.
  Proof.
    intros E1 E2 HE L ? <- C ? <- T ? <- e ? <-. rewrite /typed_body. by setoid_rewrite HE.
  Qed.

  Instance typed_body_mono E L:
    Proper (flip (cctx_incl E) ==> flip (tctx_incl E L) ==> eq ==> (⊢)) (typed_body E L).
  Proof.
    intros C1 C2 HC T1 T2 HT e ? <-. iIntros "H".
    iIntros (tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iMod (HT with "LFT HE HL HT") as "(HE & HL & HT)".
    iApply ("H" with "HEAP LFT Htl HE HL [HC] HT").
    iIntros "HE". by iApply (HC with "LFT HC").
  Qed.

  (** Instruction *)
  Definition typed_instruction (E : elctx) (L : llctx)
             (T1 : tctx) (e : expr) (T2 : val → tctx) : Prop :=
    ∀ tid qE, heap_ctx -∗ lft_ctx -∗ na_own tid ⊤ -∗
              elctx_interp E qE -∗ llctx_interp L 1 -∗ tctx_interp tid T1 -∗ 
                   WP e {{ v, na_own tid ⊤ ∗ elctx_interp E qE ∗ llctx_interp L 1 ∗ tctx_interp tid (T2 v) }}.
  Global Arguments typed_instruction _ _ _ _%E _.

  (** Writing and Reading **)
  Definition typed_write (E : elctx) (L : llctx) (ty1 ty ty2 : type) : Prop :=
    ∀ v tid F qE qL, lftE ∪ (↑lrustN) ⊆ F →
      lft_ctx -∗ elctx_interp E qE -∗ llctx_interp L qL -∗ ty1.(ty_own) tid [v] ={F}=∗
        ∃ (l : loc) vl, ⌜length vl = ty.(ty_size) ∧ v = #l⌝ ∗ l ↦∗ vl ∗
          (▷ l ↦∗: ty.(ty_own) tid ={F}=∗
            elctx_interp E qE ∗ llctx_interp L qL ∗ ty2.(ty_own) tid [v]).

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read (E : elctx) (L : llctx) (ty1 ty ty2 : type) : Prop :=
    ∀ v tid F qE qL, lftE ∪ (↑lrustN) ⊆ F →
      lft_ctx -∗ na_own tid F -∗ elctx_interp E qE -∗ llctx_interp L qL -∗ ty1.(ty_own) tid [v] ={F}=∗
        ∃ (l : loc) vl q, ⌜v = #l⌝ ∗ l ↦∗{q} vl ∗ ▷ ty.(ty_own) tid vl ∗
          (l ↦∗{q} vl ={F}=∗ na_own tid F ∗ elctx_interp E qE ∗ llctx_interp L qL ∗ ty2.(ty_own) tid [v]).
End typing.

Notation typed_instruction_ty E L T1 e ty := (typed_instruction E L T1 e (λ v : val, [TCtx_hasty v ty])).

Section typing_rules.
  Context `{typeG Σ}.

  Lemma type_let E L T1 T2 T C xb e e' :
    Closed (xb :b: []) e' →
    typed_instruction E L T1 e T2 →
    (∀ v : val, typed_body E L C (T2 v ++ T) (subst' xb v e')) →
    typed_body E L C (T1 ++ T) (let: xb := e in e').
  Proof.
    iIntros (Hc He He' tid qE) "#HEAP #LFT Htl HE HL HC HT". rewrite tctx_interp_app.
    iDestruct "HT" as "[HT1 HT]". wp_bind e. iApply (wp_wand with "[HE HL HT1 Htl]").
    { iApply (He with "HEAP LFT Htl HE HL HT1"). }
    iIntros (v) "/= (Htl & HE & HL & HT2)". iApply wp_let; first wp_done. iModIntro.
    iApply (He' with "HEAP LFT Htl HE HL HC [HT2 HT]"). rewrite tctx_interp_app. by iFrame.
  Qed.
  
  Lemma type_assign E L ty1 ty ty1' p1 p2 :
    typed_write E L ty1 ty ty1' →
    typed_instruction E L [TCtx_hasty p1 ty1; TCtx_hasty p2 ty] (p1 <- p2)
                      (λ _, [TCtx_hasty p1 ty1']).
  Proof.
    iIntros (Hwrt tid qE) "#HEAP #LFT $ HE HL".
    rewrite tctx_interp_cons tctx_interp_singleton. iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "_ Hown2".
    iMod (Hwrt with "* LFT HE HL Hown1") as (l vl) "([% %] & Hl & Hclose)"; first done.
    subst v1. iAssert (⌜1%nat = ty_size ty⌝%I) with "[#]" as %Hsz.
    { change (1%nat) with (length [v2]). by iApply ty_size_eq. }
    rewrite <-Hsz in *. destruct vl as [|v[|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_write.
    rewrite -heap_mapsto_vec_singleton.
    iMod ("Hclose" with "* [Hl Hown2]") as "($ & $ & Hown)".
    { iExists _. iFrame. }
    rewrite tctx_interp_singleton tctx_hasty_val' //.
  Qed.

  Lemma type_deref E L ty1 ty ty1' p :
    ty.(ty_size) = 1%nat → typed_read E L ty1 ty ty1' →
    typed_instruction E L [TCtx_hasty p ty1] (!p)
                      (λ v, [TCtx_hasty p ty1'; TCtx_hasty v ty]).
  Proof.
    iIntros (Hsz Hread tid qE) "#HEAP #LFT Htl HE HL Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v) "% Hown".
    iMod (Hread with "* LFT Htl HE HL Hown") as (l vl q) "(% & Hl & Hown & Hclose)"; first done.
    subst v. iAssert (▷⌜length vl = 1%nat⌝)%I with "[#]" as ">%".
    { rewrite -Hsz. iApply ty_size_eq. done. }
    destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose" with "Hl") as "($ & $ & Hown2)".
    rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
    by iFrame.
  Qed.

End typing_rules.
