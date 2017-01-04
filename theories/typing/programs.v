From iris.base_logic Require Import big_op.
From lrust.lang Require Export notation.
From lrust.lang Require Import proofmode memcpy.
From lrust.lifetime Require Import frac_borrow reborrow borrow creation.
From lrust.typing Require Export type lft_contexts type_context cont_context.

Section typing.
  Context `{typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body (E : elctx) (L : llctx) (C : cctx) (T : tctx)
                        (e : expr) : iProp Σ :=
    (∀ tid qE, heap_ctx -∗ lft_ctx -∗ na_own tid ⊤ -∗
               elctx_interp E qE -∗ llctx_interp L 1 -∗
               (elctx_interp E qE -∗ cctx_interp tid C) -∗ tctx_interp tid T -∗
               WP e {{ _, cont_postcondition }})%I.
  Global Arguments typed_body _%EL _%LL _%CC _%TC _%E.

  Global Instance typed_body_llctx_permut E :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> (⊢)) (typed_body E).
  Proof.
    intros L1 L2 HL C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HL.
  Qed.

  Global Instance typed_body_elctx_permut :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> eq ==> (⊢)) typed_body.
  Proof.
    intros E1 E2 HE L ? <- C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HE.
  Qed.

  Global Instance typed_body_mono E L:
    Proper (flip (cctx_incl E) ==> flip (tctx_incl E L) ==> eq ==> (⊢))
           (typed_body E L).
  Proof.
    intros C1 C2 HC T1 T2 HT e ? <-. iIntros "H".
    iIntros (tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iMod (HT with "LFT HE HL HT") as "(HE & HL & HT)".
    iApply ("H" with "HEAP LFT Htl HE HL [HC] HT").
    iIntros "HE". by iApply (HC with "LFT HC").
  Qed.

  Global Instance typed_body_mono_flip E L:
    Proper (cctx_incl E ==> tctx_incl E L ==> eq ==> flip (⊢))
           (typed_body E L).
  Proof. intros ?????????. by eapply typed_body_mono. Qed.

  (** Instruction *)
  Definition typed_instruction (E : elctx) (L : llctx)
             (T1 : tctx) (e : expr) (T2 : val → tctx) : Prop :=
    ∀ tid qE, heap_ctx -∗ lft_ctx -∗ na_own tid ⊤ -∗
              elctx_interp E qE -∗ llctx_interp L 1 -∗ tctx_interp tid T1 -∗
              WP e {{ v, na_own tid ⊤ ∗ elctx_interp E qE ∗
                         llctx_interp L 1 ∗ tctx_interp tid (T2 v) }}.
  Global Arguments typed_instruction _%EL _%LL _%TC _%E _.

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
      lft_ctx -∗ na_own tid F -∗
      elctx_interp E qE -∗ llctx_interp L qL -∗ ty1.(ty_own) tid [v] ={F}=∗
        ∃ (l : loc) vl q, ⌜v = #l⌝ ∗ l ↦∗{q} vl ∗ ▷ ty.(ty_own) tid vl ∗
              (l ↦∗{q} vl ={F}=∗ na_own tid F ∗ elctx_interp E qE ∗
                              llctx_interp L qL ∗ ty2.(ty_own) tid [v]).
End typing.

Notation typed_instruction_ty E L T1 e ty :=
  (typed_instruction E L T1 e (λ v : val, [v ◁ ty]%TC)).

Section typing_rules.
  Context `{typeG Σ}.

  (* TODO: notation scopes need tuing to avoid the %list here. *)
  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft E L C T κ1 κ2 e :
    typed_body ((κ1 ⊑ κ2) :: (κ2 ⊑ κ1) :: E) L C T e →
    typed_body E ((κ1 ⊑ [κ2]%list) :: L) C T e.
  Proof.
    iIntros (He tid qE) "#HEAP #LFT Htl HE HL HC HT".
    rewrite /llctx_interp big_sepL_cons. iDestruct "HL" as "[Hκ HL]".
    iMod (lctx_equalize_lft with "LFT Hκ") as "[Hκ1 Hκ2]".
    iApply (He with "HEAP LFT Htl [Hκ1 Hκ2 HE] HL [HC] HT").
    - rewrite /elctx_interp !big_sepL_cons. by iFrame.
    - rewrite /elctx_interp !big_sepL_cons. iIntros "(_ & _ & HE)".
      iApply "HC". done.
  Qed.

  Lemma type_let E L T1 T2 (T : tctx) C xb e e' :
    Closed (xb :b: []) e' →
    typed_instruction E L T1 e T2 →
    (∀ v : val, typed_body E L C (T2 v ++ T) (subst' xb v e')) →
    typed_body E L C (T1 ++ T) (let: xb := e in e').
  Proof.
    iIntros (Hc He He' tid qE) "#HEAP #LFT Htl HE HL HC HT". rewrite tctx_interp_app.
    iDestruct "HT" as "[HT1 HT]". wp_bind e. iApply (wp_wand with "[HE HL HT1 Htl]").
    { iApply (He with "HEAP LFT Htl HE HL HT1"). }
    iIntros (v) "/= (Htl & HE & HL & HT2)". iApply wp_let; first wp_done.
    iModIntro. iApply (He' with "HEAP LFT Htl HE HL HC [HT2 HT]").
    rewrite tctx_interp_app. by iFrame.
  Qed.

  Lemma type_let' E L T T' T1 T2 C xb e e' :
    Closed (xb :b: []) e' →
    typed_instruction E L T1 e T2 →
    tctx_extract_ctx E L T1 T T' →
    (∀ v : val, typed_body E L C (T2 v ++ T') (subst' xb v e')) →
    typed_body E L C T (let: xb := e in e').
  Proof.
    intros ?? HT ?. unfold tctx_extract_ctx in HT. rewrite ->HT.
    by eapply type_let.
  Qed.

  Lemma typed_newlft E L C T κs e :
    Closed [] e →
    (∀ κ, typed_body E ((κ ⊑ κs) :: L) C T e) →
    typed_body E L C T (Newlft ;; e).
  Proof.
    iIntros (Hc He tid qE) "#HEAP #LFT Htl HE HL HC HT".
    iMod (lft_create with "LFT") as (Λ) "[Htk #Hinh]"; first done.
    set (κ' := foldr (∪) static κs). wp_seq.
    iApply (He (κ' ∪ Λ) with "HEAP LFT Htl HE [HL Htk] HC HT").
    rewrite /llctx_interp big_sepL_cons. iFrame "HL".
    iExists Λ. iSplit; first done. iFrame. done.
  Qed.

  (* TODO: It should be possible to show this while taking only one step.
     Right now, we could take two. *)
  Lemma typed_endlft E L C T1 T2 κ κs e :
    Closed [] e → UnblockTctx κ T1 T2 →
    typed_body E L C T2 e → typed_body E ((κ ⊑ κs) :: L) C T1 (Endlft ;; e).
  Proof.
    iIntros (Hc Hub He tid qE) "#HEAP #LFT Htl HE". rewrite /llctx_interp big_sepL_cons.
    iIntros "[Hκ HL] HC HT". iDestruct "Hκ" as (Λ) "(% & Htok & #Hend)".
    iSpecialize ("Hend" with "Htok"). wp_bind Endlft.
    iApply (wp_fupd_step with "Hend"); try done. wp_seq.
    iIntros "!> #Hdead !>". wp_seq. iApply (He with "HEAP LFT Htl HE HL HC >").
    iApply (Hub with "[] HT"). simpl in *. subst κ. rewrite -lft_dead_or. auto.
  Qed.

  Lemma type_assign {E L} ty ty1 ty1' p1 p2 :
    typed_write E L ty1 ty ty1' →
    typed_instruction E L [p1 ◁ ty1; p2 ◁ ty] (p1 <- p2) (λ _, [p1 ◁ ty1']%TC).
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

  Lemma type_deref {E L} ty ty1 ty1' p :
    ty.(ty_size) = 1%nat → typed_read E L ty1 ty ty1' →
    typed_instruction E L [p ◁ ty1] (!p) (λ v, [p ◁ ty1'; v ◁ ty]%TC).
  Proof.
    iIntros (Hsz Hread tid qE) "#HEAP #LFT Htl HE HL Hp".
    rewrite tctx_interp_singleton. wp_bind p. iApply (wp_hasty with "Hp").
    iIntros (v) "% Hown".
    iMod (Hread with "* LFT Htl HE HL Hown") as
        (l vl q) "(% & Hl & Hown & Hclose)"; first done.
    subst v. iAssert (▷⌜length vl = 1%nat⌝)%I with "[#]" as ">%".
    { rewrite -Hsz. iApply ty_size_eq. done. }
    destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_read.
    iMod ("Hclose" with "Hl") as "($ & $ & Hown2)".
    rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
    by iFrame.
  Qed.

  Lemma type_memcpy_iris E qE L qL tid ty ty1 ty1' ty2 ty2' n p1 p2 :
    ty.(ty_size) = n → typed_write E L ty1 ty ty1' → typed_read E L ty2 ty ty2' →
    {{{ heap_ctx ∗ lft_ctx ∗ na_own tid ⊤ ∗ elctx_interp E qE ∗ llctx_interp L qL ∗
        tctx_elt_interp tid (p1 ◁ ty1) ∗ tctx_elt_interp tid (p2 ◁ ty2) }}}
      (p1 <⋯ !{n}p2)
    {{{ RET #(); na_own tid ⊤ ∗ elctx_interp E qE ∗ llctx_interp L qL ∗
                 tctx_elt_interp tid (p1 ◁ ty1') ∗ tctx_elt_interp tid (p2 ◁ ty2') }}}.
  Proof.
    iIntros (Hsz Hwrt Hread Φ) "(#HEAP & #LFT & Htl & [HE1 HE2] & [HL1 HL2] & [Hp1 Hp2]) HΦ".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "% Hown2".
    iMod (Hwrt with "* LFT HE1 HL1 Hown1")
      as (l1 vl1) "([% %] & Hl1 & Hcl1)"; first done.
    iMod (Hread with "* LFT Htl HE2 HL2 Hown2")
      as (l2 vl2 q2) "(% & Hl2 & Hown2 & Hcl2)"; first done.
    iAssert (▷⌜length vl2 = ty.(ty_size)⌝)%I with "[#]" as ">%".
    { by iApply ty_size_eq. } subst v1 v2. iApply wp_fupd.
    iApply (wp_memcpy with "[$HEAP $Hl1 $Hl2]"); first done; try congruence; [].
    iNext. iIntros "[Hl1 Hl2]". iApply ("HΦ" with ">"). rewrite !tctx_hasty_val' //.
    iMod ("Hcl1" with "[Hl1 Hown2]") as "($ & $ & $)".
    { iExists _. iFrame. }
    iMod ("Hcl2" with "Hl2") as "($ & $ & $ & $)". done.
  Qed.

  Lemma type_memcpy {E L} ty ty1 ty1' ty2 ty2' n p1 p2 :
    ty.(ty_size) = n → typed_write E L ty1 ty ty1' → typed_read E L ty2 ty ty2' →
    typed_instruction E L [p1 ◁ ty1; p2 ◁ ty2] (p1 <⋯ !{n}p2)
                      (λ _, [p1 ◁ ty1'; p2 ◁ ty2']%TC).
  Proof.
    iIntros (Hsz Hwrt Hread tid qE) "#HEAP #LFT Htl HE HL HT".
    iApply (type_memcpy_iris with "[$HEAP $LFT $Htl $HE $HL HT]"); try done.
    { by rewrite tctx_interp_cons tctx_interp_singleton. }
    rewrite tctx_interp_cons tctx_interp_singleton. auto.
  Qed.
End typing_rules.
