From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.rwlock Require Import rwlock rwlockwriteguard.
Set Default Proof Using "Type".

Section rwlockwriteguard_functions.
  Context `{typeG Σ, rwlockG Σ}.

  (* Turning a rwlockwriteguard into a shared borrow. *)
  Definition rwlockwriteguard_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" +ₗ #1 in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma rwlockwriteguard_deref_type ty :
    typed_val rwlockwriteguard_deref
      (fn (fun '(α, β) => FP [α; β; α ⊑ β]%EL
                              [# &shr{α}(rwlockwriteguard β ty)] (&shr{α}ty))).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (l') "#[Hfrac Hshr]".
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "([Hα1 Hα2] & Hβ & #Hαβ)".
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    rewrite heap_mapsto_vec_singleton.
    iDestruct (lft_intersect_acc with "Hβ Hα2") as (qβα) "[Hα2β Hcloseβα2]".
    wp_bind (!(LitV lx'))%E. iApply (wp_fupd_step with "[Hα2β]");
         [done| |by iApply ("Hshr" with "[] Hα2β")|]; first done.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. iIntros "[#Hshr' Hα2β]!>". wp_op. wp_let.
    iDestruct ("Hcloseβα2" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hcloseα1" with "[$H↦1 $H↦2]") as "Hα1".
    iApply (type_type _ _ _ [ x ◁ box (&shr{α} rwlockwriteguard β ty);
                              #(shift_loc l' 1) ◁ &shr{α}ty]%TC
            with "[] LFT Hna [Hα1 Hα2 Hβ Hαβ] HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr'"). iApply lft_incl_glb; first done.
      iApply lft_incl_refl. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.

  (* Turning a rwlockwriteguard into a unique borrow. *)
  Definition rwlockwriteguard_derefmut : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" +ₗ #1 in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma rwlockwriteguard_derefmut_type ty :
    typed_val rwlockwriteguard_derefmut
      (fn (fun '(α, β) => FP [α; β; α ⊑ β]%EL
                              [# &uniq{α}(rwlockwriteguard β ty)] (&uniq{α}ty))).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid qE) "#LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "(Hα & Hβ & #Hαβ)". destruct x' as [[|lx'|]|]; try done.
    iMod (bor_exists with "LFT Hx'") as (vl) "H". done.
    iMod (bor_sep with "LFT H") as "[H↦ H]". done.
    destruct vl as [|[[|l|]|][]];
      try by iMod (bor_persistent_tok with "LFT H Hα") as "[>[] _]".
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ _]". done.
    iMod (bor_persistent_tok with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!(LitV lx'))%E. iApply (wp_fupd_step with "[Hb]");
      [done| |by iApply (bor_unnest with "LFT Hb")|]; first done.
    wp_read. iIntros "Hb !>". wp_op. wp_let.
    iMod ("Hcloseα" with "[$H↦]") as "[_ Hα]".
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #(shift_loc l 1) ◁ &uniq{α}ty]%TC
            with "[] LFT Hna [Hα Hβ Hαβ] HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (bor_shorten with "[] Hb").
      by iApply lft_incl_glb; [iApply lft_incl_trans|iApply lft_incl_refl]. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_letalloc_1 (&uniq{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.

  (* Drop a rwlockwriteguard and release the lock. *)
  Definition rwlockwriteguard_drop : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      "x'" <-ˢᶜ #0;;
      delete [ #1; "x"];;
      let: "r" := new [ #0] in "return" ["r"].

  Lemma rwlockwriteguard_drop_type ty :
    typed_val rwlockwriteguard_drop
              (fn(∀ α, [α]; rwlockwriteguard α ty) → unit).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iIntros (tid qE) "#LFT Hna Hα HL Hk HT".
    rewrite {1}/elctx_interp big_sepL_singleton tctx_interp_cons
            tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    destruct x' as [[|lx'|]|]; try done. simpl.
    iDestruct "Hx'" as (γ β) "(Hx' & #Hαβ & #Hinv & H◯)".
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    wp_bind (#lx' <-ˢᶜ #0)%E.
    iMod (shr_bor_acc_tok with "LFT Hinv Hβ") as "[INV Hcloseβ]"; [done..|].
    iDestruct "INV" as (st) "(H↦ & H● & INV)". wp_write.
    iMod ("Hcloseβ" with ">[H↦ H● H◯ INV Hx']") as "Hβ".
    { iDestruct (own_valid_2 with "H● H◯") as %[[[=]| (? & st0 & [=<-] & -> &
         [Heq|Hle])]%option_included Hv]%auth_valid_discrete_2;
      last by destruct (exclusive_included _ _ Hle).
      destruct st0 as [[[]|]| |]; try by inversion Heq.
      iExists None. iFrame. iMod (own_update_2 with "H● H◯") as "$"; last done.
      apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
      apply cancel_local_update_empty, _. }
    iModIntro. wp_seq. iMod ("Hcloseα" with "Hβ") as "HE".
    iApply (type_type _ _ _ [ x ◁ box (uninit 1)]%TC
            with "[] LFT Hna [HE] HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val //. }
    { rewrite /elctx_interp big_sepL_singleton //. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_jump [_]); solve_typing.
  Qed.
End rwlockwriteguard_functions.
