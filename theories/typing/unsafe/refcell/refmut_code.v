From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.refcell Require Import refcell refmut.
Set Default Proof Using "Type".

Section refmut_functions.
  Context `{typeG Σ, refcellG Σ}.

  (* TODO : map, when we will have a nice story about closures. *)

  (* Turning a refmut into a shared borrow. *)
  Definition refmut_deref : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma refmut_deref_type ty :
    typed_instruction_ty [] [] [] refmut_deref
      (fn (fun '(α, β) => [☀α; ☀β; α ⊑ β])%EL
          (fun '(α, β) => [# &shr{α}(refmut β ty)]%T)
          (fun '(α, β) => &shr{α}ty)%T).
  Proof.
    iApply type_fn; [solve_typing..|]. simpl. iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|by apply read_own_move|done|]. iIntros (x').
    iIntros "!# * #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (lv lrc) "#(Hfrac & #Hshr)".
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "([Hα1 Hα2] & Hβ & #Hαβ)".
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct (lft_glb_acc with "Hβ Hα2") as (qβα) "[Hα2β Hcloseβα2]".
    wp_bind (!(LitV lx'))%E. iApply (wp_fupd_step with "[Hα2β]");
         [done| |by iApply ("Hshr" with "[] Hα2β")|]; first done.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. iIntros "[#Hshr' Hα2β]!>". wp_let.
    iDestruct ("Hcloseβα2" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hcloseα1" with "[$H↦1 $H↦2]") as "Hα1".
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #lv ◁ &shr{α}ty]%TC
            with "[] LFT Hna [Hα1 Hα2 Hβ Hαβ] HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "LFT [] Hshr'"). iApply lft_incl_glb; first done.
      iApply lft_incl_refl. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.

  (* Turning a refmut into a unique borrow. *)
  Definition refmut_derefmut : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma refmut_derefmut_type ty :
    typed_instruction_ty [] [] [] refmut_deref
      (fn (fun '(α, β) => [☀α; ☀β; α ⊑ β])%EL
          (fun '(α, β) => [# &uniq{α}(refmut β ty)]%T)
          (fun '(α, β) => &uniq{α}ty)%T).
  Proof.
    iApply type_fn; [solve_typing..|]. simpl. iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|by apply read_own_move|done|]. iIntros (x').
    iIntros "!# * #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "(Hα & Hβ & #Hαβ)". destruct x' as [[|lx'|]|]; try done.
    iMod (bor_exists with "LFT Hx'") as (vl) "H". done.
    iMod (bor_sep with "LFT H") as "[H↦ H]". done.
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent_tok with "LFT H Hα") as "[>[] _]".
    iMod (bor_exists with "LFT H") as (ν) "H". done.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_exists with "LFT H") as (ty') "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ H]". done.
    iMod (bor_persistent_tok with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    rewrite (comm _ (1).[ν])%I. rewrite (assoc _ _ _ (1).[ν])%I.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_fracture (λ q, (1 * q).[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mult_1_l. }
    iDestruct (frac_bor_lft_incl _ _ 1 with "LFT H") as "#Hαν". iClear "H".
    rewrite heap_mapsto_vec_cons. iMod (bor_sep with "LFT H↦") as "[H↦ _]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!(LitV lx'))%E. iApply (wp_fupd_step with "[Hb]");
      [done| |by iApply (bor_unnest with "LFT Hb")|]; first done.
    wp_read. iIntros "Hb !>". wp_let.
    iMod ("Hcloseα" with "[$H↦]") as "[_ Hα]".
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #lv ◁ &uniq{α}ty]%TC
            with "[] LFT Hna [Hα Hβ Hαβ] HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (bor_shorten with "[] Hb").
      by iApply lft_incl_glb; [iApply lft_incl_glb|iApply lft_incl_refl]. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_letalloc_1 (&uniq{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply (type_jump [_]); solve_typing.
  Qed.

  (* Dropping a refmut and set the count to 0 in the corresponding refcell. *)
  Definition refmut_drop : val :=
    funrec: <> ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      "rc" <- #0;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in "return" ["r"].

  Lemma refmut_drop_type ty :
    typed_instruction_ty [] [] [] refmut_drop (fn(∀ α, [☀α]; refmut α ty) → unit).
  Proof.
    iApply type_fn; [solve_typing..|]. simpl. iIntros (α ret arg). inv_vec arg=>x. simpl_subst.
    iIntros "!# * #LFT Hna Hα HL Hk Hx".
    rewrite {1}/elctx_interp big_sepL_singleton tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν γ β ty') "(Hb & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)". wp_write.
    iDestruct (own_valid_2 with "H● H◯") as %[[[=]| (? & [agν st'] & [=<-] & -> &
      [[Hag Heq]|[_ Hle]%prod_included])]%option_included []]%auth_valid_discrete_2;
      last first.
    { by destruct (exclusive_included (Cinl (Excl ())) st'). }
    setoid_subst. iDestruct "INV" as (ν') "(Hνν' & H† & _)".
    iDestruct "Hνν'" as %<-%(inj to_agree)%leibniz_equiv.
    wp_bind Endlft. iApply (wp_fupd_step with "[H† Hν]");
      [done| |iApply ("H†" with "Hν")|]; first done.
    wp_seq. iIntros "{Hb} Hb !>".
    iMod ("Hcloseβ" with ">[H↦lrc H● H◯ Hb] Hna") as "[Hβ Hna]".
    { iExists None. iFrame. iMod (own_update_2 with "H● H◯") as "$"; last done.
      apply auth_update_dealloc. rewrite -(right_id None _ (Some _)).
      apply cancel_local_update_empty, _. }
    iMod ("Hcloseα" with "Hβ") as "Hα". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)]%TC
            with "[] LFT Hna [Hα] HL Hk"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    { by rewrite /elctx_interp big_sepL_singleton. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_jump [_]); solve_typing.
  Qed.
End refmut_functions.
