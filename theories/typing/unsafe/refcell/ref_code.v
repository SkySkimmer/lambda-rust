From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.unsafe.refcell Require Import refcell ref.
Set Default Proof Using "Type".

Section ref_functions.
  Context `{typeG Σ, refcellG Σ}.

  Definition ref_clone : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      let: "rc" := !("x'" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
      letalloc: "r" <-{2} !"x'" in
      delete [ #1; "x"];; "return" ["r"].

  (* FIXME : using λ instead of fun triggers an anomaly.
     See: https://coq.inria.fr/bugs/show_bug.cgi?id=5326 *)
  Lemma ref_clone_type ty :
    typed_instruction_ty [] [] [] ref_clone
      (fn (fun '(α, β) => [☀α; ☀β])%EL (fun '(α, β) => [# &shr{α}(ref β ty)]%T)
                                       (fun '(α, β) => ref β ty)%T).
  Proof.
    apply type_fn; [apply _..|]. move=>/= [α β] ret arg. inv_vec arg=>x. simpl_subst.
    eapply type_deref; [solve_typing..|by apply read_own_move|done|]=>x'.
    iIntros "!# * #HEAP #LFT Hna HE HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    destruct x' as [[|lx'|]|]; try iDestruct "Hx'" as "[]".
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hβδ & Hinv & H◯inv)".
    wp_op. rewrite {1}/elctx_interp big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "[[Hα1 Hα2] Hβ]".
    iMod (lft_incl_acc with "Hβδ Hβ") as (qδ) "[Hδ Hcloseβ]". done.
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    iMod (na_bor_acc with "LFT Hinv Hδ Hna") as "(INV & Hna & Hcloseδ)"; [done..|].
    iMod (na_bor_acc with "LFT H◯inv Hα2 Hna") as "(H◯ & Hna & Hcloseα2)"; [solve_ndisj..|].
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)". wp_read. wp_let. wp_op. wp_write.
    iAssert (∃ q' n, st ≡ Some (Cinr (to_agree ν, q', n)))%I with "[#]" as (q' n) "Hst".
    { iDestruct (own_valid_2 with "H● H◯") as %[[[=]|
         (? & st' & [=<-] & -> & [Heq|Hle])]%option_included Hv]%auth_valid_discrete_2.
      - iExists q, xH. iPureIntro. constructor. done.
      - iClear "∗#".
        revert Hle Hv=>/csum_included [ -> // | [[?[?[//]]] | [?[st''[Heq[-> Hle]]]]]].
        revert Heq. intros [= <-]. destruct st'' as [[ag q'] n].
        revert Hle=>/Some_included_2 /Some_pair_included
               [/Some_pair_included_total_1 [/agree_included Heq _] _] [[Hag _] _].
        iExists q', n. iPureIntro. repeat constructor. apply Cinlr_equiv.
        do 2 constructor; last done. apply agree_op_inv. by rewrite comm -Heq. }
    iDestruct "Hst" as %[st' [-> Hst']]%equiv_Some_inv_r'.
    destruct st' as [|[[]]|]; try by inversion Hst'. apply (inj Cinr), (inj2 pair) in Hst'.
    destruct Hst' as [[Hst' <-%leibniz_equiv]%(inj2 pair) <-%leibniz_equiv].
    simpl. setoid_rewrite <-Hst'. clear Hst'.
    iDestruct "INV" as (q'' ν') "(Hag & Hq'q'' & [Hν1 Hν2] & INV)".
    iDestruct "Hag" as %<-%(inj to_agree)%leibniz_equiv.
    iDestruct "Hq'q''" as %Hq'q''.
    iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (reading_st (q''/2)%Qp ν))=>-[[Hagv _]_].
      split; [split|].
      - by rewrite /= agree_idemp.
      - change ((q''/2+q')%Qp ≤ 1%Qp)%Qc. rewrite -Hq'q'' comm -{2}(Qp_div_2 q'').
        apply Qcplus_le_mono_l. rewrite -{1}(Qcplus_0_l (q''/2)%Qp).
        apply Qcplus_le_mono_r, Qp_ge_0.
      - done. }
    wp_bind (new [ #2])%E. iApply wp_new; [done..|]. iNext. iIntros (lr ?) "(%&?&Hlr)".
    iAssert (lx' ↦∗{qlx'} [ #lv; #lrc])%I  with "[H↦1 H↦2]" as "H↦".
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    wp_let. wp_bind (_ <-{_} !_)%E. iApply (wp_memcpy with "[$HEAP $Hlr $H↦]"); [done..|].
    iIntros "!>[Hlr H↦]". wp_seq.
    iMod ("Hcloseα2" with "[$H◯] Hna") as "[Hα2 Hna]".
    iMod ("Hcloseδ" with "[H↦lrc H● Hν1 INV] Hna") as "[Hδ Hna]".
    { iExists _. rewrite Z.add_comm. iFrame. iExists _, _. iFrame. simpl.
      rewrite agree_idemp (comm Qp_plus) (assoc Qp_plus) Qp_div_2 (comm Qp_plus). auto. }
    iMod ("Hcloseβ" with "Hδ") as "Hβ". iMod ("Hcloseα1" with "[$H↦]") as "Hα1".
    iAssert (elctx_interp [☀ α; ☀ β] qE) with "[Hα1 Hα2 Hβ]" as "HE".
    { rewrite /elctx_interp big_sepL_cons big_sepL_singleton. iFrame. }
    iApply (type_delete _ _
        [ x ◁ box (uninit 1); #lr ◁ box(ref β ty)]%TC with "HEAP LFT Hna HE HL Hk");
      [solve_typing..| |]; first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      rewrite /= freeable_sz_full. iFrame. iExists _. iFrame. iExists _, _, _, _, _.
      iFrame "∗#". }
    eapply (type_jump [ #_]); solve_typing.
  Qed.
End ref_functions.