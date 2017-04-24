From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing util option mutex.
Set Default Proof Using "Type".

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mguard.
  Context `{!typeG Σ, !lockG Σ}.

  (*
    pub struct MutexGuard<'a, T: ?Sized + 'a> {
      // funny underscores due to how Deref/DerefMut currently work (they
      // disregard field privacy).
      __lock: &'a Mutex<T>,
      __poison: poison::Guard,
    }
  *)

  Program Definition mutexguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ γ β, locked γ ∗ α ⊑ β ∗
             &shr{α, mutexN} (lock_proto γ l (&{β} shift_loc l 1 ↦∗: ty.(ty_own) tid)) ∗
             &{β} (shift_loc l 1 ↦∗: ty.(ty_own) tid)
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l':loc), &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α⊓κ]
                ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (α⊓κ) tid (shift_loc l' 1) ∗ q.[α⊓κ]
    |}%I.
  Next Obligation. by iIntros (? ty tid [|[[]|][]]) "H". Qed.
  (* This is to a large extend copy-pasted from RWLock's write guard. *)
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hlcked H]"; first done.
    iMod (bor_sep with "LFT H") as "[Hαβ H]"; first done.
    iMod (bor_sep with "LFT H") as "[_ H]"; first done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ $]"; first done.
    iExists _. iFrame "H↦". iApply delay_sharing_nested; try done.
    (* FIXME: "iApply lft_intersect_mono" only preserves the later on the last
       goal, as does "iApply (lft_intersect_mono with ">")". *)
    iNext. iApply lft_intersect_mono. done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (l') "[#Hf #H]".
    iExists _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
      { iApply lft_intersect_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "[] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_intersect_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance mutexguard_wf α ty `{!TyWf ty} : TyWf (mutexguard α ty) :=
    { ty_lfts := [α]; ty_wf_E := ty.(ty_wf_E) ++ ty.(ty_outlives_E) α }.

End mguard.

Section code.
  Context `{!typeG Σ, !lockG Σ}.

  Lemma mutex_acc E γ l ty tid q α κ :
    ↑lftN ⊆ E → ↑mutexN ⊆ E →
    let R := (&{κ} shift_loc l 1 ↦∗: ty_own ty tid)%I in
    lft_ctx -∗ &shr{α,mutexN} lock_proto γ l R -∗ α ⊑ κ -∗
    □ ((q).[α] ={E,∅}=∗ ▷ lock_proto γ l R ∗ (▷ lock_proto γ l R ={∅,E}=∗ (q).[α])).
  Proof.
    (* FIXME: This should work: iIntros (?? R). *) intros ?? R.
    iIntros "#LFT #Hshr #Hlincl !# Htok".
    iMod (shr_bor_acc_tok with "LFT Hshr Htok") as "[Hproto Hclose1]"; [done..|].
    iMod (fupd_intro_mask') as "Hclose2"; last iModIntro; first solve_ndisj.
    iFrame. iIntros "Hproto". iMod "Hclose2" as "_".
    iMod ("Hclose1" with "Hproto") as "$". done.
  Qed.

  Definition mutex_lock : val :=
    funrec: <> ["mutex"] :=
      let: "m" := !"mutex" in
      let: "guard" := new [ #1 ] in
      acquire ["m"];;
      "guard" +ₗ #0 <- "m";;
      delete [ #1; "mutex" ];; return: ["guard"].

  Lemma mutex_lock_type ty `{!TyWf ty} :
    typed_val mutex_lock (fn(∀ α, ∅; &shr{α} mutex ty) → mutexguard α ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m); simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (g); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hx [Hm _]]]".
    rewrite !tctx_hasty_val [[x]]lock /=.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as (γ κ') "[#Hshr #Hακ']".
    iDestruct (ownptr_uninit_own with "Hg") as (lg vlg) "(% & Hg & Hg†)".
    subst g. inv_vec vlg=>g. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    wp_apply (acquire_spec with "[] Hα"); first by iApply (mutex_acc with "LFT Hshr Hακ'").
    iIntros "[Hlocked [Hcont Htok]]". wp_seq. wp_op. rewrite shift_loc_0. wp_write.
    iMod ("Hclose1" with "Htok HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ x ◁ own_ptr _ _; #lg ◁ box (mutexguard α ty)]
        with "[] LFT HE Hna HL Hk"); last first.
    (* TODO: It would be nice to say [{#}] as the last spec pattern to clear the context in there. *)
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hg".
      iExists _, _. iFrame "#∗". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition mutexguard_drop : val :=
    funrec: <> ["g"] :=
      let: "m" := !"g" in
      release ["m"];;
      delete [ #1; "g" ];;
      let: "r" := new [ #0 ] in return: ["r"].

  Lemma mutexguard_drop_type ty `{!TyWf ty} :
    typed_val mutexguard_drop (fn(∀ α, ∅; mutexguard α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros (α ϝ ret arg). inv_vec arg=>g. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (m); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #HE Hna HL Hk [Hg [Hm _]]".
    rewrite !tctx_hasty_val [[g]]lock /=.
    destruct m as [[|lm|]|]; try done. iDestruct "Hm" as (γ β) "(Hlcked & #Hαβ & #Hshr & Hcnt)".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    wp_apply (release_spec with "[] [Hα $Hlcked Hcnt]"); first by iApply (mutex_acc with "LFT Hshr Hαβ").
    { by iFrame. }
    iIntros "Htok". wp_seq. iMod ("Hclose1" with "Htok HL") as "HL".
    (* Switch back to typing mode. *)
    iApply (type_type _ _ _ [ g ◁ own_ptr _ _ ]
        with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val. unlock. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

End code.
