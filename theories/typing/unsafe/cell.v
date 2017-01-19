From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section cell.
  Context `{typeG Σ}.
  Local Hint Extern 1000 (_ ⊆ _) => set_solver : ndisj.

  Program Definition cell (ty : type) :=
    {| ty_size := ty.(ty_size);
       ty_own := ty.(ty_own);
       ty_shr κ tid l := (&na{κ, tid, shrN.@l} l ↦∗: ty.(ty_own) tid)%I |}.
  Next Obligation. apply ty_size_eq. Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hown $". by iApply bor_na.
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#LFT". iApply na_bor_shorten.
  Qed.

  (* TODO: non-expansiveness, proper wrt. eqtype *)

  Global Instance cell_copy :
    Copy ty → Copy (cell ty).
  Proof.
    intros ty Hcopy. split; first by intros; simpl; apply _.
    iIntros (κ tid E F l q ??) "#LFT #Hshr Htl Htok". iExists 1%Qp. simpl in *.
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    destruct (ty_size ty) as [|sz] eqn:Hsz.
    { iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct "Hown" as (vl) "[H↦ #Hown]".
      simpl. assert (F ∖ ∅ = F) as -> by set_solver+.
      iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
      iMod ("Hclose" with "[H↦] Htl") as "[$ $]".
      { iExists vl. by iFrame. }
      iModIntro. iSplitL "".
      { iNext. iExists vl. destruct vl; last done. iFrame "Hown".
        by iApply heap_mapsto_vec_nil. }
      by iIntros "$ _". }
    (* Now we are in the non-0 case. *)
    iMod (na_bor_acc with "LFT Hshr Htok Htl") as "($ & Htl & Hclose)"; [solve_ndisj..|].
    iDestruct (na_own_acc with "Htl") as "($ & Hclose')"; first by set_solver.
    iIntros "!> Htl Hown". iPoseProof ("Hclose'" with "Htl") as "Htl".
    iMod ("Hclose" with "Hown Htl") as "[$ $]". done.
  Qed.

  Global Instance cell_send :
    Send ty → Send (cell ty).
  Proof. intros. split. simpl. apply send_change_tid. Qed.
End cell.

Section typing.
  Context `{typeG Σ}.

  (* All of these are of course actual code in Rust, but somehow this is more fun. *)

  (* Constructing a cell is a coercion. *)
  Lemma tctx_mk_cell E L ty p :
    tctx_incl E L [p ◁ ty] [p ◁ cell ty].
  Proof.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  (* Same for the other direction *)
  Lemma tctx_unmk_cell E L ty p :
    tctx_incl E L [p ◁ cell ty] [p ◁ ty].
  Proof.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  Lemma read_cell E L κ ty :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&shr{κ} cell ty) ty (&shr{κ} cell ty).
  Proof. intros ??. exact: read_shr. Qed.

  (* Writing actually needs code; typed_write can't have thread tokens. *)
  Definition cell_write ty : val :=
    funrec: <> ["c"; "x"] :=
       let: "c'" := !"c" in
       "c'" <-{ty.(ty_size)} !"x";;
       let: "r" := new [ #0 ] in
       delete [ #1; "c"] ;; delete [ #ty.(ty_size); "x"] ;; "return" ["r"].

  Lemma cell_write_type ty :
    typed_instruction_ty [] [] [] (cell_write ty)
        (fn (λ α, [☀α])%EL (λ α, [# box (&shr{α} cell ty); box ty])
            (λ α, box unit)).
  Proof.
    apply type_fn; try apply _. move=> /= α ret arg. inv_vec arg=>c x. simpl_subst.
    eapply type_deref; [solve_typing..|by apply read_own_move|done|].
    intros c'. simpl_subst.
    eapply type_let with (T1 := [c' ◁ _; x ◁ _]%TC)
                         (T2 := λ _, [c' ◁ &shr{α} cell ty;
                                      x ◁ box (uninit ty.(ty_size))]%TC); try solve_typing; [|].
    { (* The core of the proof: Showing that the assignment is safe. *)
      iAlways. iIntros (tid qE) "#HEAP #LFT Htl HE $".
      rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
      iIntros "[Hc' Hx]". rewrite {1}/elctx_interp big_opL_singleton /=.
      iDestruct "Hc'" as (l) "[EQ #Hshr]". iDestruct "EQ" as %[=->].
      iDestruct "Hx" as (l') "[EQ [Hown >H†]]". iDestruct "EQ" as %[=->].
      iDestruct "Hown" as (vl') "[>H↦' Hown']".
      iMod (na_bor_acc with "LFT Hshr HE Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct "Hown" as (vl) "[>H↦ Hown]".
      iDestruct (ty_size_eq with "Hown") as "#>%".
      iDestruct (ty_size_eq with "Hown'") as "#>%".
      iApply wp_fupd. iApply (wp_memcpy with "[$HEAP $H↦ $H↦']"); [done..|].
      iNext. iIntros "[H↦ H↦']". rewrite {1}/elctx_interp big_opL_singleton /=.
      iMod ("Hclose" with "[H↦ Hown'] Htl") as "[$ $]".
      { iExists vl'. by iFrame. }
      rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //.
      iSplitR; iModIntro.
      - iExists _. iSplit; done.
      - iExists _. iSplit; first done. iFrame. iExists _. iFrame.
        rewrite uninit_own. auto. }
    intros v. simpl_subst. clear v.
    eapply type_new; [solve_typing..|].
    intros r. simpl_subst.
    eapply type_delete; [solve_typing..|].
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.

  (* TODO: get_mut *)
End typing.
