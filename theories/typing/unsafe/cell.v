From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs.
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

  Global Instance cell_type :
    Copy ty → Copy (cell ty).
  Proof.
    intros ty Hcopy. split; first by intros; simpl; apply _.
    iIntros (κ tid E F l q ??) "#LFT #Hshr Htl Htok". iExists 1%Qp. simpl in *.
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    destruct (ty_size ty) as [|sz] eqn:Hsz.
    { iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct "Hown" as (vl) "[H↦ #Hown]".
      simpl. assert (F ∖ ∅ = F) as -> by set_solver+.
      iAssert (▷ ⌜length vl = ty_size ty⌝)%I with "[#]" as ">EQ".
      { iNext. by iApply ty_size_eq. }
      rewrite Hsz. iDestruct "EQ" as %EQ. iMod ("Hclose" with "[H↦] Htl") as "[$ $]".
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

  (* Constructing a cell is a coercion. *)
  Lemma tctx_mk_cell E L ty p :
    tctx_incl E L [p ◁ ty] [p ◁ cell ty].
  Proof.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  (* Same for the other direction *)
  Lemma tctx_unmk_cell E L ty p :
    tctx_incl E L [p ◁ ty] [p ◁ cell ty].
  Proof.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.
  
  (* TODO: get, set; potentially more operations? *)
End typing.
