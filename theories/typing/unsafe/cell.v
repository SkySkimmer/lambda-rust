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
       ty_shr κ tid l :=
         (∃ P, ▷ □ (P ↔ l ↦∗: ty.(ty_own) tid) ∗ &na{κ, tid, shrN.@l}P)%I |}.
  Next Obligation. apply ty_size_eq. Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hown $". iExists _.
    iMod (bor_na with "Hown") as "$". set_solver. iIntros "!>!>!#". iSplit; auto.
  Qed.
  Next Obligation.
    iIntros (ty ?? tid l) "#LFT #H⊑ H". iDestruct "H" as (P) "[??]".
    iExists _. iFrame. by iApply (na_bor_shorten with "H⊑").
  Qed.

  Global Instance cell_ne n : Proper (dist n ==> dist n) cell.
  Proof.
    intros ?? EQ. split; [split|]; simpl; try apply EQ.
    intros κ tid l. repeat (apply EQ || f_contractive || f_equiv).
  Qed.

  Global Instance cell_mono E L : Proper (eqtype E L ==> subtype E L) cell.
  Proof.
    iIntros (?? EQ%eqtype_unfold) "#LFT #HE #HL".
    iDestruct (EQ with "LFT HE HL") as "(% & #Hown & #Hshr)".
    iSplit; [done|iSplit; iIntros "!# * H"].
    - iApply ("Hown" with "H").
    - iDestruct "H" as (P) "[#HP H]". iExists P. iFrame. iSplit; iNext; iIntros "!# H".
      + iDestruct ("HP" with "H") as (vl) "[??]". iExists vl. iFrame. by iApply "Hown".
      + iApply "HP". iDestruct "H" as (vl) "[??]". iExists vl. iFrame. by iApply "Hown".
  Qed.
  Lemma cell_mono' E L ty1 ty2 : eqtype E L ty1 ty2 → subtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_mono. Qed.
  Global Instance cell_proper E L : Proper (eqtype E L ==> eqtype E L) cell.
  Proof. by split; apply cell_mono. Qed.
  Lemma cell_proper' E L ty1 ty2 : eqtype E L ty1 ty2 → eqtype E L (cell ty1) (cell ty2).
  Proof. eapply cell_proper. Qed.

  Global Instance cell_copy :
    Copy ty → Copy (cell ty).
  Proof.
    intros ty Hcopy. split; first by intros; simpl; apply _.
    iIntros (κ tid E F l q ??) "#LFT #Hshr Htl Htok". iExists 1%Qp. simpl in *.
    iDestruct "Hshr" as (P) "[HP Hshr]".
    (* Size 0 needs a special case as we can't keep the thread-local invariant open. *)
    destruct (ty_size ty) as [|sz] eqn:Hsz.
    { iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct ("HP" with "Hown") as (vl) "[H↦ #Hown]".
      simpl. assert (F ∖ ∅ = F) as -> by set_solver+.
      iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
      iMod ("Hclose" with "[H↦] Htl") as "[$ $]".
      { iApply "HP". iExists vl. by iFrame. }
      iModIntro. iSplitL "".
      { iNext. iExists vl. destruct vl; last done. iFrame "Hown".
        by iApply heap_mapsto_vec_nil. }
      by iIntros "$ _". }
    (* Now we are in the non-0 case. *)
    iMod (na_bor_acc with "LFT Hshr Htok Htl") as "(H & Htl & Hclose)"; [solve_ndisj..|].
    iDestruct ("HP" with "H") as "$".
    iDestruct (na_own_acc with "Htl") as "($ & Hclose')"; first by set_solver.
    iIntros "!> Htl Hown". iPoseProof ("Hclose'" with "Htl") as "Htl".
    iMod ("Hclose" with "[Hown] Htl") as "[$ $]"; last done. by iApply "HP".
  Qed.

  Global Instance cell_send :
    Send ty → Send (cell ty).
  Proof. intros. split. simpl. apply send_change_tid. Qed.
End cell.

Section typing.
  Context `{typeG Σ}.

  (* Constructing a cell. *)
  Definition cell_new : val := funrec: <> ["x"] := "return" ["x"].

  Lemma cell_new_type ty :
    typed_instruction_ty [] [] [] cell_new
        (fn (λ _, [])%EL (λ _, [# ty]) (λ _:(), cell ty)).
  Proof.
    apply type_fn; [apply _..|]. move=>/= _ ret arg. inv_vec arg=>x. simpl_subst.
    eapply (type_jump [_]); first solve_typing.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  (* Same for the other direction.
     FIXME : this does not exist in Rust.*)
  Definition cell_into_inner : val := funrec: <> ["x"] := "return" ["x"].

  Lemma cell_into_inner_type ty :
    typed_instruction_ty [] [] [] cell_into_inner
        (fn (λ _, [])%EL (λ _, [# cell ty]) (λ _:(), ty)).
  Proof.
    apply type_fn; [apply _..|]. move=>/= _ ret arg. inv_vec arg=>x. simpl_subst.
    eapply (type_jump [_]); first solve_typing.
    iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done.
  Qed.

  (* Reading from a cell *)
  Definition cell_get ty : val :=
    funrec: <> ["x"] :=
      let: "x'" := !"x" in
      letalloc: "r" <-{ty.(ty_size)} !"x'" in
      delete [ #1; "x"];; "return" ["r"].

  Lemma cell_get_type `(!Copy ty) :
    typed_instruction_ty [] [] [] (cell_get ty)
        (fn (λ α, [☀α])%EL (λ α, [# &shr{α} (cell ty)])%T (λ _, ty)).
  Proof.
    apply type_fn; [apply _..|]. move=>/= α ret arg. inv_vec arg=>x. simpl_subst.
    eapply type_deref; [solve_typing..|apply read_own_move|done|]=>x'. simpl_subst.
    eapply type_letalloc_n; [solve_typing..| |solve_typing|intros r; simpl_subst].
    { apply (read_shr _ _ _ (cell ty)); solve_typing. }
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.

  (* Writing to a cell *)
  Definition cell_set ty : val :=
    funrec: <> ["c"; "x"] :=
       let: "c'" := !"c" in
       "c'" <-{ty.(ty_size)} !"x";;
       let: "r" := new [ #0 ] in
       delete [ #1; "c"] ;; delete [ #ty.(ty_size); "x"] ;; "return" ["r"].

  Lemma cell_set_type ty :
    typed_instruction_ty [] [] [] (cell_set ty)
        (fn (λ α, [☀α])%EL (λ α, [# &shr{α} cell ty; ty]%T) (λ α, unit)).
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
      iDestruct "Hshr" as (P) "[#HP #Hshr]".
      iDestruct "Hx" as (l') "[EQ [Hown >H†]]". iDestruct "EQ" as %[=->].
      iDestruct "Hown" as (vl') "[>H↦' Hown']".
      iMod (na_bor_acc with "LFT Hshr HE Htl") as "(Hown & Htl & Hclose)"; [solve_ndisj..|].
      iDestruct ("HP" with "Hown") as (vl) "[>H↦ Hown]".
      iDestruct (ty_size_eq with "Hown") as "#>%".
      iDestruct (ty_size_eq with "Hown'") as "#>%".
      iApply wp_fupd. iApply (wp_memcpy with "[$HEAP $H↦ $H↦']"); [done..|].
      iNext. iIntros "[H↦ H↦']". rewrite {1}/elctx_interp big_opL_singleton /=.
      iMod ("Hclose" with "[H↦ Hown'] Htl") as "[$ $]".
      { iApply "HP". iExists vl'. by iFrame. }
      rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //.
      iSplitR; iModIntro.
      - iExists _. simpl. eauto.
      - iExists _. iSplit; first done. iFrame. iExists _. iFrame.
        rewrite uninit_own. auto. }
    intros v. simpl_subst. clear v.
    eapply type_new; [solve_typing..|].
    intros r. simpl_subst.
    eapply type_delete; [solve_typing..|].
    eapply type_delete; [solve_typing..|].
    eapply (type_jump [_]); solve_typing.
  Qed.

  (* Reading from a cell *)
  Definition cell_get_mut : val :=
    funrec: <> ["x"] := "return" ["x"].

  Lemma cell_get_mut_type `(!Copy ty) :
    typed_instruction_ty [] [] [] cell_get_mut
      (fn (λ α, [☀α])%EL (λ α, [# &uniq{α} (cell ty)])%T (λ α, &uniq{α} ty)%T).
  Proof.
    apply type_fn; [apply _..|]. move=>/= α ret arg. inv_vec arg=>x. simpl_subst.
    eapply (type_jump [_]). solve_typing. rewrite /tctx_incl /=.
    iIntros (???) "_ $$". rewrite !tctx_interp_singleton /tctx_elt_interp /=.
    by iIntros "$".
  Qed.
End typing.

Hint Resolve cell_mono' cell_proper' : lrust_typing.
