From Coq Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.lang Require Export new_delete.
From lrust.lang Require Import memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.
Set Default Proof Using "Type".

Section own.
  Context `{typeG Σ}.

  Program Definition freeable_sz (n : nat) (sz : nat) (l : loc) : iProp Σ :=
    match sz, n return _ with
    | 0%nat, _ => True
    | _, 0%nat => False
    | sz, n => †{mk_Qp (sz / n) _}l…sz
    end%I.
  Next Obligation. intros _ _ _ sz0 ? n ?. by apply Qcmult_pos_pos. Qed.
  Arguments freeable_sz : simpl never.
  Global Instance freable_sz_timeless n sz l : TimelessP (freeable_sz n sz l).
  Proof. destruct sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ (†{1}l…n ∨ ⌜Z.of_nat n = 0⌝)%I.
  Proof.
    destruct n.
    - iSplit; iIntros "H /="; auto.
    - assert (Z.of_nat (S n) = 0 ↔ False) as -> by done. rewrite right_id.
      rewrite /freeable_sz (proj2 (Qp_eq (mk_Qp _ _) 1)) //= Qcmult_inv_r //.
  Qed.

  Lemma freeable_sz_split n sz1 sz2 l :
    freeable_sz n sz1 l ∗ freeable_sz n sz2 (shift_loc l sz1) ⊣⊢
                freeable_sz n (sz1 + sz2) l.
  Proof.
    destruct sz1; [|destruct sz2;[|rewrite /freeable_sz plus_Sn_m; destruct n]].
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit. by iIntros "[[]?]". by iIntros "[]".
    - rewrite heap_freeable_op_eq. f_equiv. apply Qp_eq.
      rewrite /= -Qcmult_plus_distr_l -Z2Qc_inj_add /Z.add. do 3 f_equal. lia.
  Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.

  Program Definition own_ptr (n : nat) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [subtype_own].

            Since this assertion is timeless, this should not cause
            problems. *)
           ▷ l ↦∗: ty.(ty_own) tid ∗ ▷ freeable_sz n ty.(ty_size) l
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ (∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ] ={F,F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) κ tid l' ∗ q.[κ]))%I
    |}.
  Next Obligation. by iIntros (q ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    move=>n ty N κ l tid ?? /=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb". set_solver.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]". set_solver.
    destruct vl as [|[[|l'|]|][]];
      try (iMod (bor_persistent_tok with "LFT Hb2 Htok") as "[>[]_]"; set_solver).
    iFrame. iExists l'. rewrite heap_mapsto_vec_singleton.
    iMod (bor_sep with "LFT Hb2") as "[Hb2 _]". set_solver.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$". set_solver.
    rewrite bor_unfold_idx. iDestruct "Hb2" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ tid l')%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later with "LFT [Hbtok]") as "Hb"; first solve_ndisj.
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT Hb Htok") as "[#$ $]"; first solve_ndisj.
      iApply "Hclose". auto.
    - iMod fupd_intro_mask' as "Hclose'"; last iModIntro. set_solver.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid l. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb #Hvs]".
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]"). iIntros "!# *% Htok".
    iApply (step_fupd_mask_mono F _ _ (F∖↑shrN∖↑lftN)). set_solver. set_solver.
    iMod (lft_incl_acc with "Hκ Htok") as (q') "[Htok Hclose]"; first set_solver.
    iMod ("Hvs" with "[%] Htok") as "Hvs'". set_solver. iModIntro. iNext.
    iMod "Hvs'" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty.(ty_shr_mono) with "Hκ").
  Qed.

  Lemma own_type_incl n ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (own_ptr n ty1) (own_ptr n ty2).
  Proof.
    iIntros "(#Hsz & #Ho & #Hs)". iSplit; first done. iSplit; iAlways.
    - iIntros (?[|[[| |]|][]]) "H"; try done. simpl.
      iDestruct "H" as "[Hmt H†]". iDestruct "Hmt" as (vl') "[Hmt Hown]". iNext.
      iDestruct ("Ho" with "Hown") as "Hown". iDestruct ("Hsz") as %<-.
      iFrame. iExists _. iFrame.
    - iIntros (???) "H". iDestruct "H" as (l') "[Hfb #Hvs]".
      iExists l'. iFrame. iIntros "!#". iIntros (F' q) "% Htok".
      iMod ("Hvs" with "[%] Htok") as "Hvs'". done. iModIntro. iNext.
      iMod "Hvs'" as "[Hshr $]". iApply ("Hs" with "Hshr").
  Qed.

  Global Instance own_mono E L :
    Proper (ctx_eq E L ==> subtype E L ==> subtype E L) own_ptr.
  Proof.
    intros n1 n2 Hn12 ty1 ty2 Hincl. iIntros.
    iDestruct (Hn12 with "[] []") as %->; [done..|].
    iApply own_type_incl. iApply Hincl; done.
  Qed.
  Lemma own_mono' E L n1 n2 ty1 ty2 :
    ctx_eq E L n1 n2 → subtype E L ty1 ty2 →
    subtype E L (own_ptr n1 ty1) (own_ptr n2 ty2).
  Proof. intros. by apply own_mono. Qed.
  Global Instance own_proper E L :
    Proper (ctx_eq E L ==> eqtype E L ==> eqtype E L) own_ptr.
  Proof. intros ??? ??[]; split; by apply own_mono. Qed.
  Lemma own_proper' E L n1 n2 ty1 ty2 :
    ctx_eq E L n1 n2 → eqtype E L ty1 ty2 →
    eqtype E L (own_ptr n1 ty1) (own_ptr n2 ty2).
  Proof. intros. by apply own_proper. Qed.

  Global Instance own_type_contractive n : TypeContractive (own_ptr n).
  Proof. solve_type_proper. Qed.

  Global Instance own_ne n : NonExpansive (own_ptr n).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance own_send n ty :
    Send ty → Send (own_ptr n ty).
  Proof.
    iIntros (Hsend tid1 tid2 [|[[| |]|][]]) "H"; try done.
    iDestruct "H" as "[Hm $]". iNext. iApply (heap_mapsto_pred_wand with "Hm").
    iIntros (vl) "?". by iApply Hsend.
  Qed.

  Global Instance own_sync n ty :
    Sync ty → Sync (own_ptr n ty).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists _. iFrame "Hm". iAlways. iIntros (F q) "% Htok".
    iMod ("Hshr" with "[] Htok") as "Hfin"; first done. iModIntro. iNext.
    iMod "Hfin" as "{Hshr} [Hshr $]". by iApply Hsync.
  Qed.
End own.

(* TODO: Make box a proper type with subtyping, contractivity, ... *)
Notation box ty := (own_ptr ty.(ty_size) ty).

Section typing.
  Context `{typeG Σ}.

  (** Typing *)
  Lemma write_own {E L} ty ty' n :
    ty.(ty_size) = ty'.(ty_size) → typed_write E L (own_ptr n ty') ty (own_ptr n ty).
  Proof.
    iIntros (Hsz) "!#". iIntros ([[]|] tid F qE qL ?) "_ $ $ Hown"; try done.
    rewrite /= Hsz. iDestruct "Hown" as "[H↦ $]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iExists _, _. iFrame "H↦". auto.
  Qed.

  Lemma read_own_copy E L ty n :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty).
  Proof.
    iIntros (Hsz) "!#". iIntros ([[]|] tid F qE qL ?) "_ $ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iExists l, _, _. iFrame "∗#". iSplitR; first done. iIntros "!> Hl !>".
    iExists _. auto.
  Qed.

  Lemma read_own_move E L ty n :
    typed_read E L (own_ptr n ty) ty (own_ptr n $ uninit ty.(ty_size)).
  Proof.
    iAlways. iIntros ([[]|] tid F qE qL ?) "_ $ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%".
    iExists l, vl, _. iFrame "∗#". iSplitR; first done. iIntros "!> Hl !> !>".
    iExists _. iFrame. by iApply uninit_own.
  Qed.

  Lemma type_new_instr {E L} (n : Z) :
    0 ≤ n →
    let n' := Z.to_nat n in
    typed_instruction_ty E L [] (new [ #n ]%E) (own_ptr n' (uninit n')).
  Proof.
    iIntros (? tid q) "#LFT $ $ $ _".
    iApply wp_new; first done. iModIntro.
    iIntros (l vl) "(% & H† & Hlft)". subst. rewrite tctx_interp_singleton tctx_hasty_val.
    iNext. rewrite freeable_sz_full Z2Nat.id //. iFrame.
    iExists vl. iFrame. by rewrite Nat2Z.id uninit_own.
  Qed.

  Lemma type_new E L C T x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    (∀ (v : val) (n' := Z.to_nat n),
        typed_body E L C ((v ◁ box (uninit n')) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof. iIntros. iApply type_let; [by apply type_new_instr|solve_typing..]. Qed.

  Lemma type_new_subtype ty E L C T x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    let n' := Z.to_nat n in
    subtype E L (uninit n') ty →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr n' ty) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof.
    iIntros (????) "Htyp". iApply type_let; [by apply type_new_instr|solve_typing|].
    iIntros (v). iApply typed_body_mono; last iApply "Htyp"; try done.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, own_mono.
  Qed.

  Lemma type_delete_instr {E L} ty (n : Z) p :
    Z.of_nat (ty.(ty_size)) = n →
    typed_instruction E L [p ◁ box ty] (delete [ #n; p])%E (λ _, []).
  Proof.
    iIntros (<- tid eq) "#LFT $ $ $ Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros ([[]|]) "_ Hown"; try done.
    iDestruct "Hown" as "[H↦: >H†]". iDestruct "H↦:" as (vl) "[>H↦ Hown]".
    rewrite tctx_interp_nil. iDestruct (ty_size_eq with "Hown") as "#>EQ".
    iDestruct "EQ" as %<-. iApply (wp_delete with "[-]"); auto; [].
    rewrite freeable_sz_full. by iFrame.
  Qed.

  Lemma type_delete {E L} ty C T T' (n' : nat) (n : Z)  p e :
    Closed [] e →
    tctx_extract_hasty E L p (own_ptr n' ty) T T' →
    n = n' → Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C T' e -∗
    typed_body E L C T (delete [ #n; p ] ;; e).
  Proof.
    iIntros (?? -> Hlen) "?". iApply type_seq; [by apply type_delete_instr| |done].
    by rewrite (inj _ _ _ Hlen).
  Qed.

  Lemma type_letalloc_1 {E L} ty C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty T T' →
    ty.(ty_size) = 1%nat →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr 1 ty)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <- p in e).
  Proof.
    iIntros. iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_weaken with set_solver.
    - done.
    - iIntros (xv) "/=".
      assert (subst x xv (x <- p ;; e)%E = (xv <- p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst. done. set_solver. }
      iApply type_assign; [|solve_typing|by eapply write_own|done].
      apply subst_is_closed; last done. apply is_closed_of_val.
  Qed.

  Lemma type_letalloc_n {E L} ty ty1 ty2 C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty1 T T' →
    typed_read E L ty1 ty ty2 →
    (∀ (v : val),
        typed_body E L C ((v ◁ own_ptr (ty.(ty_size)) ty)::(p ◁ ty2)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e).
  Proof.
    iIntros. iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_of_val, is_closed_weaken with set_solver.
    - lia.
    - iIntros (xv) "/=".
      assert (subst x xv (x <-{ty.(ty_size)} !p ;; e)%E =
              (xv <-{ty.(ty_size)} !p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - eapply (is_closed_subst []). apply is_closed_of_val. set_solver.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst. done. set_solver. }
      rewrite Nat2Z.id. iApply type_memcpy.
      + apply subst_is_closed; last done. apply is_closed_of_val.
      + solve_typing.
      + (* TODO: Doing "eassumption" here shows that unification takes *forever* to fail.
           I guess that's caused by it trying to unify typed_read and typed_write,
           but considering that the Iris connectives are all sealed, why does
           that take so long? *)
        by eapply (write_own ty (uninit _)).
      + solve_typing.
      + done.
      + done.
  Qed.
End typing.

Hint Resolve own_mono' own_proper' : lrust_typing.

Hint Extern 100 (_ ≤ _) => simpl; lia : lrust_typing.
Hint Extern 100 (@eq Z _ _) => simpl; lia : lrust_typing.
Hint Extern 100 (@eq nat _ _) => simpl; lia : lrust_typing.
