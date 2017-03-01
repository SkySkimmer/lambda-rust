From lrust.lang Require Import proofmode.
From lrust.typing Require Export lft_contexts type bool.
Set Default Proof Using "Type".
Import uPred.

Section fixpoint_def.
  Context `{typeG Σ}.
  Context (T : type → type) {HT: TypeContractive T}.

  Global Instance type_inhabited : Inhabited type := populate bool.
  
  Local Instance type_2_contractive : Contractive (Nat.iter 2 T).
  Proof using Type*.
    intros n ? **. simpl.
    by apply dist_later_dist, type_dist2_dist_later, HT, HT, type_later_dist2_later.
  Qed.

  Definition type_fixpoint : type := fixpointK 2 T.
End fixpoint_def.

Lemma type_fixpoint_ne `{typeG Σ} (T1 T2 : type → type)
  `{!TypeContractive T1, !TypeContractive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof. eapply fixpointK_ne; apply type_contractive_ne, _. Qed.

Section fixpoint.
  Context `{typeG Σ}.
  Context (T : type → type) {HT: TypeContractive T}.

  Global Instance fixpoint_copy :
    (∀ `(!Copy ty), Copy (T ty)) → Copy (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply copy_equiv.
    - exists bool. apply _.
    - done.
    - (* If Copy was an Iris assertion, this would be trivial -- we'd just
         use entails_lim once.  However, on the Coq side, it is more convenient
         as a record -- so this is where we pay. *)
      intros c Hc. split.
      + intros tid vl. rewrite /PersistentP. entails_lim c; [solve_proper..|].
        intros. apply (Hc n).
      + intros κ tid E F l q ? ?. entails_lim c; first solve_proper.
        * solve_proper_core ltac:(fun _ => eapply ty_size_ne || f_equiv).
        * intros n. apply (Hc n); first done. erewrite ty_size_ne; first done.
          rewrite conv_compl. done.
  Qed.

  Global Instance fixpoint_send :
    (∀ `(!Send ty), Send (T ty)) → Send (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply send_equiv.
    - exists bool. apply _.
    - done.
    - intros c Hc ???. entails_lim c; [solve_proper..|]. intros n. apply Hc.
  Qed.

  Global Instance fixpoint_sync :
    (∀ `(!Sync ty), Sync (T ty)) → Sync (type_fixpoint T).
  Proof.
    intros ?. unfold type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - apply sync_equiv.
    - exists bool. apply _.
    - done.
    - intros c Hc ????. entails_lim c; [solve_proper..|]. intros n. apply Hc.
  Qed.

  Lemma fixpoint_unfold_eqtype E L : eqtype E L (type_fixpoint T) (T (type_fixpoint T)).
  Proof.
    unfold eqtype, subtype, type_incl.
    setoid_rewrite <-fixpointK_unfold; [| by apply type_contractive_ne, _..].
    split; iIntros "_ _"; (iSplit; first done); iSplit; iIntros "!#*$".
  Qed.
End fixpoint.

Section subtyping.
  Context `{typeG Σ} (E : elctx) (L : llctx).

  (* TODO : is there a way to declare these as a [Proper] instances ? *)
  Lemma fixpoint_mono T1 `{!TypeContractive T1} T2 `{!TypeContractive T2} :
    (∀ ty1 ty2, subtype E L ty1 ty2 → subtype E L (T1 ty1) (T2 ty2)) →
    subtype E L (type_fixpoint T1) (type_fixpoint T2).
  Proof.
    intros H12. rewrite /type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - intros ?? EQ ?. etrans; last done. by apply equiv_subtype.
    - by eexists _.
    - intros. setoid_rewrite (fixpoint_unfold_eqtype T2). by apply H12.
    - intros c Hc. rewrite /subtype. entails_lim c; [solve_proper..|].
      intros n. apply Hc.
  Qed.

  Lemma fixpoint_proper T1 `{TypeContractive T1} T2 `{TypeContractive T2} :
    (∀ ty1 ty2, eqtype E L ty1 ty2 → eqtype E L (T1 ty1) (T2 ty2)) →
    eqtype E L (type_fixpoint T1) (type_fixpoint T2).
  Proof.
    intros H12. rewrite /type_fixpoint. apply fixpointK_ind.
    - apply type_contractive_ne, _.
    - intros ?? EQ ?. etrans; last done. by apply equiv_eqtype.
    - by eexists _.
    - intros. setoid_rewrite (fixpoint_unfold_eqtype T2). by apply H12.
    - intros c Hc. split; rewrite /subtype; (entails_lim c; [solve_proper..|]);
      intros n; apply Hc.
  Qed.

  (* FIXME: Some rewrites here are slower than one would expect. *)
  Lemma fixpoint_unfold_subtype_l ty T `{TypeContractive T} :
    subtype E L ty (T (type_fixpoint T)) → subtype E L ty (type_fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_subtype_r ty T `{TypeContractive T} :
    subtype E L (T (type_fixpoint T)) ty → subtype E L (type_fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_l ty T `{TypeContractive T} :
    eqtype E L ty (T (type_fixpoint T)) → eqtype E L ty (type_fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_r ty T `{TypeContractive T} :
    eqtype E L (T (type_fixpoint T)) ty → eqtype E L (type_fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
End subtyping.

Hint Resolve fixpoint_mono fixpoint_proper : lrust_typing.

(* These hints can loop if [fixpoint_mono] and [fixpoint_proper] have
   not been tried before, so we give them a high cost *)
Hint Resolve fixpoint_unfold_subtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_subtype_r|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_r|100 : lrust_typing.
