From Coq.QArith Require Import Qcanon.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
Set Default Proof Using "Type".

Definition mutexN := lrustN .@ "mutex".

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mutex.
  Context `{!typeG Σ, !lockG Σ}.

  (*
    pub struct Mutex<T: ?Sized> {
      // Note that this mutex is in a *box*, not inlined into the struct itself.
      // Once a native mutex has been used once, its address can never change (it
      // can't be moved). This mutex type can be safely moved at any time, so to
      // ensure that the native mutex is used correctly we box the inner lock to
      // give it a constant address.
      inner: Box<sys::Mutex>,
      poison: poison::Flag,
      data: UnsafeCell<T>,
    }
  *)

  Program Definition mutex (ty : type) :=
    {| ty_size := 1 + ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' =>
           ⌜∃ b, z = Z_of_bool b⌝ ∗ ty.(ty_own) tid vl'
         | _ => False end;
       ty_shr κ tid l :=
         ∃ γ κ',
           &shr{κ, mutexN} (lock_proto γ l (&{κ'} shift_loc l 1 ↦∗: ty.(ty_own) tid)) ∗ κ ⊑ κ'
    |}%I.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %] !% /=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hbor Htok".
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[H Hclose]"; first done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    rewrite heap_mapsto_vec_cons. iDestruct "H↦" as ">[Hl H↦]".
    iDestruct "H" as "[>EQ Hown]". iDestruct "EQ" as %[b ->].
    (* We need to turn the ohne borrow into two, so we close it -- and then
       we open one of them again. *)
    iMod ("Hclose" $! ((∃ b, l ↦ #(Z_of_bool b)) ∗ (shift_loc l 1 ↦∗: ty_own ty tid))%I
          with "[] [Hl H↦ Hown]") as "[Hbor Htok]".
    { clear. iNext. iIntros "[Hl Hown] !>". iNext. iDestruct "Hl" as (b) "Hl".
      iDestruct "Hown" as (vl) "[H↦ Hown]". iExists (#(Z_of_bool b) :: vl).
      rewrite heap_mapsto_vec_cons. iFrame. iPureIntro. eauto. }
    { iNext. iSplitL "Hl"; first by eauto.
      iExists vl. iFrame. }
    clear b vl. iMod (bor_sep with "LFT Hbor") as "[Hl Hbor]"; first done.
    iMod (bor_acc_cons with "LFT Hl Htok") as "[>Hl Hclose]"; first done.
    iDestruct "Hl" as (b) "Hl".
    iMod (lock_proto_create with "Hl [Hbor]") as (γ) "Hproto".
    { destruct b; last by iExact "Hbor". done. }
    iMod ("Hclose" with "[] Hproto") as "[Hl Htok]".
    { clear b. iIntros "!> Hproto !>". iDestruct (lock_proto_destroy with "Hproto") as (b) "[Hl _]".
      iNext. eauto with iFrame. }
    iFrame "Htok". iExists γ, κ.
    iMod (bor_share with "Hl") as "$"; [solve_ndisj..|].
    iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H".
    iDestruct "H" as (γ κ'') "(#Hlck & #Hlft)".
    iExists _, _. iSplit; first by iApply shr_bor_shorten.
    iApply lft_incl_trans; done.
  Qed.

  Global Instance mutex_wf ty `{!TyWf ty} : TyWf (mutex ty) :=
    { ty_lfts := ty.(ty_lfts); ty_wf_E := ty.(ty_wf_E) }.

End mutex.
