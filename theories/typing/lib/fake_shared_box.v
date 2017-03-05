From iris.proofmode Require Import tactics.
From iris.base_logic Require Import big_op.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section fake_shared_box.
  Context `{typeG Σ}.

  Definition fake_shared_box : val :=
    funrec: <> ["x"] := Skip ;; "return" ["x"].

  Lemma cell_replace_type ty :
    typed_val fake_shared_box
      (fn (fun '(α, β) => FP [# &shr{α}(&shr{β} ty)]
                             (&shr{α}box ty) [α; β; α ⊑ β]%EL)).
  Proof.
    intros. iApply type_fn; [solve_typing..|]. iIntros "/= !#".
      iIntros ([α β] ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid qE) "#LFT Hna HE HL Hk HT".
    rewrite tctx_interp_singleton tctx_hasty_val.
    rewrite {1}/elctx_interp 2!big_sepL_cons big_sepL_singleton.
    iDestruct "HE" as "(Hα & Hβ & #Hαβ)".
    iAssert (▷ ty_own (own_ptr 1 (&shr{α} box ty)) tid [x])%I with "[HT]" as "HT".
    { destruct x as [[|l|]|]=>//=. iDestruct "HT" as "[H $]".
      iNext. iDestruct "H" as ([|[[]|][]]) "[H↦ H]"; try done.
      iExists _. iFrame. iDestruct "H" as (vl) "[#Hf H]".
      iNext. destruct vl as [|[[|l'|]|][]]; try done. iExists l'. iSplit.
      { iApply frac_bor_iff; last done. iIntros "!>!# *".
        rewrite heap_mapsto_vec_singleton. iSplit; auto. }
      iDestruct "H" as "#H". iIntros "!# * % $". iApply step_fupd_intro. set_solver.
      by iApply ty_shr_mono. }
    wp_seq.
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}box ty) ]%TC
            with "[] LFT Hna [Hα Hβ Hαβ] HL Hk [HT]"); last first.
    { by rewrite tctx_interp_singleton tctx_hasty_val. }
    { rewrite /elctx_interp 2!big_sepL_cons big_sepL_singleton. by iFrame. }
    iApply (type_jump [_]); simpl; solve_typing.
  Qed.
End fake_shared_box.
