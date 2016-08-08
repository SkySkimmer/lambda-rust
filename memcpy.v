From lrust Require Export notation.
From lrust Require Import heap proofmode.

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #()
    else "dst" <- * "src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].
Opaque memcpy.

Notation "e1 <-{ n } * e2" := (memcpy [e1%RustE ; #(LitInt n) ; e2%RustE])%RustE
  (at level 80, n at next level, format "e1  <-{ n }  * e2") : lrust_expr_scope.

Notation "e1 <-[ i ]{ n } * e2" :=
  (e1%RustE <-[i] ☇ ;; e1+ₗ#1 <-{n} *e2)%RustE
  (at level 80, n, i at next level,
   format "e1  <-[ i ]{ n }  * e2") : lrust_expr_scope.

Lemma wp_memcpy `{heapG Σ} E l1 l2 vl1 vl2 q n Φ:
  nclose heapN ⊆ E →
  length vl1 = n → length vl2 = n →
  heap_ctx ★ l1 ↦★ vl1 ★ l2 ↦★{q} vl2 ★
  ▷ (l1 ↦★ vl2 ★ l2 ↦★{q} vl2 ={E}=★ Φ #())
  ⊢ WP #l1 <-{n} *#l2 @ E {{ Φ }}.
Proof.
  iIntros (? Hvl1 Hvl2) "(#Hinv&Hl1&Hl2&HΦ)".
  iLöb (n l1 l2 vl1 vl2 Hvl1 Hvl2) as "IH". wp_rec. wp_op=> ?; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n]; try discriminate.
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]; rewrite -!heap_mapsto_vec_cons_op.
    iDestruct "Hl1" as "[Hv1 Hl1]". iDestruct "Hl2" as "[Hv2 Hl2]".
    wp_read; wp_write. replace (Z.pos (Pos.of_succ_nat n)) with (n+1) by lia.
    do 3 wp_op. rewrite Z.add_simpl_r.
    iApply ("IH" with "[%] [%] Hl1 Hl2"); try done.
    iIntros "!> [Hl1 Hl2]"; iApply "HΦ"; by iFrame.
Qed.
