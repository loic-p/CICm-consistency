From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck.

(* Lemma 4.1: weak head reduction is deterministic, hence evaluation is
   functional.  Contractions have a value in head position and values do
   not reduce, so a contraction never overlaps a congruence. *)

Lemma red_det t t1 t2 : red t t1 -> red t t2 -> t1 = t2.
Proof.
  intros H; revert t2; induction H; intros t2 H2; inversion H2; subst;
    try reflexivity;
    try solve [exfalso; eapply value_nored; [constructor|eassumption]];
    f_equal; auto.
Qed.

Lemma reds_diamond A B C : reds A B -> reds A C -> reds B C \/ reds C B.
Proof.
  intros H; revert C; induction H; intros C HC; [left; assumption|].
  inversion HC; subst; [right; eauto using reds|].
  match goal with H1 : red t t', H2 : red t ?t2 |- _ =>
    rewrite <- (red_det _ _ _ H1 H2) in * end.
  auto.
Qed.

Lemma eval_whnf w : whnf w -> eval w w.
Proof. split; [constructor|assumption]. Qed.

Lemma eval_red t t' w : red t t' -> eval t' w -> eval t w.
Proof. intros H [Hr Hw]; split; eauto using reds. Qed.

Lemma eval_reds t t' w : reds t t' -> eval t' w -> eval t w.
Proof. intros H [Hr Hw]; split; eauto using reds_trans. Qed.

Lemma eval_red_inv t t' w : red t t' -> eval t w -> eval t' w.
Proof.
  intros H [Hr Hw]; inversion Hr; subst.
  - exfalso; eauto using whnf_nored.
  - match goal with H1 : red t t', H2 : red t ?t2 |- _ =>
      rewrite <- (red_det _ _ _ H1 H2) in * end.
    split; assumption.
Qed.

Lemma eval_reds_inv t t' w : reds t t' -> eval t w -> eval t' w.
Proof. induction 1; eauto using eval_red_inv. Qed.

Lemma eval_det t w w' : eval t w -> eval t w' -> w = w'.
Proof.
  intros [Hr Hw]; revert w'; induction Hr; intros w' [Hr' Hw'].
  - inversion Hr'; subst; [reflexivity|exfalso; eauto using whnf_nored].
  - inversion Hr'; subst; [exfalso; eauto using whnf_nored|].
    match goal with H1 : red t t', H2 : red t ?t2 |- _ =>
      rewrite <- (red_det _ _ _ H1 H2) in * end.
    apply IHHr; first [assumption | split; assumption].
Qed.

Lemma num_inj k k' : num k = num k' -> k = k'.
Proof.
  revert k'; induction k; intros [|k'] H; cbn in H; try discriminate; auto.
  injection H; auto.
Qed.

Lemma eval_num_det t k k' : eval t (num k) -> eval t (num k') -> k = k'.
Proof. intros H1 H2; apply num_inj; eapply eval_det; eassumption. Qed.

Lemma eval_value_id v : value v -> forall w, eval v w -> w = v.
Proof. intros Hv w He; eapply eval_det; [eassumption|apply eval_whnf; left; assumption]. Qed.

Lemma eval_stuck_id v : stuck v -> forall w, eval v w -> w = v.
Proof. intros Hv w He; eapply eval_det; [eassumption|apply eval_whnf; right; assumption]. Qed.

(* A stuck term has no non-stuck evaluation: its only whnf is itself. *)
Lemma eval_stuck_stuck t w : eval t w -> stuck t -> stuck w.
Proof. intros He Hs; rewrite (eval_stuck_id _ Hs _ He); assumption. Qed.
