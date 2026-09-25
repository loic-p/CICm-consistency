From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def.
From Stdlib Require Import Arith Lia.

(* Cumulativity (B7): LR is monotone in the level bound and in the lower
   levels; the universe clause is the only place where levels interact. *)

Lemma LR_mono n n' X X' : n <= n' ->
  (forall m, m < n -> forall A A' P, X m A A' P <-> X' m A A' P) ->
  forall A A' P, LR n X A A' P -> LR n' X' A A' P.
Proof.
  intros Hn HX.
  induction 1 as
    [ A A' P Q HLR IH HPQ
    | A B A' B' P HrA HrA' HLR IH
    | A A' HeA HeA'
    | A A' HeA HeA'
    | A A' p p' HeA HeA' HPR
    | A A' m Hm HeA HeA'
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' N N' HeA HeA' HsN HsN' ].
  - eapply LR_ext; eassumption.
  - eapply LR_exp; eassumption.
  - apply LR_nat; assumption.
  - apply LR_prop; assumption.
  - eapply LR_prf; eassumption.
  - eapply LR_ext; [apply LR_univ; [eapply Nat.lt_le_trans; eassumption | exact HeA | exact HeA'] |].
    intros C C'; split; intros [P HP]; exists P; apply (HX m Hm); assumption.
  - eapply LR_pi; eauto.
  - eapply LR_sig; eauto.
  - eapply LR_ne; eauto.
Qed.

Lemma below_mono n n' m : n <= n' -> m < n ->
  forall A A' P, below n m A A' P <-> below n' m A A' P.
Proof.
  intros Hn Hm A A' P; rewrite !below_spec; split; intros [? ?]; split; auto; lia.
Qed.

Lemma tau_cumul m n A A' P : m <= n -> tau m A A' P -> tau n A A' P.
Proof.
  intros H; apply LR_mono; auto. intros; apply below_mono; auto.
Qed.

Lemma eqty_cumul m n A A' : m <= n -> eqty m A A' -> eqty n A A'.
Proof. intros H [P HP]; exists P; eapply tau_cumul; eauto. Qed.
