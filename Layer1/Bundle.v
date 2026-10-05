From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def.
From CICM Require Export Layer1.Bundle.Inv Layer1.Bundle.Fun Layer1.Bundle.Sym
  Layer1.Bundle.Trans Layer1.Bundle.Cumul.
From Stdlib Require Import Arith Lia.

(* Lemma 6.3 assembled at every level: the hypotheses on the lower levels
   are discharged by an outer induction on the level. *)

Lemma below_XOK_of n : (forall k, k < n -> XOK (tau k)) -> forall k, k < n -> XOK (below n k).
Proof.
  intros IH k Hk; destruct (IH k Hk) as [s t e r st]; constructor.
  - intros A A' P; rewrite !below_spec; intros [? ?]; auto.
  - intros A A' A'' P Q; rewrite !below_spec; intros [? ?] [? ?]; split; eauto.
  - intros A B A' B' P ? ?; rewrite !below_spec; intros [? ?]; split; eauto.
  - intros A A' B B' P; rewrite !below_spec; intros [? ?] ? ?; split; eauto.
  - intros A A' ? ?; destruct (st A A') as [P HP]; auto; exists P; apply below_spec; auto.
Qed.

Lemma tau_XOK_lt : forall n k, k < n -> XOK (tau k).
Proof.
  induction n; intros k Hk; [lia|].
  destruct (Nat.lt_ge_cases k n) as [H|H]; [apply IHn; auto|].
  assert (k = n) by lia; subst k.
  pose proof (below_XOK_of n IHn) as HX.
  constructor.
  - apply (LR_sym n (below n) HX).
  - intros A A' A'' P Q H1 H2; eapply (LR_trans n (below n) HX); eauto.
  - intros; eapply LR_exp; eauto.
  - intros; eapply LR_red; eauto.
  - intros A A' [N [? ?]] [N' [? ?]]; exists NePer; eapply LR_ne; eauto.
Qed.

Lemma below_XOK n k : k < n -> XOK (below n k).
Proof. apply below_XOK_of; intros; eapply tau_XOK_lt; eauto. Qed.

Lemma tau_ok n A A' P : tau n A A' P -> PerOK P.
Proof. apply (LR_ok n (below n) (below_XOK n)). Qed.

Lemma tau_sym n A A' P : tau n A A' P -> tau n A' A P.
Proof. apply (LR_sym n (below n) (below_XOK n)). Qed.

Lemma tau_trans n A A' A'' P Q : tau n A A' P -> tau n A' A'' Q -> tau n A A'' P.
Proof. intros; eapply (LR_trans n (below n) (below_XOK n)); eauto. Qed.

Lemma tau_fun n A A' A'' P Q : tau n A A' P -> tau n A A'' Q -> P ≐ Q.
Proof. intros; eapply LR_fun; eauto. Qed.

Lemma tau_red n A A' B B' P : tau n A A' P -> reds A B -> reds A' B' -> tau n B B' P.
Proof. intros; eapply LR_red; eauto. Qed.

Lemma tau_exp n A A' B B' P : reds A B -> reds A' B' -> tau n B B' P -> tau n A A' P.
Proof. intros; eapply LR_exp; eauto. Qed.

Lemma tau_ext n A A' P Q : tau n A A' P -> P ≐ Q -> tau n A A' Q.
Proof. intros; eapply LR_ext; eauto. Qed.

Lemma tau_stuck n A A' : stuckv A -> stuckv A' -> tau n A A' NePer.
Proof. intros [N [? ?]] [N' [? ?]]; eapply LR_ne; eauto. Qed.

(* eqty is a PER on types, closed under expansion, at each level. *)
Lemma eqty_sym n A A' : eqty n A A' -> eqty n A' A.
Proof. intros [P H]; exists P; apply tau_sym; assumption. Qed.

Lemma eqty_trans n A A' A'' : eqty n A A' -> eqty n A' A'' -> eqty n A A''.
Proof. intros [P H] [Q H']; exists P; eapply tau_trans; eauto. Qed.

Lemma eqty_refl_l n A A' : eqty n A A' -> eqty n A A.
Proof. intros H; eapply eqty_trans; [exact H | apply eqty_sym; exact H]. Qed.

Lemma eqty_refl_r n A A' : eqty n A A' -> eqty n A' A'.
Proof. intros H; eapply eqty_trans; [apply eqty_sym; exact H | exact H]. Qed.

Lemma eqty_exp n A A' B B' : reds A B -> reds A' B' -> eqty n B B' -> eqty n A A'.
Proof. intros ? ? [P H]; exists P; eapply tau_exp; eauto. Qed.

Lemma eqty_red n A A' B B' : eqty n A A' -> reds A B -> reds A' B' -> eqty n B B'.
Proof. intros [P H] ? ?; exists P; eapply tau_red; eauto. Qed.
