From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Ranks.Pred.
From Stdlib Require Import Arith Lia.

(* Lemma 7.4: layer-1 good types are accessible for the component relation.
   With universes handled by the outer recursion on levels (Codes/), the
   universe clause has no components and a single induction on the LR
   derivation suffices.

   The relation prec is not well founded on all terms: Y (\x. Pi x B)
   evaluates to Pi A B with A its own component, so the Good hypothesis
   cannot be dropped. *)

Lemma prec_red A B : reds A B -> forall C, prec C A -> prec C B.
Proof.
  intros H C [p Hp].
  exists (Pred_red (fun w e => eval_reds_inv _ _ _ H e) p).
  rewrite pred_Pred_red; assumption.
Qed.

Lemma tau_acc n A A' P : tau n A A' P -> Acc prec A.
Proof.
  unfold tau.
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
  - exact IH.
  - constructor; intros C HC; apply (Acc_inv IH); eapply prec_red; eauto.
  - constructor; intros C [q Hq]; destruct q; eval_confl.
  - constructor; intros C [q Hq]; destruct q; eval_confl.
  - constructor; intros C [q Hq]; destruct q; eval_confl.
  - constructor; intros C [q Hq]; destruct q; eval_confl.
  - constructor; intros C [q Hq]; destruct q as [C0 D0 e | C0 D0 u e g | C0 D0 e | C0 D0 u e g];
      eval_confl; cbn in *; try subst C; cbn.
    + exact IHA.
    + apply (IHB u u). destruct g as [k [Q [HQ Hu]]].
      assert (EQ : PA ≐ Q).
      { eapply tau_fun; [apply (tau_cumul n (Nat.max n k)); [apply Nat.le_max_l | exact HA]
                        | apply (tau_cumul k (Nat.max n k)); [apply Nat.le_max_r | exact HQ]]. }
      apply EQ; exact Hu.
  - constructor; intros C [q Hq]; destruct q as [C0 D0 e | C0 D0 u e g | C0 D0 e | C0 D0 u e g];
      eval_confl; cbn in *; try subst C; cbn.
    + exact IHA.
    + apply (IHB u u). destruct g as [k [Q [HQ Hu]]].
      assert (EQ : PA ≐ Q).
      { eapply tau_fun; [apply (tau_cumul n (Nat.max n k)); [apply Nat.le_max_l | exact HA]
                        | apply (tau_cumul k (Nat.max n k)); [apply Nat.le_max_r | exact HQ]]. }
      apply EQ; exact Hu.
  - constructor; intros C [q Hq]; destruct q; eval_confl.
Qed.

Lemma eqty_acc n A A' : eqty n A A' -> Acc prec A.
Proof. intros [P H]; eapply tau_acc; eauto. Qed.

Lemma Good_ty_acc A : Good_ty A -> Acc prec A.
Proof. intros [n H]; eapply eqty_acc; eauto. Qed.
