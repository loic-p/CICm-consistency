From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def.

(* Lemma 4.2: stuck terms are inert.  Stuckness is preserved by every
   eliminator by construction; here we show stuck and value terms have no
   reduct, and that the two classes are disjoint. *)

Lemma value_nored t t' : value t -> red t t' -> False.
Proof. intros Hv Hr; inversion Hv; subst; inversion Hr. Qed.

Lemma stuck_nored t t' : stuck t -> red t t' -> False.
Proof.
  intros Hs; revert t'; induction Hs; intros t' Hr; inversion Hr; subst; eauto;
    match goal with H : stuck _ |- _ => inversion H end.
Qed.

Lemma whnf_nored t t' : whnf t -> red t t' -> False.
Proof. intros [H|H]; eauto using value_nored, stuck_nored. Qed.

Lemma stuck_not_value t : stuck t -> value t -> False.
Proof. intros Hs Hv; inversion Hv; subst; inversion Hs. Qed.

Lemma whnf_value_or_stuck t : whnf t -> value t \/ stuck t.
Proof. exact (fun H => H). Qed.

Lemma num_value k : value (num k).
Proof. destruct k; constructor. Qed.

Lemma value_whnf t : value t -> whnf t.
Proof. left; assumption. Qed.

Lemma stuck_whnf t : stuck t -> whnf t.
Proof. right; assumption. Qed.

#[export] Hint Resolve value_whnf stuck_whnf num_value : core.
#[export] Hint Constructors value stuck : core.
