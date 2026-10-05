From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.

(* Relation combinators for layer 1.  Every base combinator adjoins the
   pairs of terms that evaluate to stuck terms; forgetting this in one place
   breaks the layer-1 fundamental lemma at the rule that pushes an absurd
   into that position.  For Pi and Sigma the stuck pairs are already in the
   functional clause (a stuck function applied to anything is stuck), and
   adding them as a separate disjunct would break transitivity. *)

Definition PER := etm -> etm -> Prop.

Definition PerEq (P Q : PER) : Prop := forall a b, P a b <-> Q a b.
Notation "P ≐ Q" := (PerEq P Q) (at level 70).

Definition stuckv a := exists N, eval a N /\ stuck N.

(* The relation on naturals is an INDUCTIVE relation, not "both converge to
   the same numeral, or both are stuck".  With the flat definition it is not
   closed under the successor rule: in a context carrying a proof of falsity,
   `succ (absurd N e)` is well typed and its erasure `esucc eerr` is a VALUE
   -- neither a numeral nor stuck -- so the flat relation does not hold of it
   and the layer-1 fundamental lemma fails at t_succ.  Stuck terms have to be
   admitted at the LEAVES of a numeral, not only at the top.  (This is the
   same phenomenon as the paper's first repair, one constructor deeper.) *)
Inductive NatPer : etm -> etm -> Prop :=
| np_zero a b : eval a ezero -> eval b ezero -> NatPer a b
| np_succ a b a' b' : eval a (esucc a') -> eval b (esucc b') -> NatPer a' b' -> NatPer a b
| np_stuck a b : stuckv a -> stuckv b -> NatPer a b.

Definition NePer : PER := fun a b => stuckv a /\ stuckv b.

Definition TruePer : PER := fun _ _ => True.

Definition PiPer (PA : PER) (PB : etm -> etm -> PER) : PER := fun f g =>
  forall u u', PA u u' -> PB u u' (eapp f u) (eapp g u').

Definition SigPer (PA : PER) (PB : etm -> etm -> PER) : PER := fun p q =>
  PA (efst p) (efst q) /\ PB (efst p) (efst q) (esnd p) (esnd q).

(* W.  Unlike Pi and Sigma, whose relations are read off the eliminators, a
   tree is a CONSTRUCTED thing, so its relation is inductive -- like NatPer,
   one constructor for the shape and one for stuck terms, and for the same
   reason: `sup a (absurd ..)` is a value that is neither stuck nor a proper
   tree, so stuck terms have to be admitted at the leaves and not only at the
   top.  The branches are compared at RELATED indices, which is what makes
   the relation a PER rather than an equality of trees. *)
Inductive WPer (PA : PER) (PB : etm -> etm -> PER) : etm -> etm -> Prop :=
| wp_sup w w' a a' f f' :
    eval w (esup a f) -> eval w' (esup a' f') -> PA a a' ->
    (forall u u', PB a a' u u' -> WPer PA PB (eapp f u) (eapp f' u')) ->
    WPer PA PB w w'
| wp_stuck w w' : stuckv w -> stuckv w' -> WPer PA PB w w'.

(* PR: the shape-only relation on propositions.  Layer 1 is truth-blind, so
   two propositions are related as soon as both evaluate to Prop-shaped
   whnfs, or both are stuck. *)
Inductive PR : etm -> etm -> Prop :=
| PR_false p p' : eval p efalse -> eval p' efalse -> PR p p'
| PR_all p p' A B A' B' : eval p (eall A B) -> eval p' (eall A' B') -> PR p p'
| PR_eq p p' A t u A' t' u' :
    eval p (eeqty A t u) -> eval p' (eeqty A' t' u') -> PR p p'
| PR_ne p p' N N' : eval p N -> eval p' N' -> stuck N -> stuck N' -> PR p p'.

Lemma PerEq_refl P : P ≐ P.
Proof. intros a b; tauto. Qed.

Lemma PerEq_sym P Q : P ≐ Q -> Q ≐ P.
Proof. intros H a b; split; apply H. Qed.

Lemma PerEq_trans P Q R : P ≐ Q -> Q ≐ R -> P ≐ R.
Proof. intros H1 H2 a b; split; intro; [apply H2, H1 | apply H1, H2]; assumption. Qed.

Lemma stuckv_exp a b : reds a b -> stuckv b -> stuckv a.
Proof. intros H [N [He Hs]]; exists N; eauto using eval_reds. Qed.

Lemma stuckv_red a b : reds a b -> stuckv a -> stuckv b.
Proof. intros H [N [He Hs]]; exists N; eauto using eval_reds_inv. Qed.

Lemma stuckv_app f u : stuckv f -> stuckv (eapp f u).
Proof.
  intros [N [[Hr Hw] Hs]]; exists (eapp N u); split; [split|]; auto using reds_app, stuck.
Qed.

Lemma stuckv_fst p : stuckv p -> stuckv (efst p).
Proof.
  intros [N [[Hr Hw] Hs]]; exists (efst N); split; [split|]; auto using reds_fst, stuck.
Qed.

Lemma stuckv_snd p : stuckv p -> stuckv (esnd p).
Proof.
  intros [N [[Hr Hw] Hs]]; exists (esnd N); split; [split|]; auto using reds_snd, stuck.
Qed.

Lemma stuckv_rec z s n : stuckv n -> stuckv (enatrec z s n).
Proof.
  intros [N [[Hr _] Hs]]; exists (enatrec z s N); repeat split;
    [apply reds_rec; assumption | right | ]; apply st_rec; assumption.
Qed.

Lemma stuckv_wrec s w : stuckv w -> stuckv (ewrec s w).
Proof.
  intros [N [[Hr _] Hs]]; exists (ewrec s N); repeat split;
    [apply reds_wrec; assumption | right | ]; apply st_wrec; assumption.
Qed.

Lemma stuckv_not_value a v : stuckv a -> eval a v -> value v -> False.
Proof.
  intros [N [He Hs]] Hv Hval; rewrite (eval_det _ _ _ He Hv) in Hs.
  eapply stuck_not_value; eauto.
Qed.

Lemma stuckv_not_num a k : stuckv a -> eval a (num k) -> False.
Proof.
  intros [N [He Hs]] Hk; rewrite (eval_det _ _ _ He Hk) in Hs.
  eapply stuck_not_value; eauto.
Qed.

Ltac PR_ctor :=
  first [ solve [eapply PR_false; eauto]
        | solve [eapply PR_all; eauto]
        | solve [eapply PR_eq; eauto]
        | solve [eapply PR_ne; eauto] ].

Lemma PR_sym p p' : PR p p' -> PR p' p.
Proof. destruct 1; PR_ctor. Qed.

Lemma PR_trans p p' p'' : PR p p' -> PR p' p'' -> PR p p''.
Proof.
  intros H1 H2; destruct H1; inversion H2; subst;
    repeat match goal with
    | H1 : eval ?p ?w, H2 : eval ?p ?w' |- _ =>
        let E := fresh in assert (E := eval_det _ _ _ H1 H2); subst; clear H2;
        try discriminate E; try (injection E; intros; subst)
    end;
    try PR_ctor;
    try solve [exfalso; match goal with H : stuck _ |- _ => solve [inversion H] end].
Qed.

Lemma PR_exp p p1 p' p1' : reds p p1 -> reds p' p1' -> PR p1 p1' -> PR p p'.
Proof.
  intros H1 H2 H; destruct H;
    [eapply PR_false | eapply PR_all | eapply PR_eq | eapply PR_ne];
    eauto using eval_reds.
Qed.

Lemma PR_red p p' q q' : PR p p' -> reds p q -> reds p' q' -> PR q q'.
Proof.
  intros H H1 H2; destruct H;
    [eapply PR_false | eapply PR_all | eapply PR_eq | eapply PR_ne];
    eauto using eval_reds_inv.
Qed.

Lemma PR_stuck p p' : stuckv p -> stuckv p' -> PR p p'.
Proof. intros [N [? ?]] [N' [? ?]]; eapply PR_ne; eauto. Qed.
