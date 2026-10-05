From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per.
From Stdlib Require Import Lia.

(* The layer-1 type system at level n, Allen-style: a Prop-valued inductive
   family whose PER is an index, not computed.  X is the type system of the
   lower levels, consulted only by the universe clause, which is guarded by
   m < n so that u_m lives exactly in the levels above m. *)
Inductive LR (n : nat) (X : nat -> etm -> etm -> PER -> Prop)
  : etm -> etm -> PER -> Prop :=
| LR_ext A A' P Q : LR n X A A' P -> P ≐ Q -> LR n X A A' Q
| LR_exp A B A' B' P : reds A B -> reds A' B' -> LR n X B B' P -> LR n X A A' P
| LR_nat A A' : eval A enat -> eval A' enat -> LR n X A A' NatPer
| LR_prop A A' : eval A eprop -> eval A' eprop -> LR n X A A' PR
| LR_prf A A' p p' : eval A (eprf p) -> eval A' (eprf p') -> PR p p' ->
    LR n X A A' TruePer
| LR_univ A A' m : m < n -> eval A (euniv m) -> eval A' (euniv m) ->
    LR n X A A' (fun C C' => exists P, X m C C' P)
| LR_pi A A' A0 B0 A0' B0' PA PB :
    eval A (epi A0 B0) -> eval A' (epi A0' B0') ->
    LR n X A0 A0' PA ->
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) ->
    LR n X A A' (PiPer PA PB)
| LR_sig A A' A0 B0 A0' B0' PA PB :
    eval A (esig A0 B0) -> eval A' (esig A0' B0') ->
    LR n X A0 A0' PA ->
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) ->
    LR n X A A' (SigPer PA PB)
(* W: the same data as Pi and Sigma -- the label type and the branching
   family -- and the relation WPer they determine. *)
| LR_w A A' A0 B0 A0' B0' PA PB :
    eval A (ew A0 B0) -> eval A' (ew A0' B0') ->
    LR n X A0 A0' PA ->
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) ->
    LR n X A A' (WPer PA PB)
| LR_ne A A' N N' : eval A N -> eval A' N' -> stuck N -> stuck N' ->
    LR n X A A' NePer.

(* below n m is tau m when m < n and empty otherwise; structural in n. *)
Fixpoint below (n : nat) : nat -> etm -> etm -> PER -> Prop :=
  match n with
  | 0 => fun _ _ _ _ => False
  | S n => fun m A A' P => (m = n /\ LR n (below n) A A' P) \/ below n m A A' P
  end.

Definition tau (n : nat) := LR n (below n).

Definition eqty n A A' := exists P, tau n A A' P.
Definition Rel T a b := exists n P, tau n T T P /\ P a b.
Definition Good T a := Rel T a a.
Definition Good_ty T := exists n, eqty n T T.

Lemma below_spec n m A A' P : below n m A A' P <-> (m < n /\ tau m A A' P).
Proof.
  induction n; cbn.
  - split; [tauto | intros [H _]; inversion H].
  - rewrite IHn; unfold tau; split.
    + intros [[-> H] | [H1 H2]]; split; auto; lia.
    + intros [H1 H2]. inversion H1; subst; [left; auto | right; split; [lia | auto]].
Qed.
