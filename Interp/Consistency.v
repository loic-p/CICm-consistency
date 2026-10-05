From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules Typing.Subst Typing.WSubst.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.PiFam Interp.SigFam Interp.WFam Interp.Univ Interp.Env Interp.Elem
  Interp.PiEl Interp.SigEl Interp.WEl Interp.Rec Interp.Lift Interp.LiftN
  Interp.LiftFam Interp.Def Interp.Inv Interp.Ctx Interp.Subst Interp.Fun
  Interp.Fund.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* ================================================================== *)
(* THEOREM 9.3: CONSISTENCY.                                           *)
(*                                                                    *)
(* The empty environment is an environment for the empty context       *)
(* (`EnvITy nil nil` is `unit`), and `false_`'s interpretation is the   *)
(* proposition `False` itself: `propElem` carries the Prop it decodes   *)
(* to, and `prfF` turns it into the family of its proofs, whose          *)
(* elements' `prfVal` IS that Prop.  So a closed proof of `prf false_`   *)
(* hands 9.2 the data from which `False` is read off directly -- no      *)
(* reduction argument, no normalisation, just the totality half of the   *)
(* fundamental lemma.                                                    *)
(* ================================================================== *)

(* the interpretation of `false_ j`, at its own level: the proposition False.
   The realiser is the CONSTANT efalse -- the clause's index, not the free
   realiser the equation ties to the environment -- so the family and its
   element are environment-independent. *)
Definition falseVal (j : nat) : kElAt (propFam j) efalse :=
  propElem efalse False good_false.

Lemma itm_false rho j :
  ITm rho (false_ j) j eprop (propFam j) efalse (falseVal j).
Proof. exact (i_false rho j (ers rho (false_ j)) good_false eq_refl). Qed.

(* `prf k (false_ j)` for any j and k: the Prf's own level says nothing about
   where the proposition lives, so consistency holds at every pair. *)
Lemma ity_prf_false rho k j :
  ITy rho (prf k (false_ j)) k (eprf efalse) (prfF k (falseVal j)).
Proof.
  exact (ity_prf rho k j (false_ j) efalse (falseVal j) (itm_false rho j)).
Qed.

(* A closed proof of `false_` is a proof of False. *)
Theorem consistency (k j : nat) (e : tm) (d : ty nil e (prf k (false_ j))) :
  False.
Proof.
  destruct (fund_tot nil e (prf k (false_ j)) d) as [W He].
  destruct (He nil tt k (prfF k (falseVal j)) (ity_prf_false nil k j)) as [x _].
  exact (prfVal x).
Qed.

(* The same, phrased as the blueprint's 9.3: `prf false_` is not inhabited in
   the empty context. *)
Corollary consistency' : forall k j (e : tm),
  ty nil e (prf k (false_ j)) -> False.
Proof. exact consistency. Qed.

Corollary no_proof_of_false k j :
  { e : tm & ty nil e (prf k (false_ j)) } -> False.
Proof. intros [e d]; exact (consistency k j e d). Qed.

(* Two sanity checks that the statement is not vacuous: the type it speaks of
   is a well-formed type of the empty context, and the empty context does type
   closed terms (so `ty nil` is not empty and `EnvITy nil nil` -- which is
   `unit` -- is a real environment). *)
Example ty_prf_false k : ty nil (prf k (false_ k)) (UU k) :=
  t_prf nil k k (false_ k) (le_n k) (t_false nil k w_nil).

Example ty_one k : ty nil (succ (zero k)) (nat_ k) :=
  t_succ nil k (zero k) (t_zero nil k w_nil).

Example env_nil : EnvITy nil nil := tt.
