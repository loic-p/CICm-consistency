From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules Typing.Subst.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels Codes.Lift Codes.LiftIso.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Lift
  Interp.PiFam Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Def Interp.Inv Interp.Ctx Interp.Subst Interp.Fun Interp.Fund.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* ================================================================== *)
(* THEOREM 9.3: CONSISTENCY.                                           *)
(*                                                                    *)
(* The empty environment is an environment for the empty context       *)
(* (EnvITy nil nil is unit), and `false_`'s interpretation is the       *)
(* proposition `False` itself: propElem carries the Prop it decodes to,  *)
(* and prfF turns it into the family of its proofs, whose elements'      *)
(* prfVal IS that Prop.  So a closed proof of `prf false_` hands 9.2 the  *)
(* data from which `False` is read off directly -- no reduction argument, *)
(* no normalisation, just the totality half of the fundamental lemma.     *)
(* ================================================================== *)

(* the interpretation of `false_`, in any environment: the proposition False *)
Definition falseVal (rho : Env) : kElAt (propFam 0) (ers rho false_) :=
  propElem (ers rho false_) False good_false.

Lemma itm_false rho : ITm rho false_ 0 eprop (propFam 0) (ers rho false_)
                        (falseVal rho).
Proof. exact (i_false rho (ers rho false_) good_false eq_refl). Qed.

Lemma ity_prf_false rho :
  ITy rho (prf false_) 0 (ers rho (prf false_)) (prfF 0 (falseVal rho)).
Proof.
  exact (ity_prf rho false_ (ers rho false_) (falseVal rho) (itm_false rho)).
Qed.

(* A closed proof of `false_` is a proof of False. *)
Theorem consistency (e : tm) (d : ty nil e (prf false_)) : False.
Proof.
  destruct (fund_tot nil e (prf false_) d) as [W He].
  destruct (He nil tt 0 (prfF 0 (falseVal nil)) (ity_prf_false nil)) as [x _].
  exact (prfVal x).
Qed.

(* The same, phrased as the blueprint's 9.3: `prf false_` is not inhabited in
   the empty context. *)
Corollary consistency' : forall e : tm, ty nil e (prf false_) -> False.
Proof. exact consistency. Qed.

Corollary no_proof_of_false : notT { e : tm & ty nil e (prf false_) }.
Proof. intros [e d]; exact (consistency e d). Qed.

(* Two sanity checks that the statement is not vacuous: the type it speaks of is
   a well-formed type of the empty context, and the empty context does type
   closed terms (so `ty nil` is not empty and `EnvITy nil nil` -- which is
   `unit` -- is a real environment). *)
Example ty_prf_false : ty nil (prf false_) (univ 0) :=
  t_prf nil false_ (t_false nil w_nil).

Example ty_one : ty nil (succ zero) nat_ :=
  t_succ nil zero (t_zero nil w_nil).

Example env_nil : EnvITy nil nil := tt.
