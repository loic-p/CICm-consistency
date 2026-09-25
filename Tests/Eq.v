From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Typing.Rules.
From CICM Require Import Interp.Consistency.
From Stdlib Require Import Arith.

Import UnscopedNotations.
Open Scope list_scope.

(* ================================================================== *)
(* TEST 1: decidable equality of numerals as a PROPOSITION, by the      *)
(* large elimination of N, and a closed proof of `eq 0 1 -> False`.      *)
(*                                                                    *)
(* Everything here is a derivation in the OBJECT language CIC^-: the     *)
(* terms are `tm`, the judgements are `Typing/Rules.v`'s `ty` and `cv`.   *)
(* Nothing appeals to the model, except in the last section, where        *)
(* consistency (9.3) is used to show that the companion statement         *)
(* `eq 0 0 -> False` is NOT derivable.                                    *)
(*                                                                    *)
(* Conventions.  `prop` is the impredicative universe of propositions;    *)
(* `prf p` is the TYPE of proofs of `p : prop`, so an implication          *)
(* `p -> q` between propositions is `all (prf p) q`, the impredicative     *)
(* quantifier over the type of proofs of p.  Hence                         *)
(*                                                                    *)
(*   True_ := all (prf false_) false_    (* False -> False *)              *)
(*                                                                    *)
(* and `eq : nat -> nat -> prop` is written with two nested `natrec`s at    *)
(* the motives `pi nat_ prop` and `prop`; the outer one is a LARGE          *)
(* elimination (its motive is a type, not a proposition), which is exactly   *)
(* what this calculus is designed to support.                               *)
(* ================================================================== *)

Definition True_ : tm := all (prf false_) false_.

(* nat -> Prop, the motive of the outer recursion *)
Definition natFun : tm := pi nat_ prop.

(* eq 0 = fun m => natrec prop True_ false_ m : m is zero or it is not *)
Definition eqz : tm := lam nat_ prop (natrec prop True_ false_ (var_tm 0)).

(* eq (succ n) = fun m => natrec prop false_ (eq n (pred m)) m.
   In the step term of the outer recursion the context is
   natFun :: nat_ :: Gamma, so var 0 is `eq n` and var 1 is n; under the
   inner lambda and the inner step's two binders that `eq n` is var 3, and
   the inner predecessor is var 1. *)
Definition eqs : tm :=
  lam nat_ prop
    (natrec prop false_ (app nat_ prop (var_tm 3) (var_tm 1)) (var_tm 0)).

Definition eq_ : tm := lam nat_ natFun (natrec natFun eqz eqs (var_tm 0)).

Definition eqAt (m n : tm) : tm := app nat_ prop (app nat_ natFun eq_ m) n.

(* ---- contexts ---- *)

Lemma wfc_nat G (W : wfc G) : wfc (nat_ :: G).
Proof. exact (w_cons G nat_ 0 W (t_nat G W)). Qed.

Lemma ty_natFun G (W : wfc G) : ty G natFun (univ 0).
Proof.
  exact (t_pi G nat_ prop 0 (t_nat G W) (t_prop (nat_ :: G) (wfc_nat G W))).
Qed.

Lemma wfc_prop G (W : wfc G) : wfc (prop :: G).
Proof. exact (w_cons G prop 0 W (t_prop G W)). Qed.

Lemma wfc_natFun G (W : wfc G) : wfc (natFun :: G).
Proof. exact (w_cons G natFun 0 W (ty_natFun G W)). Qed.

(* ---- the terms are well typed ---- *)

Lemma ty_True_ G (W : wfc G) : ty G True_ prop.
Proof.
  pose proof (t_prf G false_ (t_false G W)) as dP.
  exact (t_all G (prf false_) false_ 0 dP
           (t_false (prf false_ :: G) (w_cons G (prf false_) 0 W dP))).
Qed.

Lemma ty_eqz_body G (W : wfc G) :
  ty (nat_ :: G) (natrec prop True_ false_ (var_tm 0)) prop.
Proof.
  pose proof (wfc_nat G W) as W1.
  exact (t_natrec (nat_ :: G) prop True_ false_ (var_tm 0) 0
           (t_prop (nat_ :: nat_ :: G) (wfc_nat (nat_ :: G) W1))
           (ty_True_ (nat_ :: G) W1)
           (t_false (prop :: nat_ :: nat_ :: G)
              (wfc_prop (nat_ :: nat_ :: G) (wfc_nat (nat_ :: G) W1)))
           (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_))).
Qed.

Lemma ty_eqz G (W : wfc G) : ty G eqz natFun.
Proof.
  exact (t_lam G nat_ prop (natrec prop True_ false_ (var_tm 0)) 0
           (t_nat G W) (t_prop (nat_ :: G) (wfc_nat G W)) (ty_eqz_body G W)).
Qed.

Lemma ty_eqs G (W : wfc G) : ty (natFun :: nat_ :: G) eqs (nrec_succ natFun).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (wfc_natFun (nat_ :: G) W1) as Ws.
  pose proof (wfc_nat _ Ws) as Wm.
  pose proof (wfc_nat _ Wm) as Wp.
  pose proof (wfc_prop _ Wp) as Wq.
  refine (t_lam (natFun :: nat_ :: G) nat_ prop _ 0 (t_nat _ Ws)
            (t_prop _ Wm) _).
  refine (t_natrec _ prop false_ (app nat_ prop (var_tm 3) (var_tm 1))
            (var_tm 0) 0 (t_prop _ Wp) (t_false _ Wm) _
            (t_var _ 0 nat_ Wm (lookup_O _ nat_))).
  (* the step: (eq n) applied to the predecessor of m, in
     prop :: nat_ :: nat_ :: natFun :: nat_ :: G *)
  refine (t_app _ nat_ prop (var_tm 3) (var_tm 1) 0 (t_nat _ Wq)
            (t_prop _ (wfc_nat _ Wq)) _ _).
  - refine (t_var _ 3 natFun Wq _).
    exact (lookup_S (nat_ :: nat_ :: natFun :: nat_ :: G) 2 natFun prop
             (lookup_S (nat_ :: natFun :: nat_ :: G) 1 natFun nat_
                (lookup_S (natFun :: nat_ :: G) 0 natFun nat_
                   (lookup_O (nat_ :: G) natFun)))).
  - refine (t_var _ 1 nat_ Wq _).
    exact (lookup_S (nat_ :: nat_ :: natFun :: nat_ :: G) 0 nat_ prop
             (lookup_O (nat_ :: natFun :: nat_ :: G) nat_)).
Qed.

Lemma ty_eq_body G (W : wfc G) :
  ty (nat_ :: G) (natrec natFun eqz eqs (var_tm 0)) natFun.
Proof.
  pose proof (wfc_nat G W) as W1.
  exact (t_natrec (nat_ :: G) natFun eqz eqs (var_tm 0) 0
           (ty_natFun (nat_ :: nat_ :: G) (wfc_nat (nat_ :: G) W1))
           (ty_eqz (nat_ :: G) W1) (ty_eqs (nat_ :: G) W1)
           (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_))).
Qed.

Theorem ty_eq G (W : wfc G) : ty G eq_ (pi nat_ natFun).
Proof.
  exact (t_lam G nat_ natFun (natrec natFun eqz eqs (var_tm 0)) 0
           (t_nat G W) (ty_natFun (nat_ :: G) (wfc_nat G W)) (ty_eq_body G W)).
Qed.

Lemma ty_eqApp1 G (W : wfc G) m (dm : ty G m nat_) :
  ty G (app nat_ natFun eq_ m) natFun.
Proof.
  exact (t_app G nat_ natFun eq_ m 0 (t_nat G W)
           (ty_natFun (nat_ :: G) (wfc_nat G W)) (ty_eq G W) dm).
Qed.

Theorem ty_eqAt G (W : wfc G) m n (dm : ty G m nat_) (dn : ty G n nat_) :
  ty G (eqAt m n) prop.
Proof.
  exact (t_app G nat_ prop (app nat_ natFun eq_ m) n 0 (t_nat G W)
           (t_prop (nat_ :: G) (wfc_nat G W)) (ty_eqApp1 G W m dm) dn).
Qed.

(* ---- the computations ---- *)

(* eq 0 reduces to the numeral test *)
Lemma cv_eq_zero G (W : wfc G) : cv G (app nat_ natFun eq_ zero) eqz natFun.
Proof.
  pose proof (wfc_nat G W) as W1.
  eapply c_trans.
  - exact (c_beta G nat_ natFun (natrec natFun eqz eqs (var_tm 0)) zero 0
             (t_nat G W) (ty_natFun (nat_ :: G) W1) (ty_eq_body G W)
             (t_zero G W)).
  - exact (c_rec_zero G natFun eqz eqs 0 (ty_natFun (nat_ :: G) W1)
             (ty_eqz G W) (ty_eqs G W)).
Qed.

(* eq 0 1 reduces to False *)
Theorem cv_eq01 G (W : wfc G) : cv G (eqAt zero (succ zero)) false_ prop.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G zero (t_zero G W)) as d1.
  eapply c_trans.
  - (* congruence in the function position *)
    exact (c_app G nat_ prop (app nat_ natFun eq_ zero) eqz (succ zero)
             (succ zero) 0 (t_nat G W) (t_prop (nat_ :: G) W1)
             (ty_eqApp1 G W zero (t_zero G W)) (ty_eqz G W) (cv_eq_zero G W)
             d1 d1 (c_refl G (succ zero) nat_ d1)).
  - eapply c_trans.
    + exact (c_beta G nat_ prop (natrec prop True_ false_ (var_tm 0))
               (succ zero) 0 (t_nat G W) (t_prop (nat_ :: G) W1)
               (ty_eqz_body G W) d1).
    + exact (c_rec_succ G prop True_ false_ zero 0
               (t_prop (nat_ :: G) W1) (ty_True_ G W)
               (t_false (prop :: nat_ :: G) (wfc_prop (nat_ :: G) W1))
               (t_zero G W)).
Qed.

(* ---- the derivation asked for: eq 0 1 -> False ---- *)

Definition eq01 : tm := eqAt zero (succ zero).

(* the identity, at the type `eq 0 1 -> False`: the conversion above is what
   makes its body typecheck *)
Definition eq01_absurd : tm := plam (prf eq01) (var_tm 0).

Theorem ty_eq01_absurd G (W : wfc G) :
  ty G eq01_absurd (prf (all (prf eq01) false_)).
Proof.
  pose proof (t_succ G zero (t_zero G W)) as d1.
  pose proof (ty_eqAt G W zero (succ zero) (t_zero G W) d1) as dEq.
  pose proof (t_prf G eq01 dEq) as dPrf.
  pose proof (w_cons G (prf eq01) 0 W dPrf) as W1.
  pose proof (t_succ _ zero (t_zero _ W1)) as d1'.
  pose proof (ty_eqAt (prf eq01 :: G) W1 zero (succ zero) (t_zero _ W1) d1')
    as dEq'.
  refine (t_all_intro G (prf eq01) false_ (var_tm 0) 0 dPrf (t_false _ W1) _).
  refine (t_conv (prf eq01 :: G) (var_tm 0) (prf eq01) (prf false_) 0
            (t_var _ 0 (prf eq01) W1 (lookup_O G (prf eq01)))
            (t_prf _ eq01 dEq') (t_prf _ false_ (t_false _ W1)) _).
  exact (c_prf _ eq01 false_ dEq' (t_false _ W1) (cv_eq01 _ W1)).
Qed.

(* and in the empty context *)
Theorem eq01_implies_false : ty nil eq01_absurd (prf (all (prf eq01) false_)).
Proof. exact (ty_eq01_absurd nil w_nil). Qed.

(* ================================================================== *)
(* The companion check: `eq 0 0 -> False` is NOT derivable.             *)
(* This is where the model is used -- the syntax alone cannot see it.    *)
(* ================================================================== *)

Theorem cv_eq00 G (W : wfc G) : cv G (eqAt zero zero) True_ prop.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_zero G W) as d0.
  eapply c_trans.
  - exact (c_app G nat_ prop (app nat_ natFun eq_ zero) eqz zero zero 0
             (t_nat G W) (t_prop (nat_ :: G) W1)
             (ty_eqApp1 G W zero d0) (ty_eqz G W) (cv_eq_zero G W)
             d0 d0 (c_refl G zero nat_ d0)).
  - eapply c_trans.
    + exact (c_beta G nat_ prop (natrec prop True_ false_ (var_tm 0)) zero 0
               (t_nat G W) (t_prop (nat_ :: G) W1) (ty_eqz_body G W) d0).
    + exact (c_rec_zero G prop True_ false_ 0 (t_prop (nat_ :: G) W1)
               (ty_True_ G W)
               (t_false (prop :: nat_ :: G) (wfc_prop (nat_ :: G) W1))).
Qed.

(* the canonical proof of `eq 0 0`: the identity on proofs of False, converted *)
Definition eq00_proof : tm := plam (prf false_) (var_tm 0).

Lemma ty_True_proof G (W : wfc G) : ty G eq00_proof (prf True_).
Proof.
  pose proof (t_prf G false_ (t_false G W)) as dP.
  pose proof (w_cons G (prf false_) 0 W dP) as W1.
  exact (t_all_intro G (prf false_) false_ (var_tm 0) 0 dP (t_false _ W1)
           (t_var _ 0 (prf false_) W1 (lookup_O G (prf false_)))).
Qed.

Lemma ty_eq00_proof G (W : wfc G) : ty G eq00_proof (prf (eqAt zero zero)).
Proof.
  pose proof (t_zero G W) as d0.
  pose proof (ty_eqAt G W zero zero d0 d0) as dEq.
  exact (t_conv G eq00_proof (prf True_) (prf (eqAt zero zero)) 0
           (ty_True_proof G W) (t_prf G True_ (ty_True_ G W))
           (t_prf G (eqAt zero zero) dEq)
           (c_prf G True_ (eqAt zero zero) (ty_True_ G W) dEq
              (c_sym G (eqAt zero zero) True_ prop (cv_eq00 G W)))).
Qed.

(* So a closed proof of `eq 0 0 -> False` would prove False outright. *)
Theorem eq00_not_absurd (e : tm)
  (d : ty nil e (prf (all (prf (eqAt zero zero)) false_))) : False.
Proof.
  pose proof (t_zero nil w_nil) as d0.
  pose proof (ty_eqAt nil w_nil zero zero d0 d0) as dEq.
  pose proof (t_prf nil (eqAt zero zero) dEq) as dPrf.
  pose proof (w_cons nil (prf (eqAt zero zero)) 0 w_nil dPrf) as W1.
  refine (consistency (papp e eq00_proof) _).
  exact (t_all_elim nil (prf (eqAt zero zero)) false_ e eq00_proof 0 dPrf
           (t_false _ W1) d (ty_eq00_proof nil w_nil)).
Qed.
