From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Typing.Rules.
From Stdlib Require Import Arith.

Open Scope list_scope.

(* ================================================================== *)
(* TEST 1: decidable equality of numerals as a PROPOSITION, by the      *)
(* large elimination of N, and a closed proof of `eq 0 1 -> False`.      *)
(*                                                                    *)
(* Everything here is a derivation in the OBJECT language CIC^-: the     *)
(* terms are `tm`, the judgements are `Typing/Rules.v`'s `ty` and `cv`.   *)
(* Nothing here appeals to the model: this file is pure object language.  *)
(* The companion statement -- that `eq 0 0 -> False` is NOT derivable --   *)
(* needs consistency (9.3) and waits for Interp/ to be ported.             *)
(*                                                                    *)
(* Conventions.  `prop` is the impredicative universe of propositions;    *)
(* `prf p` is the TYPE of proofs of `p : prop`, so an implication          *)
(* `p -> q` between propositions is `all (prf p) q`, the impredicative     *)
(* quantifier over the type of proofs of p.  Hence                         *)
(*                                                                    *)
(*   True_ := all 0 (prf 0 (false_ 0)) (false_ 0)   (* False -> False *)    *)
(*                                                                    *)
(* and `eq : nat -> nat -> prop` is written with two nested `natrec`s at    *)
(* the motives `pi nat_ prop` and `prop`; the outer one is a LARGE          *)
(* elimination (its motive is a type, not a proposition), which is exactly   *)
(* what this calculus is designed to support.                               *)
(*                                                                    *)
(* Every former carries the level it lives at; nothing here needs more than  *)
(* level 0, so every annotation below is 0 and every `j <= k` premise is     *)
(* `le_n 0`.                                                                *)
(* ================================================================== *)

Definition True_ : tm := all 0 (prf 0 (false_ 0)) (false_ 0).

(* nat -> Prop, the motive of the outer recursion *)
Definition natFun : tm := pi 0 (nat_ 0) (prop 0).

(* eq 0 = fun m => natrec prop True_ false_ m : m is zero or it is not *)
Definition eqz : tm :=
  lam 0 (nat_ 0) (prop 0) (natrec (prop 0) True_ (false_ 0) (var_tm 0)).

(* eq (succ n) = fun m => natrec prop false_ (eq n (pred m)) m.
   In the step term of the outer recursion the context is
   natFun :: nat_ :: Gamma, so var 0 is `eq n` and var 1 is n; under the
   inner lambda and the inner step's two binders that `eq n` is var 3, and
   the inner predecessor is var 1. *)
Definition eqs : tm :=
  lam 0 (nat_ 0) (prop 0)
    (natrec (prop 0) (false_ 0)
       (app (nat_ 0) (prop 0) (var_tm 3) (var_tm 1)) (var_tm 0)).

Definition eq_ : tm :=
  lam 0 (nat_ 0) natFun (natrec natFun eqz eqs (var_tm 0)).

Definition eqAt (m n : tm) : tm :=
  app (nat_ 0) (prop 0) (app (nat_ 0) natFun eq_ m) n.

(* ---- contexts ---- *)

Lemma wfc_nat G (W : wfc G) : wfc (nat_ 0 :: G).
Proof. exact (w_cons G (nat_ 0) 0 W (t_nat G 0 W)). Qed.

Lemma ty_natFun G (W : wfc G) : ty G natFun (UU 0).
Proof.
  exact (t_pi G 0 0 0 (nat_ 0) (prop 0) (le_n 0) (le_n 0) (t_nat G 0 W)
           (t_prop (nat_ 0 :: G) 0 (wfc_nat G W))).
Qed.

Lemma wfc_prop G (W : wfc G) : wfc (prop 0 :: G).
Proof. exact (w_cons G (prop 0) 0 W (t_prop G 0 W)). Qed.

Lemma wfc_natFun G (W : wfc G) : wfc (natFun :: G).
Proof. exact (w_cons G natFun 0 W (ty_natFun G W)). Qed.

(* ---- the terms are well typed ---- *)

Lemma ty_True_ G (W : wfc G) : ty G True_ (prop 0).
Proof.
  pose proof (t_prf G 0 0 (false_ 0) (le_n 0) (t_false G 0 W)) as dP.
  exact (t_all G (prf 0 (false_ 0)) (false_ 0) 0 0 dP
           (t_false (prf 0 (false_ 0) :: G) 0
              (w_cons G (prf 0 (false_ 0)) 0 W dP))).
Qed.

Lemma ty_eqz_body G (W : wfc G) :
  ty (nat_ 0 :: G) (natrec (prop 0) True_ (false_ 0) (var_tm 0)) (prop 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  exact (t_natrec (nat_ 0 :: G) (prop 0) True_ (false_ 0) (var_tm 0) 0 0
           (t_prop (nat_ 0 :: nat_ 0 :: G) 0 (wfc_nat (nat_ 0 :: G) W1))
           (ty_True_ (nat_ 0 :: G) W1)
           (t_false (prop 0 :: nat_ 0 :: nat_ 0 :: G) 0
              (wfc_prop (nat_ 0 :: nat_ 0 :: G) (wfc_nat (nat_ 0 :: G) W1)))
           (t_var (nat_ 0 :: G) 0 (nat_ 0) W1 (lookup_O G (nat_ 0)))).
Qed.

Lemma ty_eqz G (W : wfc G) : ty G eqz natFun.
Proof.
  exact (t_lam G 0 0 0 (nat_ 0) (prop 0)
           (natrec (prop 0) True_ (false_ 0) (var_tm 0)) (le_n 0) (le_n 0)
           (t_nat G 0 W) (t_prop (nat_ 0 :: G) 0 (wfc_nat G W))
           (ty_eqz_body G W)).
Qed.

Lemma ty_eqs G (W : wfc G) :
  ty (natFun :: nat_ 0 :: G) eqs (nrec_succ natFun).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (wfc_natFun (nat_ 0 :: G) W1) as Ws.
  pose proof (wfc_nat _ Ws) as Wm.
  pose proof (wfc_nat _ Wm) as Wp.
  pose proof (wfc_prop _ Wp) as Wq.
  refine (t_lam (natFun :: nat_ 0 :: G) 0 0 0 (nat_ 0) (prop 0) _ (le_n 0) (le_n 0)
            (t_nat _ 0 Ws) (t_prop _ 0 Wm) _).
  refine (t_natrec _ (prop 0) (false_ 0)
            (app (nat_ 0) (prop 0) (var_tm 3) (var_tm 1)) (var_tm 0) 0 0
            (t_prop _ 0 Wp) (t_false _ 0 Wm) _
            (t_var _ 0 (nat_ 0) Wm (lookup_O _ (nat_ 0)))).
  (* the step: (eq n) applied to the predecessor of m, in
     prop :: nat_ :: nat_ :: natFun :: nat_ :: G *)
  refine (t_app _ 0 0 0 (nat_ 0) (prop 0) (var_tm 3) (var_tm 1) (le_n 0) (le_n 0)
            (t_nat _ 0 Wq) (t_prop _ 0 (wfc_nat _ Wq)) _ _).
  - refine (t_var _ 3 natFun Wq _).
    exact (lookup_S (nat_ 0 :: nat_ 0 :: natFun :: nat_ 0 :: G) 2 natFun
             (prop 0)
             (lookup_S (nat_ 0 :: natFun :: nat_ 0 :: G) 1 natFun (nat_ 0)
                (lookup_S (natFun :: nat_ 0 :: G) 0 natFun (nat_ 0)
                   (lookup_O (nat_ 0 :: G) natFun)))).
  - refine (t_var _ 1 (nat_ 0) Wq _).
    exact (lookup_S (nat_ 0 :: nat_ 0 :: natFun :: nat_ 0 :: G) 0 (nat_ 0)
             (prop 0)
             (lookup_O (nat_ 0 :: natFun :: nat_ 0 :: G) (nat_ 0))).
Qed.

Lemma ty_eq_body G (W : wfc G) :
  ty (nat_ 0 :: G) (natrec natFun eqz eqs (var_tm 0)) natFun.
Proof.
  pose proof (wfc_nat G W) as W1.
  exact (t_natrec (nat_ 0 :: G) natFun eqz eqs (var_tm 0) 0 0
           (ty_natFun (nat_ 0 :: nat_ 0 :: G) (wfc_nat (nat_ 0 :: G) W1))
           (ty_eqz (nat_ 0 :: G) W1) (ty_eqs (nat_ 0 :: G) W1)
           (t_var (nat_ 0 :: G) 0 (nat_ 0) W1 (lookup_O G (nat_ 0)))).
Qed.

Theorem ty_eq G (W : wfc G) : ty G eq_ (pi 0 (nat_ 0) natFun).
Proof.
  exact (t_lam G 0 0 0 (nat_ 0) natFun (natrec natFun eqz eqs (var_tm 0))
           (le_n 0) (le_n 0) (t_nat G 0 W)
           (ty_natFun (nat_ 0 :: G) (wfc_nat G W)) (ty_eq_body G W)).
Qed.

Lemma ty_eqApp1 G (W : wfc G) m (dm : ty G m (nat_ 0)) :
  ty G (app (nat_ 0) natFun eq_ m) natFun.
Proof.
  exact (t_app G 0 0 0 (nat_ 0) natFun eq_ m (le_n 0) (le_n 0) (t_nat G 0 W)
           (ty_natFun (nat_ 0 :: G) (wfc_nat G W)) (ty_eq G W) dm).
Qed.

Theorem ty_eqAt G (W : wfc G) m n (dm : ty G m (nat_ 0)) (dn : ty G n (nat_ 0)) :
  ty G (eqAt m n) (prop 0).
Proof.
  exact (t_app G 0 0 0 (nat_ 0) (prop 0) (app (nat_ 0) natFun eq_ m) n (le_n 0) (le_n 0)
           (t_nat G 0 W) (t_prop (nat_ 0 :: G) 0 (wfc_nat G W))
           (ty_eqApp1 G W m dm) dn).
Qed.

(* ---- the computations ---- *)

(* eq 0 reduces to the numeral test *)
Lemma cv_eq_zero G (W : wfc G) :
  cv G (app (nat_ 0) natFun eq_ (zero 0)) eqz natFun.
Proof.
  pose proof (wfc_nat G W) as W1.
  eapply c_trans.
  - exact (c_beta G 0 0 0 (nat_ 0) natFun (natrec natFun eqz eqs (var_tm 0))
             (zero 0) (le_n 0) (le_n 0) (t_nat G 0 W) (ty_natFun (nat_ 0 :: G) W1)
             (ty_eq_body G W) (t_zero G 0 W)).
  - exact (c_rec_zero G natFun eqz eqs 0 0 (ty_natFun (nat_ 0 :: G) W1)
             (ty_eqz G W) (ty_eqs G W)).
Qed.

(* eq 0 1 reduces to False *)
Theorem cv_eq01 G (W : wfc G) :
  cv G (eqAt (zero 0) (succ (zero 0))) (false_ 0) (prop 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G 0 (zero 0) (t_zero G 0 W)) as d1.
  eapply c_trans.
  - (* congruence in the function position *)
    exact (c_app G 0 0 0 (nat_ 0) (prop 0) (app (nat_ 0) natFun eq_ (zero 0)) eqz
             (succ (zero 0)) (succ (zero 0)) (le_n 0) (le_n 0) (t_nat G 0 W)
             (t_prop (nat_ 0 :: G) 0 W1)
             (ty_eqApp1 G W (zero 0) (t_zero G 0 W)) (ty_eqz G W)
             (cv_eq_zero G W) d1 d1 (c_refl G (succ (zero 0)) (nat_ 0) d1)).
  - eapply c_trans.
    + exact (c_beta G 0 0 0 (nat_ 0) (prop 0)
               (natrec (prop 0) True_ (false_ 0) (var_tm 0)) (succ (zero 0))
               (le_n 0) (le_n 0) (t_nat G 0 W) (t_prop (nat_ 0 :: G) 0 W1)
               (ty_eqz_body G W) d1).
    + exact (c_rec_succ G (prop 0) True_ (false_ 0) (zero 0) 0 0
               (t_prop (nat_ 0 :: G) 0 W1) (ty_True_ G W)
               (t_false (prop 0 :: nat_ 0 :: G) 0 (wfc_prop (nat_ 0 :: G) W1))
               (t_zero G 0 W)).
Qed.

(* ---- the derivation asked for: eq 0 1 -> False ---- *)

Definition eq01 : tm := eqAt (zero 0) (succ (zero 0)).

(* the identity, at the type `eq 0 1 -> False`: the conversion above is what
   makes its body typecheck *)
Definition eq01_absurd : tm := plam (prf 0 eq01) (var_tm 0).

Theorem ty_eq01_absurd G (W : wfc G) :
  ty G eq01_absurd (prf 0 (all 0 (prf 0 eq01) (false_ 0))).
Proof.
  pose proof (t_succ G 0 (zero 0) (t_zero G 0 W)) as d1.
  pose proof (ty_eqAt G W (zero 0) (succ (zero 0)) (t_zero G 0 W) d1) as dEq.
  pose proof (t_prf G 0 0 eq01 (le_n 0) dEq) as dPrf.
  pose proof (w_cons G (prf 0 eq01) 0 W dPrf) as W1.
  pose proof (t_succ _ 0 (zero 0) (t_zero _ 0 W1)) as d1'.
  pose proof (ty_eqAt (prf 0 eq01 :: G) W1 (zero 0) (succ (zero 0))
                (t_zero _ 0 W1) d1') as dEq'.
  refine (t_all_intro G (prf 0 eq01) (false_ 0) (var_tm 0) 0 0 dPrf
            (t_false _ 0 W1) _).
  refine (t_conv (prf 0 eq01 :: G) (var_tm 0) (prf 0 eq01) (prf 0 (false_ 0)) 0
            (t_var _ 0 (prf 0 eq01) W1 (lookup_O G (prf 0 eq01)))
            (t_prf _ 0 0 eq01 (le_n 0) dEq')
            (t_prf _ 0 0 (false_ 0) (le_n 0) (t_false _ 0 W1)) _).
  exact (c_prf _ 0 0 eq01 (false_ 0) (le_n 0) dEq' (t_false _ 0 W1)
           (cv_eq01 _ W1)).
Qed.

(* and in the empty context *)
Theorem eq01_implies_false :
  ty nil eq01_absurd (prf 0 (all 0 (prf 0 eq01) (false_ 0))).
Proof. exact (ty_eq01_absurd nil w_nil). Qed.

(* ================================================================== *)
(* The companion check: `eq 0 0 -> False` is NOT derivable.             *)
(* This is where the model is used -- the syntax alone cannot see it.    *)
(* ================================================================== *)

Theorem cv_eq00 G (W : wfc G) :
  cv G (eqAt (zero 0) (zero 0)) True_ (prop 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_zero G 0 W) as d0.
  eapply c_trans.
  - exact (c_app G 0 0 0 (nat_ 0) (prop 0) (app (nat_ 0) natFun eq_ (zero 0)) eqz
             (zero 0) (zero 0) (le_n 0) (le_n 0) (t_nat G 0 W)
             (t_prop (nat_ 0 :: G) 0 W1)
             (ty_eqApp1 G W (zero 0) d0) (ty_eqz G W) (cv_eq_zero G W)
             d0 d0 (c_refl G (zero 0) (nat_ 0) d0)).
  - eapply c_trans.
    + exact (c_beta G 0 0 0 (nat_ 0) (prop 0)
               (natrec (prop 0) True_ (false_ 0) (var_tm 0)) (zero 0) (le_n 0) (le_n 0)
               (t_nat G 0 W) (t_prop (nat_ 0 :: G) 0 W1) (ty_eqz_body G W) d0).
    + exact (c_rec_zero G (prop 0) True_ (false_ 0) 0 0
               (t_prop (nat_ 0 :: G) 0 W1) (ty_True_ G W)
               (t_false (prop 0 :: nat_ 0 :: G) 0
                  (wfc_prop (nat_ 0 :: G) W1))).
Qed.

(* the canonical proof of `eq 0 0`: the identity on proofs of False, converted *)
Definition eq00_proof : tm := plam (prf 0 (false_ 0)) (var_tm 0).

Lemma ty_True_proof G (W : wfc G) : ty G eq00_proof (prf 0 True_).
Proof.
  pose proof (t_prf G 0 0 (false_ 0) (le_n 0) (t_false G 0 W)) as dP.
  pose proof (w_cons G (prf 0 (false_ 0)) 0 W dP) as W1.
  exact (t_all_intro G (prf 0 (false_ 0)) (false_ 0) (var_tm 0) 0 0 dP
           (t_false _ 0 W1)
           (t_var _ 0 (prf 0 (false_ 0)) W1 (lookup_O G (prf 0 (false_ 0))))).
Qed.

Lemma ty_eq00_proof G (W : wfc G) :
  ty G eq00_proof (prf 0 (eqAt (zero 0) (zero 0))).
Proof.
  pose proof (t_zero G 0 W) as d0.
  pose proof (ty_eqAt G W (zero 0) (zero 0) d0 d0) as dEq.
  exact (t_conv G eq00_proof (prf 0 True_) (prf 0 (eqAt (zero 0) (zero 0))) 0
           (ty_True_proof G W) (t_prf G 0 0 True_ (le_n 0) (ty_True_ G W))
           (t_prf G 0 0 (eqAt (zero 0) (zero 0)) (le_n 0) dEq)
           (c_prf G 0 0 True_ (eqAt (zero 0) (zero 0)) (le_n 0)
              (ty_True_ G W) dEq
              (c_sym G (eqAt (zero 0) (zero 0)) True_ (prop 0)
                 (cv_eq00 G W)))).
Qed.

(* The companion half -- that a closed proof of `eq 0 0 -> False` would prove
   False outright -- is the one thing here that needs the MODEL, through 9.3.
   It comes back when Interp/Consistency.v is ported; what is checked above is
   its object-language half, that `eq 0 0` really is inhabited. *)
