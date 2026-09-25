From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Iso.
From CICM Require Import Interp.Codes Interp.Fam Interp.Univ Interp.Env Interp.Elem
  Interp.Def Interp.Inv Interp.Ctx Interp.Fun Interp.Fund.
From CICM Require Import Tests.Eq.
From Stdlib Require Import Arith.

Import UnscopedNotations.
Open Scope list_scope.

(* ================================================================== *)
(* TEST 2: Sigma (n : Nat). P^n(Nat), the iterated powerset.            *)
(*                                                                    *)
(* The iteration is a LARGE ELIMINATION: `natrec` at the motive          *)
(* `UU 0` (version A) or `UU 1` (version B), i.e. recursion on a          *)
(* numeral producing a TYPE.  Both versions define the family             *)
(*                                                                    *)
(*   PowN n  ==  natrec <universe> Nat (pi (var 0) <target>) n            *)
(*                                                                    *)
(* whose step takes the recursive result (var 0, a type) to its powerset.  *)
(* ================================================================== *)

Definition one (k : nat) : tm := succ (zero k).
Definition two (k : nat) : tm := succ (succ (zero k)).

(* the naturals at level 1, the base of version B *)
Lemma wfc_nat1 G (W : wfc G) : wfc (nat_ 1 :: G).
Proof. exact (w_cons G (nat_ 1) 1 W (t_nat G 1 W)). Qed.

(* ------------------------------------------------------------------ *)
(* VERSION A: P(A) := A -> Prop.                                        *)
(*                                                                    *)
(* `prop 0` is impredicative and lives in `UU 0`, so `pi 0 A (prop 0)` is *)
(* in `UU 0` whenever A is, and the whole iteration -- and the Sigma --   *)
(* stays at level 0.  No lifts are needed anywhere.                      *)
(* ------------------------------------------------------------------ *)

Definition PowN (n : tm) : tm :=
  natrec (UU 0) (nat_ 0) (pi 0 (var_tm 0) (prop 0)) n.

(* Sigma (n : Nat). P^n(Nat) *)
Definition SigP : tm := sig_ 0 (nat_ 0) (PowN (var_tm 0)).

Lemma ty_PowN G (W : wfc G) n (dn : ty G n (nat_ 0)) : ty G (PowN n) (UU 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ 0 :: G) 1 0 (le_n 1) W1) as dU.   (* UU 0 : UU 1 *)
  pose proof (w_cons (nat_ 0 :: G) (UU 0) 1 W1 dU) as Ws.    (* UU 0 :: nat_ 0 :: G *)
  pose proof (t_var _ 0 (UU 0) Ws (lookup_O (nat_ 0 :: G) (UU 0))) as dv.
  refine (t_natrec G (UU 0) (nat_ 0) (pi 0 (var_tm 0) (prop 0)) n 1 0 dU
            (t_nat G 0 W) _ dn).
  exact (t_pi _ 0 0 (var_tm 0) (prop 0) (le_n 0) dv
           (t_prop _ 0 (w_cons _ (var_tm 0) 0 Ws dv))).
Qed.

Theorem ty_SigP G (W : wfc G) : ty G SigP (UU 0).
Proof.
  refine (t_sig G 0 0 (nat_ 0) (PowN (var_tm 0)) (le_n 0) (t_nat G 0 W) _).
  pose proof (wfc_nat G W) as W1.
  exact (ty_PowN (nat_ 0 :: G) W1 (var_tm 0)
           (t_var (nat_ 0 :: G) 0 (nat_ 0) W1 (lookup_O G (nat_ 0)))).
Qed.

(* ---- the iteration computes ---- *)

(* P^1(Nat) = Nat -> Prop *)
Theorem cv_PowN_one G (W : wfc G) :
  cv G (PowN (one 0)) (pi 0 (nat_ 0) (prop 0)) (UU 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ 0 :: G) 1 0 (le_n 1) W1) as dU.
  pose proof (w_cons (nat_ 0 :: G) (UU 0) 1 W1 dU) as Ws.
  pose proof (t_var _ 0 (UU 0) Ws (lookup_O (nat_ 0 :: G) (UU 0))) as dv.
  pose proof (t_pi _ 0 0 (var_tm 0) (prop 0) (le_n 0) dv
                (t_prop _ 0 (w_cons _ (var_tm 0) 0 Ws dv))) as ds.
  pose proof (ty_PowN G W (zero 0) (t_zero G 0 W)) as dP0.
  eapply c_trans.
  - exact (c_rec_succ G (UU 0) (nat_ 0) (pi 0 (var_tm 0) (prop 0)) (zero 0) 1 0
             dU (t_nat G 0 W) ds (t_zero G 0 W)).
  - (* pi (PowN zero) prop  ==  pi nat_ prop *)
    refine (c_pi G 0 0 (PowN (zero 0)) (nat_ 0) (prop 0) (prop 0) (le_n 0)
              dP0 _ (t_nat G 0 W) _ _ _).
    + exact (t_prop _ 0 (w_cons G (PowN (zero 0)) 0 W dP0)).
    + exact (t_prop (nat_ 0 :: G) 0 W1).
    + exact (c_rec_zero G (UU 0) (nat_ 0) (pi 0 (var_tm 0) (prop 0)) 1 0 dU
               (t_nat G 0 W) ds).
    + exact (c_refl _ (prop 0) (UU 0)
               (t_prop _ 0 (w_cons G (PowN (zero 0)) 0 W dP0))).
Qed.

(* P^2(Nat) = (Nat -> Prop) -> Prop *)
Theorem cv_PowN_two G (W : wfc G) :
  cv G (PowN (two 0)) (pi 0 (pi 0 (nat_ 0) (prop 0)) (prop 0)) (UU 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ 0 :: G) 1 0 (le_n 1) W1) as dU.
  pose proof (w_cons (nat_ 0 :: G) (UU 0) 1 W1 dU) as Ws.
  pose proof (t_var _ 0 (UU 0) Ws (lookup_O (nat_ 0 :: G) (UU 0))) as dv.
  pose proof (t_pi _ 0 0 (var_tm 0) (prop 0) (le_n 0) dv
                (t_prop _ 0 (w_cons _ (var_tm 0) 0 Ws dv))) as ds.
  pose proof (ty_PowN G W (one 0) (t_succ G 0 (zero 0) (t_zero G 0 W))) as dP1.
  pose proof (ty_natFun G W) as dNF.
  eapply c_trans.
  - exact (c_rec_succ G (UU 0) (nat_ 0) (pi 0 (var_tm 0) (prop 0)) (one 0) 1 0
             dU (t_nat G 0 W) ds (t_succ G 0 (zero 0) (t_zero G 0 W))).
  - refine (c_pi G 0 0 (PowN (one 0)) (pi 0 (nat_ 0) (prop 0)) (prop 0) (prop 0)
              (le_n 0) dP1 _ dNF _ _ _).
    + exact (t_prop _ 0 (w_cons G (PowN (one 0)) 0 W dP1)).
    + exact (t_prop _ 0 (w_cons G (pi 0 (nat_ 0) (prop 0)) 0 W dNF)).
    + exact (cv_PowN_one G W).
    + exact (c_refl _ (prop 0) (UU 0)
               (t_prop _ 0 (w_cons G (PowN (one 0)) 0 W dP1))).
Qed.

(* ---- inhabitants ---- *)

(* an element of P^1(Nat) = Nat -> Prop: the singleton {0}, i.e. test 1's eq 0 *)
Definition elt1 : tm := eqz.

(* an element of P^2(Nat) = (Nat -> Prop) -> Prop: the predicates true at 0 *)
Definition elt2 : tm :=
  lam 0 (pi 0 (nat_ 0) (prop 0)) (prop 0)
    (app (nat_ 0) (prop 0) (var_tm 0) (zero 0)).

Lemma ty_elt2 G (W : wfc G) :
  ty G elt2 (pi 0 (pi 0 (nat_ 0) (prop 0)) (prop 0)).
Proof.
  pose proof (ty_natFun G W) as dNF.
  pose proof (w_cons G (pi 0 (nat_ 0) (prop 0)) 0 W dNF) as W1.
  refine (t_lam G 0 0 (pi 0 (nat_ 0) (prop 0)) (prop 0) _ (le_n 0) dNF
            (t_prop _ 0 W1) _).
  exact (t_app _ 0 0 (nat_ 0) (prop 0) (var_tm 0) (zero 0) (le_n 0)
           (t_nat _ 0 W1) (t_prop _ 0 (wfc_nat _ W1))
           (t_var _ 0 (pi 0 (nat_ 0) (prop 0)) W1
              (lookup_O G (pi 0 (nat_ 0) (prop 0))))
           (t_zero _ 0 W1)).
Qed.

(* (1, {0}) : Sigma (n : Nat). P^n(Nat) *)
Definition pairP1 : tm := pair 0 (nat_ 0) (PowN (var_tm 0)) (one 0) elt1.

Theorem ty_pairP1 G (W : wfc G) : ty G pairP1 SigP.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G 0 (zero 0) (t_zero G 0 W)) as d1.
  pose proof (ty_PowN G W (one 0) d1) as dP1.
  refine (t_pair G 0 0 (nat_ 0) (PowN (var_tm 0)) (one 0) elt1 (le_n 0)
            (t_nat G 0 W)
            (ty_PowN (nat_ 0 :: G) W1 (var_tm 0)
               (t_var (nat_ 0 :: G) 0 (nat_ 0) W1 (lookup_O G (nat_ 0)))) d1 _).
  (* elt1 : PowN one, by conversion from Nat -> Prop *)
  exact (t_conv G elt1 (pi 0 (nat_ 0) (prop 0)) (PowN (one 0)) 0 (ty_eqz G W)
           (ty_natFun G W) dP1
           (c_sym G (PowN (one 0)) (pi 0 (nat_ 0) (prop 0)) (UU 0)
              (cv_PowN_one G W))).
Qed.

(* (2, {p | p 0}) : Sigma (n : Nat). P^n(Nat) *)
Definition pairP2 : tm := pair 0 (nat_ 0) (PowN (var_tm 0)) (two 0) elt2.

Theorem ty_pairP2 G (W : wfc G) : ty G pairP2 SigP.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G 0 (succ (zero 0)) (t_succ G 0 (zero 0) (t_zero G 0 W)))
    as d2.
  pose proof (ty_PowN G W (two 0) d2) as dP2.
  refine (t_pair G 0 0 (nat_ 0) (PowN (var_tm 0)) (two 0) elt2 (le_n 0)
            (t_nat G 0 W)
            (ty_PowN (nat_ 0 :: G) W1 (var_tm 0)
               (t_var (nat_ 0 :: G) 0 (nat_ 0) W1 (lookup_O G (nat_ 0)))) d2 _).
  refine (t_conv G elt2 (pi 0 (pi 0 (nat_ 0) (prop 0)) (prop 0)) (PowN (two 0))
            0 (ty_elt2 G W) _ dP2
            (c_sym G (PowN (two 0)) (pi 0 (pi 0 (nat_ 0) (prop 0)) (prop 0))
               (UU 0) (cv_PowN_two G W))).
  exact (t_pi G 0 0 (pi 0 (nat_ 0) (prop 0)) (prop 0) (le_n 0) (ty_natFun G W)
           (t_prop _ 0 (w_cons G (pi 0 (nat_ 0) (prop 0)) 0 W (ty_natFun G W)))).
Qed.

Theorem SigP_inhabited_closed : ty nil pairP2 SigP.
Proof. exact (ty_pairP2 nil w_nil). Qed.

(* ------------------------------------------------------------------ *)
(* VERSION B: P(A) := A -> Type.                                        *)
(*                                                                    *)
(* `UU 0` lives in `UU 1` and `t_pi` is HOMOGENEOUS in the annotation, so *)
(* `pi 1 A (UU 0)` asks for `A : UU 1`.  With the levels on the formers    *)
(* that costs nothing: `nat_ 1` IS the naturals at level 1, and it is what  *)
(* the lift of `nat_ 0` computes to (cv_lnat below, the rule c_up_nat).     *)
(* So the iteration runs at level 1 throughout AND its scrutinee is still a  *)
(* natural number natrec can eliminate -- which is what makes the DEPENDENT  *)
(* Sigma of this section formable, where with an opaque lift only the         *)
(* non-dependent one was.                                                    *)
(* ------------------------------------------------------------------ *)

Definition lnat : tm := up 0 (nat_ 0).          (* Nat, lifted to UU 1 *)

Lemma ty_lnat G (W : wfc G) : ty G lnat (UU 1).
Proof. exact (t_up G 0 (nat_ 0) (t_nat G 0 W)). Qed.

(* the lift COMPUTES on nat: the lifted naturals ARE the naturals one level up *)
Lemma cv_lnat G (W : wfc G) : cv G lnat (nat_ 1) (UU 1).
Proof. exact (c_up_nat G 0 W). Qed.

Definition PowTN (n : tm) : tm :=
  natrec (UU 1) (nat_ 1) (pi 1 (var_tm 0) (UU 0)) n.

Lemma ty_PowTN_step G (W : wfc G) :
  ty (UU 1 :: nat_ 1 :: G) (pi 1 (var_tm 0) (UU 0)) (nrec_succ (UU 1)).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  pose proof (w_cons (nat_ 1 :: G) (UU 1) 2 W1
                (t_univ (nat_ 1 :: G) 2 1 (le_n 2) W1)) as Ws.
  pose proof (t_var _ 0 (UU 1) Ws (lookup_O (nat_ 1 :: G) (UU 1))) as dv.
  exact (t_pi _ 1 1 (var_tm 0) (UU 0) (le_n 1) dv
           (t_univ _ 1 0 (le_n 1) (w_cons _ (var_tm 0) 1 Ws dv))).
Qed.

Lemma ty_PowTN G (W : wfc G) n (dn : ty G n (nat_ 1)) : ty G (PowTN n) (UU 1).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  exact (t_natrec G (UU 1) (nat_ 1) (pi 1 (var_tm 0) (UU 0)) n 2 1
           (t_univ (nat_ 1 :: G) 2 1 (le_n 2) W1) (t_nat G 1 W)
           (ty_PowTN_step G W) dn).
Qed.

(* P^1(Nat) = Nat_1 -> Type *)
Theorem cv_PowTN_one G (W : wfc G) :
  cv G (PowTN (one 1)) (pi 1 (nat_ 1) (UU 0)) (UU 1).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  pose proof (t_univ (nat_ 1 :: G) 2 1 (le_n 2) W1) as dC.
  pose proof (ty_PowTN_step G W) as ds.
  pose proof (ty_PowTN G W (zero 1) (t_zero G 1 W)) as dP0.
  eapply c_trans.
  - exact (c_rec_succ G (UU 1) (nat_ 1) (pi 1 (var_tm 0) (UU 0)) (zero 1) 2 1
             dC (t_nat G 1 W) ds (t_zero G 1 W)).
  - refine (c_pi G 1 1 (PowTN (zero 1)) (nat_ 1) (UU 0) (UU 0) (le_n 1) dP0 _
              (t_nat G 1 W) _ _ _).
    + exact (t_univ _ 1 0 (le_n 1) (w_cons G (PowTN (zero 1)) 1 W dP0)).
    + exact (t_univ _ 1 0 (le_n 1) W1).
    + exact (c_rec_zero G (UU 1) (nat_ 1) (pi 1 (var_tm 0) (UU 0)) 2 1 dC
               (t_nat G 1 W) ds).
    + exact (c_refl _ (UU 0) (UU 1)
               (t_univ _ 1 0 (le_n 1) (w_cons G (PowTN (zero 1)) 1 W dP0))).
Qed.

(* P^2(Nat) = (Nat_1 -> Type) -> Type *)
Theorem cv_PowTN_two G (W : wfc G) :
  cv G (PowTN (two 1)) (pi 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)) (UU 1).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  pose proof (t_univ (nat_ 1 :: G) 2 1 (le_n 2) W1) as dC.
  pose proof (ty_PowTN_step G W) as ds.
  pose proof (ty_PowTN G W (one 1) (t_succ G 1 (zero 1) (t_zero G 1 W))) as dP1.
  assert (dP : ty G (pi 1 (nat_ 1) (UU 0)) (UU 1))
    by exact (t_pi G 1 1 (nat_ 1) (UU 0) (le_n 1) (t_nat G 1 W)
                (t_univ _ 1 0 (le_n 1) W1)).
  eapply c_trans.
  - exact (c_rec_succ G (UU 1) (nat_ 1) (pi 1 (var_tm 0) (UU 0)) (one 1) 2 1
             dC (t_nat G 1 W) ds (t_succ G 1 (zero 1) (t_zero G 1 W))).
  - refine (c_pi G 1 1 (PowTN (one 1)) (pi 1 (nat_ 1) (UU 0)) (UU 0) (UU 0)
              (le_n 1) dP1 _ dP _ (cv_PowTN_one G W) _).
    + exact (t_univ _ 1 0 (le_n 1) (w_cons G (PowTN (one 1)) 1 W dP1)).
    + exact (t_univ _ 1 0 (le_n 1) (w_cons G (pi 1 (nat_ 1) (UU 0)) 1 W dP)).
    + exact (c_refl _ (UU 0) (UU 1)
               (t_univ _ 1 0 (le_n 1) (w_cons G (PowTN (one 1)) 1 W dP1))).
Qed.

(* ---- inhabitants ---- *)

(* an element of P^1(Nat) = Nat_1 -> Type: the constant family Nat *)
Definition powT1 : tm := lam 1 (nat_ 1) (UU 0) (nat_ 0).

Lemma ty_powT1 G (W : wfc G) : ty G powT1 (pi 1 (nat_ 1) (UU 0)).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  exact (t_lam G 1 1 (nat_ 1) (UU 0) (nat_ 0) (le_n 1) (t_nat G 1 W)
           (t_univ _ 1 0 (le_n 1) W1) (t_nat _ 0 W1)).
Qed.

(* an element of P^2(Nat) = (Nat_1 -> Type) -> Type: evaluation at 0 *)
Definition powT2 : tm :=
  lam 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)
    (app (nat_ 1) (UU 0) (var_tm 0) (zero 1)).

Lemma ty_powT2 G (W : wfc G) :
  ty G powT2 (pi 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  assert (dP : ty G (pi 1 (nat_ 1) (UU 0)) (UU 1))
    by exact (t_pi G 1 1 (nat_ 1) (UU 0) (le_n 1) (t_nat G 1 W)
                (t_univ _ 1 0 (le_n 1) W1)).
  pose proof (w_cons G (pi 1 (nat_ 1) (UU 0)) 1 W dP) as WP.
  refine (t_lam G 1 1 (pi 1 (nat_ 1) (UU 0)) (UU 0) _ (le_n 1) dP
            (t_univ _ 1 0 (le_n 1) WP) _).
  exact (t_app _ 1 1 (nat_ 1) (UU 0) (var_tm 0) (zero 1) (le_n 1)
           (t_nat _ 1 WP) (t_univ _ 1 0 (le_n 1) (wfc_nat1 _ WP))
           (t_var _ 0 (pi 1 (nat_ 1) (UU 0)) WP
              (lookup_O G (pi 1 (nat_ 1) (UU 0))))
           (t_zero _ 1 WP)).
Qed.

(* ---- the Sigma ----

   With the annotation on `nat_` the DEPENDENT Sigma is formable at level 1:
   the domain is `nat_ 1`, which is a type of `UU 1` outright, and its
   elements are numerals, which `natrec` eliminates.  The lift is not in the
   way any more -- `up 0 (nat_ 0)` IS `nat_ 1` (cv_lnat) -- so nothing here
   needs cumulativity or a transparent lift. *)

Definition SigT : tm := sig_ 1 (nat_ 1) (PowTN (var_tm 0)).

Theorem ty_SigT G (W : wfc G) : ty G SigT (UU 1).
Proof.
  pose proof (wfc_nat1 G W) as W1.
  exact (t_sig G 1 1 (nat_ 1) (PowTN (var_tm 0)) (le_n 1) (t_nat G 1 W)
           (ty_PowTN (nat_ 1 :: G) W1 (var_tm 0)
              (t_var (nat_ 1 :: G) 0 (nat_ 1) W1 (lookup_O G (nat_ 1))))).
Qed.

(* (2, {f | f 0}) : Sigma (n : Nat_1). P^n(Nat) *)
Definition pairT : tm := pair 1 (nat_ 1) (PowTN (var_tm 0)) (two 1) powT2.

Theorem ty_pairT G (W : wfc G) : ty G pairT SigT.
Proof.
  pose proof (wfc_nat1 G W) as W1.
  pose proof (t_succ G 1 (succ (zero 1)) (t_succ G 1 (zero 1) (t_zero G 1 W)))
    as d2.
  pose proof (ty_PowTN G W (two 1) d2) as dP2.
  assert (dQ : ty G (pi 1 (nat_ 1) (UU 0)) (UU 1))
    by exact (t_pi G 1 1 (nat_ 1) (UU 0) (le_n 1) (t_nat G 1 W)
                (t_univ _ 1 0 (le_n 1) W1)).
  assert (dP : ty G (pi 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)) (UU 1))
    by exact (t_pi G 1 1 (pi 1 (nat_ 1) (UU 0)) (UU 0) (le_n 1) dQ
                (t_univ _ 1 0 (le_n 1)
                   (w_cons G (pi 1 (nat_ 1) (UU 0)) 1 W dQ))).
  refine (t_pair G 1 1 (nat_ 1) (PowTN (var_tm 0)) (two 1) powT2 (le_n 1)
            (t_nat G 1 W)
            (ty_PowTN (nat_ 1 :: G) W1 (var_tm 0)
               (t_var (nat_ 1 :: G) 0 (nat_ 1) W1 (lookup_O G (nat_ 1)))) d2 _).
  exact (t_conv G powT2 (pi 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)) (PowTN (two 1)) 1
           (ty_powT2 G W) dP dP2
           (c_sym G (PowTN (two 1)) (pi 1 (pi 1 (nat_ 1) (UU 0)) (UU 0)) (UU 1)
              (cv_PowTN_two G W))).
Qed.

Theorem SigT_inhabited_closed : ty nil pairT SigT.
Proof. exact (ty_pairT nil w_nil). Qed.

(* There is still no cumulativity: `nat_ 0` is a type of `UU 0` and of no
   other universe -- what lives in `UU 1` is `nat_ 1`, a DIFFERENT type with
   the same realisers.  The model says so: `nat_ 0`'s interpretation has level
   0 (LvlDec), so a reading of it as an ELEMENT of `UU 1` would give it level
   1 as well. *)
Theorem nat_not_at_univ1 : ty nil (nat_ 0) (UU 1) -> False.
Proof.
  intros d.
  destruct (fund_tot nil (nat_ 0) (UU 1) d) as [_ Hn].
  destruct (Hn nil tt 2 (univFam 1)
              (ity_univ nil 0 1 (ers nil (UU 1)) eq_refl)) as [x Dx].
  destruct (itm_univ_ty nil (nat_ 0) 1 (ers nil (UU 1)) (univFam 1)
              (ers nil (nat_ 0)) x (iso_self (univFam 1)) Dx) as [F0 [D0 _]].
  pose proof (ity_lvl_dec nil (nat_ 0) 1 (ers nil (nat_ 0)) F0 D0) as E.
  cbn [LvlDec] in E; discriminate E.
Qed.
