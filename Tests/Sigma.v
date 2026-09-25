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
(* `univ 0` (version A) or `univ 1` (version B), i.e. recursion on a      *)
(* numeral producing a TYPE.  Both versions define the family             *)
(*                                                                    *)
(*   PowN n  ==  natrec <universe> Nat (pi (var 0) <target>) n            *)
(*                                                                    *)
(* whose step takes the recursive result (var 0, a type) to its powerset.  *)
(* ================================================================== *)

Definition one : tm := succ zero.
Definition two : tm := succ (succ zero).

(* ------------------------------------------------------------------ *)
(* VERSION A: P(A) := A -> Prop.                                        *)
(*                                                                    *)
(* `prop` is impredicative and lives in `univ 0`, so `pi A prop` is in    *)
(* `univ 0` whenever A is, and the whole iteration -- and the Sigma --    *)
(* stays at level 0.  No lifts are needed anywhere.                      *)
(* ------------------------------------------------------------------ *)

Definition PowN (n : tm) : tm :=
  natrec (univ 0) nat_ (pi (var_tm 0) prop) n.

(* Sigma (n : Nat). P^n(Nat) *)
Definition SigP : tm := sig_ nat_ (PowN (var_tm 0)).

Lemma ty_PowN G (W : wfc G) n (dn : ty G n nat_) : ty G (PowN n) (univ 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ :: G) 0 W1) as dU.               (* univ 0 : univ 1 *)
  pose proof (w_cons (nat_ :: G) (univ 0) 1 W1 dU) as Ws.    (* univ 0 :: nat_ :: G *)
  pose proof (t_var _ 0 (univ 0) Ws (lookup_O (nat_ :: G) (univ 0))) as dv.
  refine (t_natrec G (univ 0) nat_ (pi (var_tm 0) prop) n 1 dU (t_nat G W) _ dn).
  exact (t_pi _ (var_tm 0) prop 0 dv
           (t_prop _ (w_cons _ (var_tm 0) 0 Ws dv))).
Qed.

Theorem ty_SigP G (W : wfc G) : ty G SigP (univ 0).
Proof.
  refine (t_sig G nat_ (PowN (var_tm 0)) 0 (t_nat G W) _).
  pose proof (wfc_nat G W) as W1.
  exact (ty_PowN (nat_ :: G) W1 (var_tm 0)
           (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_))).
Qed.

(* ---- the iteration computes ---- *)

(* P^1(Nat) = Nat -> Prop *)
Theorem cv_PowN_one G (W : wfc G) : cv G (PowN one) (pi nat_ prop) (univ 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ :: G) 0 W1) as dU.
  pose proof (w_cons (nat_ :: G) (univ 0) 1 W1 dU) as Ws.
  pose proof (t_var _ 0 (univ 0) Ws (lookup_O (nat_ :: G) (univ 0))) as dv.
  pose proof (t_pi _ (var_tm 0) prop 0 dv
                (t_prop _ (w_cons _ (var_tm 0) 0 Ws dv))) as ds.
  pose proof (ty_PowN G W zero (t_zero G W)) as dP0.
  eapply c_trans.
  - exact (c_rec_succ G (univ 0) nat_ (pi (var_tm 0) prop) zero 1 dU
             (t_nat G W) ds (t_zero G W)).
  - (* pi (PowN zero) prop  ==  pi nat_ prop *)
    refine (c_pi G (PowN zero) nat_ prop prop 0 dP0 _ (t_nat G W)
              (t_prop (nat_ :: G) W1) _ _).
    + exact (t_prop _ (w_cons G (PowN zero) 0 W dP0)).
    + exact (c_rec_zero G (univ 0) nat_ (pi (var_tm 0) prop) 1 dU
               (t_nat G W) ds).
    + exact (c_refl _ prop (univ 0) (t_prop _ (w_cons G (PowN zero) 0 W dP0))).
Qed.

(* P^2(Nat) = (Nat -> Prop) -> Prop *)
Theorem cv_PowN_two G (W : wfc G) :
  cv G (PowN two) (pi (pi nat_ prop) prop) (univ 0).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ :: G) 0 W1) as dU.
  pose proof (w_cons (nat_ :: G) (univ 0) 1 W1 dU) as Ws.
  pose proof (t_var _ 0 (univ 0) Ws (lookup_O (nat_ :: G) (univ 0))) as dv.
  pose proof (t_pi _ (var_tm 0) prop 0 dv
                (t_prop _ (w_cons _ (var_tm 0) 0 Ws dv))) as ds.
  pose proof (ty_PowN G W one (t_succ G zero (t_zero G W))) as dP1.
  pose proof (ty_natFun G W) as dNF.
  eapply c_trans.
  - exact (c_rec_succ G (univ 0) nat_ (pi (var_tm 0) prop) one 1 dU
             (t_nat G W) ds (t_succ G zero (t_zero G W))).
  - refine (c_pi G (PowN one) (pi nat_ prop) prop prop 0 dP1 _ dNF _ _ _).
    + exact (t_prop _ (w_cons G (PowN one) 0 W dP1)).
    + exact (t_prop _ (w_cons G (pi nat_ prop) 0 W dNF)).
    + exact (cv_PowN_one G W).
    + exact (c_refl _ prop (univ 0) (t_prop _ (w_cons G (PowN one) 0 W dP1))).
Qed.

(* ---- inhabitants ---- *)

(* an element of P^1(Nat) = Nat -> Prop: the singleton {0}, i.e. test 1's eq 0 *)
Definition elt1 : tm := eqz.

(* an element of P^2(Nat) = (Nat -> Prop) -> Prop: the predicates true at 0 *)
Definition elt2 : tm := lam (pi nat_ prop) prop (app nat_ prop (var_tm 0) zero).

Lemma ty_elt2 G (W : wfc G) : ty G elt2 (pi (pi nat_ prop) prop).
Proof.
  pose proof (ty_natFun G W) as dNF.
  pose proof (w_cons G (pi nat_ prop) 0 W dNF) as W1.
  refine (t_lam G (pi nat_ prop) prop _ 0 dNF (t_prop _ W1) _).
  exact (t_app _ nat_ prop (var_tm 0) zero 0 (t_nat _ W1)
           (t_prop _ (wfc_nat _ W1))
           (t_var _ 0 (pi nat_ prop) W1 (lookup_O G (pi nat_ prop)))
           (t_zero _ W1)).
Qed.

(* (1, {0}) : Sigma (n : Nat). P^n(Nat) *)
Definition pairP1 : tm := pair nat_ (PowN (var_tm 0)) one elt1.

Theorem ty_pairP1 G (W : wfc G) : ty G pairP1 SigP.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G zero (t_zero G W)) as d1.
  pose proof (ty_PowN G W one d1) as dP1.
  refine (t_pair G nat_ (PowN (var_tm 0)) one elt1 0 (t_nat G W)
            (ty_PowN (nat_ :: G) W1 (var_tm 0)
               (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_))) d1 _).
  (* elt1 : PowN one, by conversion from Nat -> Prop *)
  exact (t_conv G elt1 (pi nat_ prop) (PowN one) 0 (ty_eqz G W)
           (ty_natFun G W) dP1
           (c_sym G (PowN one) (pi nat_ prop) (univ 0) (cv_PowN_one G W))).
Qed.

(* (2, {p | p 0}) : Sigma (n : Nat). P^n(Nat) *)
Definition pairP2 : tm := pair nat_ (PowN (var_tm 0)) two elt2.

Theorem ty_pairP2 G (W : wfc G) : ty G pairP2 SigP.
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_succ G (succ zero) (t_succ G zero (t_zero G W))) as d2.
  pose proof (ty_PowN G W two d2) as dP2.
  refine (t_pair G nat_ (PowN (var_tm 0)) two elt2 0 (t_nat G W)
            (ty_PowN (nat_ :: G) W1 (var_tm 0)
               (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_))) d2 _).
  refine (t_conv G elt2 (pi (pi nat_ prop) prop) (PowN two) 0 (ty_elt2 G W) _
            dP2 (c_sym G (PowN two) (pi (pi nat_ prop) prop) (univ 0)
                   (cv_PowN_two G W))).
  exact (t_pi G (pi nat_ prop) prop 0 (ty_natFun G W)
           (t_prop _ (w_cons G (pi nat_ prop) 0 W (ty_natFun G W)))).
Qed.

Theorem SigP_inhabited_closed : ty nil pairP2 SigP.
Proof. exact (ty_pairP2 nil w_nil). Qed.

(* ------------------------------------------------------------------ *)
(* VERSION B: P(A) := A -> Type.                                        *)
(*                                                                    *)
(* `univ 0` lives in `univ 1`, and `t_pi` is HOMOGENEOUS in the level, so *)
(* `pi A (univ 0)` asks for `A : univ 1`.  `Nat : univ 0`, so the base of  *)
(* the iteration must be lifted EXPLICITLY -- there is no cumulativity in  *)
(* CIC^-, only `up` (on types) and `uptm` (on terms).  After that one lift *)
(* the iteration is uniform: every iterate is again in `univ 1`, so no      *)
(* further lift is needed.                                                *)
(* ------------------------------------------------------------------ *)

Definition lnat : tm := up (univ 1) nat_.          (* Nat, lifted to univ 1 *)

Definition PowTN (n : tm) : tm :=
  natrec (univ 1) lnat (pi (var_tm 0) (univ 0)) n.

Lemma ty_lnat G (W : wfc G) : ty G lnat (univ 1).
Proof. exact (t_up G nat_ 0 (t_nat G W)). Qed.

Lemma ty_PowTN_step G (W : wfc G) :
  ty (univ 1 :: nat_ :: G) (pi (var_tm 0) (univ 0)) (nrec_succ (univ 1)).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (w_cons (nat_ :: G) (univ 1) 2 W1 (t_univ (nat_ :: G) 1 W1)) as Ws.
  pose proof (t_var _ 0 (univ 1) Ws (lookup_O (nat_ :: G) (univ 1))) as dv.
  exact (t_pi _ (var_tm 0) (univ 0) 1 dv
           (t_univ _ 0 (w_cons _ (var_tm 0) 1 Ws dv))).
Qed.

Lemma ty_PowTN G (W : wfc G) n (dn : ty G n nat_) : ty G (PowTN n) (univ 1).
Proof.
  pose proof (wfc_nat G W) as W1.
  exact (t_natrec G (univ 1) lnat (pi (var_tm 0) (univ 0)) n 2
           (t_univ (nat_ :: G) 1 W1) (ty_lnat G W) (ty_PowTN_step G W) dn).
Qed.

(* P^1(Nat) = |Nat| -> Type *)
Theorem cv_PowTN_one G (W : wfc G) :
  cv G (PowTN one) (pi lnat (univ 0)) (univ 1).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ :: G) 1 W1) as dC.
  pose proof (ty_PowTN_step G W) as ds.
  pose proof (ty_PowTN G W zero (t_zero G W)) as dP0.
  pose proof (ty_lnat G W) as dL.
  eapply c_trans.
  - exact (c_rec_succ G (univ 1) lnat (pi (var_tm 0) (univ 0)) zero 2 dC dL ds
             (t_zero G W)).
  - refine (c_pi G (PowTN zero) lnat (univ 0) (univ 0) 1 dP0 _ dL _ _ _).
    + exact (t_univ _ 0 (w_cons G (PowTN zero) 1 W dP0)).
    + exact (t_univ _ 0 (w_cons G lnat 1 W dL)).
    + exact (c_rec_zero G (univ 1) lnat (pi (var_tm 0) (univ 0)) 2 dC dL ds).
    + exact (c_refl _ (univ 0) (univ 1) (t_univ _ 0 (w_cons G (PowTN zero) 1 W dP0))).
Qed.

(* P^2(Nat) = (|Nat| -> Type) -> Type *)
Theorem cv_PowTN_two G (W : wfc G) :
  cv G (PowTN two) (pi (pi lnat (univ 0)) (univ 0)) (univ 1).
Proof.
  pose proof (wfc_nat G W) as W1.
  pose proof (t_univ (nat_ :: G) 1 W1) as dC.
  pose proof (ty_PowTN_step G W) as ds.
  pose proof (ty_lnat G W) as dL.
  pose proof (ty_PowTN G W one (t_succ G zero (t_zero G W))) as dP1.
  assert (dP : ty G (pi lnat (univ 0)) (univ 1))
    by exact (t_pi G lnat (univ 0) 1 dL
                (t_univ _ 0 (w_cons G lnat 1 W dL))).
  eapply c_trans.
  - exact (c_rec_succ G (univ 1) lnat (pi (var_tm 0) (univ 0)) one 2 dC dL ds
             (t_succ G zero (t_zero G W))).
  - refine (c_pi G (PowTN one) (pi lnat (univ 0)) (univ 0) (univ 0) 1 dP1 _ dP _
              (cv_PowTN_one G W) _).
    + exact (t_univ _ 0 (w_cons G (PowTN one) 1 W dP1)).
    + exact (t_univ _ 0 (w_cons G (pi lnat (univ 0)) 1 W dP)).
    + exact (c_refl _ (univ 0) (univ 1)
               (t_univ _ 0 (w_cons G (PowTN one) 1 W dP1))).
Qed.

(* ---- inhabitants ---- *)

(* an element of P^1(Nat) = |Nat| -> Type: the constant family Nat *)
Definition powT1 : tm := lam lnat (univ 0) nat_.

Lemma ty_powT1 G (W : wfc G) : ty G powT1 (pi lnat (univ 0)).
Proof.
  pose proof (ty_lnat G W) as dL.
  pose proof (w_cons G lnat 1 W dL) as W1.
  exact (t_lam G lnat (univ 0) nat_ 1 dL (t_univ _ 0 W1) (t_nat _ W1)).
Qed.

(* an element of P^2(Nat) = (|Nat| -> Type) -> Type: evaluation at 0 *)
Definition powT2 : tm :=
  lam (pi lnat (univ 0)) (univ 0)
    (app lnat (univ 0) (var_tm 0) (uptm nat_ zero)).

Lemma ty_powT2 G (W : wfc G) : ty G powT2 (pi (pi lnat (univ 0)) (univ 0)).
Proof.
  pose proof (ty_lnat G W) as dL.
  assert (dP : ty G (pi lnat (univ 0)) (univ 1))
    by exact (t_pi G lnat (univ 0) 1 dL (t_univ _ 0 (w_cons G lnat 1 W dL))).
  pose proof (w_cons G (pi lnat (univ 0)) 1 W dP) as W1.
  refine (t_lam G (pi lnat (univ 0)) (univ 0) _ 1 dP (t_univ _ 0 W1) _).
  exact (t_app _ lnat (univ 0) (var_tm 0) (uptm nat_ zero) 1 (ty_lnat _ W1)
           (t_univ _ 0 (w_cons _ lnat 1 W1 (ty_lnat _ W1)))
           (t_var _ 0 (pi lnat (univ 0)) W1 (lookup_O G (pi lnat (univ 0))))
           (t_up_tm _ nat_ zero 0 (t_nat _ W1) (t_zero _ W1))).
Qed.

(* ---- the Sigma ----

   `Nat` sits in `univ 0` and version B's family sits in `univ 1`, and
   `t_sig` is homogeneous, so `sig_ nat_ (PowTN (var 0))` can only be formed
   at level 0 -- which would need `ty G nat_ (univ 1)`, and that is FALSE
   (nat_not_at_univ1 below, proved with the fundamental lemma).  Lifting the
   domain to `lnat` instead makes the Sigma formable at level 1, but then the
   first component is a LIFTED numeral and `natrec` cannot eliminate it, so
   the family can no longer depend on it: what is definable is the
   non-dependent Sigma.  Making the dependent version definable needs either
   cumulativity or a transparent lift (`t_up_out`), and Typing/Rules.v drops
   the latter deliberately, for unicity of typing. *)

Definition SigT : tm := sig_ lnat (PowTN two).

Theorem ty_SigT G (W : wfc G) : ty G SigT (univ 1).
Proof.
  pose proof (ty_lnat G W) as dL.
  exact (t_sig G lnat (PowTN two) 1 dL
           (ty_PowTN (lnat :: G) (w_cons G lnat 1 W dL) two
              (t_succ _ (succ zero)
                 (t_succ _ zero (t_zero _ (w_cons G lnat 1 W dL)))))).
Qed.

(* (|2|, {f | f |0|}) : Sigma (_ : |Nat|). P^2(Nat) *)
Definition pairT : tm := pair lnat (PowTN two) (uptm nat_ two) powT2.

Theorem ty_pairT G (W : wfc G) : ty G pairT SigT.
Proof.
  pose proof (ty_lnat G W) as dL.
  pose proof (w_cons G lnat 1 W dL) as WL.
  pose proof (t_succ G (succ zero) (t_succ G zero (t_zero G W))) as d2.
  pose proof (ty_PowTN G W two d2) as dP2.
  assert (dP : ty G (pi (pi lnat (univ 0)) (univ 0)) (univ 1)).
  { assert (dQ : ty G (pi lnat (univ 0)) (univ 1))
      by exact (t_pi G lnat (univ 0) 1 dL (t_univ _ 0 WL)).
    exact (t_pi G (pi lnat (univ 0)) (univ 0) 1 dQ
             (t_univ _ 0 (w_cons G (pi lnat (univ 0)) 1 W dQ))). }
  refine (t_pair G lnat (PowTN two) (uptm nat_ two) powT2 1 dL
            (ty_PowTN (lnat :: G) WL two
               (t_succ _ (succ zero) (t_succ _ zero (t_zero _ WL))))
            (t_up_tm G nat_ two 0 (t_nat G W) d2) _).
  exact (t_conv G powT2 (pi (pi lnat (univ 0)) (univ 0)) (PowTN two) 1
           (ty_powT2 G W) dP dP2
           (c_sym G (PowTN two) (pi (pi lnat (univ 0)) (univ 0)) (univ 1)
              (cv_PowTN_two G W))).
Qed.

Theorem SigT_inhabited_closed : ty nil pairT SigT.
Proof. exact (ty_pairT nil w_nil). Qed.

(* The level clash of version B is real: Nat is a type of `univ 0` and of no
   other universe.  The model says so -- `nat_`'s interpretation has level 0
   (LvlDec), so a reading of `nat_` as an ELEMENT of `univ 1` would give it
   level 1 as well. *)
Theorem nat_not_at_univ1 : ty nil nat_ (univ 1) -> False.
Proof.
  intros d.
  destruct (fund_tot nil nat_ (univ 1) d) as [_ Hn].
  destruct (Hn nil tt 2 (univFam 1) (ity_univ nil 1 (ers nil (univ 1)) eq_refl))
    as [x Dx].
  destruct (itm_univ_ty nil nat_ 1 (ers nil (univ 1)) (univFam 1) (ers nil nat_)
              x (iso_self (univFam 1)) Dx) as [F0 [D0 _]].
  pose proof (ity_lvl_dec nil nat_ 1 (ers nil nat_) F0 D0) as E.
  cbn [LvlDec] in E; discriminate E.
Qed.
