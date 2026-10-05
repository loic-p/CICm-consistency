From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage.
From Stdlib Require Import Arith Lia.

(* The three binder cases of the fundamental lemma, as standalone
   constructions: each takes exactly what the induction hypotheses at the
   subderivations supply -- a code for the domain at its own node, a code for
   each codomain instance at its own node, their well-formedness, and the
   coherence of the codomain family -- and returns the code at the node
   rk T h, with its well-formedness.

   Nothing here lifts or transports a code: the components are placed by
   constructor injections (Interp/Stage.v) and a binder code has no laws to
   discharge (Interp/Codes.v).

   And the EQUALITY of two codes so built is componentwise on the nose: v1's
   `buildPi_iso` had to prove the naturality square of `isoRefine` out of the
   functoriality of the canonical transport -- sixty lines per former -- while
   here `ceq` of two Pi-codes IS the conjunction of the three hypotheses. *)

Section BuildPi.
  Context (k : nat) (T A0 B0 : etm).
  Context (fT : forall y, prec y T -> Acc prec y).
  Context (e : eval T (epi A0 B0)) (ety : tyeq T T).

  Local Notation dN := (domNode T A0 B0 fT e).
  Local Notation cN := (codNode T A0 B0 fT e).
  Local Notation node := (rk T (hT T fT)).

  Context (cA : Code k dN) (eA : tyeq (projT1 cA) A0) (wA : wfn cA).

  Local Notation aa := (placeDom k T A0 B0 fT e cA).
  Local Notation gArg := (argGood k T A0 B0 fT e cA eA).

  Context (cB : forall u (x : kElS aa u), Code k (cN u (gArg u x)))
          (eB : forall u x, tyeq (projT1 (cB u x)) (eapp B0 u))
          (wB : forall u x, wfn (cB u x)).
  (* what the subderivation of the codomain supplies: related arguments give
     EQUAL codomain codes.  v1 asked for an isomorphism plus its transport. *)
  Context (cohB : forall u x u' x', kcEl aa u x aa u' x' -> kceq (cB u x) (cB u' x')).

  Definition bb (u : etm) (x : kElS aa u) : kSub k node :=
    placeCod k T A0 B0 fT e u (gArg u x) (cB u x).

  Lemma ea_holds : tyeq (kSh aa) A0.
  Proof. exact eA. Qed.

  Lemma eb_holds : forall u x, tyeq (kSh (bb u x)) (eapp B0 u).
  Proof. intros u x; exact (eB u x). Qed.

  Definition buildPi : SRefine k node T :=
    mkPi k node T A0 B0 e aa ea_holds bb eb_holds.

  Lemma buildPi_wf : kwfa buildPi.
  Proof.
    exact (mkPi_wf k node T A0 B0 e ety aa ea_holds wA bb eb_holds wB cohB).
  Qed.
End BuildPi.

Section BuildSig.
  Context (k : nat) (T A0 B0 : etm).
  Context (fT : forall y, prec y T -> Acc prec y).
  Context (e : eval T (esig A0 B0)) (ety : tyeq T T).

  Local Notation dN := (sdomNode T A0 B0 fT e).
  Local Notation cN := (scodNode T A0 B0 fT e).
  Local Notation node := (rk T (hT T fT)).

  Context (cA : Code k dN) (eA : tyeq (projT1 cA) A0) (wA : wfn cA).

  Local Notation aa := (placeSDom k T A0 B0 fT e cA).
  Local Notation gArg := (sargGood k T A0 B0 fT e cA eA).

  Context (cB : forall u (x : kElS aa u), Code k (cN u (gArg u x)))
          (eB : forall u x, tyeq (projT1 (cB u x)) (eapp B0 u))
          (wB : forall u x, wfn (cB u x)).
  Context (cohB : forall u x u' x', kcEl aa u x aa u' x' -> kceq (cB u x) (cB u' x')).

  Definition sbb (u : etm) (x : kElS aa u) : kSub k node :=
    placeSCod k T A0 B0 fT e u (gArg u x) (cB u x).

  Lemma sea_holds : tyeq (kSh aa) A0.
  Proof. exact eA. Qed.

  Lemma seb_holds : forall u x, tyeq (kSh (sbb u x)) (eapp B0 u).
  Proof. intros u x; exact (eB u x). Qed.

  Definition buildSig : SRefine k node T :=
    mkSig k node T A0 B0 e aa sea_holds sbb seb_holds.

  Lemma buildSig_wf : kwfa buildSig.
  Proof.
    exact (mkSig_wf k node T A0 B0 e ety aa sea_holds wA sbb seb_holds wB cohB).
  Qed.
End BuildSig.

Section BuildW.
  Context (k : nat) (T A0 B0 : etm).
  Context (fT : forall y, prec y T -> Acc prec y).
  Context (e : eval T (ew A0 B0)) (ety : tyeq T T).

  Local Notation dN := (wdomNode T A0 B0 fT e).
  Local Notation cN := (wcodNode T A0 B0 fT e).
  Local Notation node := (rk T (hT T fT)).

  Context (cA : Code k dN) (eA : tyeq (projT1 cA) A0) (wA : wfn cA).

  Local Notation aa := (placeWDom k T A0 B0 fT e cA).
  Local Notation gArg := (wargGood k T A0 B0 fT e cA eA).

  Context (cB : forall u (x : kElS aa u), Code k (cN u (gArg u x)))
          (eB : forall u x, tyeq (projT1 (cB u x)) (eapp B0 u))
          (wB : forall u x, wfn (cB u x)).
  Context (cohB : forall u x u' x', kcEl aa u x aa u' x' -> kceq (cB u x) (cB u' x')).

  Definition wbb (u : etm) (x : kElS aa u) : kSub k node :=
    placeWCod k T A0 B0 fT e u (gArg u x) (cB u x).

  Lemma wea_holds : tyeq (kSh aa) A0.
  Proof. exact eA. Qed.

  Lemma web_holds : forall u x, tyeq (kSh (wbb u x)) (eapp B0 u).
  Proof. intros u x; exact (eB u x). Qed.

  Definition buildW : SRefine k node T :=
    mkW k node T A0 B0 e aa wea_holds wbb web_holds.

  Lemma buildW_wf : kwfa buildW.
  Proof.
    exact (mkW_wf k node T A0 B0 e ety aa wea_holds wA wbb web_holds wB cohB).
  Qed.
End BuildW.

(* ------------------------------------------------------------------ *)
(* Two codes built the same way are equal as soon as their components   *)
(* are.  This is the whole of v1's `PiIso`/`SigIso` (120 lines, with a   *)
(* naturality square each): here the equality of two binder codes IS    *)
(* the conjunction of the hypotheses, so each proof is one `split`.     *)
(* ------------------------------------------------------------------ *)

Section BuildEq.
  Context (k : nat).
  Context (T1 A1 B1 : etm) (fT1 : forall y, prec y T1 -> Acc prec y)
          (T2 A2 B2 : etm) (fT2 : forall y, prec y T2 -> Acc prec y).
  Context (tyT : tyeq T1 T2).

  Local Notation n1 := (rk T1 (hT T1 fT1)).
  Local Notation n2 := (rk T2 (hT T2 fT2)).

  Section Pi.
    Context (e1 : eval T1 (epi A1 B1)) (e2 : eval T2 (epi A2 B2)).
    Context (cA1 : Code k (domNode T1 A1 B1 fT1 e1)) (eA1 : tyeq (projT1 cA1) A1)
            (cB1 : forall u x, Code k (codNode T1 A1 B1 fT1 e1 u
                                         (argGood k T1 A1 B1 fT1 e1 cA1 eA1 u x)))
            (eB1 : forall u x, tyeq (projT1 (cB1 u x)) (eapp B1 u)).
    Context (cA2 : Code k (domNode T2 A2 B2 fT2 e2)) (eA2 : tyeq (projT1 cA2) A2)
            (cB2 : forall u x, Code k (codNode T2 A2 B2 fT2 e2 u
                                         (argGood k T2 A2 B2 fT2 e2 cA2 eA2 u x)))
            (eB2 : forall u x, tyeq (projT1 (cB2 u x)) (eapp B2 u)).
    Context (dEq : kceq cA1 cA2)
            (cEq : forall u x u' x',
                kcEl (placeDom k T1 A1 B1 fT1 e1 cA1) u x
                     (placeDom k T2 A2 B2 fT2 e2 cA2) u' x' ->
                kceq (cB1 u x) (cB2 u' x')).

    Lemma buildPi_ceq :
      kceq (mkCode (buildPi k T1 A1 B1 fT1 e1 cA1 eA1 cB1 eB1))
           (mkCode (buildPi k T2 A2 B2 fT2 e2 cA2 eA2 cB2 eB2)).
    Proof. split; [exact tyT | split; [exact dEq | exact cEq]]. Qed.
  End Pi.

  Section Sig.
    Context (e1 : eval T1 (esig A1 B1)) (e2 : eval T2 (esig A2 B2)).
    Context (cA1 : Code k (sdomNode T1 A1 B1 fT1 e1)) (eA1 : tyeq (projT1 cA1) A1)
            (cB1 : forall u x, Code k (scodNode T1 A1 B1 fT1 e1 u
                                         (sargGood k T1 A1 B1 fT1 e1 cA1 eA1 u x)))
            (eB1 : forall u x, tyeq (projT1 (cB1 u x)) (eapp B1 u)).
    Context (cA2 : Code k (sdomNode T2 A2 B2 fT2 e2)) (eA2 : tyeq (projT1 cA2) A2)
            (cB2 : forall u x, Code k (scodNode T2 A2 B2 fT2 e2 u
                                         (sargGood k T2 A2 B2 fT2 e2 cA2 eA2 u x)))
            (eB2 : forall u x, tyeq (projT1 (cB2 u x)) (eapp B2 u)).
    Context (dEq : kceq cA1 cA2)
            (cEq : forall u x u' x',
                kcEl (placeSDom k T1 A1 B1 fT1 e1 cA1) u x
                     (placeSDom k T2 A2 B2 fT2 e2 cA2) u' x' ->
                kceq (cB1 u x) (cB2 u' x')).

    Lemma buildSig_ceq :
      kceq (mkCode (buildSig k T1 A1 B1 fT1 e1 cA1 eA1 cB1 eB1))
           (mkCode (buildSig k T2 A2 B2 fT2 e2 cA2 eA2 cB2 eB2)).
    Proof. split; [exact tyT | split; [exact dEq | exact cEq]]. Qed.
  End Sig.

  Section W.
    Context (e1 : eval T1 (ew A1 B1)) (e2 : eval T2 (ew A2 B2)).
    Context (cA1 : Code k (wdomNode T1 A1 B1 fT1 e1)) (eA1 : tyeq (projT1 cA1) A1)
            (cB1 : forall u x, Code k (wcodNode T1 A1 B1 fT1 e1 u
                                         (wargGood k T1 A1 B1 fT1 e1 cA1 eA1 u x)))
            (eB1 : forall u x, tyeq (projT1 (cB1 u x)) (eapp B1 u)).
    Context (cA2 : Code k (wdomNode T2 A2 B2 fT2 e2)) (eA2 : tyeq (projT1 cA2) A2)
            (cB2 : forall u x, Code k (wcodNode T2 A2 B2 fT2 e2 u
                                         (wargGood k T2 A2 B2 fT2 e2 cA2 eA2 u x)))
            (eB2 : forall u x, tyeq (projT1 (cB2 u x)) (eapp B2 u)).
    Context (dEq : kceq cA1 cA2)
            (cEq : forall u x u' x',
                kcEl (placeWDom k T1 A1 B1 fT1 e1 cA1) u x
                     (placeWDom k T2 A2 B2 fT2 e2 cA2) u' x' ->
                kceq (cB1 u x) (cB2 u' x')).

    Lemma buildW_ceq :
      kceq (mkCode (buildW k T1 A1 B1 fT1 e1 cA1 eA1 cB1 eB1))
           (mkCode (buildW k T2 A2 B2 fT2 e2 cA2 eA2 cB2 eB2)).
    Proof. split; [exact tyT | split; [exact dEq | exact cEq]]. Qed.
  End W.
End BuildEq.
