From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage.

(* The complete Pi case of the fundamental lemma, as a standalone
   construction: it takes exactly what the induction hypotheses at the two
   subderivations supply -- a code for the domain at its own node, a code for
   each codomain instance at its own node, the isomorphisms between the
   codomain codes at related arguments, and the identity property of all of
   them -- and returns the code for the Pi-type at the node rk T h, with its
   identity property.

   Nothing here lifts or transports a code: the components are placed by
   constructor injections (Interp/Stage.v) and all three laws of a Pi-code
   are discharged by the isomorphism machinery (Interp/Codes.v). *)

Section BuildPi.
  Context (k : nat) (T A0 B0 : etm).
  Context (fT : forall y, prec y T -> Acc prec y).
  Context (e : eval T (epi A0 B0)) (gT : Good_ty T).

  Local Notation dN := (domNode T A0 B0 fT e).
  Local Notation cN := (codNode T A0 B0 fT e).

  Context (cA : Code k dN) (eA : tyeq (projT1 cA) A0) (idA : LIdP cA).

  Local Notation aa := (placeDom k T A0 B0 fT e cA).
  Local Notation gArg := (argGood k T A0 B0 fT e cA eA).

  Context (cB : forall u (x : kElS aa u), Code k (cN u (gArg u x)))
          (eB : forall u x, tyeq (projT1 (cB u x)) (eapp B0 u))
          (idB : forall u x, LIdP (cB u x)).
  Context (isoB : forall u x u' x', kEqS aa u x u' x' -> iso (cB u' x') (cB u x)).

  Definition bb (u : etm) (x : kElS aa u) : kSub k (rk T (hT T fT)) :=
    placeCod k T A0 B0 fT e u (gArg u x) (cB u x).

  Lemma ea_holds : tyeq (kSh aa) A0.
  Proof. exact eA. Qed.

  Lemma eb_holds : forall u x, tyeq (kSh (bb u x)) (eapp B0 u).
  Proof. intros u x; exact (eB u x). Qed.

  Definition buildPi : SRefine k (rk T (hT T fT)) T :=
    mkPi k (rk T (hT T fT)) T A0 B0 e aa ea_holds bb eb_holds isoB idB.

  Lemma buildPi_wf : kwfa k (rk T (hT T fT)) buildPi.
  Proof.
    apply (mkPi_wf k (rk T (hT T fT)) T A0 B0 e aa ea_holds bb eb_holds isoB idB);
      [exact idB | exact idA].
  Qed.

  Lemma buildPi_idp : kIdP k (rk T (hT T fT)) buildPi.
  Proof. apply kIdP_of; exact buildPi_wf. Qed.
End BuildPi.

(* Two Pi-codes built by buildPi, with isomorphic domains and codomains, are
   isomorphic.  The only real obligation is the naturality square of
   isoRefine, and it comes out of functoriality: the coherence data of a code
   built by buildPi IS the canonical transport, so both sides of the square
   are composites of canonical transports between the same pair of codes, and
   `hj_irr` identifies them. *)
Section PiIso.
  Context (k : nat).
  Context (T1 A1 B1 : etm) (fT1 : forall y, prec y T1 -> Acc prec y)
          (e1 : eval T1 (epi A1 B1)).
  Context (cA1 : Code k (domNode T1 A1 B1 fT1 e1)) (eA1 : tyeq (projT1 cA1) A1)
          (idA1 : LIdP cA1).
  Context (cB1 : forall u x, Code k (codNode T1 A1 B1 fT1 e1 u
                                       (argGood k T1 A1 B1 fT1 e1 cA1 eA1 u x)))
          (eB1 : forall u x, tyeq (projT1 (cB1 u x)) (eapp B1 u))
          (idB1 : forall u x, LIdP (cB1 u x))
          (isoB1 : forall u x u' x', kEqS (placeDom k T1 A1 B1 fT1 e1 cA1) u x u' x' ->
                     iso (cB1 u' x') (cB1 u x)).

  Context (T2 A2 B2 : etm) (fT2 : forall y, prec y T2 -> Acc prec y)
          (e2 : eval T2 (epi A2 B2)).
  Context (cA2 : Code k (domNode T2 A2 B2 fT2 e2)) (eA2 : tyeq (projT1 cA2) A2)
          (idA2 : LIdP cA2).
  Context (cB2 : forall u x, Code k (codNode T2 A2 B2 fT2 e2 u
                                       (argGood k T2 A2 B2 fT2 e2 cA2 eA2 u x)))
          (eB2 : forall u x, tyeq (projT1 (cB2 u x)) (eapp B2 u))
          (idB2 : forall u x, LIdP (cB2 u x))
          (isoB2 : forall u x u' x', kEqS (placeDom k T2 A2 B2 fT2 e2 cA2) u x u' x' ->
                     iso (cB2 u' x') (cB2 u x)).

  Local Notation b1 := (rk T1 (hT T1 fT1)).
  Local Notation b2 := (rk T2 (hT T2 fT2)).
  Local Notation aa1 := (placeDom k T1 A1 B1 fT1 e1 cA1).
  Local Notation aa2 := (placeDom k T2 A2 B2 fT2 e2 cA2).
  Local Notation bb1 := (bb k T1 A1 B1 fT1 e1 cA1 eA1 cB1).
  Local Notation bb2 := (bb k T2 A2 B2 fT2 e2 cA2 eA2 cB2).
  Local Notation tP := (hj_transP (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)).
  Local Notation PER2 := (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) b2).

  (* What relates the two codes componentwise. *)
  Context (tyT : tyeq T1 T2)
          (dIso : hj_rel (khj k b1 b2) aa1 aa2)
          (cIso : forall u x u' y, hjhet (khj k b1 b2) aa1 aa2 u x u' y ->
                    hj_rel (khj k b1 b2) (bb1 u x) (bb2 u' y)).

  Lemma buildPi_iso :
    iso (mkCode (buildPi k T1 A1 B1 fT1 e1 cA1 eA1 cB1 eB1 idB1 isoB1))
        (mkCode (buildPi k T2 A2 B2 fT2 e2 cA2 eA2 cB2 eB2 idB2 isoB2)).
  Proof.
    apply conj; [exact tyT | apply conj; [exact dIso | apply conj; [exact cIso |]]].
    intros u1 x1 u1' x1' y1 y1' Hy Hy' r1 s1 Q Q' v w.
    pose proof (proj1 (tP b1 b1 b2) (bb1 u1' x1') (bb1 u1 x1) (bb2 u1 y1)
                  (isoB1 u1 x1 u1' x1' r1) Q) as R.
    pose proof (proj1 (tP b1 b2 b2) (bb1 u1' x1') (bb2 u1' y1') (bb2 u1 y1)
                  Q' (isoB2 u1 y1 u1' y1' s1)) as R'.
    pose proof (proj1 (PER2 (bb2 u1 y1))) as Hs; unfold EqSym in Hs.
    pose proof (proj2 (PER2 (bb2 u1 y1))) as Ht; unfold EqTrans in Ht.
    eapply Ht;
      [ apply Hs;
        apply (proj2 (tP b1 b1 b2) (bb1 u1' x1') (bb1 u1 x1) (bb2 u1 y1)
                 (isoB1 u1 x1 u1' x1' r1) Q R) |].
    eapply Ht;
      [ apply (hj_irr (khj k b1 b2) (bb1 u1' x1') (bb2 u1 y1) R R') |].
    apply (proj2 (tP b1 b2 b2) (bb1 u1' x1') (bb2 u1' y1') (bb2 u1 y1)
             Q' (isoB2 u1 y1 u1' y1' s1) R').
  Qed.
End PiIso.


(* ------------------------------------------------------------------ *)
(* The same for Sigma, component for component. *)

Section BuildSig.
  Context (k : nat) (T A0 B0 : etm).
  Context (fT : forall y, prec y T -> Acc prec y).
  Context (e : eval T (esig A0 B0)) (gT : Good_ty T).

  Local Notation dN := (sdomNode T A0 B0 fT e).
  Local Notation cN := (scodNode T A0 B0 fT e).

  Context (cA : Code k dN) (eA : tyeq (projT1 cA) A0) (idA : LIdP cA).

  Local Notation aa := (placeSDom k T A0 B0 fT e cA).
  Local Notation gArg := (sargGood k T A0 B0 fT e cA eA).

  Context (cB : forall u (x : kElS aa u), Code k (cN u (gArg u x)))
          (eB : forall u x, tyeq (projT1 (cB u x)) (eapp B0 u))
          (idB : forall u x, LIdP (cB u x)).
  Context (isoB : forall u x u' x', kEqS aa u x u' x' -> iso (cB u' x') (cB u x)).

  Definition sbb (u : etm) (x : kElS aa u) : kSub k (rk T (hT T fT)) :=
    placeSCod k T A0 B0 fT e u (gArg u x) (cB u x).

  Lemma sea_holds : tyeq (kSh aa) A0.
  Proof. exact eA. Qed.

  Lemma seb_holds : forall u x, tyeq (kSh (sbb u x)) (eapp B0 u).
  Proof. intros u x; exact (eB u x). Qed.

  Definition buildSig : SRefine k (rk T (hT T fT)) T :=
    mkSig k (rk T (hT T fT)) T A0 B0 e aa sea_holds sbb seb_holds isoB idB.

  Lemma buildSig_wf : kwfa k (rk T (hT T fT)) buildSig.
  Proof.
    apply (mkSig_wf k (rk T (hT T fT)) T A0 B0 e aa sea_holds sbb seb_holds isoB idB);
      [exact idB | exact idA].
  Qed.

  Lemma buildSig_idp : kIdP k (rk T (hT T fT)) buildSig.
  Proof. apply kIdP_of; exact buildSig_wf. Qed.
End BuildSig.

Section SigIso.
  Context (k : nat).
  Context (T1 A1 B1 : etm) (fT1 : forall y, prec y T1 -> Acc prec y)
          (e1 : eval T1 (esig A1 B1)).
  Context (cA1 : Code k (sdomNode T1 A1 B1 fT1 e1)) (eA1 : tyeq (projT1 cA1) A1)
          (idA1 : LIdP cA1).
  Context (cB1 : forall u x, Code k (scodNode T1 A1 B1 fT1 e1 u
                                       (sargGood k T1 A1 B1 fT1 e1 cA1 eA1 u x)))
          (eB1 : forall u x, tyeq (projT1 (cB1 u x)) (eapp B1 u))
          (idB1 : forall u x, LIdP (cB1 u x))
          (isoB1 : forall u x u' x', kEqS (placeSDom k T1 A1 B1 fT1 e1 cA1) u x u' x' ->
                     iso (cB1 u' x') (cB1 u x)).

  Context (T2 A2 B2 : etm) (fT2 : forall y, prec y T2 -> Acc prec y)
          (e2 : eval T2 (esig A2 B2)).
  Context (cA2 : Code k (sdomNode T2 A2 B2 fT2 e2)) (eA2 : tyeq (projT1 cA2) A2)
          (idA2 : LIdP cA2).
  Context (cB2 : forall u x, Code k (scodNode T2 A2 B2 fT2 e2 u
                                       (sargGood k T2 A2 B2 fT2 e2 cA2 eA2 u x)))
          (eB2 : forall u x, tyeq (projT1 (cB2 u x)) (eapp B2 u))
          (idB2 : forall u x, LIdP (cB2 u x))
          (isoB2 : forall u x u' x', kEqS (placeSDom k T2 A2 B2 fT2 e2 cA2) u x u' x' ->
                     iso (cB2 u' x') (cB2 u x)).

  Local Notation b1 := (rk T1 (hT T1 fT1)).
  Local Notation b2 := (rk T2 (hT T2 fT2)).
  Local Notation aa1 := (placeSDom k T1 A1 B1 fT1 e1 cA1).
  Local Notation aa2 := (placeSDom k T2 A2 B2 fT2 e2 cA2).
  Local Notation sbb1 := (sbb k T1 A1 B1 fT1 e1 cA1 eA1 cB1).
  Local Notation sbb2 := (sbb k T2 A2 B2 fT2 e2 cA2 eA2 cB2).
  Local Notation tP := (hj_transP (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)).
  Local Notation PER2 := (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) b2).

  (* What relates the two codes componentwise. *)
  Context (tyT : tyeq T1 T2)
          (dIso : hj_rel (khj k b1 b2) aa1 aa2)
          (cIso : forall u x u' y, hjhet (khj k b1 b2) aa1 aa2 u x u' y ->
                    hj_rel (khj k b1 b2) (sbb1 u x) (sbb2 u' y)).

  Lemma buildSig_iso :
    iso (mkCode (buildSig k T1 A1 B1 fT1 e1 cA1 eA1 cB1 eB1 idB1 isoB1))
        (mkCode (buildSig k T2 A2 B2 fT2 e2 cA2 eA2 cB2 eB2 idB2 isoB2)).
  Proof.
    apply conj; [exact tyT | apply conj; [exact dIso | apply conj; [exact cIso |]]].
    intros u1 x1 u1' x1' y1 y1' Hy Hy' r1 s1 Q Q' v w.
    pose proof (proj1 (tP b1 b1 b2) (sbb1 u1' x1') (sbb1 u1 x1) (sbb2 u1 y1)
                  (isoB1 u1 x1 u1' x1' r1) Q) as R.
    pose proof (proj1 (tP b1 b2 b2) (sbb1 u1' x1') (sbb2 u1' y1') (sbb2 u1 y1)
                  Q' (isoB2 u1 y1 u1' y1' s1)) as R'.
    pose proof (proj1 (PER2 (sbb2 u1 y1))) as Hs; unfold EqSym in Hs.
    pose proof (proj2 (PER2 (sbb2 u1 y1))) as Ht; unfold EqTrans in Ht.
    eapply Ht;
      [ apply Hs;
        apply (proj2 (tP b1 b1 b2) (sbb1 u1' x1') (sbb1 u1 x1) (sbb2 u1 y1)
                 (isoB1 u1 x1 u1' x1' r1) Q R) |].
    eapply Ht;
      [ apply (hj_irr (khj k b1 b2) (sbb1 u1' x1') (sbb2 u1 y1) R R') |].
    apply (proj2 (tP b1 b2 b2) (sbb1 u1' x1') (sbb2 u1' y1') (sbb2 u1 y1)
             Q' (isoB2 u1 y1 u1' y1' s1) R').
  Qed.
End SigIso.
