From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From Stdlib Require Import Arith Lia.

(* Smart constructors for the codes the interpretation builds, one per type
   former, each packaged with the identity property IdP of the code it
   produces, so that it can be used in turn as a component of a bigger code.

   The Pi constructor is the point of the whole of Codes/: it takes the
   codomain family together with the *isomorphisms* between its values at
   related arguments -- which is what the fundamental lemma has at a
   subderivation -- and discharges the three laws that Refine demands of a
   Pi-code.  The coherence data is the canonical transport of Codes/Iso.v,
   the composition law is its functoriality, and the identity law is the
   identity property of the codomain codes. *)

(* ------------------------------------------------------------------ *)
(* Level-k abbreviations. *)

Definition kU (k : nat) : nat -> etm -> Type := lU (lvl k).
Definition kUEq (k : nat) : forall m u, kU k m u -> forall u', kU k m u' -> Prop :=
  lUEq (lvl k).
Definition kOK (k : nat) : nat -> Prop := lOK (lvl k).
Definition ksym (k : nat) := lsym (lvl k).
Definition ktrans (k : nat) := ltrans (lvl k).

Definition kstage (k : nat) (alpha : Ord) : Stage := stage (kU k) (kUEq k) (kOK k) alpha.
Definition kUst (k : nat) (beta : Ord) : Stage := Ust (kU k) (kUEq k) (kOK k) beta.
Definition kSub (k : nat) (alpha : Ord) : Type := (kstage k alpha).(St).
Definition kSh {k alpha} (s : kSub k alpha) : etm := (kstage k alpha).(StSh) s.
Definition kElS {k alpha} (s : kSub k alpha) (u : etm) : Type := (kstage k alpha).(StEl) s u.
Definition kEqS {k alpha} (s : kSub k alpha) u (x : kElS s u) u' (x' : kElS s u') : Prop :=
  (kstage k alpha).(StEq) s u x u' x'.

Definition khj (k : nat) := hj (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k).
Definition kirel {k alpha} (s s' : kSub k alpha) : Prop := hj_rel (khj k alpha alpha) s s'.
Definition kidps (k : nat) (alpha : Ord) : kSub k alpha -> Prop :=
  idps (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha.

(* The universe u_m is a code of level k exactly when m < k. *)
Lemma kOK_iff k m : kOK k m <-> m < k.
Proof.
  unfold kOK; destruct k as [| n]; cbn.
  - split; [intros [] | intros H; inversion H].
  - split; auto.
Qed.

Lemma kOK_of k m : m < k -> kOK k m.
Proof. apply kOK_iff. Qed.

(* A code of level k at node beta with shadow S is exactly a refinement
   over the codes strictly below beta, indexed by S. *)
Definition SRefine (k : nat) (beta : Ord) (S : etm) : Type :=
  Refine (kstage k beta) (kOK k) S.
Definition mkCode {k beta S} (r : SRefine k beta S) : U (kU k) (kUEq k) (kOK k) beta :=
  existT _ S r.

Definition kwfa (k : nat) (alpha : Ord) {S} (r : SRefine k alpha S) : Prop :=
  wfa (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha r.

(* The identity property of the code a smart constructor returns, stated at
   the node it lives at. *)
Definition kIdP (k : nat) (beta : Ord) {S} (r : SRefine k beta S) : Prop :=
  IdP (kUst k beta) (hjU (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) beta beta) (mkCode r).

Lemma kIdP_of k beta {S} (r : SRefine k beta S) : kwfa k beta r -> kIdP k beta r.
Proof. intros W; apply (idp_next (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) beta r W). Qed.

(* ------------------------------------------------------------------ *)
(* The non-dependent formers.  Their well-formedness is vacuous. *)

Definition mkNat k beta T (e : eval T enat) : SRefine k beta T := r_nat _ _ T e.
Definition mkProp k beta T (e : eval T eprop) : SRefine k beta T := r_prop _ _ T e.
Definition mkPrf k beta T p (e : eval T (eprf p)) (H : Prop) : SRefine k beta T :=
  r_prf _ _ T p e H.
Definition mkUniv k beta T m (ok : kOK k m) (e : eval T (euniv m)) : SRefine k beta T :=
  r_univ _ _ T m ok e.
Definition mkNe k beta T N (e : eval T N) (s : stuck N) : SRefine k beta T := r_ne _ _ T N e s.

Lemma mkNat_wf k beta T e : kwfa k beta (mkNat k beta T e).
Proof. exact I. Qed.
Lemma mkProp_wf k beta T e : kwfa k beta (mkProp k beta T e).
Proof. exact I. Qed.
Lemma mkPrf_wf k beta T p e H : kwfa k beta (mkPrf k beta T p e H).
Proof. exact I. Qed.
Lemma mkUniv_wf k beta T m ok e : kwfa k beta (mkUniv k beta T m ok e).
Proof. exact I. Qed.
Lemma mkNe_wf k beta T N e s : kwfa k beta (mkNe k beta T N e s).
Proof. exact I. Qed.

(* ------------------------------------------------------------------ *)
(* Pi. *)

Section Pi.
  Context (k : nat) (alpha : Ord).
  Context (T A0 B0 : etm) (e : eval T (epi A0 B0)).
  Context (a : kSub k alpha) (ea : tyeq (kSh a) A0).
  Context (b : forall u, kElS a u -> kSub k alpha)
          (eb : forall u x, tyeq (kSh (b u x)) (eapp B0 u)).
  (* what the fundamental lemma has at the subderivation of the codomain *)
  Context (isoB : forall u x u' x', kEqS a u x u' x' -> kirel (b u' x') (b u x)).
  (* and the identity property of the codomain codes *)
  Context (idb : forall u x, kidps k alpha (b u x)).

  Definition cohPi u x u' x' (r : kEqS a u x u' x')
    : Transp (kstage k alpha) (b u' x') (b u x) :=
    Build_Transp (kstage k alpha) (b u' x') (b u x)
      (hj_to (khj k alpha alpha) (b u' x') (b u x) (isoB u x u' x' r))
      (hj_to_eq (khj k alpha alpha) (b u' x') (b u x) (isoB u x u' x' r)).

  (* Composition: functoriality of the canonical transport, plus the fact
     that it does not depend on the relatedness proof. *)
  Lemma cohPi_comp : forall u0 x0 u1 x1 u2 x2
      (r01 : kEqS a u0 x0 u1 x1) (r12 : kEqS a u1 x1 u2 x2) (r02 : kEqS a u0 x0 u2 x2)
      v (y : kElS (b u2 x2) v), goodS (kstage k alpha) (b u2 x2) v y ->
      kEqS (b u0 x0) v (tr (cohPi _ _ _ _ r01) v (tr (cohPi _ _ _ _ r12) v y))
                     v (tr (cohPi _ _ _ _ r02) v y).
  Proof.
    intros u0 x0 u1 x1 u2 x2 r01 r12 r02 v y _.
    apply (proj1 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha (b u0 x0))).
    apply (proj2 (hj_transP (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha alpha alpha)
             (b u2 x2) (b u1 x1) (b u0 x0)
             (isoB u1 x1 u2 x2 r12) (isoB u0 x0 u1 x1 r01) (isoB u0 x0 u2 x2 r02) v y).
  Qed.

  (* Identity: the transport along a self-isomorphism is the identity. *)
  Lemma cohPi_id : forall u x (r : kEqS a u x u x) v (y : kElS (b u x) v),
      goodS (kstage k alpha) (b u x) v y ->
      kEqS (b u x) v (tr (cohPi _ _ _ _ r) v y) v y.
  Proof. intros u x r v y _; exact (idb u x (isoB u x u x r) v y). Qed.

  Definition mkPi : SRefine k alpha T :=
    r_pi (kstage k alpha) (kOK k) T A0 B0 e a ea b eb cohPi cohPi_comp cohPi_id.

  Lemma mkPi_wf : (forall u x, kidps k alpha (b u x)) -> kidps k alpha a -> kwfa k alpha mkPi.
  Proof.
    intros Hb Ha; split; [exact Ha | split; [exact Hb |]].
    intros u x u' x' rr v y G.
    apply (hj_irr (khj k alpha alpha)).
  Qed.
End Pi.

(* ------------------------------------------------------------------ *)
(* Sigma.  Identical data, identical laws: a Sigma-code differs from a
   Pi-code only in the head its realiser evaluates to and in how its
   decoding reads that data. *)

Section Sig.
  Context (k : nat) (alpha : Ord).
  Context (T A0 B0 : etm) (e : eval T (esig A0 B0)).
  Context (a : kSub k alpha) (ea : tyeq (kSh a) A0).
  Context (b : forall u, kElS a u -> kSub k alpha)
          (eb : forall u x, tyeq (kSh (b u x)) (eapp B0 u)).
  (* what the fundamental lemma has at the subderivation of the codomain *)
  Context (isoB : forall u x u' x', kEqS a u x u' x' -> kirel (b u' x') (b u x)).
  (* and the identity property of the codomain codes *)
  Context (idb : forall u x, kidps k alpha (b u x)).

  Definition cohSig u x u' x' (r : kEqS a u x u' x')
    : Transp (kstage k alpha) (b u' x') (b u x) :=
    Build_Transp (kstage k alpha) (b u' x') (b u x)
      (hj_to (khj k alpha alpha) (b u' x') (b u x) (isoB u x u' x' r))
      (hj_to_eq (khj k alpha alpha) (b u' x') (b u x) (isoB u x u' x' r)).

  (* Composition: functoriality of the canonical transport, plus the fact
     that it does not depend on the relatedness proof. *)
  Lemma cohSig_comp : forall u0 x0 u1 x1 u2 x2
      (r01 : kEqS a u0 x0 u1 x1) (r12 : kEqS a u1 x1 u2 x2) (r02 : kEqS a u0 x0 u2 x2)
      v (y : kElS (b u2 x2) v), goodS (kstage k alpha) (b u2 x2) v y ->
      kEqS (b u0 x0) v (tr (cohSig _ _ _ _ r01) v (tr (cohSig _ _ _ _ r12) v y))
                     v (tr (cohSig _ _ _ _ r02) v y).
  Proof.
    intros u0 x0 u1 x1 u2 x2 r01 r12 r02 v y _.
    apply (proj1 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha (b u0 x0))).
    apply (proj2 (hj_transP (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha alpha alpha)
             (b u2 x2) (b u1 x1) (b u0 x0)
             (isoB u1 x1 u2 x2 r12) (isoB u0 x0 u1 x1 r01) (isoB u0 x0 u2 x2 r02) v y).
  Qed.

  (* Identity: the transport along a self-isomorphism is the identity. *)
  Lemma cohSig_id : forall u x (r : kEqS a u x u x) v (y : kElS (b u x) v),
      goodS (kstage k alpha) (b u x) v y ->
      kEqS (b u x) v (tr (cohSig _ _ _ _ r) v y) v y.
  Proof. intros u x r v y _; exact (idb u x (isoB u x u x r) v y). Qed.

  Definition mkSig : SRefine k alpha T :=
    r_sig (kstage k alpha) (kOK k) T A0 B0 e a ea b eb cohSig cohSig_comp cohSig_id.

  Lemma mkSig_wf : (forall u x, kidps k alpha (b u x)) -> kidps k alpha a -> kwfa k alpha mkSig.
  Proof.
    intros Hb Ha; split; [exact Ha | split; [exact Hb |]].
    intros u x u' x' rr v y G.
    apply (hj_irr (khj k alpha alpha)).
  Qed.

  (* Introducing and eliminating an element of a Sigma-code.  The two
     projections are projections; the pair needs the self-relatedness that
     Stage_next bundles into the decoding, and that is the identity law of the
     code -- the transport along the self-relation of the first component does
     nothing to the second. *)
  Definition mkSigEl u (z : kElS a (efst u)) (w : kElS (b (efst u) z) (esnd u))
    (g : Good T u) : (kUst k alpha).(StEl) (mkCode mkSig) u.
  Proof.
    refine (exist _ (existT _ z w, g) _).
    split; [| split; [| exact g]].
    - exists (stage_good (kU k) (kUEq k) (kOK k) alpha a (efst u) z).
      apply (proj1 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha
                      (b (efst u) z))).
      apply cohSig_id; apply stage_good.
    - exists (stage_good (kU k) (kUEq k) (kOK k) alpha a (efst u) z).
      apply (proj1 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) alpha
                      (b (efst u) z))).
      apply cohSig_id; apply stage_good.
  Defined.

  Definition mkSigFst u (x : (kUst k alpha).(StEl) (mkCode mkSig) u) : kElS a (efst u) :=
    projT1 (Datatypes.fst (proj1_sig x)).

  Definition mkSigSnd u (x : (kUst k alpha).(StEl) (mkCode mkSig) u)
    : kElS (b (efst u) (mkSigFst u x)) (esnd u) :=
    projT2 (Datatypes.fst (proj1_sig x)).

  Definition mkSigGood u (x : (kUst k alpha).(StEl) (mkCode mkSig) u) : Good T u :=
    Datatypes.snd (proj1_sig x).

  Lemma mkSigFst_pair u z w g : mkSigFst u (mkSigEl u z w g) = z.
  Proof. reflexivity. Qed.

  Lemma mkSigSnd_pair u z w g : mkSigSnd u (mkSigEl u z w g) = w.
  Proof. reflexivity. Qed.

  (* Surjective pairing, at the level of the code: rebuilding an element from
     its projections gives one RELATED to it -- not equal, because sigT has no
     eta -- and related is all the equality of a code ever asks for. *)
  Lemma mkSig_surj u (x : (kUst k alpha).(StEl) (mkCode mkSig) u) :
    (kUst k alpha).(StEq) (mkCode mkSig) u (mkSigEl u (mkSigFst u x) (mkSigSnd u x) (mkSigGood u x)) u x.
  Proof. exact (proj2_sig x). Qed.
End Sig.

