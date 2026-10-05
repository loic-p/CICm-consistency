From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Mor Codes.Levels Codes.Lift.
From Stdlib Require Import Arith Lia.

(* Smart constructors for the codes the interpretation builds, one per type
   former, each with the well-formedness of the code it produces, so that it
   can be used in turn as a component of a bigger code.

   This is where v2's redesign shows most plainly.  A v1 Pi-code carried a
   TRANSPORT between the codomain codes at related arguments, together with
   its composition and identity laws, so `mkPi` had to build that transport
   out of the canonical one of Codes/Iso.v and discharge three laws; the
   file was 243 lines for Pi and Sigma alone.  Here a binder code carries its
   components' EQUALITIES, the interpretation hands it the canonical ones, and
   the only genuine input is the coherence of the codomain family -- "related
   arguments give equal codomain codes" -- which is exactly what the
   fundamental lemma has at the subderivation of the codomain.  Nothing has to
   be transported, so there are no laws to discharge. *)

(* PERFORMANCE.  v1's Interp/SigEl.v took ~500s and Interp/Build.v ~40s,
   because the conversion checker was asked to compare composites of canonical
   TRANSPORTS -- terms built from `hj`, a double recursion over Brouwer trees
   whose indices come from `rk`.  v2 has no transports in its codes, so the
   families above compile in under a second each; what remains of that risk is
   the COERCION of Codes/Str.v, whose value comes out of the `big` pack and is
   never needed (only its coherence is).  Sealing it, and the other
   stage-recursive constructions, keeps the oracle from ever unfolding one.

   If a later file genuinely needs one of these to compute, it can reopen it
   locally with `Transparent`; nothing below relies on their values. *)

Opaque xto xtrU xtrE nsym nsymU xsym xsymU big.
Opaque crefl subRefl elRefl.
Opaque cRed cExp cRed_rel cExp_rel bigExp.

(* ------------------------------------------------------------------ *)
(* Level-k abbreviations.                                              *)
(* ------------------------------------------------------------------ *)

Definition kU (k : nat) : nat -> etm -> Type := lU (lvl k).
Definition kUEq (k : nat)
  : forall m u, kU k m u -> forall m' u', kU k m' u' -> Prop := lUEq (lvl k).
Definition kOK (k : nat) : nat -> Prop := lOK (lvl k).
Definition krefl (k : nat) := lrefl (lvl k).
Definition ksym (k : nat) := lsym (lvl k).
Definition ktrans (k : nat) := ltrans (lvl k).

Definition kstage (k : nat) (alpha : Ord) : Stage := stage (kU k) (kOK k) alpha.
Definition kUst (k : nat) (beta : Ord) : Stage := Ust (kU k) (kOK k) beta.
Definition kSub (k : nat) (alpha : Ord) : Type := St (kstage k alpha).
Definition kCode (k : nat) (beta : Ord) : Type := U (kU k) (kOK k) beta.

Definition kSh {k alpha} (s : kSub k alpha) : etm := StSh (kstage k alpha) s.
Definition kElS {k alpha} (s : kSub k alpha) (u : etm) : Type :=
  StEl (kstage k alpha) s u.

(* the canonical equalities, HETEROGENEOUS in the code: this is the whole
   difference from v1, where `kEqS` could only compare elements of one code
   and a transport was needed to say anything about two *)
(* heterogeneous in the NODE as well as in the code: two components placed at
   two different nodes are compared directly *)
Definition kcU {k alpha alpha'} (s : kSub k alpha) (s' : kSub k alpha') : Prop :=
  cU (xcmp (kU k) (kUEq k) (kOK k) alpha alpha') s s'.
Definition kcEl {k alpha alpha'} (s : kSub k alpha) u (x : kElS s u)
  (s' : kSub k alpha') u' (x' : kElS s' u') : Prop :=
  cEl (xcmp (kU k) (kUEq k) (kOK k) alpha alpha') s u x s' u' x'.
Definition kwfS {k alpha} (s : kSub k alpha) : Prop :=
  wfsub (kU k) (kUEq k) (kOK k) alpha s.

(* and the same at a node *)
Definition kElC {k beta} (c : kCode k beta) (u : etm) : Type := StEl (kUst k beta) c u.
Definition kceq {k beta beta'} (c : kCode k beta) (c' : kCode k beta') : Prop :=
  ceq (kU k) (kUEq k) (kOK k) c c'.
Definition kcel {k beta beta'} (c : kCode k beta) u (x : kElC c u)
  (c' : kCode k beta') u' (x' : kElC c' u') : Prop :=
  cel (kU k) (kUEq k) (kOK k) c u x c' u' x'.
Definition kwfc {k beta} (c : kCode k beta) : Prop := wfc (kU k) (kUEq k) (kOK k) c.

(* The universe u_m is a code of level k exactly when m < k. *)
Lemma kOK_iff k m : kOK k m <-> m < k.
Proof. exact (lOK_lt k m). Qed.

Lemma kOK_of k m : m < k -> kOK k m.
Proof. apply kOK_iff. Qed.

(* the structure of the hierarchy, specialised to level k *)
Definition kself {k alpha} (s : kSub k alpha) : kwfS s -> kcU s s :=
  fun w => wfsub_self (kU k) (kUEq k) (kOK k) alpha s w.
Definition kselfE {k alpha} (s : kSub k alpha) (w : kwfS s) u (x : kElS s u)
  : kcEl s u x s u x :=
  subRefl (kU k) (kUEq k) (kOK k) (krefl k) alpha s w u x.
Definition kcsym {k alpha} := xsym (kU k) (kUEq k) (kOK k) (ksym k)
  (alpha := alpha) (alpha' := alpha).
Definition kcsymU {k alpha} := xsymU (kU k) (kUEq k) (kOK k) (ksym k)
  (alpha := alpha) (alpha' := alpha).

Definition kcrefl {k beta} (c : kCode k beta) (W : kwfc c) u (x : kElC c u)
  : kcel c u x c u x :=
  crefl (kU k) (kUEq k) (kOK k) (krefl k) c W u x.
Definition knsym {k b b'} (c : kCode k b) (c' : kCode k b') u x u' x'
  : kcel c u x c' u' x' -> kcel c' u' x' c u x :=
  nsym (kU k) (kUEq k) (kOK k) (ksym k) c c' u x u' x'.
Definition knsymU {k b b'} (c : kCode k b) (c' : kCode k b')
  : kceq c c' -> kceq c' c :=
  nsymU (kU k) (kUEq k) (kOK k) (ksym k) c c'.
Definition ktrU {k b b' b''} (c : kCode k b) (c' : kCode k b') (c'' : kCode k b'')
  : kwfc c -> kwfc c' -> kwfc c'' -> kceq c c' -> kceq c' c'' -> kceq c c'' :=
  xtrU (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) c c' c''.
Definition ktrE {k b b' b''} (c : kCode k b) (c' : kCode k b') (c'' : kCode k b'')
  : forall u x u' x' u'' x'', kwfc c -> kwfc c' -> kwfc c'' -> kceq c c' ->
    kcel c u x c' u' x' -> kcel c' u' x' c'' u'' x'' -> kcel c u x c'' u'' x'' :=
  xtrE (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) c c' c''.

(* the coercion, with its coherence and its respect for the equality *)
Definition kto {k b b'} (c : kCode k b) (c' : kCode k b') (W : kwfc c) (W' : kwfc c')
  (e : kceq c c') u (x : kElC c u) : kElC c' u :=
  xto (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) c c' W W' e u x.
Definition kto_coh {k b b'} (c : kCode k b) (c' : kCode k b') W W' e u x
  : kcel c u x c' u (kto c c' W W' e u x) :=
  xto_coh (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) c c' W W' e u x.
Definition kto_eq {k b b'} (c : kCode k b) (c' : kCode k b') W W' (e : kceq c c')
  (c0 : kCode k b) (c0' : kCode k b') W0 W0' (e0 : kceq c0 c0') u x u0 x0
  : kceq c c0 -> kcel c u x c0 u0 x0 ->
    kcel c' u (kto c c' W W' e u x) c0' u0 (kto c0 c0' W0 W0' e0 u0 x0) :=
  xto_eq (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) c c' W W' e
    c0 c0' W0 W0' e0 u x u0 x0.

(* ------------------------------------------------------------------ *)
(* Layer-1 types of the realisers: what the self-equality of a code     *)
(* asks for.  v1's `wfa` did not include it; v2's does, because a code's *)
(* self-equality is what the coercion's coherence needs at a Pi code.    *)
(* ------------------------------------------------------------------ *)

Lemma tyeq_nat T : eval T enat -> tyeq T T.
Proof. intros e; exists 0; exists NatPer; apply LR_nat; exact e. Qed.

Lemma tyeq_prop T : eval T eprop -> tyeq T T.
Proof. intros e; exists 0; exists PR; apply LR_prop; exact e. Qed.

Lemma tyeq_prf T p : eval T (eprf p) -> PR p p -> tyeq T T.
Proof. intros e Hp; exists 0; exists TruePer; eapply LR_prf; [exact e | exact e | exact Hp]. Qed.

Lemma tyeq_univ T m : eval T (euniv m) -> tyeq T T.
Proof.
  intros e; exists (S m); eexists; apply (LR_univ _ _ T T m); [lia | exact e | exact e].
Qed.

(* ------------------------------------------------------------------ *)
(* Codes at a node, and the four clauses that carry no components.      *)
(* ------------------------------------------------------------------ *)

Definition SRefine (k : nat) (beta : Ord) (S : etm) : Type :=
  Refine (kstage k beta) (kOK k) S.
Definition mkCode {k beta S} (r : SRefine k beta S) : kCode k beta := existT _ S r.
Definition kwfa {k beta S} (r : SRefine k beta S) : Prop :=
  wfRefine (xcmp (kU k) (kUEq k) (kOK k) beta beta) (fun s => kwfS s) r.

Lemma kwfa_code {k beta S} (r : SRefine k beta S) : kwfa r -> kwfc (mkCode r).
Proof. exact (fun h => h). Qed.

Lemma mkCode_sh {k beta S} (r : SRefine k beta S) : projT1 (mkCode r) = S.
Proof. reflexivity. Qed.

Definition mkNat k beta T (e : eval T enat) : SRefine k beta T := r_nat T e.
Definition mkProp k beta T (e : eval T eprop) : SRefine k beta T := r_prop T e.
Definition mkPrf k beta T p (e : eval T (eprf p)) (H : Prop) : SRefine k beta T :=
  r_prf T p e H.
Definition mkUniv k beta T m (ok : kOK k m) (e : eval T (euniv m)) : SRefine k beta T :=
  r_univ T m ok e.

Lemma mkNat_wf k beta T e : kwfa (mkNat k beta T e).
Proof. split; [exact I | exact (tyeq_nat T e)]. Qed.

Lemma mkProp_wf k beta T e : kwfa (mkProp k beta T e).
Proof. split; [exact I | exact (tyeq_prop T e)]. Qed.

Lemma mkPrf_wf k beta T p e H : PR p p -> kwfa (mkPrf k beta T p e H).
Proof.
  intros Hp; split; [exact I |].
  split; [exact (tyeq_prf T p e Hp) | split; exact (fun h => h)].
Qed.

Lemma mkUniv_wf k beta T m ok e : kwfa (mkUniv k beta T m ok e).
Proof. split; [exact I | split; [exact (tyeq_univ T m e) | reflexivity]]. Qed.

(* ------------------------------------------------------------------ *)
(* Pi.                                                                 *)
(*                                                                    *)
(* The code carries its components' canonical equalities, so the only   *)
(* input beyond the components themselves is `cohB`: related arguments  *)
(* give EQUAL codomain codes.  v1 needed, in place of `cohB`, a         *)
(* transport between those codes together with its composition and      *)
(* identity laws.                                                      *)
(* ------------------------------------------------------------------ *)

Section Pi.
Context (k : nat) (alpha : Ord).
Context (T A0 B0 : etm) (e : eval T (epi A0 B0)) (ety : tyeq T T).
Context (a : kSub k alpha) (ea : tyeq (kSh a) A0) (wa : kwfS a).
Context (b : forall u, kElS a u -> kSub k alpha)
        (eb : forall u x, tyeq (kSh (b u x)) (eapp B0 u))
        (wb : forall u x, kwfS (b u x)).
Context (cohB : forall u x u' x', kcEl a u x a u' x' -> kcU (b u x) (b u' x')).

Definition mkPi : SRefine k alpha T :=
  r_pi T A0 B0 e a ea (fun u x u' x' => kcEl a u x a u' x') b eb
    (fun u x u' x' v y v' y' => kcEl (b u x) v y (b u' x') v' y').

Lemma mkPi_wf : kwfa mkPi.
Proof.
  split.
  - split; [exact wa | split; [exact wb | split; intros; split; exact (fun h => h)]].
  - split; [exact ety | split; [exact (kself a wa) | exact cohB]].
Qed.

(* elements: the extensional functions *)
Definition mkPiEl u (f : forall u1 (x1 : kElS a u1), kElS (b u1 x1) (eapp u u1))
  (fext : forall u1 x1 u1' x1', kcEl a u1 x1 a u1' x1' ->
      kcEl (b u1 x1) (eapp u u1) (f u1 x1) (b u1' x1') (eapp u u1') (f u1' x1'))
  (g : Good T u) : kElC (mkCode mkPi) u := (exist _ f fext, g).

Definition mkPiApp u (F : kElC (mkCode mkPi) u) u1 (x1 : kElS a u1)
  : kElS (b u1 x1) (eapp u u1) := proj1_sig (Datatypes.fst F) u1 x1.

Definition mkPiGood u (F : kElC (mkCode mkPi) u) : Good T u := Datatypes.snd F.

Lemma mkPiApp_el u f fext g u1 x1 : mkPiApp u (mkPiEl u f fext g) u1 x1 = f u1 x1.
Proof. reflexivity. Qed.

Lemma mkPiApp_ext u (F : kElC (mkCode mkPi) u) u1 x1 u1' x1' :
  kcEl a u1 x1 a u1' x1' ->
  kcEl (b u1 x1) (eapp u u1) (mkPiApp u F u1 x1)
       (b u1' x1') (eapp u u1') (mkPiApp u F u1' x1').
Proof. exact (proj2_sig (Datatypes.fst F) u1 x1 u1' x1'). Qed.

(* the equality of two function elements IS pointwise agreement on related
   arguments: v1 had to compose with a transport to say this *)
Lemma mkPi_eq u (F : kElC (mkCode mkPi) u) u' (F' : kElC (mkCode mkPi) u') :
  (forall u1 x1 u1' x1', kcEl a u1 x1 a u1' x1' ->
     kcEl (b u1 x1) (eapp u u1) (mkPiApp u F u1 x1)
          (b u1' x1') (eapp u' u1') (mkPiApp u' F' u1' x1')) ->
  Rel T u u' -> kcel (mkCode mkPi) u F (mkCode mkPi) u' F'.
Proof. intros H HR; split; [exact H | split; [exact ety | exact HR]]. Qed.

Lemma mkPi_eq_inv u (F : kElC (mkCode mkPi) u) u' (F' : kElC (mkCode mkPi) u') :
  kcel (mkCode mkPi) u F (mkCode mkPi) u' F' ->
  forall u1 x1 u1' x1', kcEl a u1 x1 a u1' x1' ->
  kcEl (b u1 x1) (eapp u u1) (mkPiApp u F u1 x1)
       (b u1' x1') (eapp u' u1') (mkPiApp u' F' u1' x1').
Proof. intros H; exact (proj1 H). Qed.
End Pi.

(* ------------------------------------------------------------------ *)
(* Sigma.  The decoding carries no condition at all -- a pair is good    *)
(* as soon as its components are -- so the element constructor is the    *)
(* pair, and surjective pairing holds up to the equality by reflexivity  *)
(* of the components.                                                   *)
(* ------------------------------------------------------------------ *)

Section Sig.
Context (k : nat) (alpha : Ord).
Context (T A0 B0 : etm) (e : eval T (esig A0 B0)) (ety : tyeq T T).
Context (a : kSub k alpha) (ea : tyeq (kSh a) A0) (wa : kwfS a).
Context (b : forall u, kElS a u -> kSub k alpha)
        (eb : forall u x, tyeq (kSh (b u x)) (eapp B0 u))
        (wb : forall u x, kwfS (b u x)).
Context (cohB : forall u x u' x', kcEl a u x a u' x' -> kcU (b u x) (b u' x')).

Definition mkSig : SRefine k alpha T := r_sig T A0 B0 e a ea b eb.

Lemma mkSig_wf : kwfa mkSig.
Proof.
  split.
  - split; [exact wa | split; [exact wb | exact I]].
  - split; [exact ety | split; [exact (kself a wa) | exact cohB]].
Qed.

Definition mkSigEl u (z : kElS a (efst u)) (w : kElS (b (efst u) z) (esnd u))
  (g : Good T u) : kElC (mkCode mkSig) u := (existT _ z w, g).

Definition mkSigFst u (x : kElC (mkCode mkSig) u) : kElS a (efst u) :=
  projT1 (Datatypes.fst x).
Definition mkSigSnd u (x : kElC (mkCode mkSig) u)
  : kElS (b (efst u) (mkSigFst u x)) (esnd u) := projT2 (Datatypes.fst x).
Definition mkSigGood u (x : kElC (mkCode mkSig) u) : Good T u := Datatypes.snd x.

Lemma mkSigFst_pair u z w g : mkSigFst u (mkSigEl u z w g) = z.
Proof. reflexivity. Qed.
Lemma mkSigSnd_pair u z w g : mkSigSnd u (mkSigEl u z w g) = w.
Proof. reflexivity. Qed.

(* surjective pairing at the level of the code: rebuilding an element from its
   projections gives one RELATED to it (sigT has no eta), and related is all
   the equality ever asks for *)
Lemma mkSig_surj u (x : kElC (mkCode mkSig) u) :
  kcel (mkCode mkSig) u (mkSigEl u (mkSigFst u x) (mkSigSnd u x) (mkSigGood u x))
       (mkCode mkSig) u x.
Proof.
  split; [apply kselfE; exact wa |].
  split; [apply kselfE; apply wb |].
  split; [exact ety | exact (Datatypes.snd x)].
Qed.

Lemma mkSig_eq u (x : kElC (mkCode mkSig) u) u' (x' : kElC (mkCode mkSig) u') :
  kcEl a (efst u) (mkSigFst u x) a (efst u') (mkSigFst u' x') ->
  kcEl (b (efst u) (mkSigFst u x)) (esnd u) (mkSigSnd u x)
       (b (efst u') (mkSigFst u' x')) (esnd u') (mkSigSnd u' x') ->
  Rel T u u' -> kcel (mkCode mkSig) u x (mkCode mkSig) u' x'.
Proof. intros H1 H2 HR; split; [exact H1 | split; [exact H2 | split; [exact ety | exact HR]]]. Qed.
End Sig.

(* ------------------------------------------------------------------ *)
(* W.  New in v2: the trees over a label code and a branching family.   *)
(*                                                                    *)
(* An element is a tree together with its self-relation, and `WRel t t` *)
(* IS the statement that the tree's branching is hereditarily           *)
(* extensional -- so `mkWsup` asks exactly for what the interpretation   *)
(* of `sup` has: a label, a branch function into the W code, and the     *)
(* extensionality of that function.                                     *)
(* ------------------------------------------------------------------ *)

Section W.
Context (k : nat) (alpha : Ord).
Context (T A0 B0 : etm) (e : eval T (ew A0 B0)) (ety : tyeq T T).
Context (a : kSub k alpha) (ea : tyeq (kSh a) A0) (wa : kwfS a).
Context (b : forall u, kElS a u -> kSub k alpha)
        (eb : forall u x, tyeq (kSh (b u x)) (eapp B0 u))
        (wb : forall u x, kwfS (b u x)).
Context (cohB : forall u x u' x', kcEl a u x a u' x' -> kcU (b u x) (b u' x')).

Definition mkW : SRefine k alpha T :=
  r_w T A0 B0 e a ea (fun u x u' x' => kcEl a u x a u' x') b eb
    (fun u x u' x' v y v' y' => kcEl (b u x) v y (b u' x') v' y').

Lemma mkW_wf : kwfa mkW.
Proof.
  split.
  - split; [exact wa | split; [exact wb | split; intros; split; exact (fun h => h)]].
  - split; [exact ety | split; [exact (kself a wa) | exact cohB]].
Qed.

(* the trees and their relation, at the canonical equalities *)
Definition kWEl (u : etm) : Type := WEl T a b u.
Definition kWRel {u} (t : kWEl u) {u'} (t' : kWEl u') : Prop :=
  WRel T T a a b b (fun u1 x1 u1' x1' => kcEl a u1 x1 a u1' x1')
    (fun u1 x1 u1' x1' v y v' y' => kcEl (b u1 x1) v y (b u1' x1') v' y') t t'.

Definition kWgood {u} (t : kWEl u) : Good T u :=
  match t with wel_sup _ _ _ _ _ gd _ => gd end.

Definition mkWtree u (x : kElC (mkCode mkW) u) : kWEl u := proj1_sig (Datatypes.fst x).
Definition mkWrel u (x : kElC (mkCode mkW) u) : kWRel (mkWtree u x) (mkWtree u x) :=
  proj2_sig (Datatypes.fst x).
Definition mkWGood u (x : kElC (mkCode mkW) u) : Good T u := Datatypes.snd x.

Definition mkWel u (t : kWEl u) (tr : kWRel t t) (g : Good T u)
  : kElC (mkCode mkW) u := (exist (fun z : kWEl u => kWRel z z) t tr, g).

(* sup *)
Definition mkWsup (w u0 f : etm) (z : kElS a u0)
  (ev : eval w (esup u0 f)) (gd : Good T w)
  (sub : forall v (y : kElS (b u0 z) v), kElC (mkCode mkW) (eapp f v))
  (subext : forall v y v' y', kcEl (b u0 z) v y (b u0 z) v' y' ->
      kcel (mkCode mkW) (eapp f v) (sub v y) (mkCode mkW) (eapp f v') (sub v' y'))
  : kElC (mkCode mkW) w.
Proof.
  refine (mkWel w (wel_sup w u0 z f ev gd (fun v y => mkWtree _ (sub v y))) _ gd).
  cbn; split; [apply kselfE; exact wa |].
  intros v y v' y' Hy; exact (proj1 (subext v y v' y' Hy)).
Defined.

(* the equality at a W code is the tree relation *)
Lemma mkW_eq u (x : kElC (mkCode mkW) u) u' (x' : kElC (mkCode mkW) u') :
  kWRel (mkWtree u x) (mkWtree u' x') -> Rel T u u' ->
  kcel (mkCode mkW) u x (mkCode mkW) u' x'.
Proof. intros H HR; split; [exact H | split; [exact ety | exact HR]]. Qed.

Lemma mkW_eq_inv u (x : kElC (mkCode mkW) u) u' (x' : kElC (mkCode mkW) u') :
  kcel (mkCode mkW) u x (mkCode mkW) u' x' -> kWRel (mkWtree u x) (mkWtree u' x').
Proof. intros H; exact (proj1 H). Qed.

(* and the branches of a related pair of sups are related: this is what the
   recursor's step needs *)
Lemma kWRel_sup_inv w u0 z f ev gd sb w' u0' z' f' ev' gd' sb' :
  kWRel (wel_sup w u0 z f ev gd sb) (wel_sup w' u0' z' f' ev' gd' sb') ->
  kcEl a u0 z a u0' z' /\
  (forall v y v' y', kcEl (b u0 z) v y (b u0' z') v' y' -> kWRel (sb v y) (sb' v' y')).
Proof. intros [Hl Hs]; split; [exact Hl | exact Hs]. Qed.
End W.
