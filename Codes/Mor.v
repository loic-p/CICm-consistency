From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound.
From Stdlib Require Import Arith Lia.

(* A MORPHISM OF THE CODE HIERARCHY, one node at a time.

   The level lift is an instance: a map between two universe parameters
   induces a map of every stage over the first into the stage over the second,
   preserving shadows and carrying the decoding both ways.  This file does one
   node -- the seven clauses of Refine -- taking as hypotheses everything the
   stage below supplies.  Codes/Lift.v does the recursion and the instance.

   Two things differ from v1 (see DESIGN.md sec. 12).

   1. The image of a binder code carries the TARGET stage's canonical
      relations, not the pull-back of the source's.  So the well-formedness of
      the image is `reflexivity`, and the extensionality condition on the
      image function is discharged by "pull the arguments back, apply the
      source's own extensionality, push the values forward" -- one chain, no
      round trip.  The round trips are needed only where a value's CODE moves:
      at Sigma's second component, at Pi's argument in the backwards map, and
      at W's branches.

   2. Everything is indexed by well-formedness proofs, because the backwards
      map at a Pi code exists only for a well-formed one.  v1 needed no wf
      hypothesis: its codes carried their own transports. *)

Record UMor (U1 U2 : nat -> etm -> Type)
            (E1 : forall m u, U1 m u -> forall m' u', U1 m' u' -> Prop)
            (E2 : forall m u, U2 m u -> forall m' u', U2 m' u' -> Prop)
            (OK1 OK2 : nat -> Prop) := {
  um_ok : forall m, OK1 m -> OK2 m;
  um_to : forall m u, OK1 m -> U1 m u -> U2 m u;
  um_from : forall m u, OK1 m -> U2 m u -> U1 m u;
  um_to_eq : forall m (o : OK1 m) u x m' (o' : OK1 m') u' x',
      E1 m u x m' u' x' -> E2 m u (um_to m u o x) m' u' (um_to m' u' o' x');
  um_from_eq : forall m (o : OK1 m) u y m' (o' : OK1 m') u' y',
      E2 m u y m' u' y' -> E1 m u (um_from m u o y) m' u' (um_from m' u' o' y');
  um_to_from : forall m (o : OK1 m) u y, E2 m u (um_to m u o (um_from m u o y)) m u y;
  um_from_to : forall m (o : OK1 m) u x, E1 m u (um_from m u o (um_to m u o x)) m u x
}.
Arguments um_ok {U1 U2 E1 E2 OK1 OK2}. Arguments um_to {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from {U1 U2 E1 E2 OK1 OK2}. Arguments um_to_eq {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from_eq {U1 U2 E1 E2 OK1 OK2}. Arguments um_to_from {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from_to {U1 U2 E1 E2 OK1 OK2}.

(* ------------------------------------------------------------------ *)
(* A morphism of one stage into another.                              *)
(*                                                                    *)
(* Both element maps are needed, and both are indexed by a            *)
(* well-formedness proof of the source code: the backwards map at a    *)
(* Pi code has to repair the argument's round trip along the code's    *)
(* coherence, which only a well-formed code has.  The round trips hold *)
(* up to the two stages' canonical equalities, and that is all the     *)
(* codes ever ask of their elements.                                   *)
(* ------------------------------------------------------------------ *)

Record SMor (st1 st2 : Stage) (d1 : Cmp st1 st1) (d2 : Cmp st2 st2)
            (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop) : Type := {
  sm_map : forall s, wf1 s -> St st2;
  sm_sh : forall s w, StSh st2 (sm_map s w) = StSh st1 s;
  sm_to : forall s (w : wf1 s) u, StEl st1 s u -> StEl st2 (sm_map s w) u;
  sm_from : forall s (w : wf1 s) u, StEl st2 (sm_map s w) u -> StEl st1 s u;
  sm_wf : forall s w, wf2 (sm_map s w);
  sm_rt1 : forall s w u x, cEl d1 s u (sm_from s w u (sm_to s w u x)) s u x;
  sm_rt2 : forall s w u y,
      cEl d2 (sm_map s w) u (sm_to s w u (sm_from s w u y)) (sm_map s w) u y
}.
Arguments sm_map {st1 st2 d1 d2 wf1 wf2}. Arguments sm_sh {st1 st2 d1 d2 wf1 wf2}.
Arguments sm_to {st1 st2 d1 d2 wf1 wf2}. Arguments sm_from {st1 st2 d1 d2 wf1 wf2}.
Arguments sm_wf {st1 st2 d1 d2 wf1 wf2}. Arguments sm_rt1 {st1 st2 d1 d2 wf1 wf2}.
Arguments sm_rt2 {st1 st2 d1 d2 wf1 wf2}.

(* The pair statement: two morphisms carry a comparison of their sources to a
   comparison of their targets, in both directions on elements.  At m' := m
   and the diagonal comparisons this is what the node construction needs from
   the stage below; at two different nodes it is what the interpretation needs
   of the lift.  There is no naturality square: v1 needed one because its Pi
   clause was stated through the carried transport. *)
Definition MPres {st1 st1' st2 st2' : Stage}
  {d1 : Cmp st1 st1} {d1' : Cmp st1' st1'} {d2 : Cmp st2 st2} {d2' : Cmp st2' st2'}
  {wf1 wf1' wf2 wf2'}
  (c1 : Cmp st1 st1') (c2 : Cmp st2 st2')
  (m : SMor st1 st2 d1 d2 wf1 wf2) (m' : SMor st1' st2' d1' d2' wf1' wf2') : Prop :=
  (forall s w s' w', cU c1 s s' -> cU c2 (sm_map m s w) (sm_map m' s' w'))
  /\ (forall s w s' w', cU c1 s s' -> forall u x u' x', cEl c1 s u x s' u' x' ->
        cEl c2 (sm_map m s w) u (sm_to m s w u x) (sm_map m' s' w') u' (sm_to m' s' w' u' x'))
  /\ (forall s w s' w', cU c1 s s' -> forall u y u' y',
        cEl c2 (sm_map m s w) u y (sm_map m' s' w') u' y' ->
        cEl c1 s u (sm_from m s w u y) s' u' (sm_from m' s' w' u' y')).

Definition mpU {st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m'}
  (H : @MPres st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m') := proj1 H.
Definition mpTo {st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m'}
  (H : @MPres st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m') :=
  proj1 (proj2 H).
Definition mpFrom {st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m'}
  (H : @MPres st1 st1' st2 st2' d1 d1' d2 d2' wf1 wf1' wf2 wf2' c1 c2 m m') :=
  proj2 (proj2 H).

(* ------------------------------------------------------------------ *)
(* The trees.                                                          *)
(*                                                                    *)
(* The image of a W code branches over the pulled-back family, so a    *)
(* branch of the image tree is indexed by an element of the image of   *)
(* `b u (sfrom (sto x))`: pulling it back lands one round trip away    *)
(* from `b u x`, and the code's coherence takes it the rest of the way. *)
(* ------------------------------------------------------------------ *)

Section WMor.
Context (st1 st2 : Stage) (d1 : Cmp st1 st1) (d2 : Cmp st2 st2)
        (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop)
        (m : SMor st1 st2 d1 d2 wf1 wf2).
Context (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u).
Context (T : etm) (a : St st1) (b : forall u, StEl st1 a u -> St st1)
        (wa : wf1 a) (wb : forall u x, wf1 (b u x))
        (coh : forall u x u' x', cEl d1 a u x a u' x' -> cU d1 (b u x) (b u' x')).

Definition wb2 (u1 : etm) (x1 : StEl st2 (sm_map m a wa) u1) : St st2 :=
  sm_map m (b u1 (sm_from m a wa u1 x1)) (wb _ _).

Definition wbrU (u0 : etm) (x : StEl st1 a u0)
  : cU d1 (b u0 (sm_from m a wa u0 (sm_to m a wa u0 x))) (b u0 x) :=
  coh u0 (sm_from m a wa u0 (sm_to m a wa u0 x)) u0 x (sm_rt1 m a wa u0 x).

Definition wpull (u0 : etm) (x : StEl st1 a u0) (v : etm)
  (y : StEl st2 (wb2 u0 (sm_to m a wa u0 x)) v) : StEl st1 (b u0 x) v :=
  sto1 _ (b u0 x) (wb _ _) (wb _ _) (wbrU u0 x) v
    (sm_from m (b u0 (sm_from m a wa u0 (sm_to m a wa u0 x))) (wb _ _) v y).

Fixpoint Wmapto {w} (t : WEl T a b w) : WEl T (sm_map m a wa) wb2 w :=
  match t with
  | wel_sup w u0 x f ev gd sub =>
      wel_sup w u0 (sm_to m a wa u0 x) f ev gd
        (fun v y => Wmapto (sub v (wpull u0 x v y)))
  end.

Fixpoint Wmapfrom {w} (t : WEl T (sm_map m a wa) wb2 w) : WEl T a b w :=
  match t with
  | wel_sup w u0 X f ev gd sub =>
      wel_sup w u0 (sm_from m a wa u0 X) f ev gd
        (fun v y => Wmapfrom (sub v (sm_to m (b u0 (sm_from m a wa u0 X)) (wb _ _) v y)))
  end.
End WMor.


(* The two tree maps preserve the relation.  Stated between two W codes of two
   different stage pairs, because that is the form the interpretation needs;
   the node construction uses the diagonal instance, where the mixed
   transitivities below are the stage's own. *)

Section WMorRel.
Context (st1 st1' st2 st2' : Stage)
        (d1 : Cmp st1 st1) (d1' : Cmp st1' st1')
        (d2 : Cmp st2 st2) (d2' : Cmp st2' st2')
        (c1 : Cmp st1 st1') (c2 : Cmp st2 st2')
        (wf1 : St st1 -> Prop) (wf1' : St st1' -> Prop)
        (wf2 : St st2 -> Prop) (wf2' : St st2' -> Prop)
        (m : SMor st1 st2 d1 d2 wf1 wf2) (m' : SMor st1' st2' d1' d2' wf1' wf2')
        (P : MPres c1 c2 m m').
Context (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u)
        (sto1Coh : forall s s' w w' (e : cU d1 s s') u x,
            cEl d1 s u x s' u (sto1 s s' w w' e u x))
        (sto1' : forall s s', wf1' s -> wf1' s' -> cU d1' s s' ->
            forall u, StEl st1' s u -> StEl st1' s' u)
        (sto1'Coh : forall s s' w w' (e : cU d1' s s') u x,
            cEl d1' s u x s' u (sto1' s s' w w' e u x)).
(* symmetry of the source stages' own equalities, and the two mixed
   transitivities: the comparison composes with the diagonal on either side *)
Context (ssym1 : forall s u x s' u' x', cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s u x)
        (ssym1' : forall s u x s' u' x', cEl d1' s u x s' u' x' -> cEl d1' s' u' x' s u x)
        (trL : forall s s' s'' u x u' x' u'' x'',
            wf1 s -> wf1 s' -> wf1' s'' -> cU d1 s s' ->
            cEl d1 s u x s' u' x' -> cEl c1 s' u' x' s'' u'' x'' ->
            cEl c1 s u x s'' u'' x'')
        (trR : forall s s' s'' u x u' x' u'' x'',
            wf1 s -> wf1' s' -> wf1' s'' -> cU c1 s s' ->
            cEl c1 s u x s' u' x' -> cEl d1' s' u' x' s'' u'' x'' ->
            cEl c1 s u x s'' u'' x'').

Context (T : etm) (a : St st1) (b : forall u, StEl st1 a u -> St st1)
        (wa : wf1 a) (wb : forall u x, wf1 (b u x))
        (coh : forall u x u' x', cEl d1 a u x a u' x' -> cU d1 (b u x) (b u' x'))
        (T' : etm) (a' : St st1') (b' : forall u, StEl st1' a' u -> St st1')
        (wa' : wf1' a') (wb' : forall u x, wf1' (b' u x))
        (coh' : forall u x u' x', cEl d1' a' u x a' u' x' -> cU d1' (b' u x) (b' u' x'))
        (eaa : cU d1 a a) (eaa' : cU d1' a' a') (eAX : cU c1 a a')
        (cohX : forall u x u' x', cEl c1 a u x a' u' x' -> cU c1 (b u x) (b' u' x')).

Local Notation wb2_ := (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb).
Local Notation wb2'_ := (wb2 st1' st2' d1' d2' wf1' wf2' m' a' b' wa' wb').
Local Notation Wto_ := (Wmapto st1 st2 d1 d2 wf1 wf2 m sto1 T a b wa wb coh).
Local Notation Wto'_ := (Wmapto st1' st2' d1' d2' wf1' wf2' m' sto1' T' a' b' wa' wb' coh').
Local Notation Wfrom_ := (Wmapfrom st1 st2 d1 d2 wf1 wf2 m T a b wa wb).
Local Notation Wfrom'_ := (Wmapfrom st1' st2' d1' d2' wf1' wf2' m' T' a' b' wa' wb').

Lemma Wmapto_rel {w} (t : WEl T a b w) :
  forall {w'} (t' : WEl T' a' b' w'),
  WRel T T' a a' b b'
    (fun u x u' x' => cEl c1 a u x a' u' x')
    (fun u x u' x' v y v' y' => cEl c1 (b u x) v y (b' u' x') v' y') t t' ->
  WRel T T' (sm_map m a wa) (sm_map m' a' wa') wb2_ wb2'_
    (fun u X u' X' => cEl c2 (sm_map m a wa) u X (sm_map m' a' wa') u' X')
    (fun u X u' X' v y v' y' => cEl c2 (wb2_ u X) v y (wb2'_ u' X') v' y')
    (Wto_ t) (Wto'_ t').
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hl Hs]; split; [exact (mpTo P a wa a' wa' eAX u0 x u0' x' Hl) |].
  intros v y v' y' Hy.
  apply (IH v _).
  apply Hs.
  (* the two labels, after their round trips, are still related across *)
  assert (HlF : cEl c1 a u0 (sm_from m a wa u0 (sm_to m a wa u0 x))
                  a' u0' (sm_from m' a' wa' u0' (sm_to m' a' wa' u0' x'))).
  { eapply trR; [exact wa | exact wa' | exact wa' | exact eAX | | apply ssym1', sm_rt1].
    eapply trL; [exact wa | exact wa | exact wa' | exact eaa | apply sm_rt1 | exact Hl]. }
  (* pull the two branch indices back, then move them along the two
     coherences of the codomain families *)
  assert (H0 : cEl c1 (b u0 (sm_from m a wa u0 (sm_to m a wa u0 x))) v
                 (sm_from m _ (wb _ _) v y)
                 (b' u0' (sm_from m' a' wa' u0' (sm_to m' a' wa' u0' x'))) v'
                 (sm_from m' _ (wb' _ _) v' y'))
    by exact (mpFrom P _ (wb _ _) _ (wb' _ _) (cohX _ _ _ _ HlF) v y v' y' Hy).
  eapply trL;
    [ apply wb | apply wb | apply wb'
    | apply (coh _ _ _ _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 x)))
    | apply ssym1; apply sto1Coh |].
  eapply trR;
    [ apply wb | apply wb' | apply wb'
    | exact (cohX _ _ _ _ HlF) | exact H0 | apply sto1'Coh ].
Qed.

Lemma Wmapfrom_rel {w} (t : WEl T (sm_map m a wa) wb2_ w) :
  forall {w'} (t' : WEl T' (sm_map m' a' wa') wb2'_ w'),
  WRel T T' (sm_map m a wa) (sm_map m' a' wa') wb2_ wb2'_
    (fun u X u' X' => cEl c2 (sm_map m a wa) u X (sm_map m' a' wa') u' X')
    (fun u X u' X' v y v' y' => cEl c2 (wb2_ u X) v y (wb2'_ u' X') v' y') t t' ->
  WRel T T' a a' b b'
    (fun u x u' x' => cEl c1 a u x a' u' x')
    (fun u x u' x' v y v' y' => cEl c1 (b u x) v y (b' u' x') v' y')
    (Wfrom_ t) (Wfrom'_ t').
Proof.
  induction t as [w u0 X f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' X' f' ev' gd' sub']; cbn.
  intros [Hl Hs]; split; [exact (mpFrom P a wa a' wa' eAX u0 X u0' X' Hl) |].
  intros v y v' y' Hy.
  apply (IH v _).
  apply Hs.
  exact (mpTo P _ (wb _ _) _ (wb' _ _)
           (cohX _ _ _ _ (mpFrom P a wa a' wa' eAX u0 X u0' X' Hl)) v y v' y' Hy).
Qed.
End WMorRel.

(* ------------------------------------------------------------------ *)
(* One node: the image code and the two element maps.                  *)
(* ------------------------------------------------------------------ *)

Section MorRefine.
Context (st1 st2 : Stage).
Context (U1 U2 : nat -> etm -> Type)
        (E1 : forall m u, U1 m u -> forall m' u', U1 m' u' -> Prop)
        (E2 : forall m u, U2 m u -> forall m' u', U2 m' u' -> Prop)
        (OK1 OK2 : nat -> Prop).
Context (um : UMor U1 U2 E1 E2 OK1 OK2).
Context (d1 : Cmp st1 st1) (d2 : Cmp st2 st2)
        (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop).
Context (m : SMor st1 st2 d1 d2 wf1 wf2) (P : MPres d1 d2 m m).
(* the structure of the source stage *)
Context (ssym1 : forall s u x s' u' x', cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s u x)
        (strE1 : forall s s' s'' u x u' x' u'' x'', wf1 s -> wf1 s' -> wf1 s'' ->
            cU d1 s s' -> cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s'' u'' x'' ->
            cEl d1 s u x s'' u'' x'')
        (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u)
        (sto1Coh : forall s s' w w' (e : cU d1 s s') u x,
            cEl d1 s u x s' u (sto1 s s' w w' e u x)).

Local Notation El1_ := (El (st := st1) (Univ := U1) (UnivOK := OK1)).
Local Notation El2_ := (El (st := st2) (Univ := U2) (UnivOK := OK2)).
Local Notation wb2_ := (wb2 st1 st2 d1 d2 wf1 wf2 m).
Local Notation Wto_ := (Wmapto st1 st2 d1 d2 wf1 wf2 m sto1).
Local Notation Wfrom_ := (Wmapfrom st1 st2 d1 d2 wf1 wf2 m).

Definition mapRefine {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r)
  : Refine st2 OK2 T.
Proof.
  revert W; dest_code r; intros W.
  - exact (r_nat T e).
  - exact (r_prop T e).
  - exact (r_prf T p e P0).
  - exact (r_univ T m0 (um_ok um m0 ok) e).
  (* Pi: the domain's image, the family pulled back along sm_from, and the
     TARGET's canonical relations -- which is what makes the image
     well-formed by reflexivity and its decoding easy to hit *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    refine (r_pi T A1 B1 e (sm_map m a wa) _
              (fun u1 x1 u1' x1' => cEl d2 (sm_map m a wa) u1 x1 (sm_map m a wa) u1' x1')
              (wb2_ a b wa wb) _
              (fun u1 x1 u1' x1' v y v' y' =>
                 cEl d2 (wb2_ a b wa wb u1 x1) v y (wb2_ a b wa wb u1' x1') v' y')).
    + rewrite sm_sh; exact ea.
    + intros u1 x1; unfold wb2; rewrite sm_sh; exact (eb _ _).
  - destruct W as [[wa [wb _]] [ety [eaa coh]]].
    refine (r_sig T A1 B1 e (sm_map m a wa) _ (wb2_ a b wa wb) _).
    + rewrite sm_sh; exact ea.
    + intros u1 x1; unfold wb2; rewrite sm_sh; exact (eb _ _).
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    refine (r_w T A1 B1 e (sm_map m a wa) _
              (fun u1 x1 u1' x1' => cEl d2 (sm_map m a wa) u1 x1 (sm_map m a wa) u1' x1')
              (wb2_ a b wa wb) _
              (fun u1 x1 u1' x1' v y v' y' =>
                 cEl d2 (wb2_ a b wa wb u1 x1) v y (wb2_ a b wa wb u1' x1') v' y')).
    + rewrite sm_sh; exact ea.
    + intros u1 x1; unfold wb2; rewrite sm_sh; exact (eb _ _).
Defined.

Definition elTo {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r)
  : forall u, El1_ r u -> El2_ (mapRefine r W) u.
Proof.
  revert W; dest_code r; intros W u x; cbn in x |- *.
  - exact x.
  - exact x.
  - exact x.
  - exact (um_to um m0 u ok x).
  (* Pi: pull the argument back, apply, push the value forward.  The image is
     extensional because each of the three steps preserves the equality. *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn.
    destruct x as [[f fext] gd].
    refine (exist _ (fun u1 x1 => sm_to m (b u1 (sm_from m a wa u1 x1)) (wb _ _)
                                    (eapp u u1) (f u1 (sm_from m a wa u1 x1))) _, gd).
    intros u1 x1 u1' x1' HX.
    apply (mpTo P _ (wb _ _) _ (wb _ _)
             (coh _ _ _ _ (mpFrom P a wa a wa eaa u1 x1 u1' x1' HX))).
    apply beqc; apply fext; apply aeqc.
    exact (mpFrom P a wa a wa eaa u1 x1 u1' x1' HX).
  (* Sigma: the first component's value moves, so its code moves with it, and
     the source stage's own coercion takes the second component across *)
  - destruct W as [[wa [wb _]] [ety [eaa coh]]]; cbn.
    destruct x as [[y z] gd].
    refine (existT _ (sm_to m a wa (efst u) y) _, gd).
    refine (sm_to m (b (efst u) (sm_from m a wa (efst u) (sm_to m a wa (efst u) y)))
              (wb _ _) (esnd u) _).
    exact (sto1 (b (efst u) y) _ (wb _ _) (wb _ _)
             (coh (efst u) y (efst u) _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa (efst u) y)))
             (esnd u) z).
  (* W: the tree map, and Wmapto_rel at the diagonal for the self-relatedness
     the image's decoding asks of the image tree.  The carried relations of
     the source are exchanged for the canonical ones by WRel_mono; on the way
     out no exchange is needed, because the image carries the canonical ones. *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn.
    destruct x as [[t tself] gd].
    assert (tcan : WRel T T a a b b
                     (fun u1 x1 u1' x1' => cEl d1 a u1 x1 a u1' x1')
                     (fun u1 x1 u1' x1' v y v' y' => cEl d1 (b u1 x1) v y (b u1' x1') v' y')
                     t t).
    { apply (WRel_mono T T a a b b
               aeq (fun u1 x1 u1' x1' => cEl d1 a u1 x1 a u1' x1')
               beq (fun u1 x1 u1' x1' v y v' y' => cEl d1 (b u1 x1) v y (b u1' x1') v' y'));
        [ intros ? ? ? ? H; apply aeqc; exact H
        | intros ? ? ? ? ? ? ? ? H; apply beqc; exact H
        | exact tself ]. }
    refine (exist _ (Wto_ T a b wa wb coh t) _, gd).
    exact (Wmapto_rel st1 st1 st2 st2 d1 d1 d2 d2 d1 d2 wf1 wf1 wf2 wf2 m m P
             sto1 sto1Coh sto1 sto1Coh ssym1 ssym1 strE1 strE1
             T a b wa wb coh T a b wa wb coh eaa eaa coh t t tcan).
Defined.

Definition elFrom {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r)
  : forall u, El2_ (mapRefine r W) u -> El1_ r u.
Proof.
  revert W; dest_code r; intros W u y; cbn in y |- *.
  - exact y.
  - exact y.
  - exact y.
  - exact (um_from um m0 u ok y).
  (* Pi: push the argument forward, apply, pull the value back -- and the
     value comes back at the round trip of the argument, so the code's
     coherence moves it to the code it is wanted at *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[G Gext] gd].
    refine (exist _ (fun u1 x1 =>
              sto1 (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))) (b u1 x1)
                (wb _ _) (wb _ _) (coh u1 _ u1 x1 (sm_rt1 m a wa u1 x1)) (eapp u u1)
                (sm_from m (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))) (wb _ _)
                   (eapp u u1) (G u1 (sm_to m a wa u1 x1)))) _, gd).
    intros u1 x1 u1' x1' Hx; apply beqc.
    assert (Hxc : cEl d1 a u1 x1 a u1' x1') by (apply aeqc; exact Hx).
    assert (H0 : cEl d1 (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))) (eapp u u1)
                   (sm_from m _ (wb _ _) (eapp u u1) (G u1 (sm_to m a wa u1 x1)))
                   (b u1' (sm_from m a wa u1' (sm_to m a wa u1' x1'))) (eapp u u1')
                   (sm_from m _ (wb _ _) (eapp u u1') (G u1' (sm_to m a wa u1' x1'))))
      by (apply (mpFrom P _ (wb _ _) _ (wb _ _)
                   (coh _ _ _ _
                      (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa u1 x1)
                         (strE1 a a a _ _ _ _ _ _ wa wa wa eaa Hxc
                            (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1' x1'))))));
          apply Gext; exact (mpTo P a wa a wa eaa u1 x1 u1' x1' Hxc)).
    eapply (strE1 (b u1 x1) (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))));
      [ apply wb | apply wb | apply wb
      | exact (coh u1 x1 u1 _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 x1)))
      | apply ssym1; apply sto1Coh |].
    eapply (strE1 _ (b u1' (sm_from m a wa u1' (sm_to m a wa u1' x1'))));
      [ apply wb | apply wb | apply wb
      | exact (coh u1 _ u1' _
                 (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa u1 x1)
                    (strE1 a a a _ _ _ _ _ _ wa wa wa eaa Hxc
                       (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1' x1')))))
      | exact H0 | apply sto1Coh ].
  (* Sigma: nothing has to be carried -- the image code at the pulled-back
     first component IS the image of the code at it *)
  - destruct W as [[wa [wb _]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[X Z] gd].
    exact (existT _ (sm_from m a wa (efst u) X)
             (sm_from m (b (efst u) (sm_from m a wa (efst u) X)) (wb _ _) (esnd u) Z), gd).
  (* W: the branches go the other way, so no coercion appears *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[t tself] gd].
    refine (exist _ (Wfrom_ T a b wa wb t) _, gd).
    apply (WRel_mono T T a a b b
             (fun u1 x1 u1' x1' => cEl d1 a u1 x1 a u1' x1') aeq
             (fun u1 x1 u1' x1' v z v' z' => cEl d1 (b u1 x1) v z (b u1' x1') v' z') beq);
      [ intros ? ? ? ? H; apply aeqc; exact H
      | intros ? ? ? ? ? ? ? ? H; apply beqc; exact H
      | exact (Wmapfrom_rel st1 st1 st2 st2 d1 d1 d2 d2 d1 d2 wf1 wf1 wf2 wf2 m m P
                 T a b wa wb T a b wa wb eaa coh t t tself) ].
Defined.
End MorRefine.

(* ------------------------------------------------------------------ *)
(* The round trips on trees.                                           *)
(* ------------------------------------------------------------------ *)

Section WMorRT.
Context (st1 st2 : Stage) (d1 : Cmp st1 st1) (d2 : Cmp st2 st2)
        (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop)
        (m : SMor st1 st2 d1 d2 wf1 wf2) (P : MPres d1 d2 m m).
Context (ssym1 : forall s u x s' u' x', cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s u x)
        (strE1 : forall s s' s'' u x u' x' u'' x'', wf1 s -> wf1 s' -> wf1 s'' ->
            cU d1 s s' -> cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s'' u'' x'' ->
            cEl d1 s u x s'' u'' x'')
        (ssym2 : forall s u x s' u' x', cEl d2 s u x s' u' x' -> cEl d2 s' u' x' s u x)
        (strE2 : forall s s' s'' u x u' x' u'' x'', wf2 s -> wf2 s' -> wf2 s'' ->
            cU d2 s s' -> cEl d2 s u x s' u' x' -> cEl d2 s' u' x' s'' u'' x'' ->
            cEl d2 s u x s'' u'' x'')
        (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u)
        (sto1Coh : forall s s' w w' (e : cU d1 s s') u x,
            cEl d1 s u x s' u (sto1 s s' w w' e u x)).
Context (T : etm) (a : St st1) (b : forall u, StEl st1 a u -> St st1)
        (wa : wf1 a) (wb : forall u x, wf1 (b u x)) (eaa : cU d1 a a)
        (coh : forall u x u' x', cEl d1 a u x a u' x' -> cU d1 (b u x) (b u' x')).

Local Notation wb2_ := (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb).
Local Notation Wto_ := (Wmapto st1 st2 d1 d2 wf1 wf2 m sto1 T a b wa wb coh).
Local Notation Wfrom_ := (Wmapfrom st1 st2 d1 d2 wf1 wf2 m T a b wa wb).
Local Notation Rl1 := (fun u x u' x' => cEl d1 a u x a u' x').
Local Notation Rb1 := (fun u x u' x' v y v' y' => cEl d1 (b u x) v y (b u' x') v' y').
Local Notation Rl2 := (fun u X u' X' => cEl d2 (sm_map m a wa) u X (sm_map m a wa) u' X').
Local Notation Rb2 := (fun u X u' X' v y v' y' => cEl d2 (wb2_ u X) v y (wb2_ u' X') v' y').

Lemma Wmap_rt1 {w} (t : WEl T a b w) :
  forall {w'} (t' : WEl T a b w'),
  WRel T T a a b b Rl1 Rb1 t t' -> WRel T T a a b b Rl1 Rb1 (Wfrom_ (Wto_ t)) t'.
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hl Hs]; split.
  - eapply (strE1 a a a); [exact wa | exact wa | exact wa | exact eaa
                          | apply sm_rt1 | exact Hl].
  - intros v z v' z' Hz.
    apply (IH v _).
    apply Hs.
    eapply (strE1 (b u0 x) (b u0 (sm_from m a wa u0 (sm_to m a wa u0 x))));
      [ apply wb | apply wb | apply wb
      | exact (coh u0 x u0 _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 x)))
      | apply ssym1; apply sto1Coh |].
    eapply (strE1 _ (b u0 (sm_from m a wa u0 (sm_to m a wa u0 x))));
      [ apply wb | apply wb | apply wb
      | exact (coh u0 _ u0 _
                 (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa u0 x)
                    (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 x))))
      | apply sm_rt1 | exact Hz ].
Qed.

Lemma Wmap_rt2 {w} (t : WEl T (sm_map m a wa) wb2_ w) :
  forall {w'} (t' : WEl T (sm_map m a wa) wb2_ w'),
  WRel T T (sm_map m a wa) (sm_map m a wa) wb2_ wb2_ Rl2 Rb2 t t' ->
  WRel T T (sm_map m a wa) (sm_map m a wa) wb2_ wb2_ Rl2 Rb2 (Wto_ (Wfrom_ t)) t'.
Proof.
  induction t as [w u0 X f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' X' f' ev' gd' sub']; cbn.
  intros [Hl Hs]; split.
  - eapply (strE2 (sm_map m a wa) (sm_map m a wa) (sm_map m a wa));
      [ apply sm_wf | apply sm_wf | apply sm_wf | exact (mpU P a wa a wa eaa)
      | apply sm_rt2 | exact Hl ].
  - intros v y v' y' Hy.
    apply (IH v _).
    apply Hs.
    (* the branch index, pulled back and pushed forward again *)
    eapply (strE2 (wb2_ u0 X) (wb2_ u0 (sm_to m a wa u0 (sm_from m a wa u0 X))));
      [ apply sm_wf | apply sm_wf | apply sm_wf
      | apply (mpU P _ (wb _ _) _ (wb _ _));
        exact (coh u0 _ u0 _
                 (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 (sm_from m a wa u0 X))))
      | apply (mpTo P _ (wb _ _) _ (wb _ _)
                 (coh u0 _ u0 _
                    (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 (sm_from m a wa u0 X)))));
        apply ssym1; apply sto1Coh |].
    eapply (strE2 (wb2_ u0 (sm_to m a wa u0 (sm_from m a wa u0 X)))
                  (wb2_ u0 (sm_to m a wa u0 (sm_from m a wa u0 X))));
      [ apply sm_wf | apply sm_wf | apply sm_wf
      | apply (mpU P _ (wb _ _) _ (wb _ _)); apply coh;
        exact (strE1 a a a _ _ _ _ _ _ wa wa wa eaa
                 (sm_rt1 m a wa u0 (sm_from m a wa u0 X))
                 (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u0 (sm_from m a wa u0 X))))
      | apply sm_rt2 | exact Hy ].
Qed.
End WMorRT.

(* ------------------------------------------------------------------ *)
(* One node, the Prop side: the image is well formed, and the two      *)
(* element maps are inverse up to the two nodes' own equalities.       *)
(* ------------------------------------------------------------------ *)

Section MorNode.
Context (st1 st2 : Stage).
Context (U1 U2 : nat -> etm -> Type)
        (E1 : forall m u, U1 m u -> forall m' u', U1 m' u' -> Prop)
        (E2 : forall m u, U2 m u -> forall m' u', U2 m' u' -> Prop)
        (OK1 OK2 : nat -> Prop).
Context (um : UMor U1 U2 E1 E2 OK1 OK2).
Context (d1 : Cmp st1 st1) (d2 : Cmp st2 st2)
        (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop).
Context (m : SMor st1 st2 d1 d2 wf1 wf2) (P : MPres d1 d2 m m).
Context (ssym1 : forall s u x s' u' x', cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s u x)
        (strE1 : forall s s' s'' u x u' x' u'' x'', wf1 s -> wf1 s' -> wf1 s'' ->
            cU d1 s s' -> cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s'' u'' x'' ->
            cEl d1 s u x s'' u'' x'')
        (ssym2 : forall s u x s' u' x', cEl d2 s u x s' u' x' -> cEl d2 s' u' x' s u x)
        (strE2 : forall s s' s'' u x u' x' u'' x'', wf2 s -> wf2 s' -> wf2 s'' ->
            cU d2 s s' -> cEl d2 s u x s' u' x' -> cEl d2 s' u' x' s'' u'' x'' ->
            cEl d2 s u x s'' u'' x'')
        (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u)
        (sto1Coh : forall s s' w w' (e : cU d1 s s') u x,
            cEl d1 s u x s' u (sto1 s s' w w' e u x)).

Local Notation mapR_ := (mapRefine st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m).
Local Notation elTo_ :=
  (elTo st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m P ssym1 strE1 sto1 sto1Coh).
Local Notation elFrom_ :=
  (elFrom st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m P ssym1 strE1 sto1 sto1Coh).

(* the image of a well-formed code is well formed: the carried relations of
   the image ARE the canonical ones of the target stage, so three of the four
   conjuncts are `reflexivity` *)
Lemma mapRefine_wf {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r) :
  wfRefine d2 wf2 (mapR_ r W).
Proof.
  revert W; dest_code r; intros W; cbn.
  - exact (conj I (proj2 W)).
  - exact (conj I (proj2 W)).
  - exact (conj I (proj2 W)).
  - exact (conj I (proj2 W)).
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn.
    split; [split; [apply sm_wf | split; [intros; apply sm_wf | split; intros; split;
             exact (fun h => h)]] |].
    split; [exact ety | split; [exact (mpU P a wa a wa eaa) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb _ _)).
    exact (coh _ _ _ _ (mpFrom P a wa a wa eaa u1 X1 u1' X1' HX)).
  - destruct W as [[wa [wb _]] [ety [eaa coh]]]; cbn.
    split; [split; [apply sm_wf | split; [intros; apply sm_wf | exact I]] |].
    split; [exact ety | split; [exact (mpU P a wa a wa eaa) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb _ _)).
    exact (coh _ _ _ _ (mpFrom P a wa a wa eaa u1 X1 u1' X1' HX)).
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn.
    split; [split; [apply sm_wf | split; [intros; apply sm_wf | split; intros; split;
             exact (fun h => h)]] |].
    split; [exact ety | split; [exact (mpU P a wa a wa eaa) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb _ _)).
    exact (coh _ _ _ _ (mpFrom P a wa a wa eaa u1 X1 u1' X1' HX)).
Qed.
(* The round trips.  At Pi the round-tripped function agrees with the
   original at every argument, because the argument's own round trip is an
   equality of the codomain codes; at Sigma the first component's round trip
   moves the second one's code, and the source stage's coercion is what it was
   moved by; at W it is the two tree lemmas. *)

Lemma elFrom_to {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r) u x :
  eqEl d1 E1 r r u (elFrom_ r W u (elTo_ r W u x)) u x.
Proof.
  revert W u x; dest_code r; intros W u x; cbn in x |- *.
  - split; [reflexivity | split; [exact (proj2 W) | exact (Datatypes.snd x)]].
  - split; [split; exact (fun h => h)
           | split; [exact (proj2 W) | exact (Datatypes.snd x)]].
  - split; [exact (proj1 (proj2 W)) | exact (Datatypes.snd x)].
  - split; [exact (um_from_to um m0 ok u x) | exact (proj1 (proj2 W))].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in x |- *.
    destruct x as [[f fext] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    intros u1 x1 u1' x1' Hx.
    eapply (strE1 (b u1 x1) (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))));
      [ apply wb | apply wb | apply wb
      | exact (coh u1 x1 u1 _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 x1)))
      | apply ssym1; apply sto1Coh |].
    eapply (strE1 _ (b u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))));
      [ apply wb | apply wb | apply wb
      | exact (coh u1 _ u1 _
                 (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa u1 x1)
                    (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 x1))))
      | apply sm_rt1 |].
    apply beqc; apply fext; apply aeqc.
    exact (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa u1 x1) Hx).
  - destruct W as [[wa [wb _]] [ety [eaa coh]]]; cbn in x |- *.
    destruct x as [[y z] gd]; cbn.
    split; [apply sm_rt1 | split; [| split; [exact ety | exact gd]]].
    eapply (strE1 (b (efst u) (sm_from m a wa (efst u) (sm_to m a wa (efst u) y)))
                  (b (efst u) (sm_from m a wa (efst u) (sm_to m a wa (efst u) y))));
      [ apply wb | apply wb | apply wb
      | exact (coh (efst u) _ (efst u) _
                 (strE1 a a a _ _ _ _ _ _ wa wa wa eaa (sm_rt1 m a wa (efst u) y)
                    (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa (efst u) y))))
      | apply sm_rt1
      | apply ssym1; apply sto1Coh ].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in x |- *.
    destruct x as [[t tself] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    eapply Wmap_rt1; try eassumption.
    apply (WRel_mono T T a a b b
             aeq (fun u1 x1 u1' x1' => cEl d1 a u1 x1 a u1' x1')
             beq (fun u1 x1 u1' x1' v y v' y' => cEl d1 (b u1 x1) v y (b u1' x1') v' y'));
      [ intros ? ? ? ? H; apply aeqc; exact H
      | intros ? ? ? ? ? ? ? ? H; apply beqc; exact H
      | exact tself ].
Qed.

Lemma elTo_from {T} (r : Refine st1 OK1 T) (W : wfRefine d1 wf1 r) u y :
  eqEl d2 E2 (mapR_ r W) (mapR_ r W) u (elTo_ r W u (elFrom_ r W u y)) u y.
Proof.
  revert W u y; dest_code r; intros W u y; cbn in y |- *.
  - split; [reflexivity | split; [exact (proj2 W) | exact (Datatypes.snd y)]].
  - split; [split; exact (fun h => h)
           | split; [exact (proj2 W) | exact (Datatypes.snd y)]].
  - split; [exact (proj1 (proj2 W)) | exact (Datatypes.snd y)].
  - split; [exact (um_to_from um m0 ok u y) | exact (proj1 (proj2 W))].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[G Gext] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    intros u1 X1 u1' X1' HX.
    (* the value comes back through two round trips: the argument's at level
       1, under sm_to, and the value's own at level 2 *)
    eapply (strE2 (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb u1 X1)
                  (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb u1
                     (sm_to m a wa u1 (sm_from m a wa u1 X1))));
      [ apply sm_wf | apply sm_wf | apply sm_wf
      | apply (mpU P _ (wb _ _) _ (wb _ _)); apply coh;
        exact (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 (sm_from m a wa u1 X1)))
      | apply (mpTo P _ (wb _ _) _ (wb _ _)
                 (coh u1 _ u1 _
                    (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 (sm_from m a wa u1 X1)))));
        apply ssym1; apply sto1Coh |].
    eapply (strE2 _ (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb u1
                       (sm_to m a wa u1 (sm_from m a wa u1 X1))));
      [ apply sm_wf | apply sm_wf | apply sm_wf
      | apply (mpU P _ (wb _ _) _ (wb _ _)); apply coh;
        exact (strE1 a a a _ _ _ _ _ _ wa wa wa eaa
                 (sm_rt1 m a wa u1 (sm_from m a wa u1 X1))
                 (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 (sm_from m a wa u1 X1))))
      | apply sm_rt2
      | apply Gext;
        exact (strE2 _ _ _ _ _ _ _ _ _ (sm_wf m a wa) (sm_wf m a wa) (sm_wf m a wa)
                 (mpU P a wa a wa eaa) (sm_rt2 m a wa u1 X1) HX) ].
  - destruct W as [[wa [wb _]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[X Z] gd]; cbn.
    split; [apply sm_rt2 | split; [| split; [exact ety | exact gd]]].
    eapply (strE2 (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb (efst u)
                     (sm_to m a wa (efst u) (sm_from m a wa (efst u) X)))
                  (wb2 st1 st2 d1 d2 wf1 wf2 m a b wa wb (efst u) X));
      [ apply sm_wf | apply sm_wf | apply sm_wf
      | apply (mpU P _ (wb _ _) _ (wb _ _)); apply coh; apply sm_rt1
      | apply (mpTo P _ (wb _ _) _ (wb _ _)
                 (coh _ _ _ _ (sm_rt1 m a wa (efst u) (sm_from m a wa (efst u) X))));
        apply ssym1; apply sto1Coh
      | apply sm_rt2 ].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]]; cbn in y |- *.
    destruct y as [[t tself] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    eapply Wmap_rt2; try eassumption; exact tself.
Qed.
End MorNode.

(* ------------------------------------------------------------------ *)
(* One node, the pair statement: two nodes of two stage pairs.          *)
(*                                                                    *)
(* This is what v1 needed LiftIso.v for, and it is shorter here by the *)
(* whole naturality square: the image code's carried relations are the  *)
(* target's canonical ones, so the Pi clause is: pull the arguments      *)
(* back across, use the source own equality, push the values forward    *)
(* across, and nothing is transported.                                  *)
(* ------------------------------------------------------------------ *)

Section MorPair.
Context (st1 st1' st2 st2' : Stage).
Context (U1 U2 : nat -> etm -> Type)
        (E1 : forall m u, U1 m u -> forall m' u', U1 m' u' -> Prop)
        (E2 : forall m u, U2 m u -> forall m' u', U2 m' u' -> Prop)
        (OK1 OK2 : nat -> Prop).
Context (um : UMor U1 U2 E1 E2 OK1 OK2).
Context (d1 : Cmp st1 st1) (d1' : Cmp st1' st1')
        (d2 : Cmp st2 st2) (d2' : Cmp st2' st2')
        (c1 : Cmp st1 st1') (c2 : Cmp st2 st2')
        (wf1 : St st1 -> Prop) (wf1' : St st1' -> Prop)
        (wf2 : St st2 -> Prop) (wf2' : St st2' -> Prop).
Context (m : SMor st1 st2 d1 d2 wf1 wf2) (m' : SMor st1' st2' d1' d2' wf1' wf2').
Context (P : MPres c1 c2 m m')
        (P0 : MPres d1 d2 m m) (P0' : MPres d1' d2' m' m').
Context (ssym1 : forall s u x s' u' x', cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s u x)
        (ssym1' : forall s u x s' u' x', cEl d1' s u x s' u' x' -> cEl d1' s' u' x' s u x)
        (strE1 : forall s s' s'' u x u' x' u'' x'', wf1 s -> wf1 s' -> wf1 s'' ->
            cU d1 s s' -> cEl d1 s u x s' u' x' -> cEl d1 s' u' x' s'' u'' x'' ->
            cEl d1 s u x s'' u'' x'')
        (strE1' : forall s s' s'' u x u' x' u'' x'', wf1' s -> wf1' s' -> wf1' s'' ->
            cU d1' s s' -> cEl d1' s u x s' u' x' -> cEl d1' s' u' x' s'' u'' x'' ->
            cEl d1' s u x s'' u'' x'')
        (trL : forall s s' s'' u x u' x' u'' x'',
            wf1 s -> wf1 s' -> wf1' s'' -> cU d1 s s' ->
            cEl d1 s u x s' u' x' -> cEl c1 s' u' x' s'' u'' x'' ->
            cEl c1 s u x s'' u'' x'')
        (trR : forall s s' s'' u x u' x' u'' x'',
            wf1 s -> wf1' s' -> wf1' s'' -> cU c1 s s' ->
            cEl c1 s u x s' u' x' -> cEl d1' s' u' x' s'' u'' x'' ->
            cEl c1 s u x s'' u'' x'')
        (trL2 : forall s s' s'' u x u' x' u'' x'',
            wf2 s -> wf2 s' -> wf2' s'' -> cU d2 s s' ->
            cEl d2 s u x s' u' x' -> cEl c2 s' u' x' s'' u'' x'' ->
            cEl c2 s u x s'' u'' x'')
        (trR2 : forall s s' s'' u x u' x' u'' x'',
            wf2 s -> wf2' s' -> wf2' s'' -> cU c2 s s' ->
            cEl c2 s u x s' u' x' -> cEl d2' s' u' x' s'' u'' x'' ->
            cEl c2 s u x s'' u'' x'')
        (sto1 : forall s s', wf1 s -> wf1 s' -> cU d1 s s' ->
            forall u, StEl st1 s u -> StEl st1 s' u)
        (sto1Coh : forall s s' w w' (e : cU d1 s s') u x,
            cEl d1 s u x s' u (sto1 s s' w w' e u x))
        (sto1' : forall s s', wf1' s -> wf1' s' -> cU d1' s s' ->
            forall u, StEl st1' s u -> StEl st1' s' u)
        (sto1'Coh : forall s s' w w' (e : cU d1' s s') u x,
            cEl d1' s u x s' u (sto1' s s' w w' e u x)).

Local Notation mapR_ := (mapRefine st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m).
Local Notation mapR'_ := (mapRefine st1' st2' U1 U2 E1 E2 OK1 OK2 um d1' d2' wf1' wf2' m').
Local Notation elTo_ :=
  (elTo st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m P0 ssym1 strE1 sto1 sto1Coh).
Local Notation elTo'_ :=
  (elTo st1' st2' U1 U2 E1 E2 OK1 OK2 um d1' d2' wf1' wf2' m' P0' ssym1' strE1' sto1' sto1'Coh).
Local Notation elFrom_ :=
  (elFrom st1 st2 U1 U2 E1 E2 OK1 OK2 um d1 d2 wf1 wf2 m P0 ssym1 strE1 sto1 sto1Coh).
Local Notation elFrom'_ :=
  (elFrom st1' st2' U1 U2 E1 E2 OK1 OK2 um d1' d2' wf1' wf2' m' P0' ssym1' strE1' sto1' sto1'Coh).

Lemma mapRefine_eqU {T T'} (r : Refine st1 OK1 T) (r' : Refine st1' OK1 T')
  (W : wfRefine d1 wf1 r) (W' : wfRefine d1' wf1' r') :
  eqU c1 r r' -> eqU c2 (mapR_ r W) (mapR'_ r' W').
Proof.
  revert W W'; dest_code r; dest_code r'; intros W W'; cbn;
    try (exact (fun h => match h with end)).
  - exact (fun h => h).
  - exact (fun h => h).
  - exact (fun h => h).
  - exact (fun h => h).
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]]; split; [exact ea1 | split; [exact (mpU P a wa _ wa' eA) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb' _ _)).
    exact (eB _ _ _ _ (mpFrom P a wa _ wa' eA u1 X1 u1' X1' HX)).
  - destruct W as [[wa [wb _]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' _]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]]; split; [exact ea1 | split; [exact (mpU P a wa _ wa' eA) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb' _ _)).
    exact (eB _ _ _ _ (mpFrom P a wa _ wa' eA u1 X1 u1' X1' HX)).
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]]; split; [exact ea1 | split; [exact (mpU P a wa _ wa' eA) |]].
    intros u1 X1 u1' X1' HX.
    apply (mpU P _ (wb _ _) _ (wb' _ _)).
    exact (eB _ _ _ _ (mpFrom P a wa _ wa' eA u1 X1 u1' X1' HX)).
Qed.

Lemma elTo_eqEl {T T'} (r : Refine st1 OK1 T) (r' : Refine st1' OK1 T')
  (W : wfRefine d1 wf1 r) (W' : wfRefine d1' wf1' r') :
  eqU c1 r r' -> forall u x u' x',
  eqEl c1 E1 r r' u x u' x' ->
  eqEl c2 E2 (mapR_ r W) (mapR'_ r' W') u (elTo_ r W u x) u' (elTo'_ r' W' u' x').
Proof.
  revert W W'; dest_code r; dest_code r'; intros W W'; cbn;
    try (exact (fun h => match h with end)).
  - intros _ u x u' x' H; exact H.
  - intros _ u x u' x' H; exact H.
  - intros _ u x u' x' H; exact H.
  - intros _ u x u' x' [Hx ety]; split; [apply um_to_eq; exact Hx | exact ety].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[f fext] gd] u' [[f' fext'] gd'] [Hf [ety2 Hrel]].
    split; [| split; [exact ety2 | exact Hrel]].
    intros u1 X1 u1' X1' HX.
    apply (mpTo P _ (wb _ _) _ (wb' _ _)
             (eB _ _ _ _ (mpFrom P a wa _ wa' eA u1 X1 u1' X1' HX))).
    exact (Hf _ _ _ _ (mpFrom P a wa _ wa' eA u1 X1 u1' X1' HX)).
  - destruct W as [[wa [wb _]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' _]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[y z] gd] u' [[y' z'] gd'] [H1 [H2 [ety2 Hrel]]].
    split; [exact (mpTo P a wa _ wa' eA _ y _ y' H1) |].
    split; [| split; [exact ety2 | exact Hrel]].
    apply (mpTo P _ (wb _ _) _ (wb' _ _)
             (eB _ _ _ _
                (trL a a _ _ _ _ _ _ _ wa wa wa' eaa
                   (sm_rt1 m a wa (efst u) y)
                   (trR a _ _ _ _ _ _ _ _ wa wa' wa' eA H1
                      (ssym1' _ _ _ _ _ _ (sm_rt1 m' _ wa' (efst u') y')))))).
    eapply trL;
      [ apply wb | apply wb | apply wb'
      | exact (coh _ _ _ _ (sm_rt1 m a wa (efst u) y))
      | apply ssym1; apply sto1Coh |].
    eapply trR;
      [ apply wb | apply wb' | apply wb'
      | exact (eB _ _ _ _ H1) | exact H2 | apply sto1'Coh ].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[t tself] gd] u' [[t' tself'] gd'] [Ht [ety2 Hrel]].
    split; [| split; [exact ety2 | exact Hrel]].
    eapply Wmapto_rel; try eassumption.
Qed.

Lemma elFrom_eqEl {T T'} (r : Refine st1 OK1 T) (r' : Refine st1' OK1 T')
  (W : wfRefine d1 wf1 r) (W' : wfRefine d1' wf1' r') :
  eqU c1 r r' -> forall u y u' y',
  eqEl c2 E2 (mapR_ r W) (mapR'_ r' W') u y u' y' ->
  eqEl c1 E1 r r' u (elFrom_ r W u y) u' (elFrom'_ r' W' u' y').
Proof.
  revert W W'; dest_code r; dest_code r'; intros W W'; cbn;
    try (exact (fun h => match h with end)).
  - intros _ u y u' y' H; exact H.
  - intros _ u y u' y' H; exact H.
  - intros _ u y u' y' H; exact H.
  - intros _ u y u' y' [Hy ety]; split; [apply um_from_eq; exact Hy | exact ety].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[G Gext] gd] u' [[G' Gext'] gd'] [HG [ety2 Hrel]].
    split; [| split; [exact ety2 | exact Hrel]].
    intros u1 x1 u1' x1' Hx.
    (* the two values come back at the round trips of the two arguments *)
    assert (HX : cEl c1 a u1 (sm_from m a wa u1 (sm_to m a wa u1 x1))
                   _ u1' (sm_from m' _ wa' u1' (sm_to m' _ wa' u1' x1'))).
    { eapply trR; [exact wa | exact wa' | exact wa' | exact eA
                  | | apply ssym1', sm_rt1].
      eapply trL; [exact wa | exact wa | exact wa' | exact eaa | apply sm_rt1 | exact Hx]. }
    eapply trL;
      [ apply wb | apply wb | apply wb'
      | exact (coh u1 x1 u1 _ (ssym1 _ _ _ _ _ _ (sm_rt1 m a wa u1 x1)))
      | apply ssym1; apply sto1Coh |].
    eapply trR;
      [ apply wb | apply wb' | apply wb'
      | exact (eB _ _ _ _ HX)
      | apply (mpFrom P _ (wb _ _) _ (wb' _ _) (eB _ _ _ _ HX));
        apply HG; exact (mpTo P a wa _ wa' eA u1 x1 u1' x1' Hx)
      | apply sto1'Coh ].
  - destruct W as [[wa [wb _]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' _]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[X Z] gd] u' [[X' Z'] gd'] [H1 [H2 [ety2 Hrel]]].
    split; [exact (mpFrom P a wa _ wa' eA _ X _ X' H1) |].
    split; [exact (mpFrom P _ (wb _ _) _ (wb' _ _)
                     (eB _ _ _ _ (mpFrom P a wa _ wa' eA _ X _ X' H1)) _ Z _ Z' H2)
           | split; [exact ety2 | exact Hrel]].
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct W' as [[wa' [wb' [aeqc' beqc']]] [ety' [eaa' coh']]]; cbn.
    intros [ea1 [eA eB]] u [[t tself] gd] u' [[t' tself'] gd'] [Ht [ety2 Hrel]].
    split; [| split; [exact ety2 | exact Hrel]].
    eapply Wmapfrom_rel; try eassumption.
Qed.
End MorPair.
