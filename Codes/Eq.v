From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def.
From Stdlib Require Import Arith Lia.

(* The canonical equalities of the code hierarchy: HETEROGENEOUS in the code,
   and defined for codes of two arbitrary stages.

   Two codes of different shape are unrelated, and their relation is `False`
   ON THE NOSE, which is what lets Codes/Str.v build the coercion out of the
   Prop-valued equality: a shape mismatch is eliminated rather than decided.

   Every clause carries `tyeq T T'` beside the layer-1 relation of the
   realisers.  It is what makes the equality SYMMETRIC with no hypothesis on
   the two codes -- a heterogeneous equality relates realisers of two
   different shadows, and `Rel T u u'` alone cannot be turned round.

   The Pi clause is where the redesign shows: it says "related arguments give
   related values", with no transport, because the equality it recurses into
   is itself heterogeneous.  v1 had to add a fourth conjunct relating the two
   codes' carried transports. *)

Record Cmp (st st' : Stage) := {
  cU : St st -> St st' -> Prop;
  cEl : forall (s : St st) u, StEl st s u ->
        forall (s' : St st') u', StEl st' s' u' -> Prop
}.
Arguments cU {st st'}. Arguments cEl {st st'}.

(* ------------------------------------------------------------------ *)
(* One step: the codes over two compared stages.                       *)
(* ------------------------------------------------------------------ *)

Section Step.
Context {st st' : Stage} (c : Cmp st st').
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).

Definition eqU {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T') : Prop :=
  match r, r' with
  | r_nat T _, r_nat T' _ => tyeq T T'
  | r_prop T _, r_prop T' _ => tyeq T T'
  | r_prf T _ _ H, r_prf T' _ _ H' => tyeq T T' /\ (H <-> H')
  | r_univ T m _ _, r_univ T' m' _ _ => tyeq T T' /\ m = m'
  | r_pi T _ _ _ a _ _ b _ _, r_pi T' _ _ _ a' _ _ b' _ _ =>
      tyeq T T' /\ cU c a a' /\
      (forall u x u' x', cEl c a u x a' u' x' -> cU c (b u x) (b' u' x'))
  | r_sig T _ _ _ a _ b _, r_sig T' _ _ _ a' _ b' _ =>
      tyeq T T' /\ cU c a a' /\
      (forall u x u' x', cEl c a u x a' u' x' -> cU c (b u x) (b' u' x'))
  | r_w T _ _ _ a _ _ b _ _, r_w T' _ _ _ a' _ _ b' _ _ =>
      tyeq T T' /\ cU c a a' /\
      (forall u x u' x', cEl c a u x a' u' x' -> cU c (b u x) (b' u' x'))
  | _, _ => False
  end.

Definition eqEl {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T')
  : forall u, El (Univ := Univ) r u -> forall u', El (Univ := Univ) r' u' -> Prop :=
  match r as r0 in Refine _ _ T0, r' as r0' in Refine _ _ T0'
    return forall u, El (Univ := Univ) r0 u ->
           forall u', El (Univ := Univ) r0' u' -> Prop with
  | r_nat T _, r_nat T' _ => fun u x u' x' =>
      projT1 (Datatypes.fst x) = projT1 (Datatypes.fst x') /\ tyeq T T' /\ Rel T u u'
  | r_prop T _, r_prop T' _ => fun u x u' x' =>
      (Datatypes.fst x <-> Datatypes.fst x') /\ tyeq T T' /\ Rel T u u'
  | r_prf T _ _ _, r_prf T' _ _ _ => fun u x u' x' => tyeq T T' /\ Rel T u u'
  | r_univ T m _ _, r_univ T' m' _ _ => fun u x u' x' =>
      UnivEq m u x m' u' x' /\ tyeq T T'
  (* the two functions agree, up to nothing, on related arguments *)
  | r_pi T _ _ _ a _ _ b _ _, r_pi T' _ _ _ a' _ _ b' _ _ => fun u f u' f' =>
      (forall u1 x1 u1' x1', cEl c a u1 x1 a' u1' x1' ->
         cEl c (b u1 x1) (eapp u u1) (proj1_sig (Datatypes.fst f) u1 x1)
               (b' u1' x1') (eapp u' u1') (proj1_sig (Datatypes.fst f') u1' x1'))
      /\ tyeq T T' /\ Rel T u u'
  (* componentwise.  ONE direction suffices, unlike v1, where the transports
     made the two directions inequivalent. *)
  | r_sig T _ _ _ a _ b _, r_sig T' _ _ _ a' _ b' _ => fun u p u' p' =>
      cEl c a (efst u) (projT1 (Datatypes.fst p)) a' (efst u') (projT1 (Datatypes.fst p'))
      /\ cEl c (b (efst u) (projT1 (Datatypes.fst p))) (esnd u) (projT2 (Datatypes.fst p))
               (b' (efst u') (projT1 (Datatypes.fst p'))) (esnd u') (projT2 (Datatypes.fst p'))
      /\ tyeq T T' /\ Rel T u u'
  | r_w T _ _ _ a _ _ b _ _, r_w T' _ _ _ a' _ _ b' _ _ => fun u t u' t' =>
      WRel T T' a a' b b'
        (fun u0 x u0' x' => cEl c a u0 x a' u0' x')
        (fun u0 x u0' x' v y v' y' => cEl c (b u0 x) v y (b' u0' x') v' y')
        (proj1_sig (Datatypes.fst t)) (proj1_sig (Datatypes.fst t'))
      /\ tyeq T T' /\ Rel T u u'
  | _, _ => fun _ _ _ _ => False
  end.

Definition Cmp_next : Cmp (Stage_next st Univ UnivOK) (Stage_next st' Univ UnivOK).
Proof.
  unshelve refine (Build_Cmp _ _ _ _); cbn.
  - exact (fun c1 c2 => eqU (projT2 c1) (projT2 c2)).
  - exact (fun c1 u x c2 u' x' => eqEl (projT2 c1) (projT2 c2) u x u' x').
Defined.
End Step.

Arguments eqU {st st'} c {UnivOK T T'}.
Arguments eqEl {st st'} c {Univ} UnivEq {UnivOK T T'}.

(* ------------------------------------------------------------------ *)
(* The plumbing of the hierarchy, as for v1's HJ but with two fields.  *)
(* ------------------------------------------------------------------ *)

Definition Cmp_emptyL st' : Cmp Stage_empty st'.
Proof. unshelve refine (Build_Cmp _ _ _ _); cbn; intros []. Defined.

Definition Cmp_emptyR st : Cmp st Stage_empty.
Proof. unshelve refine (Build_Cmp _ _ _ _); cbn; intros s; try intros u x; intros []. Defined.

Definition Cmp_sumL {a b d} (ca : Cmp a d) (cb : Cmp b d) : Cmp (Stage_sum a b) d.
Proof.
  unshelve refine (Build_Cmp _ _ _ _); cbn.
  - intros [s|s]; [exact (cU ca s) | exact (cU cb s)].
  - intros [s|s]; [exact (cEl ca s) | exact (cEl cb s)].
Defined.

Definition Cmp_sumR {a b d} (cb : Cmp a b) (cd : Cmp a d) : Cmp a (Stage_sum b d).
Proof.
  unshelve refine (Build_Cmp _ _ _ _); cbn.
  - intros s [s'|s']; [exact (cU cb s s') | exact (cU cd s s')].
  - intros s u x [s'|s']; [exact (cEl cb s u x s') | exact (cEl cd s u x s')].
Defined.

Definition Cmp_supL {T F d} (H : forall p, Cmp (F p) d) : Cmp (Stage_sup T F) d.
Proof.
  unshelve refine (Build_Cmp _ _ _ _); cbn.
  - intros [p s]; exact (cU (H p) s).
  - intros [p s]; exact (cEl (H p) s).
Defined.

Definition Cmp_supR {a T' F'} (H : forall p', Cmp a (F' p')) : Cmp a (Stage_sup T' F').
Proof.
  unshelve refine (Build_Cmp _ _ _ _); cbn.
  - intros s [p' s']; exact (cU (H p') s s').
  - intros s u x [p' s']; exact (cEl (H p') s u x s').
Defined.

Definition Cmp_restrL {a b d} (H : Cmp (Stage_sum a b) d) : Cmp a d := {|
  cU s s' := cU H (inl s) s';
  cEl s u x s' u' x' := cEl H (inl s) u x s' u' x'
|}.

Definition Cmp_restrR {a b d} (H : Cmp a (Stage_sum b d)) : Cmp a b := {|
  cU s s' := cU H s (inl s');
  cEl s u x s' u' x' := cEl H s u x (inl s') u' x'
|}.

Definition Cmp_supL_at {T F d} (p : Pred T) (H : Cmp (Stage_sup T F) d) : Cmp (F p) d := {|
  cU s s' := cU H (existT _ p s) s';
  cEl s u x s' u' x' := cEl H (existT _ p s) u x s' u' x'
|}.

Definition Cmp_supR_at {a T' F'} (p' : Pred T') (H : Cmp a (Stage_sup T' F'))
  : Cmp a (F' p') := {|
  cU s s' := cU H s (existT _ p' s');
  cEl s u x s' u' x' := cEl H s u x (existT _ p' s') u' x'
|}.

(* ------------------------------------------------------------------ *)
(* The hierarchy of comparisons, by an outer recursion on the first     *)
(* stage and an inner one on the second, so that a stage is peeled on    *)
(* both sides at once.  At a pair of successors the four blocks are:     *)
(* node against node (one level up, Cmp_next), node against the stage    *)
(* below (the inner call, restricted), the stage below against a node    *)
(* (the outer call at a successor, restricted), and the two stages       *)
(* below (the outer call).                                              *)
(* ------------------------------------------------------------------ *)

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation U_ := (U Univ UnivOK).

Definition Cmp_nextS beta beta' (g : Cmp (stage_ beta) (stage_ beta'))
  : Cmp (Ust_ beta) (Ust_ beta') := Cmp_next g Univ UnivEq UnivOK.

Fixpoint xcmp (alpha : Ord) : forall alpha', Cmp (stage_ alpha) (stage_ alpha') :=
  match alpha as a return forall alpha', Cmp (stage_ a) (stage_ alpha') with
  | ozero => fun alpha' => Cmp_emptyL _
  | osucc beta =>
      fix inner (alpha' : Ord)
        : Cmp (Stage_sum (Ust_ beta) (stage_ beta)) (stage_ alpha') :=
        match alpha' as a'
          return Cmp (Stage_sum (Ust_ beta) (stage_ beta)) (stage_ a') with
        | ozero => Cmp_emptyR _
        | osucc beta' =>
            Cmp_sumL (Cmp_sumR (Cmp_nextS beta beta' (xcmp beta beta'))
                               (Cmp_restrL (inner beta')))
                     (Cmp_sumR (Cmp_restrR (xcmp beta (osucc beta')))
                               (xcmp beta beta'))
        | osup T' f' =>
            Cmp_supR (fun p' =>
              Cmp_sumL (Cmp_sumR (Cmp_nextS beta (f' p') (xcmp beta (f' p')))
                                 (Cmp_restrL (inner (f' p'))))
                       (Cmp_sumR (Cmp_restrR (Cmp_supR_at p' (xcmp beta (osup T' f'))))
                                 (xcmp beta (f' p'))))
        end
  | osup T f =>
      fix inner (alpha' : Ord)
        : Cmp (Stage_sup T (fun p => Stage_sum (Ust_ (f p)) (stage_ (f p))))
              (stage_ alpha') :=
        match alpha' as a'
          return Cmp (Stage_sup T (fun p => Stage_sum (Ust_ (f p)) (stage_ (f p))))
                     (stage_ a') with
        | ozero => Cmp_emptyR _
        | osucc beta' =>
            Cmp_supL (fun p =>
              Cmp_sumL (Cmp_sumR (Cmp_nextS (f p) beta' (xcmp (f p) beta'))
                                 (Cmp_restrL (Cmp_supL_at p (inner beta'))))
                       (Cmp_sumR (Cmp_restrR (xcmp (f p) (osucc beta')))
                                 (xcmp (f p) beta')))
        | osup T' f' =>
            Cmp_supL (fun p => Cmp_supR (fun p' =>
              Cmp_sumL (Cmp_sumR (Cmp_nextS (f p) (f' p') (xcmp (f p) (f' p')))
                                 (Cmp_restrL (Cmp_supL_at p (inner (f' p')))))
                       (Cmp_sumR (Cmp_restrR (Cmp_supR_at p' (xcmp (f p) (osup T' f'))))
                                 (xcmp (f p) (f' p')))))
        end
  end.

(* The working interface: the equality of two codes at arbitrary nodes of one
   level, and of their elements. *)
Definition xcmpU (beta beta' : Ord) : Cmp (Ust_ beta) (Ust_ beta') :=
  Cmp_nextS beta beta' (xcmp beta beta').

Definition ceq {beta beta'} (c : U_ beta) (c' : U_ beta') : Prop :=
  cU (xcmpU beta beta') c c'.

Definition cel {beta beta'} (c : U_ beta) u (x : StEl (Ust_ beta) c u)
                            (c' : U_ beta') u' (x' : StEl (Ust_ beta') c' u') : Prop :=
  cEl (xcmpU beta beta') c u x c' u' x'.

(* Both are the refinement-level relations outright: one projection and one
   match, so that nothing of the Brouwer tree is unfolded when they are used
   at a concrete pair of codes. *)
Lemma ceq_refine {beta beta'} (c : U_ beta) (c' : U_ beta') :
  ceq c c' = eqU (xcmp beta beta') (projT2 c) (projT2 c').
Proof. reflexivity. Qed.

Lemma cel_refine {beta beta'} (c : U_ beta) u x (c' : U_ beta') u' x' :
  cel c u x c' u' x' = eqEl (xcmp beta beta') UnivEq (projT2 c) (projT2 c') u x u' x'.
Proof. reflexivity. Qed.
End Level.
