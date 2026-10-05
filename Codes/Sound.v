From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.Eq.
From Stdlib Require Import Arith Lia.

(* Lemma 8.4: every semantic element of a code is a layer-1 good realiser of
   the code's shadow, and related elements have layer-1 related realisers.

   No induction is needed for either.  `Good T u` is a conjunct of every clause
   of the decoding but the universe's, where the decoding is the parameter and
   the property is assumed of it; and `Rel T u u'` is a conjunct of every clause
   of the equality but the universe's, for the same reason.  With the neutral
   clause gone there is no vacuous case left to discharge. *)

Record UnivSound (Univ : nat -> etm -> Type)
                 (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
                 (UnivOK : nat -> Prop) := {
  us_ty : forall m u, Univ m u -> eqty m u u;
  us_eq : forall m u x m' u' x', UnivEq m u x m' u' x' -> eqty m u u';
  us_ok : forall m T, UnivOK m -> eval T (euniv m) -> Good_ty T
}.
Arguments us_ty {Univ UnivEq UnivOK}. Arguments us_eq {Univ UnivEq UnivOK}.
Arguments us_ok {Univ UnivEq UnivOK}.

Ltac dest_code r :=
  destruct r as [?T ?e | ?T ?e | ?T ?p ?e ?P0 | ?T ?m ?ok ?e
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq
                | ?T ?A1 ?B1 ?e ?a ?ea ?b ?eb
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq].

Section Sound.
Context (st st' : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (US : UnivSound Univ UnivEq UnivOK).

Lemma El_good {T} (r : Refine st UnivOK T) u : El (Univ := Univ) r u -> Good T u.
Proof.
  dest_code r; cbn; intros x.
  - exact (Datatypes.snd x).
  - exact (Datatypes.snd x).
  - exact (Datatypes.snd x).
  - eapply Rel_univ_intro;
      [ exact (us_ok US _ _ ok e) | exact e | exact (us_ty US _ _ x) ].
  - exact (Datatypes.snd x).
  - exact (Datatypes.snd x).
  - exact (Datatypes.snd x).
Qed.

Lemma eqEl_rel (c : Cmp st st') {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T')
  u x u' x' : eqEl c UnivEq r r' u x u' x' -> Rel T u u'.
Proof.
  revert x x'; dest_code r; dest_code r'; cbn; intros x x';
    try (exact (fun H => match H with end)).
  - intros H; exact (proj2 (proj2 H)).
  - intros H; exact (proj2 (proj2 H)).
  - intros H; exact (proj2 H).
  - intros [H1 H2]; eapply Rel_univ_intro;
      [ exact (us_ok US _ _ ok e) | exact e | exact (us_eq US _ _ _ _ _ _ H1) ].
  - intros H; exact (proj2 (proj2 H)).
  - intros H; exact (proj2 (proj2 (proj2 H))).
  - intros H; exact (proj2 (proj2 H)).
Qed.

(* The shadows of two related codes are layer-1 equal: it is the first
   conjunct of every clause of the code equality. *)
Lemma eqU_tyeq (c : Cmp st st') {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T') :
  eqU c r r' -> tyeq T T'.
Proof.
  dest_code r; dest_code r'; cbn; try (exact (fun H => match H with end));
    try (exact (fun H => H)); exact (fun H => proj1 H).
Qed.
End Sound.

Arguments El_good {st Univ UnivEq UnivOK} US {T} r u.
Arguments eqEl_rel {st st' Univ UnivEq UnivOK} US c {T T'} r r' u x u' x'.
Arguments eqU_tyeq {st st' UnivOK} c {T T'} r r'.

(* ------------------------------------------------------------------ *)
(* The same at a whole stage and at a node of the hierarchy.           *)
(* ------------------------------------------------------------------ *)

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (US : UnivSound Univ UnivEq UnivOK).

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).

(* One induction on the Brouwer tree: every node is a Stage_next, where the
   lemma above applies verbatim. *)
Lemma sub_good alpha : forall (s : Sub Univ UnivOK alpha) u,
  StEl (stage_ alpha) s u -> Good (StSh (stage_ alpha) s) u.
Proof.
  induction alpha as [| beta IHb | T f IHf]; cbn.
  - intros [].
  - intros [c | s] u; [intros x | apply IHb].
    exact (El_good US (projT2 c) u x).
  - intros [p [c | s]] u; [intros x | apply (IHf p)].
    exact (El_good US (projT2 c) u x).
Qed.

(* The layer-1 relation of two related realisers, at two arbitrary stages.
   Unlike `sub_good` this needs a PAIR induction: v2's equality compares a
   node's code with the codes below it, so the diagonal's blocks are
   comparisons at smaller PAIRS of ordinals, not at smaller ordinals. *)
Lemma sub_rel : forall alpha alpha' (s : Sub Univ UnivOK alpha) u x
  (s' : Sub Univ UnivOK alpha') u' x',
  cEl (xcmp_ alpha alpha') s u x s' u' x' -> Rel (StSh (stage_ alpha) s) u u'.
Proof.
  induction alpha as [| beta IHb | T f IHf]; intros alpha'.
  - intros [].
  - induction alpha' as [| beta' IHb' | T' f' IHf'].
    + intros s u x [].
    + intros [c | s0] u x [c' | s0'] u' x'.
      * exact (eqEl_rel US _ (projT2 c) (projT2 c') u x u' x').
      * exact (IHb' (inl c) u x s0' u' x').
      * exact (IHb (osucc beta') s0 u x (inl c') u' x').
      * exact (IHb beta' s0 u x s0' u' x').
    + intros [c | s0] u x [p' [c' | s0']] u' x'.
      * exact (eqEl_rel US _ (projT2 c) (projT2 c') u x u' x').
      * exact (IHf' p' (inl c) u x s0' u' x').
      * exact (IHb (osup T' f') s0 u x (existT _ p' (inl c')) u' x').
      * exact (IHb (f' p') s0 u x s0' u' x').
  - induction alpha' as [| beta' IHb' | T' f' IHf'].
    + intros s u x [].
    + intros [p [c | s0]] u x [c' | s0'] u' x'.
      * exact (eqEl_rel US _ (projT2 c) (projT2 c') u x u' x').
      * exact (IHb' (existT _ p (inl c)) u x s0' u' x').
      * exact (IHf p (osucc beta') s0 u x (inl c') u' x').
      * exact (IHf p beta' s0 u x s0' u' x').
    + intros [p [c | s0]] u x [p' [c' | s0']] u' x'.
      * exact (eqEl_rel US _ (projT2 c) (projT2 c') u x u' x').
      * exact (IHf' p' (existT _ p (inl c)) u x s0' u' x').
      * exact (IHf p (osup T' f') s0 u x (existT _ p' (inl c')) u' x').
      * exact (IHf p (f' p') s0 u x s0' u' x').
Qed.

Lemma U_good beta (c : U Univ UnivOK beta) u :
  StEl (Ust_ beta) c u -> Good (projT1 c) u.
Proof. exact (El_good US (projT2 c) u). Qed.

Lemma U_rel {beta beta'} (c : U Univ UnivOK beta) (c' : U Univ UnivOK beta') u x u' x' :
  cel Univ UnivEq UnivOK c u x c' u' x' -> Rel (projT1 c) u u'.
Proof. exact (eqEl_rel US (xcmp_ beta beta') (projT2 c) (projT2 c') u x u' x'). Qed.

Lemma U_tyeq {beta beta'} (c : U Univ UnivOK beta) (c' : U Univ UnivOK beta') :
  ceq Univ UnivEq UnivOK c c' -> tyeq (projT1 c) (projT1 c').
Proof. exact (eqU_tyeq (xcmp_ beta beta') (projT2 c) (projT2 c')). Qed.
End Level.
