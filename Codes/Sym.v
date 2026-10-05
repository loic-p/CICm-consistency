From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.Eq.
From Stdlib Require Import Arith Lia.

(* Symmetry of the two equalities, for codes of any two nodes.

   This is the one structural property that needs NOTHING else: not the
   coercion, not transitivity, not well-formedness.  The reason is that the
   equalities never mention the equalities a code carries -- they recurse into
   the canonical ones -- so symmetry is a pure induction, and the `tyeq T T'`
   conjunct of every clause is what lets the layer-1 relation of the realisers
   be turned round. *)

(* The tree relation is symmetric as soon as the label and branch relations
   are.  Induction on the first tree. *)
Lemma WRel_sym {st st' : Stage} (T T' : etm) (a : St st) (a' : St st')
  (b : forall u, StEl st a u -> St st) (b' : forall u, StEl st' a' u -> St st')
  (Rlab : forall u, StEl st a u -> forall u', StEl st' a' u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st' a' u') v, StEl st (b u x) v ->
         forall v', StEl st' (b' u' x') v' -> Prop)
  (Rlab' : forall u, StEl st' a' u -> forall u', StEl st a u' -> Prop)
  (Rbr' : forall u (x : StEl st' a' u) u' (x' : StEl st a u') v, StEl st' (b' u x) v ->
          forall v', StEl st (b u' x') v' -> Prop)
  (Hl : forall u x u' x', Rlab u x u' x' -> Rlab' u' x' u x)
  (Hb : forall u x u' x' v y v' y', Rbr' u' x' u x v' y' v y -> Rbr u x u' x' v y v' y')
  {w} (t : WEl T a b w) : forall {w'} (t' : WEl T' a' b' w'),
  WRel T T' a a' b b' Rlab Rbr t t' -> WRel T' T a' a b' b Rlab' Rbr' t' t.
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hlab Hsub]; split.
  - apply Hl, Hlab.
  - intros v1 y1 v2 y2 Hbr.
    apply (IH v2 y2 _ (sub' v1 y1)).
    apply Hsub, Hb, Hbr.
Qed.

(* ------------------------------------------------------------------ *)
(* One node against another.                                          *)
(* ------------------------------------------------------------------ *)

Section SymRefine.
Context (st st' : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (c : Cmp st st') (d : Cmp st' st).
Context (HU : forall s s', cU c s s' -> cU d s' s)
        (HU' : forall s' s, cU d s' s -> cU c s s')
        (HE : forall s u x s' u' x', cEl c s u x s' u' x' -> cEl d s' u' x' s u x)
        (HE' : forall s' u' x' s u x, cEl d s' u' x' s u x -> cEl c s u x s' u' x').
Context (UEsym : forall m u x m' u' x', UnivEq m u x m' u' x' -> UnivEq m' u' x' m u x).

Ltac dest_r r :=
  destruct r as [?T ?e | ?T ?e | ?T ?p ?e ?P0 | ?T ?m ?ok ?e
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq
                | ?T ?A1 ?B1 ?e ?a ?ea ?b ?eb
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq].

Lemma eqU_sym {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T') :
  eqU c r r' -> eqU d r' r.
Proof.
  dest_r r; dest_r r'; cbn; try (exact (fun H => match H with end)).
  (* nat *) 1: exact (fun H => tyeq_sym _ _ H).
  (* prop *) 1: exact (fun H => tyeq_sym _ _ H).
  (* prf *) 1: exact (fun H => conj (tyeq_sym _ _ (proj1 H)) (iff_sym (proj2 H))).
  (* univ *) 1: exact (fun H => conj (tyeq_sym _ _ (proj1 H)) (eq_sym (proj2 H))).
  (* pi, sig, w: the same three conjuncts *)
  all: intros [H1 [H2 H3]]; split; [apply tyeq_sym; exact H1 |];
       split; [apply HU; exact H2 |];
       intros u x u' x' He; apply HU, H3, HE'; exact He.
Qed.

Lemma eqEl_sym {T T'} (r : Refine st UnivOK T) (r' : Refine st' UnivOK T') u x u' x' :
  eqEl c UnivEq r r' u x u' x' -> eqEl d UnivEq r' r u' x' u x.
Proof.
  revert x x'; dest_r r; dest_r r'; cbn; intros x x';
    try (exact (fun H => match H with end)).
  (* nat *)
  - intros [H1 [H2 H3]]; split; [apply eq_sym; exact H1 |].
    split; [apply tyeq_sym; exact H2 |].
    apply Rel_sym, (Rel_tyeq _ _ _ _ H2); exact H3.
  (* prop *)
  - intros [H1 [H2 H3]]; split; [apply iff_sym; exact H1 |].
    split; [apply tyeq_sym; exact H2 |].
    apply Rel_sym, (Rel_tyeq _ _ _ _ H2); exact H3.
  (* prf *)
  - intros [H2 H3]; split; [apply tyeq_sym; exact H2 |].
    apply Rel_sym, (Rel_tyeq _ _ _ _ H2); exact H3.
  (* univ *)
  - intros [H1 H2]; split; [apply UEsym; exact H1 | apply tyeq_sym; exact H2].
  (* pi *)
  - intros [H1 [H2 H3]]; split.
    + intros u1 x1 u1' x1' He; apply HE, H1, HE'; exact He.
    + split; [apply tyeq_sym; exact H2 |].
      apply Rel_sym, (Rel_tyeq _ _ _ _ H2); exact H3.
  (* sig *)
  - intros [H1 [H2 [H3 H4]]]; split; [apply HE; exact H1 |].
    split; [apply HE; exact H2 |].
    split; [apply tyeq_sym; exact H3 |].
    apply Rel_sym, (Rel_tyeq _ _ _ _ H3); exact H4.
  (* w *)
  - intros [H1 [H2 H3]]; split.
    + eapply WRel_sym; [| | exact H1]; cbn.
      * intros u0 y0 u0' y0' He; apply HE; exact He.
      * intros u0 y0 u0' y0' v1 z1 v2 z2 He; apply HE'; exact He.
    + split; [apply tyeq_sym; exact H2 |].
      apply Rel_sym, (Rel_tyeq _ _ _ _ H2); exact H3.
Qed.
End SymRefine.

(* ------------------------------------------------------------------ *)
(* The whole hierarchy, by the same double recursion as Codes/Eq.v:    *)
(* outer on the first node, inner on the second, so that a stage is    *)
(* peeled on both sides at once.                                      *)
(* ------------------------------------------------------------------ *)

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop)
        (UEsym : forall m u x m' u' x', UnivEq m u x m' u' x' -> UnivEq m' u' x' m u x).

Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).

Definition SymP (alpha alpha' : Ord) : Prop :=
  (forall s s', cU (xcmp_ alpha alpha') s s' -> cU (xcmp_ alpha' alpha) s' s) /\
  (forall s u x s' u' x', cEl (xcmp_ alpha alpha') s u x s' u' x' ->
                          cEl (xcmp_ alpha' alpha) s' u' x' s u x).

(* one node against another, from the two directions at the stages below it *)
Lemma symU_node b1 b2 (H12 : SymP b1 b2) (H21 : SymP b2 b1) T T'
  (r : Refine (stage Univ UnivOK b1) UnivOK T)
  (r' : Refine (stage Univ UnivOK b2) UnivOK T') :
  eqU (xcmp_ b1 b2) r r' -> eqU (xcmp_ b2 b1) r' r.
Proof.
  apply (eqU_sym _ _ UnivOK (xcmp_ b1 b2) (xcmp_ b2 b1));
    [apply (proj1 H12) | apply (proj2 H21)].
Qed.

Lemma symEl_node b1 b2 (H12 : SymP b1 b2) (H21 : SymP b2 b1) T T'
  (r : Refine (stage Univ UnivOK b1) UnivOK T)
  (r' : Refine (stage Univ UnivOK b2) UnivOK T') u x u' x' :
  eqEl (xcmp_ b1 b2) UnivEq r r' u x u' x' -> eqEl (xcmp_ b2 b1) UnivEq r' r u' x' u x.
Proof.
  apply (eqEl_sym _ _ Univ UnivEq UnivOK (xcmp_ b1 b2) (xcmp_ b2 b1));
    [apply (proj2 H12) | apply (proj2 H21) | exact UEsym].
Qed.

Lemma sym_pair : forall alpha alpha', SymP alpha alpha' /\ SymP alpha' alpha.
Proof.
  induction alpha as [| beta IHb | T f IHf].
  - intros alpha'; split; split;
      [intros [] | intros [] | intros s [] | intros s u x []].
  - intros alpha'; induction alpha' as [| beta' IHb' | T' f' IHf'].
    + split; split; [intros s [] | intros s u x [] | intros [] | intros []].
    + pose proof (IHb beta') as Hbb'.
      pose proof (IHb (osucc beta')) as Hbs'.
      split; split.
      * intros [c|s0] [c'|s0'].
        -- exact (symU_node beta beta' (proj1 Hbb') (proj2 Hbb') _ _ (projT2 c) (projT2 c')).
        -- exact (proj1 (proj1 IHb') (inl c) s0').
        -- exact (proj1 (proj1 Hbs') s0 (inl c')).
        -- exact (proj1 (proj1 Hbb') s0 s0').
      * intros [c|s0] u x [c'|s0'] u' x'.
        -- exact (symEl_node beta beta' (proj1 Hbb') (proj2 Hbb') _ _
                    (projT2 c) (projT2 c') u x u' x').
        -- exact (proj2 (proj1 IHb') (inl c) u x s0' u' x').
        -- exact (proj2 (proj1 Hbs') s0 u x (inl c') u' x').
        -- exact (proj2 (proj1 Hbb') s0 u x s0' u' x').
      * intros [c'|s0'] [c|s0].
        -- exact (symU_node beta' beta (proj2 Hbb') (proj1 Hbb') _ _ (projT2 c') (projT2 c)).
        -- exact (proj1 (proj2 Hbs') (inl c') s0).
        -- exact (proj1 (proj2 IHb') s0' (inl c)).
        -- exact (proj1 (proj2 Hbb') s0' s0).
      * intros [c'|s0'] u' x' [c|s0] u x.
        -- exact (symEl_node beta' beta (proj2 Hbb') (proj1 Hbb') _ _
                    (projT2 c') (projT2 c) u' x' u x).
        -- exact (proj2 (proj2 Hbs') (inl c') u' x' s0 u x).
        -- exact (proj2 (proj2 IHb') s0' u' x' (inl c) u x).
        -- exact (proj2 (proj2 Hbb') s0' u' x' s0 u x).
    + split; split.
      * intros [c|s0] [p' [c'|s0']].
        -- exact (symU_node beta (f' p') (proj1 (IHb (f' p'))) (proj2 (IHb (f' p')))
                    _ _ (projT2 c) (projT2 c')).
        -- exact (proj1 (proj1 (IHf' p')) (inl c) s0').
        -- exact (proj1 (proj1 (IHb (osup T' f'))) s0 (existT _ p' (inl c'))).
        -- exact (proj1 (proj1 (IHb (f' p'))) s0 s0').
      * intros [c|s0] u x [p' [c'|s0']] u' x'.
        -- exact (symEl_node beta (f' p') (proj1 (IHb (f' p'))) (proj2 (IHb (f' p')))
                    _ _ (projT2 c) (projT2 c') u x u' x').
        -- exact (proj2 (proj1 (IHf' p')) (inl c) u x s0' u' x').
        -- exact (proj2 (proj1 (IHb (osup T' f'))) s0 u x (existT _ p' (inl c')) u' x').
        -- exact (proj2 (proj1 (IHb (f' p'))) s0 u x s0' u' x').
      * intros [p' [c'|s0']] [c|s0].
        -- exact (symU_node (f' p') beta (proj2 (IHb (f' p'))) (proj1 (IHb (f' p')))
                    _ _ (projT2 c') (projT2 c)).
        -- exact (proj1 (proj2 (IHb (osup T' f'))) (existT _ p' (inl c')) s0).
        -- exact (proj1 (proj2 (IHf' p')) s0' (inl c)).
        -- exact (proj1 (proj2 (IHb (f' p'))) s0' s0).
      * intros [p' [c'|s0']] u' x' [c|s0] u x.
        -- exact (symEl_node (f' p') beta (proj2 (IHb (f' p'))) (proj1 (IHb (f' p')))
                    _ _ (projT2 c') (projT2 c) u' x' u x).
        -- exact (proj2 (proj2 (IHb (osup T' f'))) (existT _ p' (inl c')) u' x' s0 u x).
        -- exact (proj2 (proj2 (IHf' p')) s0' u' x' (inl c) u x).
        -- exact (proj2 (proj2 (IHb (f' p'))) s0' u' x' s0 u x).
  - intros alpha'; induction alpha' as [| beta' IHb' | T' f' IHf'].
    + split; split; [intros s [] | intros s u x [] | intros [] | intros []].
    + split; split.
      * intros [p [c|s0]] [c'|s0'].
        -- exact (symU_node (f p) beta' (proj1 (IHf p beta')) (proj2 (IHf p beta'))
                    _ _ (projT2 c) (projT2 c')).
        -- exact (proj1 (proj1 IHb') (existT _ p (inl c)) s0').
        -- exact (proj1 (proj1 (IHf p (osucc beta'))) s0 (inl c')).
        -- exact (proj1 (proj1 (IHf p beta')) s0 s0').
      * intros [p [c|s0]] u x [c'|s0'] u' x'.
        -- exact (symEl_node (f p) beta' (proj1 (IHf p beta')) (proj2 (IHf p beta'))
                    _ _ (projT2 c) (projT2 c') u x u' x').
        -- exact (proj2 (proj1 IHb') (existT _ p (inl c)) u x s0' u' x').
        -- exact (proj2 (proj1 (IHf p (osucc beta'))) s0 u x (inl c') u' x').
        -- exact (proj2 (proj1 (IHf p beta')) s0 u x s0' u' x').
      * intros [c'|s0'] [p [c|s0]].
        -- exact (symU_node beta' (f p) (proj2 (IHf p beta')) (proj1 (IHf p beta'))
                    _ _ (projT2 c') (projT2 c)).
        -- exact (proj1 (proj2 (IHf p (osucc beta'))) (inl c') s0).
        -- exact (proj1 (proj2 IHb') s0' (existT _ p (inl c))).
        -- exact (proj1 (proj2 (IHf p beta')) s0' s0).
      * intros [c'|s0'] u' x' [p [c|s0]] u x.
        -- exact (symEl_node beta' (f p) (proj2 (IHf p beta')) (proj1 (IHf p beta'))
                    _ _ (projT2 c') (projT2 c) u' x' u x).
        -- exact (proj2 (proj2 (IHf p (osucc beta'))) (inl c') u' x' s0 u x).
        -- exact (proj2 (proj2 IHb') s0' u' x' (existT _ p (inl c)) u x).
        -- exact (proj2 (proj2 (IHf p beta')) s0' u' x' s0 u x).
    + split; split.
      * intros [p [c|s0]] [p' [c'|s0']].
        -- exact (symU_node (f p) (f' p') (proj1 (IHf p (f' p'))) (proj2 (IHf p (f' p')))
                    _ _ (projT2 c) (projT2 c')).
        -- exact (proj1 (proj1 (IHf' p')) (existT _ p (inl c)) s0').
        -- exact (proj1 (proj1 (IHf p (osup T' f'))) s0 (existT _ p' (inl c'))).
        -- exact (proj1 (proj1 (IHf p (f' p'))) s0 s0').
      * intros [p [c|s0]] u x [p' [c'|s0']] u' x'.
        -- exact (symEl_node (f p) (f' p') (proj1 (IHf p (f' p'))) (proj2 (IHf p (f' p')))
                    _ _ (projT2 c) (projT2 c') u x u' x').
        -- exact (proj2 (proj1 (IHf' p')) (existT _ p (inl c)) u x s0' u' x').
        -- exact (proj2 (proj1 (IHf p (osup T' f'))) s0 u x (existT _ p' (inl c')) u' x').
        -- exact (proj2 (proj1 (IHf p (f' p'))) s0 u x s0' u' x').
      * intros [p' [c'|s0']] [p [c|s0]].
        -- exact (symU_node (f' p') (f p) (proj2 (IHf p (f' p'))) (proj1 (IHf p (f' p')))
                    _ _ (projT2 c') (projT2 c)).
        -- exact (proj1 (proj2 (IHf p (osup T' f'))) (existT _ p' (inl c')) s0).
        -- exact (proj1 (proj2 (IHf' p')) s0' (existT _ p (inl c))).
        -- exact (proj1 (proj2 (IHf p (f' p')))  s0' s0).
      * intros [p' [c'|s0']] u' x' [p [c|s0]] u x.
        -- exact (symEl_node (f' p') (f p) (proj2 (IHf p (f' p'))) (proj1 (IHf p (f' p')))
                    _ _ (projT2 c') (projT2 c) u' x' u x).
        -- exact (proj2 (proj2 (IHf p (osup T' f'))) (existT _ p' (inl c')) u' x' s0 u x).
        -- exact (proj2 (proj2 (IHf' p')) s0' u' x' (existT _ p (inl c)) u x).
        -- exact (proj2 (proj2 (IHf p (f' p')))  s0' u' x' s0 u x).
Qed.

Definition xsymU {alpha alpha'} : forall s s',
    cU (xcmp_ alpha alpha') s s' -> cU (xcmp_ alpha' alpha) s' s :=
  proj1 (proj1 (sym_pair alpha alpha')).

Definition xsym {alpha alpha'} : forall s u x s' u' x',
    cEl (xcmp_ alpha alpha') s u x s' u' x' -> cEl (xcmp_ alpha' alpha) s' u' x' s u x :=
  proj2 (proj1 (sym_pair alpha alpha')).
End Level.
