From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Str Codes.Sound.
From Stdlib Require Import Arith Lia.

(* Every element of a well-formed code is related to itself.

   v1 had this for free: its `Stage_next` bundled self-relatedness into the
   decoding, so an element WAS a pair of a value and its self-relation.  v2's
   decoding carries, clause by clause, only what the code's own former needs --
   extensionality at Pi, the tree relation at W, nothing at Sigma -- so
   self-relatedness has to be assembled, and it needs well-formedness twice:
   to read the carried relations as the canonical ones, and to get `tyeq T T`
   out of the code's self-equality (a realiser's layer-1 type cannot be
   recovered from an element).

   It is what every use of `xto_eq` and of the Sigma rules wants, so it
   belongs here rather than in Interp/. *)

Section ReflRefine.
Context (st : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (dg : Cmp st st) (wfS : St st -> Prop).
Context (UErefl : forall m u x, UnivEq m u x m u x).
(* self-relatedness one stage down *)
Context (Sself : forall s, wfS s -> forall u x, cEl dg s u x s u x).

Lemma elRefl {T} (r : Refine st UnivOK T) (W : wfRefine dg wfS r) u
  (x : El (Univ := Univ) r u) : eqEl dg UnivEq r r u x u x.
Proof.
  revert W u x; dest_code r; intros W u x; cbn in x |- *.
  - split; [reflexivity | split; [exact (proj2 W) | exact (Datatypes.snd x)]].
  - split; [split; exact (fun h => h)
           | split; [exact (proj2 W) | exact (Datatypes.snd x)]].
  - split; [exact (proj1 (proj2 W)) | exact (Datatypes.snd x)].
  - split; [apply UErefl | exact (proj1 (proj2 W))].
  (* Pi: the extensionality the decoding carries IS self-relatedness, once
     well-formedness has exchanged the carried relations for the canonical *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct x as [[f fext] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    intros u1 x1 u1' x1' Hx; apply beqc; apply fext; apply aeqc; exact Hx.
  (* Sigma: componentwise, from the stage below *)
  - destruct W as [[wa [wb _]] [ety [eaa coh]]].
    destruct x as [[y z] gd]; cbn.
    split; [apply Sself; exact wa |].
    split; [apply Sself; apply wb | split; [exact ety | exact gd]].
  (* W: the tree relation the decoding carries, again with the carried
     relations exchanged for the canonical ones *)
  - destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    destruct x as [[t tself] gd]; cbn.
    split; [| split; [exact ety | exact gd]].
    apply (WRel_mono T T a a b b
             aeq (fun u1 x1 u1' x1' => cEl dg a u1 x1 a u1' x1')
             beq (fun u1 x1 u1' x1' v y v' y' => cEl dg (b u1 x1) v y (b u1' x1') v' y'));
      [ intros ? ? ? ? H; apply aeqc; exact H
      | intros ? ? ? ? ? ? ? ? H; apply beqc; exact H
      | exact tself ].
Qed.
End ReflRefine.

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop)
        (UErefl : forall m u x, UnivEq m u x m u x).

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Sub_ := (Sub Univ UnivOK).
Local Notation U_ := (U Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).
Local Notation wfsub_ := (wfsub Univ UnivEq UnivOK).
Local Notation wfc_ := (wfc Univ UnivEq UnivOK).

(* By recursion on the node: a node's elements are elements of a refinement
   over the stage below, which is where the recursive call goes. *)
Fixpoint subRefl (alpha : Ord)
  : forall (s : Sub_ alpha), wfsub_ alpha s ->
    forall u (x : StEl (stage_ alpha) s u), cEl (xcmp_ alpha alpha) s u x s u x :=
  match alpha as a return forall (s : Sub_ a), wfsub_ a s ->
      forall u (x : StEl (stage_ a) s u), cEl (xcmp_ a a) s u x s u x with
  | ozero => fun s => match s with end
  | osucc beta => fun s =>
      match s as s0 return wfsub_ (osucc beta) s0 ->
        forall u (x : StEl (stage_ (osucc beta)) s0 u),
          cEl (xcmp_ (osucc beta) (osucc beta)) s0 u x s0 u x with
      | inl c => fun W => elRefl (stage_ beta) Univ UnivEq UnivOK
                            (xcmp_ beta beta) (wfsub_ beta) UErefl (subRefl beta)
                            (projT2 c) W
      | inr s0 => subRefl beta s0
      end
  | osup T f => fun s =>
      match s as s0 return wfsub_ (osup T f) s0 ->
        forall u (x : StEl (stage_ (osup T f)) s0 u),
          cEl (xcmp_ (osup T f) (osup T f)) s0 u x s0 u x with
      | existT _ p s0 =>
          match s0 as s1 return wfsub_ (osup T f) (existT _ p s1) ->
            forall u (x : StEl (stage_ (osup T f)) (existT _ p s1) u),
              cEl (xcmp_ (osup T f) (osup T f)) (existT _ p s1) u x (existT _ p s1) u x with
          | inl c => fun W => elRefl (stage_ (f p)) Univ UnivEq UnivOK
                                (xcmp_ (f p) (f p)) (wfsub_ (f p)) UErefl
                                (subRefl (f p)) (projT2 c) W
          | inr s1 => subRefl (f p) s1
          end
      end
  end.

(* the working interface: an element of a well-formed code is self-related *)
Definition crefl {beta} (c : U_ beta) (W : wfc_ c) u (x : StEl (Ust_ beta) c u)
  : cel Univ UnivEq UnivOK c u x c u x :=
  elRefl (stage_ beta) Univ UnivEq UnivOK (xcmp_ beta beta) (wfsub_ beta) UErefl
    (subRefl beta) (projT2 c) W u x.
End Level.
