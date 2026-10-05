From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.Eq.
From Stdlib Require Import Arith Lia.

(* Well-formed codes: the equalities a binder code carries about its
   components are the canonical ones of Codes/Eq.v.

   This is what the carried equalities cost, and it is the whole cost: the
   codes the interpretation builds carry the canonical equalities by
   construction, so well-formedness is free there, and for well-formed codes
   the decoding is exactly what it should be -- at Pi the functions that are
   extensional for the canonical equality, at W the trees whose branching is.

   A well-formed binder code is also COHERENT: its codomain family takes
   related arguments to equal codes.  That conjunct is not about the carried
   relations at all -- it is what v1 carried as the transport `coh` inside the
   code -- and it is what the coherence of the coercion needs at a Pi code, to
   compose the extensionality of a function with the coercion of its values.

   Nothing else needs it.  In particular the equalities themselves never
   mention the carried relations (they recurse into the canonical ones), so
   symmetry and transitivity of the equality are independent of this file;
   only the COERCION is not, because a coerced element has to satisfy the
   target code's carried condition. *)

Section WFRefine.
Context (st : Stage) (UnivOK : nat -> Prop).
Context (dg : Cmp st st) (wfS : St st -> Prop).

Definition wfCarried {T} (r : Refine st UnivOK T) : Prop :=
  match r with
  | r_pi _ _ _ _ a _ aeq b _ beq =>
      wfS a /\ (forall u x, wfS (b u x)) /\
      (forall u x u' x', aeq u x u' x' <-> cEl dg a u x a u' x') /\
      (forall u x u' x' v y v' y',
         beq u x u' x' v y v' y' <-> cEl dg (b u x) v y (b u' x') v' y')
  | r_w _ _ _ _ a _ aeq b _ beq =>
      wfS a /\ (forall u x, wfS (b u x)) /\
      (forall u x u' x', aeq u x u' x' <-> cEl dg a u x a u' x') /\
      (forall u x u' x' v y v' y',
         beq u x u' x' v y v' y' <-> cEl dg (b u x) v y (b u' x') v' y')
  (* the trailing True keeps the three binder clauses the same shape, so that
     a proof that only needs the components' well-formedness can destruct any
     of them uniformly *)
  | r_sig _ _ _ _ a _ b _ => wfS a /\ (forall u x, wfS (b u x)) /\ True
  | _ => True
  end.

(* A well-formed code is also SELF-EQUAL.  That is not a property of the
   carried relations: it says the shadow is a layer-1 type and the codomain
   family takes related arguments to equal codes -- the second being exactly
   what v1 carried as the transport `coh` inside the code, and the first not
   being derivable from a code at all (the layer-1 codomain equality is needed
   at every related pair of realisers, while the semantic one only covers the
   realisers that carry semantic elements).  v1 carries it too, as `UFam`'s
   field `uf_coh : LIso c c`.

   It is what the coherence of the coercion needs at a Pi code, to compose the
   extensionality of a function with the coercion of its values. *)
Definition wfRefine {T} (r : Refine st UnivOK T) : Prop :=
  wfCarried r /\ eqU dg r r.

Definition WF_next : U_of UnivOK -> Prop := fun c => wfRefine (projT2 c).
End WFRefine.

Arguments wfCarried {st UnivOK} dg wfS {T}.
Arguments wfRefine {st UnivOK} dg wfS {T}.
Arguments WF_next {st} UnivOK dg wfS.

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).

(* Well-formedness of every code below alpha, by recursion on the node.  The
   diagonal comparison xcmp beta beta is the canonical equality of the stage
   the code's components live in. *)
Fixpoint wfsub (alpha : Ord) : Sub Univ UnivOK alpha -> Prop :=
  match alpha as a return Sub Univ UnivOK a -> Prop with
  | ozero => fun s => match s with end
  | osucc beta => fun s =>
      match s with
      | inl c => WF_next UnivOK (xcmp_ beta beta) (wfsub beta) c
      | inr s0 => wfsub beta s0
      end
  | osup T f => fun s =>
      match s with
      | existT _ p s0 =>
          match s0 with
          | inl c => WF_next UnivOK (xcmp_ (f p) (f p)) (wfsub (f p)) c
          | inr s1 => wfsub (f p) s1
          end
      end
  end.

Definition wfc {beta} (c : U Univ UnivOK beta) : Prop :=
  WF_next UnivOK (xcmp_ beta beta) (wfsub beta) c.

(* The injections preserve well-formedness, definitionally. *)
Lemma wfc_Sub_succ beta (c : U Univ UnivOK beta) :
  wfsub (osucc beta) (U_Sub_succ Univ UnivOK c) = wfc c.
Proof. reflexivity. Qed.

Lemma wfc_Sub_sup T f (p : Pred T) (c : U Univ UnivOK (f p)) :
  wfsub (osup T f) (U_Sub_sup Univ UnivOK p c) = wfc c.
Proof. reflexivity. Qed.

Lemma wfsub_Sub_succ beta (s : Sub Univ UnivOK beta) :
  wfsub (osucc beta) (Sub_Sub_succ Univ UnivOK s) = wfsub beta s.
Proof. reflexivity. Qed.

Lemma wfsub_Sub_sup T f (p : Pred T) (s : Sub Univ UnivOK (f p)) :
  wfsub (osup T f) (Sub_Sub_sup Univ UnivOK p s) = wfsub (f p) s.
Proof. reflexivity. Qed.
(* A well-formed code is self-equal: read off the second conjunct at a node,
   and the recursive call below it. *)
Lemma wfsub_self : forall (alpha : Ord) (s : Sub Univ UnivOK alpha),
  wfsub alpha s -> cU (xcmp_ alpha alpha) s s.
Proof.
  induction alpha as [| beta IH | T f IH]; intros s.
  - destruct s.
  - destruct s as [c|s0]; [intros H; exact (proj2 H) | apply IH].
  - destruct s as [p [c|s0]]; [intros H; exact (proj2 H) | apply (IH p)].
Qed.
End Level.
