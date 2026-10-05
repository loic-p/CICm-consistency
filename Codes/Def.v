From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord.
From Stdlib Require Import Arith Lia.

(* The stratified universe of assembly codes, v2.

   The design and its rationale are in Codes/DESIGN.md; the four points that
   differ from v1 are these.

   1. THE EQUALITY IS HETEROGENEOUS and it is not part of a stage.  A `Stage`
      is a carrier, a decoding and a shadow -- nothing else.  The equalities
      are defined in Codes/Eq.v, by a double recursion over the Brouwer trees,
      as relations between codes of TWO stages.  That is what removes the
      transport data from the codes: v1 could only say "f maps related
      arguments to related values" through a transport carried by the Pi-code,
      because its equality was homogeneous.

   2. THE BINDER CLAUSES CARRY THEIR COMPONENTS' EQUALITIES.  A Pi-code's
      decoding must contain only the EXTENSIONAL functions -- a codomain
      family is indexed by the domain's elements, and the interpretation has
      nothing to give at a non-extensional one -- and extensionality is a
      statement about the heterogeneous equality of the codomain codes, which
      is the very thing being defined.  Carrying the components' equalities as
      parameters breaks that circularity (it is what `cPi` does in the setoid
      universe's univ0.v), and Codes/WF.v then pins them to the canonical
      ones.  Read positively: a binder code carries its components AS
      ASSEMBLIES, which is exactly the input a type former expects.

      Sigma carries nothing: a pair is good as soon as its components are.

   3. GOODNESS IS INSIDE THE DECODING, clause by clause (the sig at Pi, the
      WExt at W), not bundled by Stage_next as in v1.  This is what lets a
      Stage have no equality field at all.

   4. THERE IS NO NEUTRAL CLAUSE.  v1 carried `r_ne`, a code for a stuck type
      with an empty decoding, to mirror layer 1's LR_ne.  Nothing ever built
      one: a code is produced by the interpretation from a derivation and a
      GOOD environment, and the only rule whose subject can have a stuck
      erasure is `absurd`, whose case is vacuous -- it needs an element of the
      interpretation of Prf False, of which there are none.  So no code has a
      stuck shadow, hence no environment can supply a stuck type either, and
      the clause is unreachable.  Dropping it removes a case from every match
      and, in the double ones, fifteen.

   5. W IS NEW.  Its decoding is an inductive family of trees and its relation
      is a recursion on trees, generic in the two stages so that ONE
      definition serves both the carried equalities (inside the decoding) and
      the canonical cross-code comparison (in Codes/Eq.v).  The extensional
      trees need no predicate of their own: `WRel t t` at the carried
      relations already says "hereditarily, related branches give related
      subtrees", which is what the setoid universe's `Wext` carves out by an
      inductive. *)

Definition tyeq A B := exists n, eqty n A B.

Lemma tyeq_sym A B : tyeq A B -> tyeq B A.
Proof. intros [n H]; exists n; apply eqty_sym; exact H. Qed.

Lemma tyeq_trans A B C : tyeq A B -> tyeq B C -> tyeq A C.
Proof.
  intros [n H] [m H']; exists (Nat.max n m); eapply eqty_trans;
    [apply (eqty_cumul n (Nat.max n m) _ _ (Nat.le_max_l _ _)); exact H
    |apply (eqty_cumul m (Nat.max n m) _ _ (Nat.le_max_r _ _)); exact H'].
Qed.

Lemma Good_tyeq T T' u : tyeq T T' -> Good T u -> Good T' u.
Proof. intros [n E] G; eapply (Rel_resp n T T' E); exact G. Qed.

Lemma Rel_tyeq T T' u u' : tyeq T T' -> Rel T u u' -> Rel T' u u'.
Proof. intros [n E] H; eapply (Rel_resp n T T' E); exact H. Qed.

(* ------------------------------------------------------------------ *)
(* The semantic natural numbers, verbatim from v1.                     *)
(* ------------------------------------------------------------------ *)

(* u is the j-th numeral, level by level, up to weak head evaluation at each
   level.  NOT "eval u (num j)": esucc w is already a value, so it evaluates
   only to itself, and asking for a syntactically numeral whnf would leave the
   decoding of N empty at every realiser that is not literally a numeral -- in
   particular at the erasure of `succ n` for any n that is not already one.
   This is the same mistake as a flat NatPer one layer down (see the note on
   NatPer in Layer1/Per.v); here it matters for the DECODING, so it would have
   made the interpretation of succ undefined.

   Unlike NatPer there is no stuck clause, and that is the point: layer 2 is
   truth-sensitive, so a stuck realiser carries no semantic element.

   This is Type-valued, and deliberately so: the semantic recursor for natrec
   recurses on j and needs the PREDECESSOR REALISER u' at each step to build a
   Type-valued element, which a Prop-valued existential would not release. *)
Fixpoint NatAt (j : nat) (u : etm) : Type :=
  match j with
  | 0 => eval u ezero
  | S j0 => { u' : etm & (eval u (esucc u') * NatAt j0 u')%type }
  end.

Definition NatAt_zero : NatAt 0 ezero := eval_whnf ezero (or_introl v_zero).

Definition NatAt_succ j u (H : NatAt j u) : NatAt (S j) (esucc u) :=
  existT _ u (eval_whnf _ (or_introl (v_succ u)), H).

Definition NatAt_pred j u (H : NatAt (S j) u) : etm := projT1 H.
Definition NatAt_pred_ev j u (H : NatAt (S j) u) : eval u (esucc (NatAt_pred j u H)) :=
  Datatypes.fst (projT2 H).
Definition NatAt_pred_at j u (H : NatAt (S j) u) : NatAt j (NatAt_pred j u H) :=
  Datatypes.snd (projT2 H).

Definition NatAt_exp : forall j u u1, reds u u1 -> NatAt j u1 -> NatAt j u :=
  fun j => match j with
  | 0 => fun u u1 Hr H => eval_reds _ _ _ Hr H
  | S j0 => fun u u1 Hr H =>
      existT _ (projT1 H)
        (eval_reds _ _ _ Hr (Datatypes.fst (projT2 H)), Datatypes.snd (projT2 H))
  end.

Definition NatAt_red : forall j u u1, reds u u1 -> NatAt j u -> NatAt j u1 :=
  fun j => match j with
  | 0 => fun u u1 Hr H => eval_reds_inv _ _ _ Hr H
  | S j0 => fun u u1 Hr H =>
      existT _ (projT1 H)
        (eval_reds_inv _ _ _ Hr (Datatypes.fst (projT2 H)), Datatypes.snd (projT2 H))
  end.

(* Determinism: the numeral a realiser sits at is unique.  Needed for
   functionality of the interpretation. *)
Lemma NatAt_fun j j' u : NatAt j u -> NatAt j' u -> j = j'.
Proof.
  revert j' u; induction j as [| j IH]; intros [| j'] u; cbn.
  - reflexivity.
  - intros H0 [u' [He _]]; exfalso.
    assert (E := eval_det _ _ _ H0 He); discriminate E.
  - intros [u' [He _]] H0; exfalso.
    assert (E := eval_det _ _ _ He H0); discriminate E.
  - intros [a [Ha Ha']] [b [Hb Hb']].
    assert (E := eval_det _ _ _ Ha Hb); injection E; intros <-.
    f_equal; eapply IH; eassumption.
Qed.

(* The layer-1 shadow of a semantic natural number. *)
Lemma NatAt_NatPer j u u' : NatAt j u -> NatAt j u' -> NatPer u u'.
Proof.
  revert u u'; induction j as [| j IH]; cbn; intros u u'.
  - intros H H'; apply np_zero; assumption.
  - intros [a [Ha Ha']] [b [Hb Hb']]; eapply np_succ;
      [exact Ha | exact Hb | eapply IH; eassumption].
Qed.

(* ------------------------------------------------------------------ *)
(* Stages: the codes available below, their decodings, their shadows.  *)
(* ------------------------------------------------------------------ *)

Record Stage := {
  St : Type;
  StEl : St -> etm -> Type;
  StSh : St -> etm
}.

(* The two shapes of carried equality: on the elements of one code of the
   stage, and between the elements of two instances of a family. *)
Definition DomEq (st : Stage) (a : St st) : Type :=
  forall u, StEl st a u -> forall u', StEl st a u' -> Prop.

Definition FamEq (st : Stage) (a : St st) (b : forall u, StEl st a u -> St st) : Type :=
  forall u (x : StEl st a u) u' (x' : StEl st a u') v, StEl st (b u x) v ->
  forall v', StEl st (b u' x') v' -> Prop.

(* ------------------------------------------------------------------ *)
(* The codes at one stage.                                            *)
(* ------------------------------------------------------------------ *)

Section Codes.
Context (st : Stage) (UnivOK : nat -> Prop).

Inductive Refine : etm -> Type :=
| r_nat T : eval T enat -> Refine T
| r_prop T : eval T eprop -> Refine T
| r_prf T p : eval T (eprf p) -> Prop -> Refine T
| r_univ T m : UnivOK m -> eval T (euniv m) -> Refine T
| r_pi T A1 B1 : eval T (epi A1 B1) ->
    forall (a : St st) (ea : tyeq (StSh st a) A1) (aeq : DomEq st a)
           (b : forall u, StEl st a u -> St st)
           (eb : forall u x, tyeq (StSh st (b u x)) (eapp B1 u))
           (beq : FamEq st a b),
    Refine T
(* Sigma carries only the components: a pair is self-related as soon as its
   two components are, so there is no condition on the decoding and nothing
   to state it with. *)
| r_sig T A1 B1 : eval T (esig A1 B1) ->
    forall (a : St st) (ea : tyeq (StSh st a) A1)
           (b : forall u, StEl st a u -> St st)
           (eb : forall u x, tyeq (StSh st (b u x)) (eapp B1 u)),
    Refine T
(* W carries exactly what Pi does, and for the same reason: a tree's
   branching function has to be extensional. *)
| r_w T A1 B1 : eval T (ew A1 B1) ->
    forall (a : St st) (ea : tyeq (StSh st a) A1) (aeq : DomEq st a)
           (b : forall u, StEl st a u -> St st)
           (eb : forall u x, tyeq (StSh st (b u x)) (eapp B1 u))
           (beq : FamEq st a b),
    Refine T.

(* The trees over a label code a and a branching family b.  Every node
   carries the layer-1 goodness of its own realiser, because the subtrees of
   a tree are elements of the same code and so cannot inherit it from a
   lower stage as Pi's and Sigma's components do. *)
Inductive WEl (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  : etm -> Type :=
| wel_sup w u0 (x : StEl st a u0) (f : etm) :
    eval w (esup u0 f) -> Good T w ->
    (forall v (y : StEl st (b u0 x) v), WEl T a b (eapp f v)) ->
    WEl T a b w.
End Codes.

Arguments r_nat {st UnivOK}. Arguments r_prop {st UnivOK}. Arguments r_prf {st UnivOK}.
Arguments r_univ {st UnivOK}. Arguments r_pi {st UnivOK}. Arguments r_sig {st UnivOK}.
Arguments r_w {st UnivOK}.
Arguments WEl {st}. Arguments wel_sup {st T a b}.

(* The tree relation.  Generic in the two stages and in the label and branch
   relations, so that one definition serves both the carried equalities and
   the canonical cross-code comparison of Codes/Eq.v. *)
Fixpoint WRel {st st' : Stage} (T T' : etm) (a : St st) (a' : St st')
  (b : forall u, StEl st a u -> St st) (b' : forall u, StEl st' a' u -> St st')
  (Rlab : forall u, StEl st a u -> forall u', StEl st' a' u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st' a' u') v, StEl st (b u x) v ->
         forall v', StEl st' (b' u' x') v' -> Prop)
  {w} (t : WEl T a b w) {w'} (t' : WEl T' a' b' w') : Prop :=
  match t, t' with
  | wel_sup _ u0 x f _ _ sub, wel_sup _ u0' x' f' _ _ sub' =>
      Rlab u0 x u0' x' /\
      (forall v y v' y', Rbr u0 x u0' x' v y v' y' ->
         WRel T T' a a' b b' Rlab Rbr (sub v y) (sub' v' y'))
  end.

(* ------------------------------------------------------------------ *)
(* The decoding.                                                      *)
(* ------------------------------------------------------------------ *)

Section Decode.
Context (st : Stage) (Univ : nat -> etm -> Type) (UnivOK : nat -> Prop).

Definition El {T} (r : Refine st UnivOK T) (u : etm) : Type :=
  match r with
  | r_nat T _ => ({ j : nat & NatAt j u } * Good T u)%type
  | r_prop T _ => (Prop * Good T u)%type
  | r_prf T _ _ H => (H * Good T u)%type
  | r_univ _ m _ _ => Univ m u
  (* the EXTENSIONAL functions: the condition is what makes every element of
     the decoding self-related, hence a legitimate index of a codomain
     family one stage up *)
  | r_pi T _ _ _ a _ aeq b _ beq =>
      ({ f : forall u1 (x1 : StEl st a u1), StEl st (b u1 x1) (eapp u u1)
         | forall u1 x1 u1' x1', aeq u1 x1 u1' x1' ->
             beq u1 x1 u1' x1' _ (f u1 x1) _ (f u1' x1') } * Good T u)%type
  (* a pair is its two projections: the first component's value, and the
     second one's in the codomain instance that value picks out.  This is the
     shape SigPer has at layer 1, and it needs no eta-expansion because
     surjective pairing is a rule of the theory. *)
  | r_sig T _ _ _ a _ b _ =>
      ({ x : StEl st a (efst u) & StEl st (b (efst u) x) (esnd u) } * Good T u)%type
  (* the extensional trees: `WRel .. t t` unfolds to "hereditarily, related
     branches give related subtrees", which is the tree's self-relatedness --
     the same condition as Pi's, so no separate predicate is needed *)
  | r_w T _ _ _ a _ aeq b _ beq =>
      ({ t : WEl T a b u | WRel T T a a b b aeq beq t t } * Good T u)%type
  end.

Definition U_of : Type := { T : etm & Refine st UnivOK T }.

Definition Stage_next : Stage := {|
  St := U_of;
  StEl c u := El (projT2 c) u;
  StSh c := projT1 c
|}.
End Decode.

Arguments El {st Univ UnivOK T}.
Arguments U_of {st} UnivOK.

(* ------------------------------------------------------------------ *)
(* The hierarchy over Brouwer trees.  Unchanged from v1 except that    *)
(* only carriers, decodings and shadows have to be dispatched.         *)
(* ------------------------------------------------------------------ *)

Definition Stage_empty : Stage := {|
  St := Empty_set;
  StEl s := match s with end;
  StSh s := match s with end
|}.

Definition Stage_sum (st1 st2 : Stage) : Stage := {|
  St := (St st1 + St st2)%type;
  StEl s := match s with inl s => StEl st1 s | inr s => StEl st2 s end;
  StSh s := match s with inl s => StSh st1 s | inr s => StSh st2 s end
|}.

Definition Stage_sup T (F : Pred T -> Stage) : Stage := {|
  St := { p : Pred T & St (F p) };
  StEl s := StEl (F (projT1 s)) (projT2 s);
  StSh s := StSh (F (projT1 s)) (projT2 s)
|}.

Section Level.
Context (Univ : nat -> etm -> Type) (UnivOK : nat -> Prop).

(* stage alpha: every code strictly below alpha.  A successor adds the node
   beta on top of everything below it, a sup collects the branches. *)
Fixpoint stage (alpha : Ord) : Stage :=
  match alpha with
  | ozero => Stage_empty
  | osucc beta => Stage_sum (Stage_next (stage beta) Univ UnivOK) (stage beta)
  | osup T f =>
      Stage_sup T (fun p =>
        Stage_sum (Stage_next (stage (f p)) Univ UnivOK) (stage (f p)))
  end.

(* The codes at node beta. *)
Definition Ust (beta : Ord) : Stage := Stage_next (stage beta) Univ UnivOK.

Definition Sub alpha : Type := St (stage alpha).
Definition U beta : Type := St (Ust beta).

(* Injections, all definitional on decodings and shadows. *)
Definition U_Sub_succ {beta} (c : U beta) : Sub (osucc beta) := inl c.
Definition Sub_Sub_succ {beta} (s : Sub beta) : Sub (osucc beta) := inr s.
Definition U_Sub_sup {T f} (p : Pred T) (c : U (f p)) : Sub (osup T f) :=
  existT _ p (inl c).
Definition Sub_Sub_sup {T f} (p : Pred T) (s : Sub (f p)) : Sub (osup T f) :=
  existT _ p (inr s).

Lemma El_U_Sub_succ beta (c : U beta) u :
  StEl (stage (osucc beta)) (U_Sub_succ c) u = StEl (Ust beta) c u.
Proof. reflexivity. Qed.

Lemma El_U_Sub_sup T f (p : Pred T) (c : U (f p)) u :
  StEl (stage (osup T f)) (U_Sub_sup p c) u = StEl (Ust (f p)) c u.
Proof. reflexivity. Qed.

Lemma Sh_U_Sub_succ beta (c : U beta) :
  StSh (stage (osucc beta)) (U_Sub_succ c) = StSh (Ust beta) c.
Proof. reflexivity. Qed.
End Level.
