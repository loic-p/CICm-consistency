From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Ranks.Pred Ranks.Ord.

(* The stratified universe of assembly codes.

   Deviations from the blueprint, all forced by Rocq rather than chosen:

   1. A code at stage alpha is a refinement over the codes strictly below,
      packaged as a record Stage (carrier, decoding, equality, shadow).  The
      hierarchy is a plain Fixpoint on Brouwer trees returning a Stage.
      Sub alpha contains the codes at *every* node strictly below alpha, not
      only at the immediate predecessors, so that placing a code into a
      higher stage is a constructor injection, definitional on decodings.

   2. A Pi-code carries its coherence as transport *data* between the codomain
      codes at related arguments, with the setoid laws (preservation,
      composition, identity).  The blueprint states coherence as a Prop about
      an isomorphism between two different codes; that needs an equality
      between elements of different codes at the same stage, which cannot be
      defined before the stage is.  With transports, every condition in
      Refine only mentions the equality of a single component.

   3. The universe clause does not mention S: its decoding is a parameter,
      instantiated by the completed lower level (Codes/Levels.v) as a family
      over every term and accessibility proof, so that no transport along
      the rank is ever needed.  Ranks therefore never mention universes; the
      embedding up is a level lift.

   4. The decoding of a code contains only self-related elements: Stage_next
      bundles the equality proof into the decoding with a sig.  This is what
      makes "El of a Pi-code is the functions respecting the equality" true
      by construction, and it is forced by Codes/Iso.v: the image of a
      function under an isomorphism is built by pulling an *arbitrary*
      argument of the target domain back along the inverse transport, and
      the pullback is only a legitimate argument of the source function
      because every element is self-related. *)

Definition tyeq A B := exists n, eqty n A B.

(* u is the j-th numeral, level by level, up to weak head evaluation at each
   level.  NOT "eval u (num j)": esucc w is already a value, so it evaluates
   only to itself, and asking for a syntactically numeral whnf would leave
   the decoding of N empty at every realiser that is not literally a numeral
   -- in particular at the erasure of `succ n` for any n that is not already
   one.  This is the same mistake as a flat NatPer one layer down (see the
   note on NatPer in Layer1/Per.v); here it matters for the DECODING, so it
   would have made the interpretation of succ undefined.

   Unlike NatPer there is no stuck clause, and that is the point: layer 2 is
   truth-sensitive, so a stuck realiser carries no semantic element. *)
(* This is Type-valued, not Prop-valued, and deliberately so: the semantic
   recursor for natrec recurses on j and needs the PREDECESSOR REALISER u' at
   each step to build a Type-valued element, which a Prop-valued existential
   would not release.  The equality on the decoding never looks at the
   witness -- only at j -- so nothing is lost. *)
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

Record Stage := {
  St : Type;
  StEl : St -> etm -> Type;
  StEq : forall s u, StEl s u -> forall u', StEl s u' -> Prop;
  StSh : St -> etm
}.

(* Point 4 above, as a property: it holds definitionally of every stage in
   the hierarchy, but has to be assumed where the stage is a parameter. *)
Definition StGood (st : Stage) : Prop := forall s u x, st.(StEq) s u x u x.

Section Refine.
  Context (st : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).

  Local Notation S := st.(St).
  Local Notation ElS := st.(StEl).
  Local Notation eqS := st.(StEq).
  Local Notation shS := st.(StSh).

  Definition goodS (s : S) u (x : ElS s u) : Prop := eqS s u x u x.

  Record Transp (s s' : S) := {
    tr : forall u, ElS s u -> ElS s' u;
    tr_eq : forall u x u' x', eqS s u x u' x' -> eqS s' u (tr u x) u' (tr u' x')
  }.
  Arguments tr {s s'}.

  Inductive Refine : etm -> Type :=
  | r_nat T : eval T enat -> Refine T
  | r_prop T : eval T eprop -> Refine T
  | r_prf T p : eval T (eprf p) -> Prop -> Refine T
  | r_univ T m : UnivOK m -> eval T (euniv m) -> Refine T
  | r_pi T A0 B0 : eval T (epi A0 B0) ->
      forall a : S, tyeq (shS a) A0 ->
      forall b : (forall u, ElS a u -> S),
      (forall u x, tyeq (shS (b u x)) (eapp B0 u)) ->
      forall coh : (forall u x u' x', eqS a u x u' x' -> Transp (b u' x') (b u x)),
      (* composition *)
      (forall u0 x0 u1 x1 u2 x2
              (r01 : eqS a u0 x0 u1 x1) (r12 : eqS a u1 x1 u2 x2) (r02 : eqS a u0 x0 u2 x2)
              v (y : ElS (b u2 x2) v), goodS _ v y ->
         eqS (b u0 x0) v (tr (coh _ _ _ _ r01) v (tr (coh _ _ _ _ r12) v y))
                         v (tr (coh _ _ _ _ r02) v y)) ->
      (* identity *)
      (forall u x (r : eqS a u x u x) v (y : ElS (b u x) v), goodS _ v y ->
         eqS (b u x) v (tr (coh _ _ _ _ r) v y) v y) ->
      Refine T
  (* Sigma carries EXACTLY the data of Pi -- the domain, the codomain family,
     its coherence, and the composition and identity laws of that coherence.
     What differs is only the head the realiser evaluates to, and the
     decoding: a Pi-code decodes to functions and a Sigma-code to pairs.  The
     paper puts it as "arguments for Pi; componentwise for Sigma". *)
  | r_sig T A0 B0 : eval T (esig A0 B0) ->
      forall a : S, tyeq (shS a) A0 ->
      forall b : (forall u, ElS a u -> S),
      (forall u x, tyeq (shS (b u x)) (eapp B0 u)) ->
      forall coh : (forall u x u' x', eqS a u x u' x' -> Transp (b u' x') (b u x)),
      (* composition *)
      (forall u0 x0 u1 x1 u2 x2
              (r01 : eqS a u0 x0 u1 x1) (r12 : eqS a u1 x1 u2 x2) (r02 : eqS a u0 x0 u2 x2)
              v (y : ElS (b u2 x2) v), goodS _ v y ->
         eqS (b u0 x0) v (tr (coh _ _ _ _ r01) v (tr (coh _ _ _ _ r12) v y))
                         v (tr (coh _ _ _ _ r02) v y)) ->
      (* identity *)
      (forall u x (r : eqS a u x u x) v (y : ElS (b u x) v), goodS _ v y ->
         eqS (b u x) v (tr (coh _ _ _ _ r) v y) v y) ->
      Refine T
  | r_ne T N : eval T N -> stuck N -> Refine T.

  Definition El {T} (r : Refine T) (u : etm) : Type :=
    match r with
    | r_nat T _ => ({ j : nat & NatAt j u } * Good T u)%type
    | r_prop T _ => (Prop * Good T u)%type
    | r_prf T _ _ H => (H * Good T u)%type
    | r_univ _ m _ _ => Univ m u
    | r_pi T _ _ _ a _ b _ _ _ _ =>
        ((forall u' x, ElS (b u' x) (eapp u u')) * Good T u)%type
    (* a pair is its two projections: the first component's value, and the
       second one's in the codomain instance that value picks out.  This is
       the shape SigPer has at layer 1, and it needs no eta-expansion
       because surjective pairing is a rule of the theory. *)
    | r_sig T _ _ _ a _ b _ _ _ _ =>
        ({ x : ElS a (efst u) & ElS (b (efst u) x) (esnd u) } * Good T u)%type
    | r_ne _ _ _ _ => Empty_set
    end.

  (* The unary equality.  At Pi it records that the two functions agree, up
     to the coherence transports, on related arguments in both directions;
     without both directions neither symmetry nor transitivity is provable.
     The goodness of the values is not stated: it is automatic, because the
     decoding of a code contains only self-related elements. *)
  Definition eqEl {T} (r : Refine T) : forall u, El r u -> forall u', El r u' -> Prop :=
    match r as r0 return forall u, El r0 u -> forall u', El r0 u' -> Prop with
    | r_nat T _ => fun u x u' x' =>
        projT1 (Datatypes.fst x) = projT1 (Datatypes.fst x') /\ Rel T u u'
    | r_prop T _ => fun u x u' x' => (Datatypes.fst x <-> Datatypes.fst x') /\ Rel T u u'
    | r_prf T _ _ _ => fun u x u' x' => Rel T u u'
    | r_univ _ m _ _ => fun u x u' x' => UnivEq m u x u' x'
    | r_pi T _ _ _ a _ b _ coh _ _ => fun u f u' f' =>
        (forall u1 x1 u1' x1' (r : eqS a u1 x1 u1' x1') (r' : eqS a u1' x1' u1 x1),
           eqS (b u1 x1) (eapp u u1) (Datatypes.fst f u1 x1)
                         (eapp u' u1') (tr (coh _ _ _ _ r) _ (Datatypes.fst f' u1' x1')) /\
           eqS (b u1' x1') (eapp u' u1') (Datatypes.fst f' u1' x1')
                           (eapp u u1) (tr (coh _ _ _ _ r') _ (Datatypes.fst f u1 x1)))
        /\ Rel T u u'
    (* Componentwise, in both directions as at Pi.  The relation of the FIRST
       components is existentially bound rather than universally quantified:
       at Pi the arguments are given from outside, so the clause can quantify
       over them, but at Sigma they are the elements' own projections, and a
       universally quantified clause would be vacuous exactly when the first
       components are unrelated -- which is what has to be excluded. *)
    | r_sig T _ _ _ a _ b _ coh _ _ => fun u p u' p' =>
        (exists r : eqS a (efst u) (projT1 (Datatypes.fst p))
                          (efst u') (projT1 (Datatypes.fst p')),
           eqS (b (efst u) (projT1 (Datatypes.fst p)))
               (esnd u) (projT2 (Datatypes.fst p))
               (esnd u') (tr (coh _ _ _ _ r) _ (projT2 (Datatypes.fst p'))))
        /\ (exists r' : eqS a (efst u') (projT1 (Datatypes.fst p'))
                           (efst u) (projT1 (Datatypes.fst p)),
           eqS (b (efst u') (projT1 (Datatypes.fst p')))
               (esnd u') (projT2 (Datatypes.fst p'))
               (esnd u) (tr (coh _ _ _ _ r') _ (projT2 (Datatypes.fst p))))
        /\ Rel T u u'
    | r_ne _ _ _ _ => fun _ _ _ _ => True
    end.

  Definition U_of : Type := { T : etm & Refine T }.

  Definition Stage_next : Stage := {|
    St := U_of;
    StEl c u := { x : El (projT2 c) u | eqEl (projT2 c) u x u x };
    StEq c u x u' x' := eqEl (projT2 c) u (proj1_sig x) u' (proj1_sig x');
    StSh c := projT1 c
  |}.

  Lemma Stage_next_good : StGood Stage_next.
  Proof. intros c u x; exact (proj2_sig x). Qed.
End Refine.

Arguments tr {st s s'}.

Definition Stage_empty : Stage := {|
  St := Empty_set;
  StEl s := match s with end;
  StEq s := match s with end;
  StSh s := match s with end
|}.

Definition Stage_sum (st1 st2 : Stage) : Stage := {|
  St := (st1.(St) + st2.(St))%type;
  StEl s := match s with inl s => st1.(StEl) s | inr s => st2.(StEl) s end;
  StEq s := match s as s0 return forall u, (match s0 with inl s => st1.(StEl) s | inr s => st2.(StEl) s end) u ->
                                  forall u', (match s0 with inl s => st1.(StEl) s | inr s => st2.(StEl) s end) u' -> Prop with
            | inl s => st1.(StEq) s
            | inr s => st2.(StEq) s
            end;
  StSh s := match s with inl s => st1.(StSh) s | inr s => st2.(StSh) s end
|}.

Definition Stage_sup T (F : Pred T -> Stage) : Stage := {|
  St := { p : Pred T & (F p).(St) };
  StEl s := (F (projT1 s)).(StEl) (projT2 s);
  StEq s := (F (projT1 s)).(StEq) (projT2 s);
  StSh s := (F (projT1 s)).(StSh) (projT2 s)
|}.

Lemma Stage_empty_good : StGood Stage_empty.
Proof. intros []. Qed.

Lemma Stage_sum_good st1 st2 : StGood st1 -> StGood st2 -> StGood (Stage_sum st1 st2).
Proof. intros H1 H2 [s|s]; [apply H1 | apply H2]. Qed.

Lemma Stage_sup_good T F : (forall p, StGood (F p)) -> StGood (Stage_sup T F).
Proof. intros H [p s]; apply H. Qed.

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).

  (* stage alpha: every code strictly below alpha.  A successor adds the
     node beta on top of everything below it, a sup collects the branches. *)
  Fixpoint stage (alpha : Ord) : Stage :=
    match alpha with
    | ozero => Stage_empty
    | osucc beta => Stage_sum (Stage_next (stage beta) Univ UnivEq UnivOK) (stage beta)
    | osup T f =>
        Stage_sup T (fun p => Stage_sum (Stage_next (stage (f p)) Univ UnivEq UnivOK) (stage (f p)))
    end.

  (* The codes at node beta. *)
  Definition Ust (beta : Ord) : Stage := Stage_next (stage beta) Univ UnivEq UnivOK.

  Definition Sub alpha : Type := (stage alpha).(St).
  Definition U beta : Type := (Ust beta).(St).

  Lemma stage_good alpha : StGood (stage alpha).
  Proof.
    induction alpha as [| beta IH | T f IH]; cbn.
    - apply Stage_empty_good.
    - apply Stage_sum_good; [apply Stage_next_good | exact IH].
    - apply Stage_sup_good; intros p; apply Stage_sum_good;
        [apply Stage_next_good | apply IH].
  Qed.

  Lemma Ust_good beta : StGood (Ust beta).
  Proof. apply Stage_next_good. Qed.

  (* Injections, all definitional on decodings, equalities and shadows. *)
  Definition U_Sub_succ {beta} (c : U beta) : Sub (osucc beta) := inl c.
  Definition Sub_Sub_succ {beta} (s : Sub beta) : Sub (osucc beta) := inr s.
  Definition U_Sub_sup {T f} (p : Pred T) (c : U (f p)) : Sub (osup T f) := existT _ p (inl c).
  Definition Sub_Sub_sup {T f} (p : Pred T) (s : Sub (f p)) : Sub (osup T f) := existT _ p (inr s).

  Lemma El_U_Sub_succ beta (c : U beta) u :
    (stage (osucc beta)).(StEl) (U_Sub_succ c) u = (Ust beta).(StEl) c u.
  Proof. reflexivity. Qed.

  Lemma El_U_Sub_sup T f (p : Pred T) (c : U (f p)) u :
    (stage (osup T f)).(StEl) (U_Sub_sup p c) u = (Ust (f p)).(StEl) c u.
  Proof. reflexivity. Qed.
End Level.
