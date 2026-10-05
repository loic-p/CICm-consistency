From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Univ
  Interp.Env.
From Stdlib Require Import Arith Lia.

(* Introducing and eliminating the semantic elements of the families with no
   components.  Each of these is a definitional unfolding of Codes/Def.v's El
   and eqEl at the corresponding clause.

   Shorter than v1 in two places.  The decoding no longer bundles
   self-relatedness, so an element IS the data -- no `exist _ ... (conj ...)`
   wrapper -- and `kRel_same` is immediate where v1 had to appeal to the
   identity law of the carried transport.  What is new is that every clause of
   the equality carries `tyeq T T'` beside the layer-1 relation, so each `_iff`
   lemma below supplies it from the shadow.

   The pattern to notice is still the one at Prf: the equality does not mention
   the element at all, so any two elements of a Prf-family at related
   realisers are related.  That is proof irrelevance, and it is why the
   clauses of the interpretation at proof terms need no condition on the
   value. *)

(* ------------------------------------------------------------------ *)
(* Lemma 8.7 in the form the interpretation uses: the decoding of a     *)
(* family is closed under reduction and expansion of the realiser, and  *)
(* the two realisers are related.                                       *)
(* ------------------------------------------------------------------ *)

Definition famRed {k u} (F : kUFam k u) w w1 (H : reds w w1) (x : kElAt F w)
  : kElAt F w1 :=
  cRed (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) (lexp (lvl k))
    (kAt F) (famAtWf F) w w1 H x.

Definition famExp {k u} (F : kUFam k u) w w1 (H : reds w w1) (y : kElAt F w1)
  : kElAt F w :=
  cExp (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) (lexp (lvl k))
    (kAt F) (famAtWf F) w w1 H y.

Lemma famRed_rel {k u} (F : kUFam k u) w w1 (H : reds w w1) x :
  kEqAt F w x F w1 (famRed F w w1 H x).
Proof.
  exact (cRed_rel (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k)
           (lexp (lvl k)) (kAt F) (famAtWf F) w w1 H x).
Qed.

Lemma famExp_rel {k u} (F : kUFam k u) w w1 (H : reds w w1) y :
  kEqAt F w (famExp F w w1 H y) F w1 y.
Proof.
  exact (cExp_rel (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k)
           (lexp (lvl k)) (kAt F) (famAtWf F) w w1 H y).
Qed.

(* Relatedness inside one family is `kRel` with the family's own
   self-equality.  v1 needed the identity law of the carried transport here. *)
Lemma kRel_same {k u} (F : kUFam k u) w x w' x' :
  kEqAt F w x F w' x' <-> kRel F w x F w' x'.
Proof.
  split; [intros H; split; [exact (famAtSelf F) | exact H] | intros H; exact (kRel_at H)].
Qed.

(* ------------------------------------------------------------------ *)
(* N.                                                                  *)
(* ------------------------------------------------------------------ *)

Definition natElem {k} (u : etm) (j : nat) (e : NatAt j u) (g : Good enat u)
  : kElAt (natFam k) u := (existT _ j e, g).

Definition natIdx {k u} (x : kElAt (natFam k) u) : nat := projT1 (Datatypes.fst x).
Definition natSpec {k u} (x : kElAt (natFam k) u) : NatAt (natIdx x) u :=
  projT2 (Datatypes.fst x).
Definition natGood {k u} (x : kElAt (natFam k) u) : Good enat u := Datatypes.snd x.

Lemma natEq_iff {k u u'} (x : kElAt (natFam k) u) (x' : kElAt (natFam k) u') :
  kEqAt (natFam k) u x (natFam k) u' x' <-> (natIdx x = natIdx x' /\ Rel enat u u').
Proof.
  split.
  - intros [H1 [_ H2]]; split; [exact H1 | exact H2].
  - intros [H1 H2]; split; [exact H1 |].
    split; [exact (tyeq_nat enat ev_nat) | exact H2].
Qed.

(* Any two elements at the same realiser agree: the index is determined by the
   realiser (NatAt_fun) and the goodness is irrelevant to the equality. *)
Lemma natEq_self {k u} (x x' : kElAt (natFam k) u) :
  kEqAt (natFam k) u x (natFam k) u x'.
Proof.
  apply natEq_iff; split;
    [exact (NatAt_fun _ _ u (natSpec x) (natSpec x')) | exact (natGood x)].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop.                                                               *)
(* ------------------------------------------------------------------ *)

Definition propElem {k} (u : etm) (P : Prop) (g : Good eprop u)
  : kElAt (propFam k) u := (P, g).

Definition propVal {k u} (x : kElAt (propFam k) u) : Prop := Datatypes.fst x.
Definition propGood {k u} (x : kElAt (propFam k) u) : Good eprop u := Datatypes.snd x.

Lemma propEq_iff {k u u'} (x : kElAt (propFam k) u) (x' : kElAt (propFam k) u') :
  kEqAt (propFam k) u x (propFam k) u' x' <->
  ((propVal x <-> propVal x') /\ Rel eprop u u').
Proof.
  split.
  - intros [H1 [_ H2]]; split; [exact H1 | exact H2].
  - intros [H1 H2]; split; [exact H1 |].
    split; [exact (tyeq_prop eprop ev_prop) | exact H2].
Qed.

(* ------------------------------------------------------------------ *)
(* Prf: proof irrelevance.                                             *)
(* ------------------------------------------------------------------ *)

Definition prfElem {k p Hp H} (u : etm) (h : H) (g : Good (eprf p) u)
  : kElAt (prfFam k p Hp H) u := (h, g).

Definition prfVal {k p Hp H u} (x : kElAt (prfFam k p Hp H) u) : H := Datatypes.fst x.
Definition prfGood {k p Hp H u} (x : kElAt (prfFam k p Hp H) u) : Good (eprf p) u :=
  Datatypes.snd x.

(* The equality at Prf does not look at the elements. *)
Lemma prfEq_iff {k p Hp H u u'} (x : kElAt (prfFam k p Hp H) u)
  (x' : kElAt (prfFam k p Hp H) u') :
  kEqAt (prfFam k p Hp H) u x (prfFam k p Hp H) u' x' <-> Rel (eprf p) u u'.
Proof.
  split.
  - intros [_ H2]; exact H2.
  - intros H2; split;
      [exact (tyeq_prf (eprf p) p (eval_whnf _ (whnf_prf p)) Hp) | exact H2].
Qed.

Lemma prfEq_of {k p Hp H u u'} (x : kElAt (prfFam k p Hp H) u)
  (x' : kElAt (prfFam k p Hp H) u') :
  Rel (eprf p) u u' -> kEqAt (prfFam k p Hp H) u x (prfFam k p Hp H) u' x'.
Proof. apply prfEq_iff. Qed.

(* ------------------------------------------------------------------ *)
(* The semantic naturals, and moving a value to an equal family.        *)
(* ------------------------------------------------------------------ *)

Definition natGoodOf {j u} (e : NatAt j u) : Good enat u :=
  Rel_nat_intro enat u u gt_nat ev_nat (NatAt_NatPer j u u e e).

Definition natE {k u} (j : nat) (e : NatAt j u) : kElAt (natFam k) u :=
  natElem u j e (natGoodOf e).

Definition natSucc {k u} (x : kElAt (natFam k) u) : kElAt (natFam k) (esucc u) :=
  natE (S (natIdx x)) (NatAt_succ _ _ (natSpec x)).

Lemma natIdx_natE {k u} (j : nat) (e : NatAt j u) : natIdx (@natE k u j e) = j.
Proof. reflexivity. Qed.

Lemma natE_eq {k u u'} (j : nat) (e : NatAt j u) (e' : NatAt j u') :
  kEqAt (natFam k) u (natE j e) (natFam k) u' (natE j e').
Proof.
  apply natEq_iff; split;
    [reflexivity | apply Rel_nat_intro; [apply gt_nat | apply ev_nat |]].
  exact (NatAt_NatPer j u u' e e').
Qed.

(* Every computation rule of the interpretation is one of these: move the
   value along an equality of families, then expand its realiser. *)
Definition moveTo {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) w0 (Hr : reds w0 w) : kElAt F' w0 :=
  famExp F' w0 w Hr (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).

Lemma moveTo_rel {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) w0 (Hr : reds w0 w) :
  kRel F w x F' w0 (moveTo F F' P w x w0 Hr).
Proof.
  split; [exact P |].
  eapply kEqAt_trans;
    [ exact P
    | exact (kto_coh (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x)
    | apply kEqAt_sym; exact (famExp_rel F' w0 w Hr _) ].
Qed.
