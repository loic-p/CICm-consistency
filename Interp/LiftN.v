From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Lift
  Interp.Univ Interp.Env Interp.Elem.
From Stdlib Require Import Arith Lia.

(* THE LEVEL LIFT, IN THE FORM THE LEVEL-ANNOTATED FORMERS NEED.

   Every type former carries the level it lives at, and its components may
   live at any level below it: `pi k A B` with A and B at level j <= k.  A
   Pi-code is built from component codes at ITS OWN level, so the two levels
   have to be reconciled, and there is only one way that keeps the universe
   lift's computation rules DEFINITIONAL:

     the value of `pi (d + j) A B` is the d-fold LIFT of the value of the
     level-j Pi-family built from the components.

   Then `up (d + j) (pi (d + j) A B)`, whose value is one more lift, and
   `pi (S d + j) A B`, whose value is the (S d)-fold lift, have literally the
   same value -- no commutation lemma for Pi or Sigma is needed.  In v1 that
   mattered a great deal: an isomorphism of two Pi-CODES asked for the
   naturality square of `Codes/Iso.v`'s isoRefine, the one piece of the
   hierarchy the interpretation never had to build by hand.  In v2 there is
   no transport to be natural in, but the arrangement is kept, because it is
   still the one that makes the lift's own rules hold on the nose.

   The component-free formers keep their canonical family at every level
   (natFam k, propFam k, prfFam k), and their commutations are the one-liners
   at the bottom of `Interp/Lift.v`, iterated here.

   What was v1's reason for this file being separate from `Interp/Lift.v` --
   `famFrom_famTo` only became available after the 500 s `Interp/SigEl.v` --
   is gone; `Interp/Lift.v` now carries the one-step material, and what
   remains here is the iteration and the level casts. *)

(* ------------------------------------------------------------------ *)
(* d steps, by iteration.  `famLiftN d F : kUFam (d + k) u` -- the level *)
(* adds on the LEFT, so famLiftK (famLiftN d F) IS famLiftN (S d) F,     *)
(* definitionally, which is the whole point.                            *)
(* ------------------------------------------------------------------ *)

Fixpoint famLiftN (d : nat) {k u} (F : kUFam k u) : kUFam (d + k) u :=
  match d with
  | 0 => F
  | S d' => famLiftK (famLiftN d' F)
  end.

Lemma famLiftN_S d {k u} (F : kUFam k u) :
  famLiftN (S d) F = famLiftK (famLiftN d F).
Proof. reflexivity. Qed.

Fixpoint elLiftN (d : nat) {k u} (F : kUFam k u) w (x : kElAt F w)
  : kElAt (famLiftN d F) w :=
  match d with
  | 0 => x
  | S d' => elLift (famLiftN d' F) w (elLiftN d' F w x)
  end.

Fixpoint elUnliftN (d : nat) {k u} (F : kUFam k u) w
  : kElAt (famLiftN d F) w -> kElAt F w :=
  match d with
  | 0 => fun y => y
  | S d' => fun y => elUnliftN d' F w (elUnlift (famLiftN d' F) w y)
  end.

(* the lift preserves the equality of families, at every depth *)
Lemma famLiftN_ceq d {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> kceq (kAt (famLiftN d F)) (kAt (famLiftN d F')).
Proof.
  intros H; induction d as [| d IH]; [exact H | apply famLiftK_ceq; exact IH].
Qed.

Lemma elLiftN_eq d {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kceq (kAt F) (kAt F') -> kEqAt F w x F' w' x' ->
  kEqAt (famLiftN d F) w (elLiftN d F w x) (famLiftN d F') w' (elLiftN d F' w' x').
Proof.
  intros He; revert w x w' x'.
  induction d as [| d IH]; intros w x w' x' H; [exact H |].
  apply elLift_eq; [apply famLiftN_ceq; exact He | apply IH; exact H].
Qed.

Lemma elUnliftN_eq d {k u u'} (F : kUFam k u) w y (F' : kUFam k u') w' y' :
  kceq (kAt F) (kAt F') ->
  kEqAt (famLiftN d F) w y (famLiftN d F') w' y' ->
  kEqAt F w (elUnliftN d F w y) F' w' (elUnliftN d F' w' y').
Proof.
  intros He; revert w y w' y'.
  induction d as [| d IH]; intros w y w' y' H; [exact H |].
  apply IH; apply elUnlift_eq; [apply famLiftN_ceq; exact He | exact H].
Qed.

Lemma elUnliftN_elLiftN d {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (elUnliftN d F w (elLiftN d F w x)) F w x.
Proof.
  revert w x; induction d as [| d IH]; intros w x; [apply kEqAt_refl |].
  eapply kEqAt_trans; [exact (famAtSelf F) | | exact (IH w x)].
  apply (elUnliftN_eq d F w _ F w (elLiftN d F w x));
    [ exact (famAtSelf F) | apply elUnlift_elLift ].
Qed.

Lemma elLiftN_elUnliftN d {k u} (F : kUFam k u) w (y : kElAt (famLiftN d F) w) :
  kEqAt (famLiftN d F) w (elLiftN d F w (elUnliftN d F w y)) (famLiftN d F) w y.
Proof.
  revert w y; induction d as [| d IH]; intros w y; [apply kEqAt_refl |].
  eapply kEqAt_trans;
    [ exact (famAtSelf (famLiftN (S d) F))
    | apply elLift_eq;
        [ exact (famAtSelf (famLiftN d F))
        | exact (IH w (elUnlift (famLiftN d F) w y)) ]
    | apply elLift_elUnlift ].
Qed.

(* ------------------------------------------------------------------ *)
(* The d-fold commutations, which is what a former at an annotated     *)
(* level asks for: natFam (d + k) and the d-fold lift of natFam k are   *)
(* equal.                                                             *)
(* ------------------------------------------------------------------ *)

Lemma famLiftN_natFam d k :
  kceq (kAt (famLiftN d (natFam k))) (kAt (natFam (d + k))).
Proof.
  induction d as [| d IH]; [apply famAtSelf |].
  eapply ktrU;
    [ exact (famAtWf (famLiftN (S d) (natFam k)))
    | exact (famAtWf (famLiftK (natFam (d + k))))
    | exact (famAtWf (natFam (S (d + k))))
    | apply famLiftK_ceq; exact IH
    | apply famLiftK_natFam ].
Qed.

Lemma famLiftN_propFam d k :
  kceq (kAt (famLiftN d (propFam k))) (kAt (propFam (d + k))).
Proof.
  induction d as [| d IH]; [apply famAtSelf |].
  eapply ktrU;
    [ exact (famAtWf (famLiftN (S d) (propFam k)))
    | exact (famAtWf (famLiftK (propFam (d + k))))
    | exact (famAtWf (propFam (S (d + k))))
    | apply famLiftK_ceq; exact IH
    | apply famLiftK_propFam ].
Qed.

Lemma famLiftN_prfFam d k p Hp H :
  kceq (kAt (famLiftN d (prfFam k p Hp H))) (kAt (prfFam (d + k) p Hp H)).
Proof.
  induction d as [| d IH]; [apply famAtSelf |].
  eapply ktrU;
    [ exact (famAtWf (famLiftN (S d) (prfFam k p Hp H)))
    | exact (famAtWf (famLiftK (prfFam (d + k) p Hp H)))
    | exact (famAtWf (prfFam (S (d + k)) p Hp H))
    | apply famLiftK_ceq; exact IH
    | apply famLiftK_prfFam ].
Qed.

(* ------------------------------------------------------------------ *)
(* Moving a family along an equality of LEVELS.                       *)
(*                                                                    *)
(* The interpretation reads a former at its annotation, which the Pi    *)
(* and Sigma clauses present as `d + j`; an inversion that hands back   *)
(* the components' level j and the gap d therefore has to say what the  *)
(* family in hand is, and the two sides of that equation live at levels *)
(* that are only PROVABLY equal.  One eq_rect does it, and it           *)
(* disappears as soon as the equation is destructed -- which is what    *)
(* every consumer does first.                                          *)
(* ------------------------------------------------------------------ *)

Definition lvlCast {k k' u} (E : k = k') (F : kUFam k u) : kUFam k' u :=
  eq_rect k (fun z => kUFam z u) F k' E.

Lemma lvlCast_refl {k u} (F : kUFam k u) : lvlCast (@eq_refl nat k) F = F.
Proof. reflexivity. Qed.

(* At a reflexive equation the cast is the identity -- by UIP at nat, which
   is decidable, so this costs no axiom.  It is what a consumer uses after it
   has learnt that the two levels agree but not that the proof is eq_refl. *)
Lemma lvlCast_irr {k u} (E : k = k) (F : kUFam k u) : lvlCast E F = F.
Proof.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec E eq_refl); reflexivity.
Qed.

(* An element travels with its family, and everything the decoder says about
   an element -- the family's own equality, the coercion along an equality of
   codes -- travels with it.  Each of these is `destruct E` and nothing else,
   and each disappears the moment a consumer destructs the equation. *)
Definition lvlCastEl {k k' u} (E : k = k') (F : kUFam k u) w (x : kElAt F w)
  : kElAt (lvlCast E F) w :=
  match E as e in _ = z return kElAt (lvlCast (k' := z) e F) w with
  | eq_refl => x
  end.

Lemma lvlCast_ceq {k k' u u'} (E : k = k') (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> kceq (kAt (lvlCast E F)) (kAt (lvlCast E F')).
Proof. destruct E; exact (fun H => H). Defined.

Lemma lvlCastEl_eq {k k' u u'} (E : k = k') (F : kUFam k u) w x
  (F' : kUFam k u') w' x' :
  kEqAt F w x F' w' x' ->
  kEqAt (lvlCast E F) w (lvlCastEl E F w x) (lvlCast E F') w' (lvlCastEl E F' w' x').
Proof. destruct E; exact (fun H => H). Qed.

Lemma lvlCastEl_moveTo {k k' u u'} (E : k = k') (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) w0 (Hr : reds w0 w) :
  moveTo (lvlCast E F) (lvlCast E F') (lvlCast_ceq E F F' P) w
    (lvlCastEl E F w x) w0 Hr
  = lvlCastEl E F' w0 (moveTo F F' P w x w0 Hr).
Proof. destruct E; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* A COMPONENT AT THE FORMER'S LEVEL.                                  *)
(*                                                                    *)
(* In v2 a binder-former's two components live at INDEPENDENT levels    *)
(* below the annotation -- `pi k A B` with A : U_i, B : U_j and only    *)
(* i <= k, j <= k (`Typing/Rules.v`'s t_pi; the W of Aczel sets needs   *)
(* exactly this, its label type being one level above its branching     *)
(* type).  A Pi-code, though, is built from component codes at ITS OWN  *)
(* level, so each component is read at its own level and then lifted    *)
(* the remaining way.  The gap is a number `d` with `d + i = k`: the    *)
(* sum cannot be written as the level in the conclusion of a clause,    *)
(* because that level is the syntax's annotation, so the equation is    *)
(* carried and `lvlCast` consumes it.  Everything below is one line.    *)
(*                                                                    *)
(* The cast costs nothing downstream: every operation of the element    *)
(* layer -- piApp, sigFst, wSup, wRecS -- is generic in the component   *)
(* families, so it does not care that one of them is a cast.           *)
(* ------------------------------------------------------------------ *)

Definition lvlUncastEl {k k' u} (E : k = k') (F : kUFam k u) w
  (x : kElAt (lvlCast E F) w) : kElAt F w :=
  match E as e in _ = z return kElAt (lvlCast (k' := z) e F) w -> kElAt F w with
  | eq_refl => fun y => y
  end x.

Definition upF {i u} (d k : nat) (E : d + i = k) (F : kUFam i u) : kUFam k u :=
  lvlCast E (famLiftN d F).

Definition upEl {i u} (d k : nat) (E : d + i = k) (F : kUFam i u) w (x : kElAt F w)
  : kElAt (upF d k E F) w :=
  lvlCastEl E (famLiftN d F) w (elLiftN d F w x).

Definition dnEl {i u} (d k : nat) (E : d + i = k) (F : kUFam i u) w
  (x : kElAt (upF d k E F) w) : kElAt F w :=
  elUnliftN d F w (lvlUncastEl E (famLiftN d F) w x).

Lemma upF_ceq {i u u'} (d k : nat) (E : d + i = k) (F : kUFam i u) (F' : kUFam i u') :
  kceq (kAt F) (kAt F') -> kceq (kAt (upF d k E F)) (kAt (upF d k E F')).
Proof. intros H; apply lvlCast_ceq; apply famLiftN_ceq; exact H. Qed.

Lemma upEl_eq {i u u'} (d k : nat) (E : d + i = k) (F : kUFam i u) w x
  (F' : kUFam i u') w' x' :
  kceq (kAt F) (kAt F') -> kEqAt F w x F' w' x' ->
  kEqAt (upF d k E F) w (upEl d k E F w x) (upF d k E F') w' (upEl d k E F' w' x').
Proof.
  intros He H; apply lvlCastEl_eq; apply elLiftN_eq; [exact He | exact H].
Qed.

Lemma dnEl_eq {i u u'} (d k : nat) (E : d + i = k) (F : kUFam i u) w x
  (F' : kUFam i u') w' x' :
  kceq (kAt F) (kAt F') ->
  kEqAt (upF d k E F) w x (upF d k E F') w' x' ->
  kEqAt F w (dnEl d k E F w x) F' w' (dnEl d k E F' w' x').
Proof.
  revert x x'; destruct E; cbn; intros x x' He H.
  apply elUnliftN_eq; [exact He | exact H].
Qed.

Lemma dnEl_upEl {i u} (d k : nat) (E : d + i = k) (F : kUFam i u) w (x : kElAt F w) :
  kEqAt F w (dnEl d k E F w (upEl d k E F w x)) F w x.
Proof. destruct E; cbn; apply elUnliftN_elLiftN. Qed.

Lemma upEl_dnEl {i u} (d k : nat) (E : d + i = k) (F : kUFam i u) w
  (x : kElAt (upF d k E F) w) :
  kEqAt (upF d k E F) w (upEl d k E F w (dnEl d k E F w x)) (upF d k E F) w x.
Proof. revert x; destruct E; cbn; intros x; apply elLiftN_elUnliftN. Qed.

(* and the gap is irrelevant: two presentations of the same component at the
   same level agree, by UIP at nat *)
Lemma upF_irr {i u} (d : nat) (E : d + i = d + i) (F : kUFam i u) :
  upF d (d + i) E F = famLiftN d F.
Proof. apply lvlCast_irr. Qed.

(* One component, presented at TWO levels at once: the branching type of a W
   sits at the W's level in the tree code and at the induction hypothesis's
   level in the step's Pi, and `t_wrec` constrains both separately (j <= k and
   j <= n).  An index therefore has to travel down to its own level and back
   up to the other. *)
Definition reLvl {j S} (G : kUFam j S) (d k : nat) (E : d + j = k)
  (d' k' : nat) (E' : d' + j = k') v (y : kElAt (upF d' k' E' G) v)
  : kElAt (upF d k E G) v :=
  upEl d k E G v (dnEl d' k' E' G v y).

Lemma reLvl_eq {j S S'} (G : kUFam j S) (G' : kUFam j S') d k E d' k' E' v y v' y' :
  kceq (kAt G) (kAt G') ->
  kEqAt (upF d' k' E' G) v y (upF d' k' E' G') v' y' ->
  kEqAt (upF d k E G) v (reLvl G d k E d' k' E' v y)
        (upF d k E G') v' (reLvl G' d k E d' k' E' v' y').
Proof.
  intros Q H; apply upEl_eq; [exact Q | apply dnEl_eq; [exact Q | exact H]].
Qed.

(* The gap's equation is irrelevant: two presentations of one component at one
   level agree, by UIP at nat.  Inversion produces its own equation, and this
   is what reconciles it with the clause's. *)
Lemma upF_pirr {i u} (d k : nat) (E E' : d + i = k) (F : kUFam i u) :
  upF d k E F = upF d k E' F.
Proof.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec E E'); reflexivity.
Qed.
