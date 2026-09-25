From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels Codes.Lift Codes.LiftIso.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift.
From Stdlib Require Import Arith Lia.

(* THE LEVEL LIFT, IN THE FORM THE LEVEL-ANNOTATED FORMERS NEED.

   Every type former carries the level it lives at, and its components may live
   at any level below it: `pi k A B` with A and B at level j <= k.  A Pi-code
   is built from component codes at ITS OWN level, so the two levels have to be
   reconciled, and there is only one way that keeps the universe lift's
   computation rules DEFINITIONAL:

     the value of `pi (d + j) A B` is the d-fold LIFT of the value of the
     level-j Pi-family built from the components.

   Then `up (d + j) (pi (d + j) A B)`, whose value is one more lift, and
   `pi (S d + j) A B`, whose value is the (S d)-fold lift, have literally the
   same value -- no commutation lemma for Pi or Sigma is needed, which matters:
   an isomorphism of two Pi-CODES asks for the naturality square of
   Codes/Iso.v's isoRefine, and that is the one piece of the hierarchy the
   interpretation has so far never had to build by hand.

   The component-free formers keep their canonical family at every level
   (natFam k, propFam k, prfFam k, univFam) and their commutation isomorphisms
   are the three one-liners at the bottom of this file: at nat, prop and prf,
   isoRefine asks for the layer-1 equality of the shadows and nothing else.

   The eliminators therefore have to bring a value back DOWN from a lifted
   family, which is possible because Codes/Lift.v's SMor is an EQUIVALENCE --
   sm_from with both round trips -- while Interp/Lift.v exports only the
   forward half.  Here is the other half, and its iteration.

   This file morally belongs in Interp/Lift.v; it sits here because
   famFrom_famTo needs Interp/SigEl.v, which takes ~500s to compile. *)

(* ------------------------------------------------------------------ *)
(* One step down.                                                     *)
(* ------------------------------------------------------------------ *)

Definition lvlSMor (k : nat) (b : Ord) :=
  nextOf (kU k) (kU (S k)) (kUEq k) (kUEq (S k)) (kOK k) (kOK (S k))
    (lvlUMor k) (ksym k) (ktrans k) (ksym (S k)) (ktrans (S k)) b
    (smorStage (kU k) (kU (S k)) (kUEq k) (kUEq (S k)) (kOK k) (kOK (S k))
       (lvlUMor k) (ksym k) (ktrans k) (ksym (S k)) (ktrans (S k)) b).

Definition unliftEl (k : nat) (b : Ord) (c : Code k b) (u : etm)
  (y : (kUst (S k) b).(StEl) (liftCode k b c) u) : (kUst k b).(StEl) c u :=
  sm_from (lvlSMor k b) c u y.

Lemma unliftEl_eq k b (c : Code k b) u y u' y' :
  (kUst (S k) b).(StEq) (liftCode k b c) u y u' y' ->
  (kUst k b).(StEq) c u (unliftEl k b c u y) u' (unliftEl k b c u' y').
Proof. exact (sm_from_eq (lvlSMor k b) c u y u' y'). Qed.

Lemma liftEl_unliftEl k b (c : Code k b) u y :
  (kUst (S k) b).(StEq) (liftCode k b c) u (liftEl k b c u (unliftEl k b c u y)) u y.
Proof. exact (sm_to_from (lvlSMor k b) c u y). Qed.

Lemma unliftEl_liftEl k b (c : Code k b) u x :
  (kUst k b).(StEq) c u (unliftEl k b c u (liftEl k b c u x)) u x.
Proof. exact (sm_from_to (lvlSMor k b) c u x). Qed.

(* the missing companion of famTo_eq *)
Lemma famFrom_eq {k u0} (F : kUFam k u0) v h pf w x w' x' :
  kEqAt F w x w' x' ->
  (kUst k (rk v h)).(StEq) (uf_c F v h pf) w (famFrom F v h pf w x)
                                           w' (famFrom F v h pf w' x').
Proof. apply (cto_eq (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Definition elUnlift {k u} (F : kUFam k u) w (y : kElAt (famLiftK F) w) : kElAt F w :=
  unliftEl k (rk u (kAcc F)) (kAt F) w
    (famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y).

Lemma elUnlift_eq {k u} (F : kUFam k u) w y w' y' :
  kEqAt (famLiftK F) w y w' y' -> kEqAt F w (elUnlift F w y) w' (elUnlift F w' y').
Proof.
  intros H.
  exact (unliftEl_eq k (rk u (kAcc F)) (kAt F) w _ w' _
           (famFrom_eq (famLiftK F) u (kAcc F) (evalAg_refl u) w y w' y' H)).
Qed.

Lemma elUnlift_elLift {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (elUnlift F w (elLift F w x)) w x.
Proof.
  unfold elUnlift, elLift.
  eapply kEqC_trans;
    [ exact (unliftEl_eq k (rk u (kAcc F)) (kAt F) w _ w _
               (famFrom_famTo (famLiftK F) u (kAcc F) (evalAg_refl u) w
                  (liftEl k (rk u (kAcc F)) (kAt F) w x))) |].
  exact (unliftEl_liftEl k (rk u (kAcc F)) (kAt F) w x).
Qed.

Lemma elLift_elUnlift {k u} (F : kUFam k u) w (y : kElAt (famLiftK F) w) :
  kEqAt (famLiftK F) w (elLift F w (elUnlift F w y)) w y.
Proof.
  unfold elUnlift, elLift.
  eapply kEqC_trans;
    [ exact (famTo_eq (famLiftK F) u (kAcc F) (evalAg_refl u) w _ w _
               (liftEl_unliftEl k (rk u (kAcc F)) (kAt F) w
                  (famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y))) |].
  exact (famTo_famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y).
Qed.

(* ------------------------------------------------------------------ *)
(* d steps, by iteration.  `famLiftN d F : kUFam (d + k) u` -- the level *)
(* adds on the LEFT, so famLiftK (famLiftN d F) IS famLiftN (S d) F,     *)
(* definitionally, which is the whole point.                            *)
(* ------------------------------------------------------------------ *)

Lemma kEqAt_refl_ {k u} (F : kUFam k u) w (x : kElAt F w) : kEqAt F w x w x.
Proof. exact (proj2 (kRel_same F w x w x) (kRel_refl F w x)). Qed.

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

Lemma elLiftN_eq d {k u} (F : kUFam k u) w x w' x' :
  kEqAt F w x w' x' ->
  kEqAt (famLiftN d F) w (elLiftN d F w x) w' (elLiftN d F w' x').
Proof.
  revert w x w' x'; induction d as [| d IH]; intros w x w' x' H; [exact H |].
  apply elLift_eq, IH, H.
Qed.

Lemma elUnliftN_eq d {k u} (F : kUFam k u) w y w' y' :
  kEqAt (famLiftN d F) w y w' y' ->
  kEqAt F w (elUnliftN d F w y) w' (elUnliftN d F w' y').
Proof.
  revert w y w' y'; induction d as [| d IH]; intros w y w' y' H; [exact H |].
  apply IH, elUnlift_eq, H.
Qed.

Lemma elUnliftN_elLiftN d {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (elUnliftN d F w (elLiftN d F w x)) w x.
Proof.
  revert w x; induction d as [| d IH]; intros w x; [apply kEqAt_refl_ |].
  eapply kEqC_trans;
    [ apply (elUnliftN_eq d F w _ w (elLiftN d F w x));
      apply elUnlift_elLift
    | apply IH ].
Qed.

Lemma elLiftN_elUnliftN d {k u} (F : kUFam k u) w (y : kElAt (famLiftN d F) w) :
  kEqAt (famLiftN d F) w (elLiftN d F w (elUnliftN d F w y)) w y.
Proof.
  revert w y; induction d as [| d IH]; intros w y; [apply kEqAt_refl_ |].
  eapply kEqC_trans;
    [ apply elLift_eq; apply (IH w (elUnlift (famLiftN d F) w y))
    | apply elLift_elUnlift ].
Qed.

(* and the lift preserves isomorphism of families, at every depth *)
Lemma famLiftN_iso d {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  iso (kAt F) (kAt F') -> iso (kAt (famLiftN d F)) (kAt (famLiftN d F')).
Proof.
  intros H; induction d as [| d IH]; [exact H | apply famLiftK_iso, IH].
Qed.

(* ------------------------------------------------------------------ *)
(* The lift commutes with the component-free formers.                 *)
(* ------------------------------------------------------------------ *)

Lemma famLiftK_natFam k :
  iso (kAt (famLiftK (natFam k))) (kAt (natFam (S k))).
Proof.
  exists (S k); apply eqty_nat; apply eval_whnf; exact whnf_nat.
Qed.

Lemma famLiftK_propFam k :
  iso (kAt (famLiftK (propFam k))) (kAt (propFam (S k))).
Proof.
  exists (S k); apply eqty_prop; apply eval_whnf; exact whnf_prop.
Qed.

Lemma famLiftK_prfFam k p Hp H :
  iso (kAt (famLiftK (prfFam k p Hp H))) (kAt (prfFam (S k) p Hp H)).
Proof.
  split; [| split; auto].
  exists (S k); eapply eqty_prf;
    [ apply eval_whnf; exact (whnf_prf p)
    | apply eval_whnf; exact (whnf_prf p)
    | exact Hp ].
Qed.

(* their d-fold versions, which is what a former at an annotated level asks
   for: natFam (d + k) and the d-fold lift of natFam k are isomorphic. *)
Lemma famLiftN_natFam d k :
  iso (kAt (famLiftN d (natFam k))) (kAt (natFam (d + k))).
Proof.
  induction d as [| d IH]; [apply iso_self |].
  eapply iso_trans; [apply (famLiftK_iso _ _ IH) | apply famLiftK_natFam].
Qed.

Lemma famLiftN_propFam d k :
  iso (kAt (famLiftN d (propFam k))) (kAt (propFam (d + k))).
Proof.
  induction d as [| d IH]; [apply iso_self |].
  eapply iso_trans; [apply (famLiftK_iso _ _ IH) | apply famLiftK_propFam].
Qed.

Lemma famLiftN_prfFam d k p Hp H :
  iso (kAt (famLiftN d (prfFam k p Hp H))) (kAt (prfFam (d + k) p Hp H)).
Proof.
  induction d as [| d IH]; [apply iso_self |].
  eapply iso_trans; [apply (famLiftK_iso _ _ IH) | apply famLiftK_prfFam].
Qed.

(* ------------------------------------------------------------------ *)
(* Moving a family along an equality of LEVELS.                       *)
(*                                                                    *)
(* The interpretation reads a former at its annotation, which the Pi   *)
(* and Sigma clauses present as `d + j`; an inversion that hands back  *)
(* the components' level j and the gap d therefore has to say what the *)
(* family in hand is, and the two sides of that isomorphism live at    *)
(* levels that are only PROVABLY equal.  One eq_rect does it, and it   *)
(* disappears as soon as the equation is destructed -- which is what   *)
(* every consumer does first.                                         *)
(* ------------------------------------------------------------------ *)

Definition lvlCast {k k' u} (E : k = k') (F : kUFam k u) : kUFam k' u :=
  eq_rect k (fun z => kUFam z u) F k' E.

Lemma lvlCast_refl {k u} (F : kUFam k u) : lvlCast (eq_refl k) F = F.
Proof. reflexivity. Qed.

(* At a reflexive equation the cast is the identity -- by UIP at nat, which is
   decidable, so this costs no axiom.  It is what a consumer uses after it has
   learnt that the two levels agree but not that the proof is eq_refl. *)
Lemma lvlCast_irr {k u} (E : k = k) (F : kUFam k u) : lvlCast E F = F.
Proof.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec E eq_refl); reflexivity.
Qed.

(* An element travels with its family, and everything the decoder says about an
   element -- the family's own equality, the transport along an isomorphism --
   travels with it.  Each of these is `destruct E` and nothing else, and each
   disappears the moment a consumer destructs the equation. *)
Definition lvlCastEl {k k' u} (E : k = k') (F : kUFam k u) w (x : kElAt F w)
  : kElAt (lvlCast E F) w :=
  match E as e in _ = z return kElAt (lvlCast (k' := z) e F) w with
  | eq_refl => x
  end.

Lemma lvlCast_iso {k k' u u'} (E : k = k') (F : kUFam k u) (F' : kUFam k u') :
  iso (kAt F) (kAt F') -> iso (kAt (lvlCast E F)) (kAt (lvlCast E F')).
Proof. destruct E; exact (fun H => H). Defined.

Lemma lvlCastEl_eq {k k' u} (E : k = k') (F : kUFam k u) w x w' x' :
  kEqAt F w x w' x' ->
  kEqAt (lvlCast E F) w (lvlCastEl E F w x) w' (lvlCastEl E F w' x').
Proof. destruct E; exact (fun H => H). Qed.

Lemma lvlCastEl_ctoK {k k' u u'} (E : k = k') (F : kUFam k u) (F' : kUFam k u')
  (P : iso (kAt F) (kAt F')) w (x : kElAt F w) :
  ctoK (kAt (lvlCast E F)) (kAt (lvlCast E F')) (lvlCast_iso E F F' P) w
       (lvlCastEl E F w x)
  = lvlCastEl E F' w (ctoK (kAt F) (kAt F') P w x).
Proof. destruct E; reflexivity. Qed.
