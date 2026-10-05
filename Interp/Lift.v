From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The universe lift on families and on their elements: blueprint Lemma 7.7
   in the form the interpretation consumes.

   `up (univ k) A` erases to `er A`, so the realiser is UNCHANGED by the
   lift -- which is why it costs nothing at layer 1 and everything at layer 2.
   What changes is the level of the codes: a level-k code becomes a
   level-(S k) code by Codes/Lift.v's `liftCode`, and its decoding travels
   along `liftEl`.

   One wrinkle, as in v1: `kAcc` is computed from `uf_ty`, and the lifted
   family's `uf_ty` is at level S k, so `kAcc (famLiftK F)` is a DIFFERENT
   accessibility proof and hence a different node.  The family's own coherence
   (`famTo`) moves the element from the node the lift produces to the node the
   lifted family's canonical instance lives at.

   What is NOT here is v1's `liftEl_to`, the lift/transport naturality square:
   in v2 it is a corollary of `xto_coh`, exported by Codes/Lift.v as
   `liftEl_xto`, and restated below for families. *)

Definition famLiftK {k u} (F : kUFam k u) : kUFam (S k) u :=
  famLift k k (S k) (Nat.le_succ_diag_r k) u F.

Lemma famLiftK_c {k u} (F : kUFam k u) v h pf :
  uf_c (famLiftK F) v h pf = liftCode k (uf_c F v h pf) (uf_wf F v h pf).
Proof. reflexivity. Qed.

(* the decoding travels with the code: this is what the lift of a TERM is *)
Definition elLift {k u} (F : kUFam k u) w (x : kElAt F w) : kElAt (famLiftK F) w :=
  famTo (famLiftK F) u (kAcc F) (evalAg_refl u) w
    (liftEl k (kAt F) (famAtWf F) w x).

(* the lift preserves the equality of codes, and of elements *)
Lemma famLiftK_ceq {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> kceq (kAt (famLiftK F)) (kAt (famLiftK F')).
Proof.
  intros H.
  apply (famCeq_of (famLiftK F) (famLiftK F') u (kAcc F) (evalAg_refl u)
           u' (kAcc F') (evalAg_refl u')).
  exact (liftCode_ceq k (kAt F) (kAt F') (famAtWf F) (famAtWf F') H).
Qed.

Lemma elLift_eq {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kceq (kAt F) (kAt F') -> kEqAt F w x F' w' x' ->
  kEqAt (famLiftK F) w (elLift F w x) (famLiftK F') w' (elLift F' w' x').
Proof.
  intros He H.
  apply (famTo_eqX (famLiftK F) u (kAcc F) (evalAg_refl u) w _
           (famLiftK F') u' (kAcc F') (evalAg_refl u') w' _).
  - exact (liftCode_ceq k (kAt F) (kAt F') (famAtWf F) (famAtWf F') He).
  - exact (liftEl_cel k (kAt F) (kAt F') (famAtWf F) (famAtWf F') He w x w' x' H).
Qed.

Lemma elLift_refl {k u} (F : kUFam k u) w x :
  kEqAt (famLiftK F) w (elLift F w x) (famLiftK F) w (elLift F w x).
Proof. apply elLift_eq; [exact (famAtSelf F) | exact (kEqAt_refl F w x)]. Qed.

(* ------------------------------------------------------------------ *)
(* ONE STEP DOWN.                                                      *)
(*                                                                    *)
(* `SMor` is an equivalence, so an element of a lifted family comes     *)
(* back: `famFrom` into the instance the lift produced, `unliftEl`      *)
(* there, and the two round trips survive.  The eliminators need this,  *)
(* because a term at an annotated level d + j is read in a d-fold lift  *)
(* of the level-j family while its elimination happens at level j.      *)
(*                                                                    *)
(* In v1 this half lived in `Interp/LiftN.v`, because it needed         *)
(* `famFrom_famTo`, which v1 could only prove after `Interp/SigEl.v`    *)
(* (~500 s).  In v2 both round trips are in `Interp/Fam.v`, so the      *)
(* file split is no longer forced and only the thematic one remains.    *)
(* ------------------------------------------------------------------ *)

Definition elUnlift {k u} (F : kUFam k u) w (y : kElAt (famLiftK F) w) : kElAt F w :=
  unliftEl k (kAt F) (famAtWf F) w
    (famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y).

Lemma elUnlift_eq {k u u'} (F : kUFam k u) w y (F' : kUFam k u') w' y' :
  kceq (kAt F) (kAt F') ->
  kEqAt (famLiftK F) w y (famLiftK F') w' y' ->
  kEqAt F w (elUnlift F w y) F' w' (elUnlift F' w' y').
Proof.
  intros He H.
  exact (unliftEl_cel k (kAt F) (kAt F') (famAtWf F) (famAtWf F') He w _ w' _
           (famFrom_eqX (famLiftK F) u (kAcc F) (evalAg_refl u) w y
              (famLiftK F') u' (kAcc F') (evalAg_refl u') w' y'
              (famLiftK_ceq F F' He) H)).
Qed.

Lemma elUnlift_elLift {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (elUnlift F w (elLift F w x)) F w x.
Proof.
  unfold elUnlift, elLift.
  eapply ktrE;
    [ exact (famAtWf F) | exact (famAtWf F) | exact (famAtWf F) | exact (famAtSelf F)
    | exact (unliftEl_cel k (kAt F) (kAt F) (famAtWf F) (famAtWf F) (famAtSelf F)
               w _ w _
               (famFrom_famTo (famLiftK F) u (kAcc F) (evalAg_refl u) w
                  (liftEl k (kAt F) (famAtWf F) w x)))
    | exact (unliftEl_liftEl k (kAt F) (famAtWf F) w x) ].
Qed.

Lemma elLift_elUnlift {k u} (F : kUFam k u) w (y : kElAt (famLiftK F) w) :
  kEqAt (famLiftK F) w (elLift F w (elUnlift F w y)) (famLiftK F) w y.
Proof.
  unfold elUnlift, elLift.
  eapply ktrE;
    [ exact (famAtWf (famLiftK F)) | exact (famAtWf (famLiftK F))
    | exact (famAtWf (famLiftK F)) | exact (famAtSelf (famLiftK F))
    | exact (famTo_eq (famLiftK F) u (kAcc F) (evalAg_refl u) w _
               u (kAcc F) (evalAg_refl u) w _
               (liftEl_unliftEl k (kAt F) (famAtWf F) w
                  (famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y)))
    | exact (famTo_famFrom (famLiftK F) u (kAcc F) (evalAg_refl u) w y) ].
Qed.

(* ------------------------------------------------------------------ *)
(* The lift commutes with the component-free formers.  Each of these is *)
(* the equality of two codes with the same clause, so all it asks for   *)
(* is the layer-1 equality of the shadows -- and the lift does not move *)
(* the shadow.                                                         *)
(* ------------------------------------------------------------------ *)

Lemma famLiftK_natFam k :
  kceq (kAt (famLiftK (natFam k))) (kAt (natFam (S k))).
Proof.
  exists (S k); apply eqty_nat; apply eval_whnf; exact whnf_nat.
Qed.

Lemma famLiftK_propFam k :
  kceq (kAt (famLiftK (propFam k))) (kAt (propFam (S k))).
Proof.
  exists (S k); apply eqty_prop; apply eval_whnf; exact whnf_prop.
Qed.

Lemma famLiftK_prfFam k p Hp H :
  kceq (kAt (famLiftK (prfFam k p Hp H))) (kAt (prfFam (S k) p Hp H)).
Proof.
  split; [| split; exact (fun h => h)].
  exists (S k); eapply eqty_prf;
    [ apply eval_whnf; exact (whnf_prf p)
    | apply eval_whnf; exact (whnf_prf p)
    | exact Hp ].
Qed.
