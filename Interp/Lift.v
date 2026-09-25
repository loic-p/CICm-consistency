From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels Codes.Lift Codes.LiftIso.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The universe lift on families and on their elements: blueprint Lemma 7.7
   in the form the interpretation consumes.

   `up (univ k) A` erases to `er A`, so the realiser is UNCHANGED by the
   lift -- the lift is invisible on realisers, which is exactly why it costs
   nothing at layer 1 and everything at layer 2.  What changes is the level
   of the codes: a level-k code becomes a level-(S k) code by Codes/Lift.v's
   `liftCode`, and its decoding travels along `liftEl`.

   One wrinkle: `kAcc` is computed from `uf_ty`, and the lifted family's
   uf_ty is at level S k, so `kAcc (famLiftK F)` is a DIFFERENT accessibility
   proof from `kAcc F` and hence a different node of the hierarchy.  The
   family's own coherence (famTo) is what moves the element from the node
   the lift produces to the node the lifted family's canonical instance
   lives at. *)

Definition famLiftK {k u} (F : kUFam k u) : kUFam (S k) u :=
  famLift k k (S k) (Nat.le_succ_diag_r k) u F.

Lemma famLiftK_c {k u} (F : kUFam k u) v h pf :
  uf_c (famLiftK F) v h pf = liftCode k (rk v h) (uf_c F v h pf).
Proof. reflexivity. Qed.

Definition elLift {k u} (F : kUFam k u) w (x : kElAt F w) : kElAt (famLiftK F) w :=
  famTo (famLiftK F) u (kAcc F) (evalAg_refl u) w
    (liftEl k (rk u (kAcc F)) (kAt F) w x).

Lemma elLift_eq {k u} (F : kUFam k u) w x w' x' :
  kEqAt F w x w' x' -> kEqAt (famLiftK F) w (elLift F w x) w' (elLift F w' x').
Proof.
  intros H; apply famTo_eq; apply (liftEl_eq k (rk u (kAcc F)) (kAt F)); exact H.
Qed.

(* The lift preserves isomorphism of FAMILIES, not just of codes: move both
   sides to the instance the lifted family's own accessibility proof names
   (that proof is computed from uf_ty, which the lift changes), then apply
   liftIso. *)
Lemma famLiftK_iso {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  iso (kAt F) (kAt F') -> iso (kAt (famLiftK F)) (kAt (famLiftK F')).
Proof.
  intros H; apply liftIso.
  eapply ciso_trans; [apply uf_coh |].
  eapply ciso_trans; [exact H | apply uf_coh].
Qed.
