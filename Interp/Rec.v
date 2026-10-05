From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.Univ Interp.Env Interp.Elem.
From Stdlib Require Import Arith Lia.

(* The semantic recursor: large elimination of N.

   The recursion is on the NUMERAL the scrutinee's realiser carries, not on
   any derivation -- the blueprint's warning.  Each step does the same two
   things: move the value to the motive instance the goal asks for (the two
   instances are EQUAL, because their arguments are related), and expand the
   realiser along the recursor's computation rule.  That is `moveTo`.

   Nothing here mentions the level of the motive, which is where the large
   elimination lives: the motive is at Typek for an arbitrary k.

   Against v1: the motive's input is `cohC`, "related scrutinees give EQUAL
   motive instances", where v1 had an `iso`.  Nothing else in the file
   changes -- which is the point of the heterogeneous equality: `moveTo` and
   `moveTo_rel` have the same shape whether they carry a transport or an
   equality, so the recursor never sees the difference. *)

Section SemRec.
  (* k is the motive's level; k0 is the level at which the scrutinee's family
     sits.  They need not agree: the scrutinee's own derivation puts N at
     level 0, while the step function's Pi-type puts it at the motive's
     level, and natE/natIdx move a semantic natural between the two. *)
  Context (k k0 : nat).

  (* The motive, as a family for every scrutinee value, with the coherence
     that related scrutinees give equal motive instances. *)
  Context (SC : etm -> etm).
  Context (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m)).
  Context (cohC : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
                    kceq (kAt (FC m x)) (kAt (FC m' x'))).

  (* The two branches.  The step function is the semantic content of
     s : nrec_step C, i.e. the result of applying its value twice. *)
  Context (zr sr : etm).
  Context (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr).
  Context (step : forall m (x : kElAt (natFam k0) m) w (y : kElAt (FC m x) w),
             kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w)).

  (* Relatedness of the scrutinee values the two clauses compare. *)
  Lemma rec_zero_eq m (e : NatAt 0 m) :
    kEqAt (natFam k0) ezero (natE 0 NatAt_zero) (natFam k0) m (natE 0 e).
  Proof. apply natE_eq. Qed.

  Lemma rec_succ_eq j m (e : NatAt (S j) m) :
    kEqAt (natFam k0) (esucc (NatAt_pred j m e))
            (natSucc (natE j (NatAt_pred_at j m e)))
          (natFam k0) m (natE (S j) e).
  Proof.
    apply natEq_iff; split; [reflexivity |].
    apply Rel_nat_intro; [apply gt_nat | apply ev_nat |].
    eapply np_succ;
      [apply ev_succ | exact (NatAt_pred_ev j m e) |].
    exact (NatAt_NatPer j _ _ (NatAt_pred_at j m e) (NatAt_pred_at j m e)).
  Qed.

  Fixpoint semrec (j : nat) : forall (m : etm) (e : NatAt j m),
      kElAt (FC m (natE j e)) (enatrec zr sr m) :=
    match j as j0 return forall (m : etm) (e : NatAt j0 m),
        kElAt (FC m (natE j0 e)) (enatrec zr sr m) with
    | 0 => fun m e =>
        moveTo (FC ezero (natE 0 NatAt_zero)) (FC m (natE 0 e))
          (cohC _ _ _ _ (rec_zero_eq m e)) zr xz
          (enatrec zr sr m) (reds_rec_zero zr sr m e)
    | S j0 => fun m e =>
        moveTo (FC (esucc (NatAt_pred j0 m e))
                   (natSucc (natE j0 (NatAt_pred_at j0 m e))))
               (FC m (natE (S j0) e))
          (cohC _ _ _ _ (rec_succ_eq j0 m e))
          (eapp (eapp sr (NatAt_pred j0 m e)) (enatrec zr sr (NatAt_pred j0 m e)))
          (step (NatAt_pred j0 m e) (natE j0 (NatAt_pred_at j0 m e))
                (enatrec zr sr (NatAt_pred j0 m e))
                (semrec j0 (NatAt_pred j0 m e) (NatAt_pred_at j0 m e)))
          (enatrec zr sr m)
          (reds_rec_succ zr sr m (NatAt_pred j0 m e) (NatAt_pred_ev j0 m e))
    end.
End SemRec.

(* ------------------------------------------------------------------ *)
(* The recursor respects relatedness: two instances whose branches are *)
(* related give related values.  Each case is the same three-step       *)
(* composition -- out of the motive instance the goal asks for, across  *)
(* the branch, and back in -- because every step of semrec is one       *)
(* `moveTo` and `moveTo_rel` says a moveTo is related to its input.     *)
(* ------------------------------------------------------------------ *)

Lemma semrec_rel (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (cohC : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
            kceq (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  (SC' : etm -> etm) (FC' : forall m (x : kElAt (natFam k0) m), kUFam k (SC' m))
  (cohC' : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             kceq (kAt (FC' m x)) (kAt (FC' m' x')))
  (zr' sr' : etm) (xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) zr')
  (step' : forall m x w (y : kElAt (FC' m x) w),
             kElAt (FC' (esucc m) (natSucc x)) (eapp (eapp sr' m) w))
  (Hz : kRel (FC ezero (natE 0 NatAt_zero)) zr xz
             (FC' ezero (natE 0 NatAt_zero)) zr' xz')
  (Hstep : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             forall w y w' y', kRel (FC m x) w y (FC' m' x') w' y' ->
             kRel (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w) (step m x w y)
                  (FC' (esucc m') (natSucc x')) (eapp (eapp sr' m') w')
                  (step' m' x' w' y')) :
  forall j m (e : NatAt j m) m' (e' : NatAt j m'),
    kRel (FC m (natE j e)) (enatrec zr sr m) (semrec k k0 SC FC cohC zr sr xz step j m e)
         (FC' m' (natE j e')) (enatrec zr' sr' m')
         (semrec k k0 SC' FC' cohC' zr' sr' xz' step' j m' e').
Proof.
  induction j as [| j IH]; intros m e m' e'; cbn [semrec].
  - eapply kRel_trans; [apply kRel_sym, moveTo_rel |].
    eapply kRel_trans; [exact Hz | apply moveTo_rel].
  - eapply kRel_trans; [apply kRel_sym, moveTo_rel |].
    eapply kRel_trans; [| apply moveTo_rel].
    apply Hstep; [apply natE_eq | apply IH].
Qed.
