From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels Codes.Lift.
From Stdlib Require Import Arith Lia.

(* The level lift preserves the isomorphism relation.
   This is what `uf_coh` of a lifted family needs, and it is the last piece of
   blueprint Lemma 7.7.

   The statement has to carry the TRANSPORT as well as the relation: the Pi
   clause of isoRefine is stated in terms of hj_to, and the naturality square
   compares two composites of transports, so knowing only that the relation is
   preserved would not let either travel.  `PresH` below is therefore a
   conjunction -- the relation is preserved, and the square

       to2 o sm_to  =  sm_to o to1

   commutes up to the target stage's equality. *)

Definition PresH {s1 s1' s2 s2' : Stage} (m : SMor s1 s2) (m' : SMor s1' s2')
  (h1 : HJ s1 s1') (h2 : HJ s2 s2') : Prop :=
  (forall s s', hj_rel h1 s s' -> hj_rel h2 (sm_map m s) (sm_map m' s'))
  /\ (forall s s' (P1 : hj_rel h1 s s')
        (P2 : hj_rel h2 (sm_map m s) (sm_map m' s')) u x,
      s2'.(StEq) (sm_map m' s') u
        (hj_to h2 _ _ P2 u (sm_to m s u x))
        u (sm_to m' s' u (hj_to h1 s s' P1 u x))).

(* ------------------------------------------------------------------ *)
(* The combinators: each is a match or a projection, so each lemma is  *)
(* the corresponding case split.                                       *)
(* ------------------------------------------------------------------ *)

Lemma PresH_emptyL {s1' s2'} (m' : SMor s1' s2') :
  PresH SMor_empty m' (HJ_emptyL s1') (HJ_emptyL s2').
Proof. split; intros []. Qed.

Lemma PresH_emptyR {s1 s2} (m : SMor s1 s2) :
  PresH m SMor_empty (HJ_emptyR s1) (HJ_emptyR s2).
Proof. split; intros s []. Qed.

Lemma PresH_sum_L {a b c a2 b2 c2} (ma : SMor a a2) (mb : SMor b b2) (mc : SMor c c2)
  (hac : HJ a c) (hbc : HJ b c) (hac2 : HJ a2 c2) (hbc2 : HJ b2 c2) :
  PresH ma mc hac hac2 -> PresH mb mc hbc hbc2 ->
  PresH (SMor_sum a b a2 b2 ma mb) mc (HJ_sum_L hac hbc) (HJ_sum_L hac2 hbc2).
Proof.
  intros [R1 T1] [R2 T2]; split.
  - intros [s | s] s'; [apply R1 | apply R2].
  - intros [s | s] s' P1 P2 u x; [apply T1 | apply T2].
Qed.

Lemma PresH_sum_R {a b c a2 b2 c2} (ma : SMor a a2) (mb : SMor b b2) (mc : SMor c c2)
  (hab : HJ a b) (hac : HJ a c) (hab2 : HJ a2 b2) (hac2 : HJ a2 c2) :
  PresH ma mb hab hab2 -> PresH ma mc hac hac2 ->
  PresH ma (SMor_sum b c b2 c2 mb mc) (HJ_sum_R hab hac) (HJ_sum_R hab2 hac2).
Proof.
  intros [R1 T1] [R2 T2]; split.
  - intros s [s' | s']; [apply R1 | apply R2].
  - intros s [s' | s'] P1 P2 u x; [apply T1 | apply T2].
Qed.

Lemma PresH_sup_L {T F F2 c c2} (mf : forall p, SMor (F p) (F2 p)) (mc : SMor c c2)
  (h : forall p, HJ (F p) c) (h2 : forall p, HJ (F2 p) c2) :
  (forall p, PresH (mf p) mc (h p) (h2 p)) ->
  PresH (SMor_sup T F F2 mf) mc (HJ_sup_L h) (HJ_sup_L h2).
Proof.
  intros HP; split.
  - intros [p s] s'; apply (proj1 (HP p)).
  - intros [p s] s' P1 P2 u x; apply (proj2 (HP p)).
Qed.

Lemma PresH_sup_R {T' a a2 F' F2'} (ma : SMor a a2) (mf : forall p, SMor (F' p) (F2' p))
  (h : forall p', HJ a (F' p')) (h2 : forall p', HJ a2 (F2' p')) :
  (forall p', PresH ma (mf p') (h p') (h2 p')) ->
  PresH ma (SMor_sup T' F' F2' mf) (HJ_sup_R h) (HJ_sup_R h2).
Proof.
  intros HP; split.
  - intros s [p' s']; apply (proj1 (HP p')).
  - intros s [p' s'] P1 P2 u x; apply (proj2 (HP p')).
Qed.

Lemma PresH_restrL {a b c a2 b2 c2} (ma : SMor a a2) (mb : SMor b b2) (mc : SMor c c2)
  (H : HJ (Stage_sum a b) c) (H2 : HJ (Stage_sum a2 b2) c2) :
  PresH (SMor_sum a b a2 b2 ma mb) mc H H2 ->
  PresH ma mc (HJ_restrL H) (HJ_restrL H2).
Proof.
  intros [R T]; split.
  - intros s s'; apply (R (inl s) s').
  - intros s s' P1 P2 u x; apply (T (inl s) s').
Qed.

Lemma PresH_restrR {a b c a2 b2 c2} (ma : SMor a a2) (mb : SMor b b2) (mc : SMor c c2)
  (H : HJ a (Stage_sum b c)) (H2 : HJ a2 (Stage_sum b2 c2)) :
  PresH ma (SMor_sum b c b2 c2 mb mc) H H2 ->
  PresH ma mb (HJ_restrR H) (HJ_restrR H2).
Proof.
  intros [R T]; split.
  - intros s s'; apply (R s (inl s')).
  - intros s s' P1 P2 u x; apply (T s (inl s')).
Qed.

Lemma PresH_supL {T F F2 c c2} (p : Pred T)
  (mf : forall q, SMor (F q) (F2 q)) (mc : SMor c c2)
  (H : HJ (Stage_sup T F) c) (H2 : HJ (Stage_sup T F2) c2) :
  PresH (SMor_sup T F F2 mf) mc H H2 ->
  PresH (mf p) mc (HJ_supL p H) (HJ_supL p H2).
Proof.
  intros [R T0]; split.
  - intros s s'; apply (R (existT _ p s) s').
  - intros s s' P1 P2 u x; apply (T0 (existT _ p s) s').
Qed.

Lemma PresH_supR {T' a a2 F' F2'} (p' : Pred T')
  (ma : SMor a a2) (mf : forall q, SMor (F' q) (F2' q))
  (H : HJ a (Stage_sup T' F')) (H2 : HJ a2 (Stage_sup T' F2')) :
  PresH ma (SMor_sup T' F' F2' mf) H H2 ->
  PresH ma (mf p') (HJ_supR p' H) (HJ_supR p' H2).
Proof.
  intros [R T0]; split.
  - intros s s'; apply (R s (existT _ p' s')).
  - intros s s' P1 P2 u x; apply (T0 s (existT _ p' s')).
Qed.

(* ------------------------------------------------------------------ *)
(* The step.  One node of the hierarchy: the relation is isoRefine and  *)
(* the transport is toRefine, so preservation is a 6x6 case analysis,   *)
(* trivial off the diagonal and at every clause whose decoding mentions *)
(* neither the stage nor the universes.  Only r_univ and r_pi do any    *)
(* work, and only r_pi any real work.                                   *)
(* ------------------------------------------------------------------ *)

Section NextPres.
  Context (st1 st1' st2 st2' : Stage).
  Context (sm : SMor st1 st2) (sm' : SMor st1' st2').
  Context (U1 U2 : nat -> etm -> Type)
          (E1 : forall m u, U1 m u -> forall u', U1 m u' -> Prop)
          (E2 : forall m u, U2 m u -> forall u', U2 m u' -> Prop)
          (OK1 OK2 : nat -> Prop)
          (um : UMor U1 U2 E1 E2 OK1 OK2).

  (* The one extra law the universe morphism has to satisfy: its action on
     a code does not depend on WHICH proof of OK1 it is given.  A UMor's
     um_to takes that proof because the map may need to refute an
     out-of-range level, but the surviving branch never looks at it.  This
     is not derivable -- OK1 m is an arbitrary Prop -- but it holds for the
     level lift by the same case split that defines it. *)
  Context (um_irr : forall m u (o o' : OK1 m) (x : U1 m u),
              E1 m u x u x -> E2 m u (um_to um m u o x) u (um_to um m u o' x)).

  Context (good1 : StGood st1) (good1' : StGood st1')
          (good2 : StGood st2) (good2' : StGood st2').
  Context (sym1 : forall s, EqSym st1 s) (trans1 : forall s, EqTrans st1 s)
          (sym1' : forall s, EqSym st1' s) (trans1' : forall s, EqTrans st1' s)
          (sym2 : forall s, EqSym st2 s) (trans2 : forall s, EqTrans st2 s)
          (sym2' : forall s, EqSym st2' s) (trans2' : forall s, EqTrans st2' s).
  Context (h1 : HJ st1 st1') (h2 : HJ st2 st2').
  Context (HP : PresH sm sm' h1 h2).

  Local Notation mapR := (mapRefine st1 st2 sm U1 U2 E1 E2 OK1 OK2 um trans2).
  Local Notation mapR' := (mapRefine st1' st2' sm' U1 U2 E1 E2 OK1 OK2 um trans2').
  Local Notation eTo := (elTo st1 st2 sm U1 U2 E1 E2 OK1 OK2 um trans2).
  Local Notation eTo' := (elTo st1' st2' sm' U1 U2 E1 E2 OK1 OK2 um trans2').
  Local Notation iso1 := (isoRefine st1 st1' OK1 h1).
  Local Notation iso2 := (isoRefine st2 st2' OK2 h2).
  Local Notation to1 := (toRefine st1 st1' U1 OK1 h1).
  Local Notation to2 := (toRefine st2 st2' U2 OK2 h2).

  Let R1 := proj1 HP.
  Let T1 := proj2 HP.

  (* Corresponding arguments of the image domains come from corresponding
     arguments of the domains: the round trip through sm' is absorbed by the
     square, and the two isomorphism proofs by hj_irr. *)
  Lemma het_down (a : st1.(St)) (a' : st1'.(St)) (Ra : hj_rel h1 a a')
    u X u' X' :
    hjhet h2 (sm_map sm a) (sm_map sm' a') u X u' X' ->
    hjhet h1 a a' u (sm_from sm a u X) u' (sm_from sm' a' u' X').
  Proof.
    intros [P2 HE]; exists Ra.
    eapply (trans1' a'); [apply (sym1' a'); apply (sm_from_to sm') |].
    apply (sm_from_eq sm').
    eapply (trans2' (sm_map sm' a')); [| exact HE].
    eapply (trans2' (sm_map sm' a'));
      [ apply (sym2' (sm_map sm' a')); apply (T1 a a' Ra (R1 a a' Ra) u) |].
    eapply (trans2' (sm_map sm' a'));
      [ apply (hj_to_eq h2); apply (sm_to_from sm) | apply (hj_irr h2) ].
  Qed.


  (* Preservation of the relation.  Off the diagonal isoRefine is False and
     every other clause but Pi is literally the same proposition on both
     sides; at Pi the second conjunct is R1, the third is R1 after het_down,
     and the fourth is the hypothesis's own square, sandwiched between two
     instances of T1. *)
  Lemma isoPres {T T'} (r : Refine st1 OK1 T) (r' : Refine st1' OK1 T') :
    iso1 r r' -> iso2 (mapR r) (mapR' r').
  Proof.
    destruct r as [T0 e | T0 e | T0 p e H | T0 m ok e
                  | T0 A0 B0 e a ea b eb coh cL iL | T0 A0 B0 e a ea b eb coh cL iL | T0 N e s];
    destruct r' as [T0' e' | T0' e' | T0' p' e' H' | T0' m' ok' e'
                   | T0' A0' B0' e' a' ea' b' eb' coh' cL' iL' | T0' A0' B0' e' a' ea' b' eb' coh' cL' iL' | T0' N' e' s'];
    cbn [mapRefine isoRefine]; try (exact (fun i => match i with end));
      try (exact (fun i => i)).
    { intros [Ht [Ra [Rb Hsq]]].
    split; [exact Ht |].
    split; [exact (R1 a a' Ra) |].
    split.
    - intros u X u' X' Hhet; unfold mapB.
      apply R1; apply Rb; apply (het_down a a' Ra); exact Hhet.
    - intros u1 X1 u1' X1' Y1 Y1' Hy Hy' r2 s2 Q Q' v w.
      assert (Hy1 : hjhet h1 a a' u1 (sm_from sm a u1 X1) u1 (sm_from sm' a' u1 Y1))
        by (apply (het_down a a' Ra); exact Hy).
      assert (Hy1' : hjhet h1 a a' u1' (sm_from sm a u1' X1') u1' (sm_from sm' a' u1' Y1'))
        by (apply (het_down a a' Ra); exact Hy').
      pose proof (Rb u1 (sm_from sm a u1 X1) u1 (sm_from sm' a' u1 Y1) Hy1) as P1.
      pose proof (Rb u1' (sm_from sm a u1' X1') u1' (sm_from sm' a' u1' Y1') Hy1') as P1'.
      cbn [mapB mapCoh tr].
      eapply (trans2' (sm_map sm' (b' u1 (sm_from sm' a' u1 Y1))));
        [ apply (T1 (b u1 (sm_from sm a u1 X1)) (b' u1 (sm_from sm' a' u1 Y1)) P1 Q v) |].
      apply (sm_to_eq sm').
      eapply (trans1' (b' u1 (sm_from sm' a' u1 Y1)));
        [ exact (Hsq u1 (sm_from sm a u1 X1) u1' (sm_from sm a u1' X1')
                   (sm_from sm' a' u1 Y1) (sm_from sm' a' u1' Y1') Hy1 Hy1'
                   (sm_from_eq sm a u1 X1 u1' X1' r2)
                   (sm_from_eq sm' a' u1 Y1 u1' Y1' s2) P1 P1' v
                   (sm_from sm (b u1' (sm_from sm a u1' X1')) v w)) |].
      apply (tr_eq st1' _ _ (coh' u1 (sm_from sm' a' u1 Y1) u1' (sm_from sm' a' u1' Y1')
                               (sm_from_eq sm' a' u1 Y1 u1' Y1' s2))).
      apply (sym1' (b' u1' (sm_from sm' a' u1' Y1'))).
      eapply (trans1' (b' u1' (sm_from sm' a' u1' Y1')));
        [| apply (sm_from_to sm')].
      apply (sm_from_eq sm').
      eapply (trans2' (sm_map sm' (b' u1' (sm_from sm' a' u1' Y1'))));
        [ apply (hj_to_eq h2); apply (sym2 (sm_map sm (b u1' (sm_from sm a u1' X1'))));
          apply (sm_to_from sm) |].
      apply (T1 (b u1' (sm_from sm a u1' X1')) (b' u1' (sm_from sm' a' u1' Y1')) P1' Q' v). }
    (* Sigma: same clause, same data, same proof. *)
    { intros [Ht [Ra [Rb Hsq]]].
    split; [exact Ht |].
    split; [exact (R1 a a' Ra) |].
    split.
    - intros u X u' X' Hhet; unfold mapB.
      apply R1; apply Rb; apply (het_down a a' Ra); exact Hhet.
    - intros u1 X1 u1' X1' Y1 Y1' Hy Hy' r2 s2 Q Q' v w.
      assert (Hy1 : hjhet h1 a a' u1 (sm_from sm a u1 X1) u1 (sm_from sm' a' u1 Y1))
        by (apply (het_down a a' Ra); exact Hy).
      assert (Hy1' : hjhet h1 a a' u1' (sm_from sm a u1' X1') u1' (sm_from sm' a' u1' Y1'))
        by (apply (het_down a a' Ra); exact Hy').
      pose proof (Rb u1 (sm_from sm a u1 X1) u1 (sm_from sm' a' u1 Y1) Hy1) as P1.
      pose proof (Rb u1' (sm_from sm a u1' X1') u1' (sm_from sm' a' u1' Y1') Hy1') as P1'.
      cbn [mapB mapCoh tr].
      eapply (trans2' (sm_map sm' (b' u1 (sm_from sm' a' u1 Y1))));
        [ apply (T1 (b u1 (sm_from sm a u1 X1)) (b' u1 (sm_from sm' a' u1 Y1)) P1 Q v) |].
      apply (sm_to_eq sm').
      eapply (trans1' (b' u1 (sm_from sm' a' u1 Y1)));
        [ exact (Hsq u1 (sm_from sm a u1 X1) u1' (sm_from sm a u1' X1')
                   (sm_from sm' a' u1 Y1) (sm_from sm' a' u1' Y1') Hy1 Hy1'
                   (sm_from_eq sm a u1 X1 u1' X1' r2)
                   (sm_from_eq sm' a' u1 Y1 u1' Y1' s2) P1 P1' v
                   (sm_from sm (b u1' (sm_from sm a u1' X1')) v w)) |].
      apply (tr_eq st1' _ _ (coh' u1 (sm_from sm' a' u1 Y1) u1' (sm_from sm' a' u1' Y1')
                               (sm_from_eq sm' a' u1 Y1 u1' Y1' s2))).
      apply (sym1' (b' u1' (sm_from sm' a' u1' Y1'))).
      eapply (trans1' (b' u1' (sm_from sm' a' u1' Y1')));
        [| apply (sm_from_to sm')].
      apply (sm_from_eq sm').
      eapply (trans2' (sm_map sm' (b' u1' (sm_from sm' a' u1' Y1'))));
        [ apply (hj_to_eq h2); apply (sym2 (sm_map sm (b u1' (sm_from sm a u1' X1'))));
          apply (sm_to_from sm) |].
      apply (T1 (b u1' (sm_from sm a u1' X1')) (b' u1' (sm_from sm' a' u1' Y1')) P1' Q' v). }
  Qed.

  (* A Pi-element is related to a self-related one as soon as it agrees with
     it pointwise: the two heterogeneous clauses of eqEl then follow by
     transitivity through the self-relatedness, the second one after the
     pointwise equation has been pushed under the coherence. *)
  Lemma pi_pointwise T0' A0' B0' (e2' : eval T0' (epi A0' B0'))
    (a2' : st2'.(St)) (ea2' : tyeq (StSh st2' a2') A0')
    (b2' : forall v, st2'.(StEl) a2' v -> st2'.(St))
    (eb2' : forall v y, tyeq (StSh st2' (b2' v y)) (eapp B0' v))
    (coh2' : forall v y v' y', st2'.(StEq) a2' v y v' y' -> Transp st2' (b2' v' y') (b2' v y))
    (cL2' : forall v0 y0 v1 y1 v2 y2
              (r01 : st2'.(StEq) a2' v0 y0 v1 y1) (r12 : st2'.(StEq) a2' v1 y1 v2 y2)
              (r02 : st2'.(StEq) a2' v0 y0 v2 y2) w (z : st2'.(StEl) (b2' v2 y2) w),
            goodS st2' (b2' v2 y2) w z ->
            st2'.(StEq) (b2' v0 y0) w
              (tr (coh2' v0 y0 v1 y1 r01) w (tr (coh2' v1 y1 v2 y2 r12) w z)) w
              (tr (coh2' v0 y0 v2 y2 r02) w z))
    (iL2' : forall v y (r : st2'.(StEq) a2' v y v y) w (z : st2'.(StEl) (b2' v y) w),
            goodS st2' (b2' v y) w z ->
            st2'.(StEq) (b2' v y) w (tr (coh2' v y v y r) w z) w z)
    u (f g : El st2' U2 OK2
               (r_pi st2' OK2 T0' A0' B0' e2' a2' ea2' b2' eb2' coh2' cL2' iL2') u) :
    eqEl st2' U2 E2 OK2
      (r_pi st2' OK2 T0' A0' B0' e2' a2' ea2' b2' eb2' coh2' cL2' iL2') u g u g ->
    (forall v y, st2'.(StEq) (b2' v y) (eapp u v)
       (Datatypes.fst f v y) (eapp u v) (Datatypes.fst g v y)) ->
    eqEl st2' U2 E2 OK2
      (r_pi st2' OK2 T0' A0' B0' e2' a2' ea2' b2' eb2' coh2' cL2' iL2') u f u g.
  Proof.
    intros Hg step; split; [| exact (proj2 Hg)].
    intros u1 Y1 u1' Y1' rr rr'; split.
    - eapply (trans2' (b2' u1 Y1));
        [ apply step | exact (proj1 (proj1 Hg u1 Y1 u1' Y1' rr rr')) ].
    - eapply (trans2' (b2' u1' Y1'));
        [ exact (proj2 (proj1 Hg u1 Y1 u1' Y1' rr rr')) |].
      apply (tr_eq st2' _ _ (coh2' u1' Y1' u1 Y1 rr')).
      apply (sym2' (b2' u1 Y1)); apply step.
  Qed.

  (* Preservation of the transport.  The isomorphism proof at the image is
     arbitrary -- nothing forces it to be isoPres of the one below -- so the
     Pi case has to compare two DIFFERENT pullbacks of the same argument:
     the one the image isomorphism chooses and the image of the one the
     isomorphism below chooses.  They agree up to the stage's equality, by
     injectivity of hj_to, and the naturality square of the isomorphism
     below then moves the element between the two codomain codes. *)
  Lemma toPres {T T'} (r : Refine st1 OK1 T) (r' : Refine st1' OK1 T') :
    forall (i1 : iso1 r r') (i2 : iso2 (mapR r) (mapR' r')) u x,
      eqEl st1 U1 E1 OK1 r u x u x ->
      eqEl st2' U2 E2 OK2 (mapR' r') u
        (to2 (mapR r) (mapR' r') i2 u (eTo r u x))
        u (eTo' r' u (to1 r r' i1 u x)).
  Proof.
    destruct r as [T0 e | T0 e | T0 p e H0 | T0 m ok e
                  | T0 A0 B0 e a ea b eb coh cL iL | T0 A0 B0 e a ea b eb coh cL iL | T0 N e s];
    destruct r' as [T0' e' | T0' e' | T0' p' e' H0' | T0' m' ok' e'
                   | T0' A0' B0' e' a' ea' b' eb' coh' cL' iL' | T0' A0' B0' e' a' ea' b' eb' coh' cL' iL' | T0' N' e' s'];
    cbn [isoRefine]; try (exact (fun i1 => match i1 with end)).
    - (* nat *)
      intros i1 i2 u x H;
        cbn [mapRefine elTo toRefine eqEl Datatypes.fst Datatypes.snd]; split;
        [ reflexivity | exact (Good_tyeq T0 T0' u i1 (Datatypes.snd x)) ].
    - (* prop *)
      intros i1 i2 u x H;
        cbn [mapRefine elTo toRefine eqEl Datatypes.fst Datatypes.snd]; split;
        [ split; exact (fun z => z) | exact (Good_tyeq T0 T0' u i1 (Datatypes.snd x)) ].
    - (* prf *)
      intros i1 i2 u x H;
        cbn [mapRefine elTo toRefine eqEl Datatypes.fst Datatypes.snd];
        exact (Good_tyeq T0 T0' u (proj1 i1) (Datatypes.snd x)).
    - (* univ *)
      intros i1 i2 u x H;
        cbn [mapRefine elTo toRefine eqEl Datatypes.fst Datatypes.snd].
      destruct (Nat.eq_dec m m') as [E | NE]; [| destruct (NE (proj2 i1))].
      destruct E; exact (um_irr m u ok ok' x H).
    - (* Pi *)
      intros i1 i2 u x H; cbn [mapRefine eqEl].
      apply (pi_pointwise T0' A0' B0' e' (sm_map sm' a') _ _ _ _ _ _ u).
      + exact (elTo_eq st1' st2' sm' U1 U2 E1 E2 OK1 OK2 um good1' sym1' trans1' trans2'
                 (r_pi st1' OK1 T0' A0' B0' e' a' ea' b' eb' coh' cL' iL') u _ u _
                 (toRefine_eq st1 st1' U1 E1 OK1 h1 trans1'
                    (r_pi st1 OK1 T0 A0 B0 e a ea b eb coh cL iL)
                    (r_pi st1' OK1 T0' A0' B0' e' a' ea' b' eb' coh' cL' iL')
                    i1 u x u x H)).
      + intros u1 Y1; cbn [toRefine elTo Datatypes.fst].
        (* the image isomorphism's pullback of Y1, pulled back along sm, and
           the pullback of Y1's own preimage: two arguments of the domain *)
        assert (Hwy : hjhet h1 a a' u1
                  (sm_from sm a u1
                     (hj_pull h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) u1 Y1))
                  u1 (sm_from sm' a' u1 Y1))
          by (apply (het_down a a' (proj1 (proj2 i1)));
              unfold hjhet; exists (proj1 (proj2 i2)); apply (hj_pull_to h2)).
        assert (Hpy : hjhet h1 a a' u1
                  (hj_pull h1 a a' (proj1 (proj2 i1)) u1 (sm_from sm' a' u1 Y1))
                  u1 (sm_from sm' a' u1 Y1))
          by (unfold hjhet; exists (proj1 (proj2 i1)); apply (hj_pull_to h1)).
        (* both are sent to Y1's preimage, so they agree *)
        assert (rwp : st1.(StEq) a u1
                  (sm_from sm a u1
                     (hj_pull h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) u1 Y1))
                  u1 (hj_pull h1 a a' (proj1 (proj2 i1)) u1 (sm_from sm' a' u1 Y1))).
        { apply (to_inj st1 st1' h1 sym1 trans1 a a' (proj1 (proj2 i1))).
          destruct Hwy as [P HPw].
          eapply (trans1' a'); [ apply (hj_irr h1) |].
          eapply (trans1' a'); [ exact HPw |].
          apply (sym1' a'); apply (hj_pull_to h1). }
        (* push the image transport down to the stage below, ... *)
        eapply (trans2' (mapB st1' st2' sm' a' b' u1 Y1));
          [ apply (T1 (b u1 (sm_from sm a u1
                       (hj_pull h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) u1 Y1)))
                      (b' u1 (sm_from sm' a' u1 Y1))
                      (proj1 (proj2 (proj2 i1)) u1 _ u1 _ Hwy) _ (eapp u u1)) |].
        apply (sm_to_eq sm').
        (* ... where the naturality square moves the value across, the
           identity coherence on the right and x's own respect-property on
           the left absorbing the two round trips *)
        eapply (trans1' (b' u1 (sm_from sm' a' u1 Y1)));
          [ | apply (iL' u1 (sm_from sm' a' u1 Y1)
                       (good1' a' u1 (sm_from sm' a' u1 Y1)));
              apply good1' ].
        eapply (trans1' (b' u1 (sm_from sm' a' u1 Y1)));
          [ apply (hj_to_eq h1);
            exact (proj1 (proj1 H u1 _ u1 _ rwp (sym1 a u1 _ u1 _ rwp))) |].
        apply (proj2 (proj2 (proj2 i1)) u1 _ u1 _ _ _ Hwy Hpy rwp
                 (good1' a' u1 (sm_from sm' a' u1 Y1))).
    - (* Sigma.  The first components are related by the square T1 itself; on
         the second ones the square is applied at the round-tripped argument,
         and the two coherences left over -- the one mapCoh' inserts and the
         one elTo' inserts -- compose into the single one the naturality
         square of the isomorphism below produces. *)
      intros i1 i2 u x H; cbn [mapRefine eqEl].
      destruct H as [H1 [H2 HR]].
      assert (HYD : hjhet h1 a a' (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))).
      { apply (het_down a a' (proj1 (proj2 i1))).
        exists (proj1 (proj2 i2)); apply (hj_irr h2). }
      split;
        [| split; [| exact (Good_tyeq T0 T0' u (proj1 i1) (Datatypes.snd x))]].
      + exists (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x))).
        eapply (trans2' (sm_map sm' (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))))));
          [ apply (T1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))) ((proj1 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) HYD) _ (esnd u)) |].
        apply (sm_to_eq sm').
        eapply (trans1' (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))))); [ apply ((proj2 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     HYD (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))
                     (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) (trans1' a' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))) (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) HYD) ((proj1 (proj2 (proj2 i1))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (esnd u) (projT2 (Datatypes.fst x))) |].
        apply (sym1' (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))))).
        eapply (trans1' (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))));
          [ apply (tr_eq st1' _ _ (coh' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x))))));
            apply (sm_from_to sm') |].
        apply (cL' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                 (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (trans1' a' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))) (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (esnd u) (hj_to h1 (b (efst u) (projT1 (Datatypes.fst x))) (b' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 i1))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (esnd u) (projT2 (Datatypes.fst x))) (good1' _ _ _)).
      + exists (sym2' (sm_map sm' a') _ _ _ _ (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))).
        apply (sm_to_eq sm').
        apply (sym1' (b' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))))).
        eapply (trans1' (b' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))))));
          [ apply (tr_eq st1' _ _ (coh' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (sm_from_eq sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (sym2' (sm_map sm' a') _ _ _ _ (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))))));
            eapply (trans1' (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))));
              [ apply (sm_from_eq sm'); apply (T1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (b' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))) ((proj1 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) HYD) _ (esnd u)) | apply (sm_from_to sm') ] |].
        eapply (trans1' (b' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))))));
          [ apply (tr_eq st1' _ _ (coh' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (sm_from_eq sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (sym2' (sm_map sm' a') _ _ _ _ (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))))));
            apply ((proj2 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     HYD (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))
                     (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) (trans1' a' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))) (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 i1))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) HYD) ((proj1 (proj2 (proj2 i1))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (esnd u) (projT2 (Datatypes.fst x))) |].
        apply (cL' (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                 (sm_from_eq sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (sym2' (sm_map sm' a') _ _ _ _ (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x))))) (trans1' a' (efst u) (sm_from sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (efst u) (sm_from sm' a' (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))) (sm_from_eq sm' a' (efst u) (hj_to h2 (sm_map sm a) (sm_map sm' a') (proj1 (proj2 i2)) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (sm_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (T1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i2)) (efst u) (projT1 (Datatypes.fst x)))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (sm_from_to sm' a' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) (esnd u) (hj_to h1 (b (efst u) (projT1 (Datatypes.fst x))) (b' (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 i1))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h1 a a' (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i1)) (hj_irr h1 a a' (proj1 (proj2 i1)) (proj1 (proj2 i1)) (efst u) (projT1 (Datatypes.fst x))))) (esnd u) (projT2 (Datatypes.fst x))) (good1' _ _ _)).
    - (* ne *)
      intros i1 i2 u x H; cbn [mapRefine eqEl]; exact I.
  Qed.

  (* One node: both components are the two lemmas above, read through the
     projections that Stage_next and HJ_next are built from. *)
  Theorem PresH_next :
    PresH (SMor_next st1 st2 sm U1 U2 E1 E2 OK1 OK2 um good1 sym1 trans1 sym2 trans2)
          (SMor_next st1' st2' sm' U1 U2 E1 E2 OK1 OK2 um good1' sym1' trans1' sym2' trans2')
          (HJ_next st1 st1' U1 E1 OK1 h1 good1 good1' sym1 trans1 sym1' trans1')
          (HJ_next st2 st2' U2 E2 OK2 h2 good2 good2' sym2 trans2 sym2' trans2').
  Proof.
    split.
    - intros c c' i; exact (isoPres (projT2 c) (projT2 c') i).
    - intros c c' P1 P2 u x;
        exact (toPres (projT2 c) (projT2 c') P1 P2 u (proj1_sig x) (proj2_sig x)).
  Qed.
End NextPres.

(* ------------------------------------------------------------------ *)
(* The whole hierarchy.  The recursion mirrors hj exactly: an outer     *)
(* fixpoint on the first tree and an inner one on the second, so that   *)
(* at a pair of successors the four blocks are the node (PresH_next),   *)
(* the node against the stage below, the stage below against the node,  *)
(* and the two stages below.                                           *)
(* ------------------------------------------------------------------ *)

Section StagePres.
  Context (U1 U2 : nat -> etm -> Type)
          (E1 : forall m u, U1 m u -> forall u', U1 m u' -> Prop)
          (E2 : forall m u, U2 m u -> forall u', U2 m u' -> Prop)
          (OK1 OK2 : nat -> Prop)
          (um : UMor U1 U2 E1 E2 OK1 OK2).
  Context (um_irr : forall m u (o o' : OK1 m) (x : U1 m u),
              E1 m u x u x -> E2 m u (um_to um m u o x) u (um_to um m u o' x)).
  Context (E1sym : forall m u x u' x', E1 m u x u' x' -> E1 m u' x' u x)
          (E1trans : forall m u x u' x' u'' x'',
              E1 m u x u' x' -> E1 m u' x' u'' x'' -> E1 m u x u'' x'')
          (E2sym : forall m u x u' x', E2 m u x u' x' -> E2 m u' x' u x)
          (E2trans : forall m u x u' x' u'' x'',
              E2 m u x u' x' -> E2 m u' x' u'' x'' -> E2 m u x u'' x'').

  Local Notation sms :=
    (smorStage U1 U2 E1 E2 OK1 OK2 um E1sym E1trans E2sym E2trans).
  Local Notation hj1_ := (hj U1 E1 OK1 E1sym E1trans).
  Local Notation hj2_ := (hj U2 E2 OK2 E2sym E2trans).

  Lemma presStage : forall alpha alpha',
    PresH (sms alpha) (sms alpha') (hj1_ alpha alpha') (hj2_ alpha alpha').
  Proof.
    fix IH 1.
    intros alpha; destruct alpha as [| beta | T f].
    - intros alpha'; apply PresH_emptyL.
    - fix inner 1.
      intros alpha'; destruct alpha' as [| beta' | T' f'].
      + apply PresH_emptyR.
      + apply PresH_sum_L.
        * apply PresH_sum_R.
          -- apply PresH_next; [exact um_irr | exact (IH beta beta')].
          -- exact (PresH_restrL _ _ _ _ _ (inner beta')).
        * apply PresH_sum_R.
          -- exact (PresH_restrR _ _ _ _ _ (IH beta (osucc beta'))).
          -- exact (IH beta beta').
      + apply PresH_sup_R; intros p'.
        apply PresH_sum_L.
        * apply PresH_sum_R.
          -- apply PresH_next; [exact um_irr | exact (IH beta (f' p'))].
          -- exact (PresH_restrL _ _ _ _ _ (inner (f' p'))).
        * apply PresH_sum_R.
          -- exact (PresH_restrR _ _ _ _ _
                      (PresH_supR p' _ _ _ _ (IH beta (osup T' f')))).
          -- exact (IH beta (f' p')).
    - fix inner 1.
      intros alpha'; destruct alpha' as [| beta' | T' f'].
      + apply PresH_emptyR.
      + apply PresH_sup_L; intros p.
        apply PresH_sum_L.
        * apply PresH_sum_R.
          -- apply PresH_next; [exact um_irr | exact (IH (f p) beta')].
          -- exact (PresH_restrL _ _ _ _ _
                      (PresH_supL p _ _ _ _ (inner beta'))).
        * apply PresH_sum_R.
          -- exact (PresH_restrR _ _ _ _ _ (IH (f p) (osucc beta'))).
          -- exact (IH (f p) beta').
      + apply PresH_sup_L; intros p.
        apply PresH_sup_R; intros p'.
        apply PresH_sum_L.
        * apply PresH_sum_R.
          -- apply PresH_next; [exact um_irr | exact (IH (f p) (f' p'))].
          -- exact (PresH_restrL _ _ _ _ _
                      (PresH_supL p _ _ _ _ (inner (f' p')))).
        * apply PresH_sum_R.
          -- exact (PresH_restrR _ _ _ _ _
                      (PresH_supR p' _ _ _ _ (IH (f p) (osup T' f')))).
          -- exact (IH (f p) (f' p')).
  Qed.
End StagePres.

(* ------------------------------------------------------------------ *)
(* IdP travels with a morphism too.  It needs the code to be related to *)
(* itself downstairs -- nothing produces a level-1 isomorphism proof out *)
(* of a level-2 one -- which is exactly what uf_coh supplies at the      *)
(* diagonal.                                                            *)
(* ------------------------------------------------------------------ *)

Lemma IdP_pres {s1 s2 : Stage} (m : SMor s1 s2) (h1 : HJ s1 s1) (h2 : HJ s2 s2)
  (sym2 : forall s, EqSym s2 s) (trans2 : forall s, EqTrans s2 s) :
  PresH m m h1 h2 ->
  forall s, hj_rel h1 s s -> IdP s1 h1 s -> IdP s2 h2 (sm_map m s).
Proof.
  intros [R T] s P1 Hs P2 u X.
  eapply (trans2 (sm_map m s));
    [ apply (hj_irr h2 (sm_map m s) (sm_map m s) P2 (R s s P1)) |].
  eapply (trans2 (sm_map m s));
    [ apply (hj_to_eq h2); apply (sym2 (sm_map m s)); apply (sm_to_from m) |].
  eapply (trans2 (sm_map m s)); [ apply (T s s P1 (R s s P1) u) |].
  eapply (trans2 (sm_map m s)); [ apply (sm_to_eq m); apply Hs |].
  apply (sm_to_from m).
Qed.

(* ------------------------------------------------------------------ *)
(* The instance: level k into level S k, and the lift of a whole        *)
(* universe family.  This completes blueprint Lemma 7.7.               *)
(* ------------------------------------------------------------------ *)

Lemma lvl_um_irr (k : nat) : forall m u (o o' : lOK (lvl k) m) (x : lU (lvl k) m u),
  lUEq (lvl k) m u x u x ->
  lUEq (lvl (S k)) m u (lvlTo k m u o x) u (lvlTo k m u o' x).
Proof.
  intros m u o o'; unfold lvlTo; cbn; unfold sU, sUEq;
    destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - intros x; exact (fun H => H).
Qed.

Section LevelLift.
  Context (k : nat).

  Local Notation U1_ := (lU (lvl k)).
  Local Notation U2_ := (lU (lvl (S k))).
  Local Notation E1_ := (lUEq (lvl k)).
  Local Notation E2_ := (lUEq (lvl (S k))).
  Local Notation OK1_ := (lOK (lvl k)).
  Local Notation OK2_ := (lOK (lvl (S k))).
  Local Notation s1_ := (lsym (lvl k)).
  Local Notation t1_ := (ltrans (lvl k)).
  Local Notation s2_ := (lsym (lvl (S k))).
  Local Notation t2_ := (ltrans (lvl (S k))).
  Local Notation pres :=
    (presStage U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k) (lvl_um_irr k) s1_ t1_ s2_ t2_).
  Local Notation g1 := (sgood U1_ E1_ OK1_).
  Local Notation g2 := (sgood U2_ E2_ OK2_).
  Local Notation y1 := (ssym U1_ E1_ OK1_ s1_ t1_).
  Local Notation r1 := (strans U1_ E1_ OK1_ s1_ t1_).
  Local Notation y2 := (ssym U2_ E2_ OK2_ s2_ t2_).
  Local Notation r2 := (strans U2_ E2_ OK2_ s2_ t2_).
  Local Notation hj1_ := (hj U1_ E1_ OK1_ s1_ t1_).
  Local Notation hj2_ := (hj U2_ E2_ OK2_ s2_ t2_).

  Lemma liftIso (b b' : Ord) (c : Code k b) (c' : Code k b') :
    iso c c' -> iso (liftCode k b c) (liftCode k b' c').
  Proof.
    intros i.
    exact (proj1 (PresH_next _ _ _ _ _ _ U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k)
                    (lvl_um_irr k) (g1 b) (g1 b') (g2 b) (g2 b')
                    (y1 b) (r1 b) (y1 b') (r1 b') (y2 b) (r2 b) (y2 b') (r2 b')
                    (hj1_ b b') (hj2_ b b') (pres b b')) c c' i).
  Qed.

  Lemma liftIdP (b : Ord) (c : Code k b) :
    iso c c -> LIdP c -> LIdP (liftCode k b c).
  Proof.
    intros i H.
    exact (IdP_pres _ _ _
             (eqU_sym U2_ E2_ OK2_ s2_ t2_ b) (eqU_trans U2_ E2_ OK2_ s2_ t2_ b)
             (PresH_next _ _ _ _ _ _ U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k)
                (lvl_um_irr k) (g1 b) (g1 b) (g2 b) (g2 b)
                (y1 b) (r1 b) (y1 b) (r1 b) (y2 b) (r2 b) (y2 b) (r2 b)
                (hj1_ b b) (hj2_ b b) (pres b b)) c i H).
  Qed.

  (* The decoding travels with the code: this is what the lift of a TERM is. *)
  Local Notation nxt :=
    (nextOf U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k) s1_ t1_ s2_ t2_).
  Local Notation smst :=
    (smorStage U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k) s1_ t1_ s2_ t2_).

  Definition liftEl (b : Ord) (c : Code k b) (u : etm)
    (x : (Ust U1_ E1_ OK1_ b).(StEl) c u)
    : (Ust U2_ E2_ OK2_ b).(StEl) (liftCode k b c) u :=
    sm_to (nxt b (smst b)) c u x.

  Lemma liftEl_eq (b : Ord) (c : Code k b) u x u' x' :
    (Ust U1_ E1_ OK1_ b).(StEq) c u x u' x' ->
    (Ust U2_ E2_ OK2_ b).(StEq) (liftCode k b c) u (liftEl b c u x) u' (liftEl b c u' x').
  Proof. apply (sm_to_eq (nxt b (smst b))). Qed.

  (* Naturality of the lift against the transport: the lift of a transported
     element is the transport of the lifted one.  This is PresH's SECOND
     component -- the square -- and it is what the lift of a term needs in
     order to be functional: the two readings of `uptm A t` lift elements of
     two DIFFERENT families, so the square is the only thing that brings the
     two lifted values into one code. *)
  Lemma liftEl_to (b b' : Ord) (c : Code k b) (c' : Code k b')
    (P : ciso U1_ E1_ OK1_ s1_ t1_ c c')
    (Q : ciso U2_ E2_ OK2_ s2_ t2_ (liftCode k b c) (liftCode k b' c')) u x :
    (Ust U2_ E2_ OK2_ b').(StEq) (liftCode k b' c') u
      (cto U2_ E2_ OK2_ s2_ t2_ (liftCode k b c) (liftCode k b' c') Q u
         (liftEl b c u x))
      u (liftEl b' c' u (cto U1_ E1_ OK1_ s1_ t1_ c c' P u x)).
  Proof.
    exact (proj2 (PresH_next _ _ _ _ _ _ U1_ U2_ E1_ E2_ OK1_ OK2_ (lvlUMor k)
                    (lvl_um_irr k) (g1 b) (g1 b') (g2 b) (g2 b')
                    (y1 b) (r1 b) (y1 b') (r1 b') (y2 b) (r2 b) (y2 b') (r2 b')
                    (hj1_ b b') (hj2_ b b') (pres b b')) c c' P Q u x).
  Qed.

  (* The lift of a universe family: every field travels, the shadow by
     liftCode_sh and the two layer-1 equations by cumulativity. *)
  Definition famLift (n n' : nat) (Hn : n <= n') (u : etm)
    (F : UFam (lvl k) n u) : UFam (lvl (S k)) n' u.
  Proof.
    refine (Build_UFam (lvl (S k)) n' u
              (fun v h pf => liftCode k (rk v h) (uf_c F v h pf)) _ _ _ _).
    - exact (eqty_cumul n n' u u Hn (uf_ty F)).
    - intros v h pf; rewrite liftCode_sh.
      exact (eqty_cumul n n' _ u Hn (uf_sh F v h pf)).
    - intros v h pf v' h' pf'; exact (liftIso _ _ _ _ (uf_coh F v h pf v' h' pf')).
    - intros v h pf; exact (liftIdP _ _ (uf_coh F v h pf v h pf) (uf_idp F v h pf)).
  Defined.
End LevelLift.
