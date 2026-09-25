From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From Stdlib Require Import Arith Lia.

(* THE LEVEL LIFT -- blueprint Lemma 7.7.  Started here; the functorial map
   itself is not yet built.

   What it has to be.  `Code k beta = LCode (lvl k) beta` is indexed by the Lvl
   RECORD, so a level-k code is not literally a level-(S k) code: the lift is a
   morphism of the code hierarchy along `lvl k -> lvl (S k)`, by recursion on
   the Brouwer tree (for stage elements) and on Refine (for the six clauses),
   carrying with it that the DECODINGS agree -- which is what makes the
   equality, the shadow and the isomorphism survive.

   Why the decodings agree at all.  `lvl (S k) = lvl_step k (lvl k)`, and

       lU (lvl (S k)) m u  =  match Nat.eq_dec m k with
                              | left _  => LUniv (lvl k) k u   (* the new one *)
                              | right _ => lU (lvl k) m u      (* the old ones *)
                              end

   so the two universe parameters differ ONLY at m = k, and the level-k codes
   cannot mention that level at all: `r_univ` at level k demands
   `lOK (lvl k) m`, i.e. m < k.  Hence every universe a level-k code decodes is
   one that level S k decodes the same way (lU_agree below).  The two facts
   below are exactly the side conditions the r_univ clause of the lift will
   need; everything else in Refine is structural.

   The obstruction to watch: lU_agree is a TYPE equality, proved from lU_spec
   (which is opaque, being proved by induction on the level), so transporting a
   universe element along it will not compute.  The r_univ case of the lift
   should therefore be written by `destruct (Nat.eq_dec m k)` -- refuting the
   `m = k` branch from m < k -- rather than by eq_rect along lU_agree, exactly
   as Interp/Univ.v does for the universe bridge. *)

(* Level k admits the universes strictly below it, and each step admits more. *)
Lemma lOK_lt k m : lOK (lvl k) m <-> m < k.
Proof.
  destruct k as [| n]; cbn.
  - split; [intros [] | intros H; inversion H].
  - split; intros H; exact H.
Qed.

Lemma lOK_mono k m : lOK (lvl k) m -> lOK (lvl (S k)) m.
Proof. intros H; apply lOK_lt; apply lOK_lt in H; lia. Qed.

(* Below k the two levels decode the universes identically: both give the
   completed family of level m. *)
Lemma lU_agree k m u : m < k -> lU (lvl (S k)) m u = lU (lvl k) m u.
Proof.
  intros H; rewrite (lU_spec (S k) m u), (lU_spec k m u); [reflexivity | lia | lia].
Qed.

(* And the same for the shadows of the universe decoding, which is what
   UnivSound asks of the lifted parameter. *)
Lemma lU_sound_agree k m u (x : lU (lvl k) m u) : m < k -> eqty m u u.
Proof. intros H; exact (us_ty _ _ _ (lsound (lvl k)) m u x). Qed.


(* ------------------------------------------------------------------ *)
(* A MORPHISM OF THE CODE HIERARCHY.                                   *)
(*                                                                    *)
(* The lift is an instance of a general construction: given a map      *)
(* between two universe parameters, every stage over the first maps to *)
(* the stage over the second, preserving the shadow and the decoding.  *)
(* The decoding has to be preserved in BOTH directions -- the Pi       *)
(* clause indexes its codomain by an element of the domain's decoding, *)
(* so building the image code needs to move an argument backwards --   *)
(* and the round trips only have to hold up to the stage's own         *)
(* equality, which is all the codes ever ask of their elements.        *)
(* ------------------------------------------------------------------ *)

Record UMor (U1 U2 : nat -> etm -> Type)
            (E1 : forall m u, U1 m u -> forall u', U1 m u' -> Prop)
            (E2 : forall m u, U2 m u -> forall u', U2 m u' -> Prop)
            (OK1 OK2 : nat -> Prop) := {
  um_ok : forall m, OK1 m -> OK2 m;
  um_to : forall m u, OK1 m -> U1 m u -> U2 m u;
  um_from : forall m u, OK1 m -> U2 m u -> U1 m u;
  um_to_eq : forall m (o : OK1 m) u x u' x',
      E1 m u x u' x' -> E2 m u (um_to m u o x) u' (um_to m u' o x');
  um_from_eq : forall m (o : OK1 m) u y u' y',
      E2 m u y u' y' -> E1 m u (um_from m u o y) u' (um_from m u' o y');
  um_to_from : forall m (o : OK1 m) u y, E2 m u (um_to m u o (um_from m u o y)) u y;
  um_from_to : forall m (o : OK1 m) u x, E1 m u (um_from m u o (um_to m u o x)) u x
}.
Arguments um_ok {U1 U2 E1 E2 OK1 OK2}. Arguments um_to {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from {U1 U2 E1 E2 OK1 OK2}. Arguments um_to_eq {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from_eq {U1 U2 E1 E2 OK1 OK2}. Arguments um_to_from {U1 U2 E1 E2 OK1 OK2}.
Arguments um_from_to {U1 U2 E1 E2 OK1 OK2}.

Record SMor (st1 st2 : Stage) := {
  sm_map : st1.(St) -> st2.(St);
  sm_sh : forall s, st2.(StSh) (sm_map s) = st1.(StSh) s;
  sm_to : forall s u, st1.(StEl) s u -> st2.(StEl) (sm_map s) u;
  sm_from : forall s u, st2.(StEl) (sm_map s) u -> st1.(StEl) s u;
  sm_to_eq : forall s u x u' x', st1.(StEq) s u x u' x' ->
      st2.(StEq) (sm_map s) u (sm_to s u x) u' (sm_to s u' x');
  sm_from_eq : forall s u y u' y', st2.(StEq) (sm_map s) u y u' y' ->
      st1.(StEq) s u (sm_from s u y) u' (sm_from s u' y');
  sm_to_from : forall s u y, st2.(StEq) (sm_map s) u (sm_to s u (sm_from s u y)) u y;
  sm_from_to : forall s u x, st1.(StEq) s u (sm_from s u (sm_to s u x)) u x
}.
Arguments sm_map {st1 st2}. Arguments sm_sh {st1 st2}. Arguments sm_to {st1 st2}.
Arguments sm_from {st1 st2}. Arguments sm_to_eq {st1 st2}. Arguments sm_from_eq {st1 st2}.
Arguments sm_to_from {st1 st2}. Arguments sm_from_to {st1 st2}.

(* The three stage combinators are pure bookkeeping. *)
Definition SMor_empty : SMor Stage_empty Stage_empty :=
  Build_SMor Stage_empty Stage_empty
    (fun s => match s with end) (fun s => match s with end)
    (fun s => match s with end) (fun s => match s with end)
    (fun s => match s with end) (fun s => match s with end)
    (fun s => match s with end) (fun s => match s with end).

Section SumMor.
  Context (st1 st2 st1' st2' : Stage) (m1 : SMor st1 st1') (m2 : SMor st2 st2').

  Definition sum_map (s : (Stage_sum st1 st2).(St)) : (Stage_sum st1' st2').(St) :=
    match s with inl a => inl (sm_map m1 a) | inr b => inr (sm_map m2 b) end.

  Definition sum_to : forall s u, (Stage_sum st1 st2).(StEl) s u ->
      (Stage_sum st1' st2').(StEl) (sum_map s) u :=
    fun s => match s with inl a => sm_to m1 a | inr b => sm_to m2 b end.

  Definition sum_from : forall s u, (Stage_sum st1' st2').(StEl) (sum_map s) u ->
      (Stage_sum st1 st2).(StEl) s u :=
    fun s => match s with inl a => sm_from m1 a | inr b => sm_from m2 b end.

  Definition SMor_sum : SMor (Stage_sum st1 st2) (Stage_sum st1' st2').
  Proof.
    refine (Build_SMor _ _ sum_map _ sum_to sum_from _ _ _ _).
    - intros [a | b]; [exact (sm_sh m1 a) | exact (sm_sh m2 b)].
    - intros [a | b] u x u' x';
        [exact (sm_to_eq m1 a u x u' x') | exact (sm_to_eq m2 b u x u' x')].
    - intros [a | b] u y u' y';
        [exact (sm_from_eq m1 a u y u' y') | exact (sm_from_eq m2 b u y u' y')].
    - intros [a | b] u y; [exact (sm_to_from m1 a u y) | exact (sm_to_from m2 b u y)].
    - intros [a | b] u x; [exact (sm_from_to m1 a u x) | exact (sm_from_to m2 b u x)].
  Defined.
End SumMor.

Section SupMor.
  Context (T : etm) (F F' : Pred T -> Stage) (m : forall p, SMor (F p) (F' p)).

  Definition sup_map (s : (Stage_sup T F).(St)) : (Stage_sup T F').(St) :=
    existT _ (projT1 s) (sm_map (m (projT1 s)) (projT2 s)).

  Definition sup_to : forall s u, (Stage_sup T F).(StEl) s u ->
      (Stage_sup T F').(StEl) (sup_map s) u :=
    fun s => sm_to (m (projT1 s)) (projT2 s).

  Definition sup_from : forall s u, (Stage_sup T F').(StEl) (sup_map s) u ->
      (Stage_sup T F).(StEl) s u :=
    fun s => sm_from (m (projT1 s)) (projT2 s).

  Definition SMor_sup : SMor (Stage_sup T F) (Stage_sup T F').
  Proof.
    refine (Build_SMor _ _ sup_map _ sup_to sup_from _ _ _ _).
    - intros [p s]; exact (sm_sh (m p) s).
    - intros [p s] u x u' x'; exact (sm_to_eq (m p) s u x u' x').
    - intros [p s] u y u' y'; exact (sm_from_eq (m p) s u y u' y').
    - intros [p s] u y; exact (sm_to_from (m p) s u y).
    - intros [p s] u x; exact (sm_from_to (m p) s u x).
  Defined.
End SupMor.

(* ------------------------------------------------------------------ *)
(* The step: one node of the hierarchy.  This is where the six clauses *)
(* of Refine are mapped, and the only interesting clause is Pi, where   *)
(* the codomain is indexed by an element of the domain's decoding and   *)
(* so has to be composed with sm_from on the way in and sm_to on the    *)
(* way out.  The two laws of a Pi-code then need the target stage's     *)
(* equality to be a PER, because the round trips hold only up to it --  *)
(* the same hypotheses Codes/Expand.v takes for the same reason.        *)
(* ------------------------------------------------------------------ *)

Section NextMor.
  Context (st1 st2 : Stage) (sm : SMor st1 st2).
  Context (U1 U2 : nat -> etm -> Type)
          (E1 : forall m u, U1 m u -> forall u', U1 m u' -> Prop)
          (E2 : forall m u, U2 m u -> forall u', U2 m u' -> Prop)
          (OK1 OK2 : nat -> Prop).
  Context (um : UMor U1 U2 E1 E2 OK1 OK2).
  Context (good1 : StGood st1) (good2 : StGood st2).
  Context (sym1 : forall s, EqSym st1 s) (trans1 : forall s, EqTrans st1 s).
  Context (sym2 : forall s, EqSym st2 s) (trans2 : forall s, EqTrans st2 s).

  Local Notation El1_ := (El st1 U1 OK1).
  Local Notation El2_ := (El st2 U2 OK2).
  Local Notation eq1_ := (eqEl st1 U1 E1 OK1).
  Local Notation eq2_ := (eqEl st2 U2 E2 OK2).

  (* The codomain of the image Pi-code. *)
  Definition mapB (a : st1.(St)) (b : forall u, st1.(StEl) a u -> st1.(St))
    (u : etm) (x : st2.(StEl) (sm_map sm a) u) : st2.(St) :=
    sm_map sm (b u (sm_from sm a u x)).

  (* Its coherence: pull the argument back, transport there, push forward. *)
  Definition mapCoh (a : st1.(St)) (b : forall u, st1.(StEl) a u -> st1.(St))
    (coh : forall u x u' x', st1.(StEq) a u x u' x' ->
             Transp st1 (b u' x') (b u x))
    u x u' x' (r : st2.(StEq) (sm_map sm a) u x u' x')
    : Transp st2 (mapB a b u' x') (mapB a b u x).
  Proof.
    refine (Build_Transp st2 (mapB a b u' x') (mapB a b u x)
      (fun v y => sm_to sm _ v (tr (coh u (sm_from sm a u x) u' (sm_from sm a u' x')
                                      (sm_from_eq sm a u x u' x' r)) v
                                 (sm_from sm _ v y))) _).
    intros v y v' y' Hy.
    apply (sm_to_eq sm).
    apply (tr_eq st1 _ _ (coh u (sm_from sm a u x) u' (sm_from sm a u' x')
                            (sm_from_eq sm a u x u' x' r))).
    apply (sm_from_eq sm); exact Hy.
  Defined.

  Definition mapRefine {T} (r : Refine st1 OK1 T) : Refine st2 OK2 T.
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s].
    - exact (r_nat st2 OK2 T e).
    - exact (r_prop st2 OK2 T e).
    - exact (r_prf st2 OK2 T p e H).
    - exact (r_univ st2 OK2 T m (um_ok um m ok) e).
    - refine (r_pi st2 OK2 T A0 B0 e (sm_map sm a) _ (mapB a b) _ (mapCoh a b coh) _ _).
      + rewrite (sm_sh sm a); exact ea.
      + intros u x; unfold mapB; rewrite (sm_sh sm); apply eb.
      + (* composition *)
        intros u0 x0 u1 x1 u2 x2 r01 r12 r02 v y Hy; cbn.
        eapply (trans2 (mapB a b u0 x0));
          [ apply (sm_to_eq sm);
            apply (tr_eq st1 _ _ (coh u0 (sm_from sm a u0 x0) u1 (sm_from sm a u1 x1)
                                    (sm_from_eq sm a u0 x0 u1 x1 r01)));
            apply (sm_from_to sm) |].
        apply (sm_to_eq sm).
        apply (cL u0 (sm_from sm a u0 x0) u1 (sm_from sm a u1 x1)
                 u2 (sm_from sm a u2 x2)
                 (sm_from_eq sm a u0 x0 u1 x1 r01)
                 (sm_from_eq sm a u1 x1 u2 x2 r12)
                 (sm_from_eq sm a u0 x0 u2 x2 r02) v (sm_from sm _ v y)).
        unfold goodS; apply (sm_from_eq sm); exact Hy.
      + (* identity *)
        intros u x r0 v y Hy; cbn.
        eapply (trans2 (mapB a b u x));
          [ apply (sm_to_eq sm);
            apply (iL u (sm_from sm a u x) (sm_from_eq sm a u x u x r0) v
                     (sm_from sm _ v y));
            unfold goodS; apply (sm_from_eq sm); exact Hy |].
        exact (sm_to_from sm _ v y).
    - refine (r_sig st2 OK2 T A0 B0 e (sm_map sm a) _ (mapB a b) _ (mapCoh a b coh) _ _).
      + rewrite (sm_sh sm a); exact ea.
      + intros u x; unfold mapB; rewrite (sm_sh sm); apply eb.
      + (* composition *)
        intros u0 x0 u1 x1 u2 x2 r01 r12 r02 v y Hy; cbn.
        eapply (trans2 (mapB a b u0 x0));
          [ apply (sm_to_eq sm);
            apply (tr_eq st1 _ _ (coh u0 (sm_from sm a u0 x0) u1 (sm_from sm a u1 x1)
                                    (sm_from_eq sm a u0 x0 u1 x1 r01)));
            apply (sm_from_to sm) |].
        apply (sm_to_eq sm).
        apply (cL u0 (sm_from sm a u0 x0) u1 (sm_from sm a u1 x1)
                 u2 (sm_from sm a u2 x2)
                 (sm_from_eq sm a u0 x0 u1 x1 r01)
                 (sm_from_eq sm a u1 x1 u2 x2 r12)
                 (sm_from_eq sm a u0 x0 u2 x2 r02) v (sm_from sm _ v y)).
        unfold goodS; apply (sm_from_eq sm); exact Hy.
      + (* identity *)
        intros u x r0 v y Hy; cbn.
        eapply (trans2 (mapB a b u x));
          [ apply (sm_to_eq sm);
            apply (iL u (sm_from sm a u x) (sm_from_eq sm a u x u x r0) v
                     (sm_from sm _ v y));
            unfold goodS; apply (sm_from_eq sm); exact Hy |].
        exact (sm_to_from sm _ v y).
    - exact (r_ne st2 OK2 T N e s).
  Defined.

  (* The decoding travels with the code: the identity at every clause whose
     decoding mentions neither the stage nor the universes, the universe
     morphism at r_univ, and the argument round trip at r_pi. *)
  Definition elTo {T} (r : Refine st1 OK1 T) u : El1_ r u -> El2_ (mapRefine r) u.
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun x => x).
    - exact (fun x => x).
    - exact (fun x => x).
    - exact (um_to um m u ok).
    - exact (fun x => (fun u' x' => sm_to sm _ _ (Datatypes.fst x u' (sm_from sm a u' x')),
                       Datatypes.snd x)).
    (* At Sigma the first component's value MOVES, so -- unlike at Pi, where
       the argument is pulled back before the function is applied -- the
       second component has to be carried along the codomain's coherence at
       the round trip of the first. *)
    - exact (fun x =>
        (existT _ (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))
           (sm_to sm (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))) (esnd u)
              (tr (coh (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x)))) (esnd u) (projT2 (Datatypes.fst x)))),
         Datatypes.snd x)).
    - exact (fun x => match x with end).
  Defined.

  Definition elFrom {T} (r : Refine st1 OK1 T) u : El2_ (mapRefine r) u -> El1_ r u.
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun x => x).
    - exact (fun x => x).
    - exact (fun x => x).
    - exact (um_from um m u ok).
    - (* the argument's round trip is not the identity, only related to it, so
         the value comes back along the codomain's own coherence *)
      refine (fun y => (fun u' x => _, Datatypes.snd y)).
      refine (tr (coh u' x u' (sm_from sm a u' (sm_to sm a u' x))
                    (sym1 a u' (sm_from sm a u' (sm_to sm a u' x)) u' x
                       (sm_from_to sm a u' x))) (eapp u u') _).
      exact (sm_from sm _ _ (Datatypes.fst y u' (sm_to sm a u' x))).
    (* The other way round nothing has to be carried: the image code at the
       pulled-back first component IS the image of the code at it. *)
    - exact (fun y => (existT _ (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))
                         (sm_from sm _ (esnd u) (projT2 (Datatypes.fst y))),
                       Datatypes.snd y)).
    - exact (fun y => match y with end).
  Defined.

  (* The equality travels too.  Only Pi needs an argument: the hypothesis
     applies at the pulled-back arguments, and what is left over is one round
     trip, which the codomain's transport absorbs. *)
  Lemma elTo_eq {T} (r : Refine st1 OK1 T) u x u' x' :
    eq1_ r u x u' x' -> eq2_ (mapRefine r) u (elTo r u x) u' (elTo r u' x').
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (um_to_eq um m ok u x u' x').
    - intros [Hf Hrel]; split; [| exact Hrel].
      intros u1 y1 u1' y1' r2 r2'; split.
      + eapply (trans2 (mapB a b u1 y1));
          [ apply (sm_to_eq sm);
            exact (proj1 (Hf u1 (sm_from sm a u1 y1) u1' (sm_from sm a u1' y1')
                            (sm_from_eq sm a u1 y1 u1' y1' r2)
                            (sm_from_eq sm a u1' y1' u1 y1 r2'))) |].
        apply (sm_to_eq sm).
        apply (tr_eq st1 _ _ (coh u1 (sm_from sm a u1 y1) u1' (sm_from sm a u1' y1')
                                (sm_from_eq sm a u1 y1 u1' y1' r2))).
        apply (sym1 (b u1' (sm_from sm a u1' y1'))).
        apply (sm_from_to sm).
      + eapply (trans2 (mapB a b u1' y1'));
          [ apply (sm_to_eq sm);
            exact (proj2 (Hf u1 (sm_from sm a u1 y1) u1' (sm_from sm a u1' y1')
                            (sm_from_eq sm a u1 y1 u1' y1' r2)
                            (sm_from_eq sm a u1' y1' u1 y1 r2'))) |].
        apply (sm_to_eq sm).
        apply (tr_eq st1 _ _ (coh u1' (sm_from sm a u1' y1') u1 (sm_from sm a u1 y1)
                                (sm_from_eq sm a u1' y1' u1 y1 r2'))).
        apply (sym1 (b u1 (sm_from sm a u1 y1))).
        apply (sm_from_to sm).
    - (* Sigma: what is left over after the hypothesis is applied at the two
         round-tripped first components is a composite of three coherences
         against one, which the composition law settles. *)
      intros [[r0 Ea] [[r0' Eb] Hrel]].
      split; [| split; [| exact Hrel]].
      + exists (sm_to_eq sm a (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x')) r0).
        apply (sm_to_eq sm).
        eapply (trans1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))));
          [ apply (tr_eq st1 _ _ (coh (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x)))));
            exact Ea |].
        eapply (trans1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))));
          [ apply (cL (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x'))
                     (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) r0 (trans1 a (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x')) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) r0) (esnd u') (projT2 (Datatypes.fst x')) (good1 _ _ _)) |].
        apply (sym1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))))).
        eapply (trans1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))))));
          [ apply (tr_eq st1 _ _ (coh (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (sm_from_eq sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))) (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))) (sm_to_eq sm a (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x')) r0))));
            apply (sm_from_to sm) |].
        apply (cL (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u') (projT1 (Datatypes.fst x'))
                 (sm_from_eq sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))) (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))) (sm_to_eq sm a (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x')) r0)) (sm_from_to sm a (efst u') (projT1 (Datatypes.fst x'))) (trans1 a (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (efst u') (projT1 (Datatypes.fst x')) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) r0) (esnd u') (projT2 (Datatypes.fst x')) (good1 _ _ _)).
      + exists (sm_to_eq sm a (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x)) r0').
        apply (sm_to_eq sm).
        eapply (trans1 (b (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))))));
          [ apply (tr_eq st1 _ _ (coh (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u') (projT1 (Datatypes.fst x')) (sm_from_to sm a (efst u') (projT1 (Datatypes.fst x')))));
            exact Eb |].
        eapply (trans1 (b (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))))));
          [ apply (cL (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x))
                     (sm_from_to sm a (efst u') (projT1 (Datatypes.fst x'))) r0' (trans1 a (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x)) (sm_from_to sm a (efst u') (projT1 (Datatypes.fst x'))) r0') (esnd u) (projT2 (Datatypes.fst x)) (good1 _ _ _)) |].
        apply (sym1 (b (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))))).
        eapply (trans1 (b (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))))));
          [ apply (tr_eq st1 _ _ (coh (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (sm_from_eq sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))) (sm_to_eq sm a (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x)) r0'))));
            apply (sm_from_to sm) |].
        apply (cL (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x))
                 (sm_from_eq sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x'))) (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x))) (sm_to_eq sm a (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x)) r0')) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) (trans1 a (efst u') (sm_from sm a (efst u') (sm_to sm a (efst u') (projT1 (Datatypes.fst x')))) (efst u') (projT1 (Datatypes.fst x')) (efst u) (projT1 (Datatypes.fst x)) (sm_from_to sm a (efst u') (projT1 (Datatypes.fst x'))) r0') (esnd u) (projT2 (Datatypes.fst x)) (good1 _ _ _)).
    - exact (fun H => H).
  Qed.

  Lemma elFrom_eq {T} (r : Refine st1 OK1 T) u y u' y' :
    eq2_ (mapRefine r) u y u' y' -> eq1_ r u (elFrom r u y) u' (elFrom r u' y').
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (um_from_eq um m ok u y u' y').
    - intros [Hf Hrel]; split; [| exact Hrel].
      intros u1 x1 u1' x1' r1 r1'.
      (* the arguments, pushed forward and pulled back *)
      set (X1 := sm_to sm a u1 x1). set (X1' := sm_to sm a u1' x1').
      set (x1r := sm_from sm a u1 X1). set (x1r' := sm_from sm a u1' X1').
      (* these must be LET-bound, not asserted: the coherence takes the proof
         as an argument, so an opaque hypothesis would not match the proof
         that elFrom's own transport carries *)
      pose (rt1 := sym1 a u1 x1r u1 x1 (sm_from_to sm a u1 x1)).
      pose (rt1' := sym1 a u1' x1r' u1' x1' (sm_from_to sm a u1' x1')).
      assert (r02 : st1.(StEq) a u1 x1 u1' x1r')
        by (apply (trans1 a u1 x1 u1' x1'); [exact r1 | exact rt1']).
      assert (r02' : st1.(StEq) a u1' x1' u1 x1r)
        by (apply (trans1 a u1' x1' u1 x1); [exact r1' | exact rt1]).
      split.
      + (* forward component *)
        eapply (trans1 (b u1 x1));
          [ apply (tr_eq st1 _ _ (coh u1 x1 u1 x1r rt1));
            apply (sm_from_eq sm);
            exact (proj1 (Hf u1 X1 u1' X1'
                            (sm_to_eq sm a u1 x1 u1' x1' r1)
                            (sm_to_eq sm a u1' x1' u1 x1 r1'))) |].
        (* what is left is the composite of two coherences against one *)
        eapply (trans1 (b u1 x1));
          [ apply (tr_eq st1 _ _ (coh u1 x1 u1 x1r rt1));
            apply (sm_from_to sm) |].
        eapply (trans1 (b u1 x1));
          [ exact (cL u1 x1 u1 x1r u1' x1r' rt1
                     (sm_from_eq sm a u1 X1 u1' X1'
                        (sm_to_eq sm a u1 x1 u1' x1' r1))
                     r02 _ _ (good1 _ _ _)) |].
        apply (sym1 (b u1 x1)).
        eapply (trans1 (b u1 x1));
          [ exact (cL u1 x1 u1' x1' u1' x1r' r1 rt1' r02 _ _ (good1 _ _ _)) |].
        apply (good1 (b u1 x1)).
      + (* backward component *)
        eapply (trans1 (b u1' x1'));
          [ apply (tr_eq st1 _ _ (coh u1' x1' u1' x1r' rt1'));
            apply (sm_from_eq sm);
            exact (proj2 (Hf u1 X1 u1' X1'
                            (sm_to_eq sm a u1 x1 u1' x1' r1)
                            (sm_to_eq sm a u1' x1' u1 x1 r1'))) |].
        eapply (trans1 (b u1' x1'));
          [ apply (tr_eq st1 _ _ (coh u1' x1' u1' x1r' rt1'));
            apply (sm_from_to sm) |].
        eapply (trans1 (b u1' x1'));
          [ exact (cL u1' x1' u1' x1r' u1 x1r rt1'
                     (sm_from_eq sm a u1' X1' u1 X1
                        (sm_to_eq sm a u1' x1' u1 x1 r1'))
                     r02' _ _ (good1 _ _ _)) |].
        apply (sym1 (b u1' x1')).
        eapply (trans1 (b u1' x1'));
          [ exact (cL u1' x1' u1 x1 u1 x1r r1' rt1 r02' _ _ (good1 _ _ _)) |].
        apply (good1 (b u1' x1')).
    - (* Sigma: only one round trip is left, on the second component, and
         sm_from_to absorbs it. *)
      intros [[R0 Ea] [[R0' Eb] Hrel]].
      split; [| split; [| exact Hrel]].
      + exists (sm_from_eq sm a (efst u) (projT1 (Datatypes.fst y)) (efst u') (projT1 (Datatypes.fst y')) R0).
        eapply (trans1 (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))));
          [ apply (sm_from_eq sm); exact Ea | apply (sm_from_to sm) ].
      + exists (sm_from_eq sm a (efst u') (projT1 (Datatypes.fst y')) (efst u) (projT1 (Datatypes.fst y)) R0').
        eapply (trans1 (b (efst u') (sm_from sm a (efst u') (projT1 (Datatypes.fst y')))));
          [ apply (sm_from_eq sm); exact Eb | apply (sm_from_to sm) ].
    - exact (fun H => H).
  Qed.

  (* The round trips, up to the stage's equality.  At Pi each reduces to a
     POINTWISE statement -- the round-tripped function agrees with the original
     at every argument -- and that holds because the element is self-related:
     its own respect-property relates its values at an argument and at the
     argument's round trip. *)
  Lemma elFrom_to {T} (r : Refine st1 OK1 T) u x :
    eq1_ r u x u x -> eq1_ r u (elFrom r u (elTo r u x)) u x.
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (fun H => H).
    - intros _; exact (um_from_to um m ok u x).
    - intros [Hx Hrel].
      (* pointwise: the round trip agrees with x at every argument *)
      assert (step : forall u1 x1, st1.(StEq) (b u1 x1) (eapp u u1)
                (tr (coh u1 x1 u1 (sm_from sm a u1 (sm_to sm a u1 x1))
                       (sym1 a u1 (sm_from sm a u1 (sm_to sm a u1 x1)) u1 x1
                          (sm_from_to sm a u1 x1))) (eapp u u1)
                   (sm_from sm _ (eapp u u1)
                      (sm_to sm _ (eapp u u1)
                         (Datatypes.fst x u1 (sm_from sm a u1 (sm_to sm a u1 x1))))))
                (eapp u u1) (Datatypes.fst x u1 x1)).
      { intros u1 x1.
        eapply (trans1 (b u1 x1));
          [ apply (tr_eq st1 _ _ (coh u1 x1 u1 _ _)); apply (sm_from_to sm) |].
        apply (sym1 (b u1 x1)).
        exact (proj1 (Hx u1 x1 u1 _
                        (sym1 a u1 _ u1 x1 (sm_from_to sm a u1 x1))
                        (sm_from_to sm a u1 x1))). }
      split; [| exact Hrel].
      intros u1 x1 u1' x1' r1 r1'; split.
      + eapply (trans1 (b u1 x1)); [apply step | exact (proj1 (Hx u1 x1 u1' x1' r1 r1'))].
      + eapply (trans1 (b u1' x1'));
          [ exact (proj2 (Hx u1 x1 u1' x1' r1 r1')) |].
        apply (tr_eq st1 _ _ (coh u1' x1' u1 x1 r1')).
        apply (sym1 (b u1 x1)); apply step.
    - (* Sigma: the first component's round trip is sm_from_to, and so is the
         second one's, because the image's coherence is applied to the very
         same proof. *)
      intros [H1 [H2 HR]].
      split; [| split; [| exact HR]].
      + exists (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))).
        apply (sm_from_to sm).
      + exists (sym1 a _ _ _ _ (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x)))).
        apply (sig_flipL st1 good1 sym1 trans1 a b coh cL iL
                 (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))) (sym1 a _ _ _ _ (sm_from_to sm a (efst u) (projT1 (Datatypes.fst x))))).
        apply (sm_from_to sm).
    - exact (fun H => H).
  Qed.

  Lemma elTo_from {T} (r : Refine st1 OK1 T) u y :
    eq2_ (mapRefine r) u y u y ->
    eq2_ (mapRefine r) u (elTo r u (elFrom r u y)) u y.
  Proof.
    destruct r as [T e | T e | T p e H | T m ok e
                  | T A0 B0 e a ea b eb coh cL iL | T A0 B0 e a ea b eb coh cL iL | T N e s]; cbn.
    - exact (fun H => H).
    - exact (fun H => H).
    - exact (fun H => H).
    - intros _; exact (um_to_from um m ok u y).
    - intros [Hy Hrel].
      assert (step : forall u1 X1, st2.(StEq) (mapB a b u1 X1) (eapp u u1)
                (sm_to sm (b u1 (sm_from sm a u1 X1)) (eapp u u1)
                   (tr (coh u1 (sm_from sm a u1 X1) u1
                          (sm_from sm a u1 (sm_to sm a u1 (sm_from sm a u1 X1)))
                          (sym1 a u1 _ u1 (sm_from sm a u1 X1)
                             (sm_from_to sm a u1 (sm_from sm a u1 X1)))) (eapp u u1)
                      (sm_from sm _ (eapp u u1)
                         (Datatypes.fst y u1 (sm_to sm a u1 (sm_from sm a u1 X1))))))
                (eapp u u1) (Datatypes.fst y u1 X1)).
      { intros u1 X1.
        eapply (trans2 (mapB a b u1 X1));
          [ apply (sm_to_eq sm) |
            exact (sm_to_from sm (b u1 (sm_from sm a u1 X1)) (eapp u u1)
                     (Datatypes.fst y u1 X1)) ].
        (* at level 1: the transport of the pulled-back value is the value *)
        eapply (trans1 (b u1 (sm_from sm a u1 X1)));
          [ apply (tr_eq st1 _ _ (coh u1 (sm_from sm a u1 X1) u1 _ _));
            apply (sm_from_eq sm);
            exact (proj1 (Hy u1 (sm_to sm a u1 (sm_from sm a u1 X1)) u1 X1
                            (sm_to_from sm a u1 X1)
                            (sym2 (sm_map sm a) u1 (sm_to sm a u1 (sm_from sm a u1 X1))
                               u1 X1 (sm_to_from sm a u1 X1)))) |].
        eapply (trans1 (b u1 (sm_from sm a u1 X1)));
          [ apply (tr_eq st1 _ _ (coh u1 (sm_from sm a u1 X1) u1 _ _));
            apply (sm_from_to sm) |].
        eapply (trans1 (b u1 (sm_from sm a u1 X1)));
          [ exact (cL u1 (sm_from sm a u1 X1) u1 _ u1 (sm_from sm a u1 X1) _
                     (sm_from_eq sm a u1 _ u1 X1 (sm_to_from sm a u1 X1))
                     (good1 a u1 (sm_from sm a u1 X1)) _ _ (good1 _ _ _)) |].
        exact (iL u1 (sm_from sm a u1 X1) (good1 a u1 (sm_from sm a u1 X1)) _ _
                 (good1 _ _ _)). }
      split; [| exact Hrel].
      intros u1 X1 u1' X1' r2 r2'; split.
      + eapply (trans2 (mapB a b u1 X1));
          [apply step | exact (proj1 (Hy u1 X1 u1' X1' r2 r2'))].
      + eapply (trans2 (mapB a b u1' X1'));
          [ exact (proj2 (Hy u1 X1 u1' X1' r2 r2')) |].
        apply (tr_eq st2 _ _ (mapCoh a b coh u1' X1' u1 X1 r2')).
        apply (sym2 (mapB a b u1 X1)); apply step.
    - (* Sigma: the image's coherence is applied to the proof sm_from_eq builds
         out of sm_to_from, not to the one elTo used, so the two transports
         have to be reconciled -- which the composition law does, since it
         takes the composite's own proof as an argument. *)
      intros [H1 [H2 HR]].
      split; [| split; [| exact HR]].
      + exists (sm_to_from sm a (efst u) (projT1 (Datatypes.fst y))).
        apply (sm_to_eq sm).
        eapply (trans1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))))));
          [ apply (sym1 (b (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))))));
            apply (tr_eq st1 _ _ (coh (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))) (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))) (sm_from_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))));
            apply (iL (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))) (good1 a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))); apply good1 |].
        apply (cL (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))) (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))) (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))
                 (sm_from_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (good1 a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (sm_from_eq sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (efst u) (projT1 (Datatypes.fst y)) (sm_to_from sm a (efst u) (projT1 (Datatypes.fst y)))) (esnd u) (sm_from sm (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (esnd u) (projT2 (Datatypes.fst y))) (good1 _ _ _)).
      + exists (sym2 (sm_map sm a) _ _ _ _ (sm_to_from sm a (efst u) (projT1 (Datatypes.fst y)))).
        apply (sym2 (sm_map sm (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))))).
        eapply (trans2 (sm_map sm (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))));
          [ apply (sm_to_eq sm);
            apply (tr_eq st1 _ _ (coh (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))) (sm_from_eq sm a (efst u) (projT1 (Datatypes.fst y)) (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (sym2 (sm_map sm a) _ _ _ _ (sm_to_from sm a (efst u) (projT1 (Datatypes.fst y)))))));
            apply (sm_from_to sm) |].
        eapply (trans2 (sm_map sm (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))));
          [ apply (sm_to_eq sm);
            eapply (trans1 (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))));
              [ apply (cL (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))) (efst u) (sm_from sm a (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y))))) (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))
                         (sm_from_eq sm a (efst u) (projT1 (Datatypes.fst y)) (efst u) (sm_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (sym2 (sm_map sm a) _ _ _ _ (sm_to_from sm a (efst u) (projT1 (Datatypes.fst y))))) (sm_from_to sm a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (good1 a (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (esnd u) (sm_from sm (b (efst u) (sm_from sm a (efst u) (projT1 (Datatypes.fst y)))) (esnd u) (projT2 (Datatypes.fst y)))
                         (good1 _ _ _))
              | apply iL; apply good1 ] |].
        apply (sm_to_from sm).
    - exact (fun H => H).
  Qed.

  (* One node.  The decoding of Stage_next is the sig that bundles
     self-relatedness, so the two maps carry it along by elTo_eq/elFrom_eq,
     and the round trips are exactly the two lemmas above. *)
  Definition SMor_next
    : SMor (Stage_next st1 U1 E1 OK1) (Stage_next st2 U2 E2 OK2).
  Proof.
    refine (Build_SMor (Stage_next st1 U1 E1 OK1) (Stage_next st2 U2 E2 OK2)
      (fun c => existT _ (projT1 c) (mapRefine (projT2 c)))
      (fun c => eq_refl)
      (fun c u x => exist (fun z => eq2_ (mapRefine (projT2 c)) u z u z)
                      (elTo (projT2 c) u (proj1_sig x))
                      (elTo_eq (projT2 c) u _ u _ (proj2_sig x)))
      (fun c u y => exist (fun z => eq1_ (projT2 c) u z u z)
                      (elFrom (projT2 c) u (proj1_sig y))
                      (elFrom_eq (projT2 c) u _ u _ (proj2_sig y)))
      _ _ _ _).
    - intros c u x u' x'; exact (elTo_eq (projT2 c) u _ u' _).
    - intros c u y u' y'; exact (elFrom_eq (projT2 c) u _ u' _).
    - intros c u y; exact (elTo_from (projT2 c) u _ (proj2_sig y)).
    - intros c u x; exact (elFrom_to (projT2 c) u _ (proj2_sig x)).
  Defined.
End NextMor.


(* ------------------------------------------------------------------ *)
(* The whole hierarchy, by recursion on the Brouwer tree.             *)
(* ------------------------------------------------------------------ *)

Section StageMor.
  Context (U1 U2 : nat -> etm -> Type)
          (E1 : forall m u, U1 m u -> forall u', U1 m u' -> Prop)
          (E2 : forall m u, U2 m u -> forall u', U2 m u' -> Prop)
          (OK1 OK2 : nat -> Prop)
          (um : UMor U1 U2 E1 E2 OK1 OK2).
  Context (E1sym : forall m u x u' x', E1 m u x u' x' -> E1 m u' x' u x)
          (E1trans : forall m u x u' x' u'' x'',
              E1 m u x u' x' -> E1 m u' x' u'' x'' -> E1 m u x u'' x'')
          (E2sym : forall m u x u' x', E2 m u x u' x' -> E2 m u' x' u x)
          (E2trans : forall m u x u' x' u'' x'',
              E2 m u x u' x' -> E2 m u' x' u'' x'' -> E2 m u x u'' x'').

  Local Notation st1_ := (stage U1 E1 OK1).
  Local Notation st2_ := (stage U2 E2 OK2).

  Definition nextOf (beta : Ord) (m : SMor (st1_ beta) (st2_ beta))
    : SMor (Stage_next (st1_ beta) U1 E1 OK1) (Stage_next (st2_ beta) U2 E2 OK2) :=
    SMor_next (st1_ beta) (st2_ beta) m U1 U2 E1 E2 OK1 OK2 um
      (stage_good U1 E1 OK1 beta)
      (fun s => proj1 (eqs_PER U1 E1 OK1 E1sym E1trans beta s))
      (fun s => proj2 (eqs_PER U1 E1 OK1 E1sym E1trans beta s))
      (fun s => proj1 (eqs_PER U2 E2 OK2 E2sym E2trans beta s))
      (fun s => proj2 (eqs_PER U2 E2 OK2 E2sym E2trans beta s)).

  Fixpoint smorStage (alpha : Ord) : SMor (st1_ alpha) (st2_ alpha) :=
    match alpha with
    | ozero => SMor_empty
    | osucc beta =>
        SMor_sum _ _ _ _ (nextOf beta (smorStage beta)) (smorStage beta)
    | osup T f =>
        SMor_sup T _ _ (fun p =>
          SMor_sum _ _ _ _ (nextOf (f p) (smorStage (f p))) (smorStage (f p)))
    end.

  (* The map on codes at a node, which is what the families are built from. *)
  Definition morCode (beta : Ord) (c : U U1 E1 OK1 beta) : U U2 E2 OK2 beta :=
    sm_map (nextOf beta (smorStage beta)) c.

  Lemma morCode_sh beta c : projT1 (morCode beta c) = projT1 c.
  Proof. exact (sm_sh (nextOf beta (smorStage beta)) c). Qed.
End StageMor.

(* ------------------------------------------------------------------ *)
(* The instance: level k into level S k.                              *)
(*                                                                    *)
(* The two universe parameters differ only at m = k, and a level-k     *)
(* code cannot mention that level, so the map is the identity in the   *)
(* branch that survives.  It is written by destructing Nat.eq_dec and  *)
(* refuting m = k from m < k, NOT by transporting along lU_agree,      *)
(* which comes from the opaque lU_spec and would not compute.          *)
(* ------------------------------------------------------------------ *)

(* The equality on the universe decoding is reflexive: at the level it was
   added, an element is a family, and LUnivEq is exactly its uf_ty and
   uf_coh. *)
Lemma lUEq_refl : forall n m u (x : lU (lvl n) m u), m < n -> lUEq (lvl n) m u x u x.
Proof.
  induction n as [| j IH]; intros m u x H; [inversion H |].
  revert x; cbn; unfold sU, sUEq; destruct (Nat.eq_dec m j) as [E | NE].
  - intros x; split; [exact (uf_ty x) | intros; apply uf_coh].
  - intros x; apply IH; lia.
Qed.

Definition lvlTo (k : nat) : forall m u, lOK (lvl k) m -> lU (lvl k) m u -> lU (lvl (S k)) m u.
Proof.
  intros m u o; cbn; unfold sU; destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - exact (fun x => x).
Defined.

Definition lvlFrom (k : nat) : forall m u, lOK (lvl k) m -> lU (lvl (S k)) m u -> lU (lvl k) m u.
Proof.
  intros m u o; cbn; unfold sU; destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - exact (fun x => x).
Defined.

Lemma lvlTo_eq (k : nat) m (o : lOK (lvl k) m) u x u' x' :
  lUEq (lvl k) m u x u' x' ->
  lUEq (lvl (S k)) m u (lvlTo k m u o x) u' (lvlTo k m u' o x').
Proof.
  revert x x'; unfold lvlTo; cbn; unfold sU, sUEq;
    destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - intros x x'; exact (fun H => H).
Qed.

Lemma lvlFrom_eq (k : nat) m (o : lOK (lvl k) m) u y u' y' :
  lUEq (lvl (S k)) m u y u' y' ->
  lUEq (lvl k) m u (lvlFrom k m u o y) u' (lvlFrom k m u' o y').
Proof.
  revert y y'; unfold lvlFrom; cbn; unfold sU, sUEq;
    destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - intros y y'; exact (fun H => H).
Qed.

Lemma lvlTo_from (k : nat) m (o : lOK (lvl k) m) u y :
  lUEq (lvl (S k)) m u (lvlTo k m u o (lvlFrom k m u o y)) u y.
Proof.
  assert (Hm : m < S k) by (apply (lOK_lt k m) in o; lia).
  revert y; unfold lvlTo, lvlFrom; cbn; unfold sU, sUEq;
    destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - intros y; exact (proj1 (conj (lUEq_refl k m u y (proj1 (lOK_lt k m) o)) I)).
Qed.

Lemma lvlFrom_to (k : nat) m (o : lOK (lvl k) m) u x :
  lUEq (lvl k) m u (lvlFrom k m u o (lvlTo k m u o x)) u x.
Proof.
  revert x; unfold lvlTo, lvlFrom; cbn; unfold sU, sUEq;
    destruct (Nat.eq_dec m k) as [E | NE].
  - exfalso; apply (lOK_lt k m) in o; lia.
  - intros x; exact (lUEq_refl k m u x (proj1 (lOK_lt k m) o)).
Qed.

Definition lvlUMor (k : nat)
  : UMor (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k)) (lUEq (lvl (S k)))
         (lOK (lvl k)) (lOK (lvl (S k))) :=
  Build_UMor _ _ _ _ _ _ (lOK_mono k) (lvlTo k) (lvlFrom k)
    (lvlTo_eq k) (lvlFrom_eq k) (lvlTo_from k) (lvlFrom_to k).

(* The code lift at a node: this is Lemma 7.7 on codes. *)
Definition liftCode (k : nat) (beta : Ord) (c : Code k beta) : Code (S k) beta :=
  morCode (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k)) (lUEq (lvl (S k)))
          (lOK (lvl k)) (lOK (lvl (S k))) (lvlUMor k)
          (lsym (lvl k)) (ltrans (lvl k)) (lsym (lvl (S k))) (ltrans (lvl (S k)))
          beta c.

Lemma liftCode_sh k beta (c : Code k beta) : LSh (liftCode k beta c) = LSh c.
Proof. apply morCode_sh. Qed.
