From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def.

(* Lemma 8.4: every semantic element of a code is a layer-1 good realiser of
   the code's shadow, and related elements have related realisers.  No
   induction is needed: the Good conjunct is built into every clause of El
   but the universe one, where the decoding is the parameter Univ and the
   property is assumed of it (discharged in Codes/Levels.v).  The r_ne
   clause is vacuous because its decoding is empty -- which is the whole
   point of carrying stuck types as codes with no elements. *)

(* What the universe decoding must satisfy for soundness.  These are
   properties of the completed lower level, not of the current stage. *)
Record UnivSound (Univ : nat -> etm -> Type)
                 (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
                 (UnivOK : nat -> Prop) := {
  us_ty : forall m u, Univ m u -> eqty m u u;
  us_eq : forall m u x u' x', UnivEq m u x u' x' -> eqty m u u';
  us_ok : forall m T, UnivOK m -> eval T (euniv m) -> Good_ty T
}.

Section SoundRefine.
  Context (st : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (US : UnivSound Univ UnivEq UnivOK).

  Lemma El_good {T} (r : Refine st UnivOK T) u :
    El st Univ UnivOK r u -> Good T u.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
      cbn; intros x.
    - exact (Datatypes.snd x).
    - exact (Datatypes.snd x).
    - exact (Datatypes.snd x).
    - eapply Rel_univ_intro; eauto using us_ok, us_ty.
    - exact (Datatypes.snd x).
    - exact (Datatypes.snd x).
    - destruct x.
  Qed.

  Lemma eqEl_rel {T} (r : Refine st UnivOK T) u x u' x' :
    eqEl st Univ UnivEq UnivOK r u x u' x' -> Rel T u u'.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
      cbn in x, x' |- *; intros H.
    - exact (proj2 H).
    - exact (proj2 H).
    - exact H.
    - eapply Rel_univ_intro; eauto using us_ok, us_eq.
    - exact (proj2 H).
    - exact (proj2 (proj2 H)).
    - destruct x.
  Qed.
End SoundRefine.

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (US : UnivSound Univ UnivEq UnivOK).

  Local Notation stage_ := (stage Univ UnivEq UnivOK).

  (* The same statement at a whole stage, by structural recursion on the
     Brouwer tree: every node is a Stage_next, where the two lemmas above
     apply verbatim. *)
  Lemma sub_good alpha : forall (s : (stage_ alpha).(St)) u,
    (stage_ alpha).(StEl) s u -> Good ((stage_ alpha).(StSh) s) u.
  Proof.
    induction alpha as [| beta IHb | T f IHf]; cbn.
    - intros [].
    - intros [c | s] u; [intros x | apply IHb].
      exact (@El_good _ Univ UnivEq UnivOK US _ (projT2 c) u (proj1_sig x)).
    - intros [p [c | s]] u; [intros x | apply (IHf p)].
      exact (@El_good _ Univ UnivEq UnivOK US _ (projT2 c) u (proj1_sig x)).
  Qed.

  Lemma sub_rel alpha : forall (s : (stage_ alpha).(St)) u x u' x',
    (stage_ alpha).(StEq) s u x u' x' -> Rel ((stage_ alpha).(StSh) s) u u'.
  Proof.
    induction alpha as [| beta IHb | T f IHf]; cbn.
    - intros [].
    - intros [c | s] u x u' x'; [intros H | apply IHb].
      exact (@eqEl_rel _ Univ UnivEq UnivOK US _ (projT2 c) u (proj1_sig x) u' (proj1_sig x') H).
    - intros [p [c | s]] u x u' x'; [intros H | apply (IHf p)].
      exact (@eqEl_rel _ Univ UnivEq UnivOK US _ (projT2 c) u (proj1_sig x) u' (proj1_sig x') H).
  Qed.

  Lemma U_good beta (c : U Univ UnivEq UnivOK beta) u :
    (Ust Univ UnivEq UnivOK beta).(StEl) c u -> Good (projT1 c) u.
  Proof. exact (@sub_good (osucc beta) (inl c) u). Qed.

  Lemma U_rel beta (c : U Univ UnivEq UnivOK beta) u x u' x' :
    (Ust Univ UnivEq UnivOK beta).(StEq) c u x u' x' -> Rel (projT1 c) u u'.
  Proof. exact (@sub_rel (osucc beta) (inl c) u x u' x'). Qed.
End Level.
