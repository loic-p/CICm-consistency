From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.EqPER Codes.Iso.
From Stdlib Require Import Arith Eqdep_dec.

(* Well-formed codes: the transport data carried by a Pi-code is the
   canonical one, i.e. it agrees with the transport of Codes/Iso.v.  The
   interpretation only ever builds codes whose coh IS that transport, so
   well-formedness is free there; and for well-formed codes the transport
   along a self-isomorphism is the identity up to the equality, which is the
   last clause of blueprint Lemma 8.6 and what validates both the identity
   law of a Pi-code and the computation rule of transp at refl. *)

Section WFRefine.
  Context (st : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (hd : HJ st st) (wfS : st.(St) -> Prop).

  Local Notation eqS := st.(StEq).
  Local Notation eqEl_ := (eqEl st Univ UnivEq UnivOK).

  Definition wfRefine {T} (r : Refine st UnivOK T) : Prop :=
    match r with
    | r_pi _ _ _ _ _ _ a _ b _ coh _ _ =>
        wfS a /\ (forall u x, wfS (b u x)) /\
        (forall u x u' x' (rr : eqS a u x u' x')
                (Q : hj_rel hd (b u' x') (b u x)) v y,
           eqS (b u x) v (tr (coh _ _ _ _ rr) v y) v (hj_to hd (b u' x') (b u x) Q v y))
    | r_sig _ _ _ _ _ _ a _ b _ coh _ _ =>
        wfS a /\ (forall u x, wfS (b u x)) /\
        (forall u x u' x' (rr : eqS a u x u' x')
                (Q : hj_rel hd (b u' x') (b u x)) v y,
           eqS (b u x) v (tr (coh _ _ _ _ rr) v y) v (hj_to hd (b u' x') (b u x) Q v y))
    | _ => True
    end.

  Definition WF_next : U_of st UnivOK -> Prop := fun c => wfRefine (projT2 c).

  (* The identity clause.  The Pi case is where well-formedness is spent:
     the pullback of an argument along a self-isomorphism is equal to it, so
     the two codomain codes are related by coh, and well-formedness says the
     transport between them is coh. *)
  Context (Hgood : StGood st)
          (Hsym : forall s, EqSym st s) (Htrans : forall s, EqTrans st s)
          (IH : forall s, wfS s -> forall (P : hj_rel hd s s) u x,
                    eqS s u (hj_to hd s s P u x) u x).

  Lemma toRefine_id {T} (r : Refine st UnivOK T) :
    wfRefine r ->
    forall (P : isoRefine st st UnivOK hd r r) u x,
      eqEl_ r u x u x ->
      eqEl_ r u (toRefine st st Univ UnivOK hd r r P u x) u x.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
      cbn; intros W P u x Hx.
    - split; [reflexivity | exact (Datatypes.snd x)].
    - split; [tauto | exact (Datatypes.snd x)].
    - exact (Datatypes.snd x).
    - destruct (Nat.eq_dec m m) as [E | NE]; [| destruct (NE eq_refl)].
      replace E with (eq_refl : m = m) by (apply UIP_dec; apply Nat.eq_dec).
      exact Hx.
    - destruct W as [Wa [Wb Wc]]; destruct Hx as [Hf HR].
      (* the pullback of y1 along the self-isomorphism of the domain is y1 *)
      assert (Epull : forall u1 y1,
                 eqS a u1 (hj_pull hd a a (proj1 (proj2 P)) u1 y1) u1 y1).
      { intros u1 y1.
        eapply Htrans; [apply Hsym; apply (IH a Wa) | apply (hj_pull_to hd)]. }
      split; [| exact HR].
      intros u1 y1 u1' y1' r2 r2'.
      pose proof (Epull u1 y1) as ey.
      pose proof (Hsym a _ _ _ _ ey) as ey'.
      split.
      + eapply Htrans; [| exact (proj1 (Hf u1 y1 u1' y1' r2 r2'))].
        eapply Htrans; [| apply Hsym; exact (proj1 (Hf u1 y1 u1 _ ey' ey))].
        apply Hsym; apply Wc.
      + eapply Htrans; [exact (proj2 (Hf u1 y1 u1' y1' r2 r2')) |].
        apply (tr_eq _ _ _ (coh _ _ _ _ r2')); apply Hsym.
        eapply Htrans; [| apply Hsym; exact (proj1 (Hf u1 y1 u1 _ ey' ey))].
        apply Hsym; apply Wc.
    - (* Sigma: the first component's self-transport is the identity by the
         hypothesis on the domain, and well-formedness says the second one's
         is the coherence at exactly that relation. *)
      destruct W as [Wa [Wb Wc]]; destruct Hx as [H1 [H2 HR]].
      split; [| split; [| exact HR]].
      + exists (IH a Wa (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))).
        apply Hsym; apply Wc.
      + exists (Hsym a _ _ _ _ (IH a Wa (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))).
        apply (sig_flipL st Hgood Hsym Htrans a b coh cL iL
                 (efst u) (hj_to hd a a (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (projT1 (Datatypes.fst x))
                 (IH a Wa (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (Hsym a _ _ _ _ (IH a Wa (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))).
        apply Hsym; apply Wc.
    - destruct x.
  Qed.
End WFRefine.

(* The identity property of a code, as a predicate on a stage: transporting
   along any self-isomorphism does nothing.  The interpretation carries this
   through its own induction -- it is not proved here by a recursion on the
   stage, because the relation hj alpha alpha at an arbitrary element of
   Sub alpha does not reduce until that element's node is known, whereas at
   the injections the interpretation actually uses (Def.v's U_Sub_succ and
   Sub_Sub_sup) it reduces to hjU gamma gamma on the nose. *)
Definition IdP (st : Stage) (hd : HJ st st) (s : st.(St)) : Prop :=
  forall (P : hj_rel hd s s) u x, st.(StEq) s u (hj_to hd s s P u x) u x.

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).
  Local Notation Ust_ := (Ust Univ UnivEq UnivOK).
  Local Notation hj_ := (hj Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation hjU_ := (hjU Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).

  (* Good codes at stage alpha: those whose self-transports are identities. *)
  Definition idps (alpha : Ord) : (stage_ alpha).(St) -> Prop :=
    IdP (stage_ alpha) (hj_ alpha alpha).

  Definition wfa (alpha : Ord) {T} (r : Refine (stage_ alpha) UnivOK T) : Prop :=
    wfRefine (stage_ alpha) UnivOK (hj_ alpha alpha) (idps alpha) r.

  (* Blueprint Lemma 8.6, last clause, in the form the interpretation uses:
     a code whose components have identity self-transports and whose own
     coherence data is the canonical transport has an identity
     self-transport too. *)
  Lemma idp_next (alpha : Ord) {T} (r : Refine (stage_ alpha) UnivOK T) :
    wfa alpha r -> IdP (Ust_ alpha) (hjU_ alpha alpha) (existT _ T r).
  Proof.
    intros W P u x.
    exact (toRefine_id (stage_ alpha) Univ UnivEq UnivOK (hj_ alpha alpha) (idps alpha)
             (stage_good Univ UnivEq UnivOK alpha)
             (ssym Univ UnivEq UnivOK UnivEq_sym UnivEq_trans alpha)
             (strans Univ UnivEq UnivOK UnivEq_sym UnivEq_trans alpha)
             (fun s W' => W') r W P u (proj1_sig x) (proj2_sig x)).
  Qed.
End Level.
