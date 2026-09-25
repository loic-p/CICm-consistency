From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift Interp.LiftN Interp.Def.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* Inversion of the interpretation at a type.

   This is what the fundamental lemma needs everywhere a rule eliminates a
   type: the family the induction hypothesis hands over has to be decomposed
   into the families of the type's components.  It is the reason ITy is a
   judgement of its own (see Interp/Def.v's header).

   The shape is passed as a MOTIVE -- a match on the term index -- rather than
   as an equation on the term, so that `destruct` on the derivation specialises
   the term and the family in one go and no equation is ever produced, hence
   none can be lost.  Since the realiser became a free index of ITy, the
   family's type no longer mentions the term and the match no longer has to be
   dependent: that is one more place where the free-realiser form pays.

   At Pi and Sigma the components' level j and the gap d up to the annotation
   are existential, and the family in hand lives at the annotation's level,
   which is only provably `d + j`: hence the one lvlCast, which the consumer
   destructs away immediately. *)

Definition PiData (rho : Env) (A B : tm) (d j : nat) (w : etm)
  (F : kUFam (d + j) w) : Type :=
  { wA : etm & { FA : kUFam j wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (x : kElAt FA u), kUFam j (wB u x) &
  { redB : forall u x, reds (eapp B0 u) (wB u x) &
  { isoB : forall u x u' x', kEqAt FA u x u' x' ->
             iso (kAt (FB u' x')) (kAt (FB u x)) &
  { gPi : eqty j (epi wA B0) (epi wA B0) &
    ((ITy rho A j wA FA) *
     (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) *
     tyeq w (epi wA B0) *
     iso (kAt F)
         (kAt (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi))))%type } } } } } } } }.

Definition PiDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi _ A B =>
      { d : nat & { j : nat & { E : d + j = k &
        PiData rho A B d j w (lvlCast (eq_sym E) F) } } }
  | _ => unit
  end.

Ltac ity_cases D :=
  destruct D as
    [ rho k w Ew | rho k w Ew | rho d j w Ew
    | rho k j p wp xp Dp
    | rho A B d j wA FA B0 wB FB redB isoB gPi Ew DA DB
    | rho A B d j wA FA B0 wB FB redB isoB gSig Ew DA DB
    | rho A k w F DA
    | rho A k w v nf Dv
    | rho A k w Fc Fc' Pc Dc ].

(* Each *Dec ends in an isomorphism to the canonical family, so it travels
   along ity_conv by composing one more iso.  That is what keeps the inversions
   single-case now that ITy has a conversion clause. *)
Lemma PiDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  PiDec rho t k w F -> PiDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PiDec] in H |- *; try exact tt.
  destruct H as [d [j [E Hd]]]; exists d, j, E; destruct E.
  cbn [lvlCast eq_sym] in Hd |- *.
  destruct Hd as [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hw] Hiso]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gPi.
  split; [split; [split; [exact DA | exact DB] | exact Hw] |].
  exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso).
Qed.

Lemma ity_pi_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PiDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exists d, j, eq_refl; cbn [lvlCast eq_sym].
    exists wA, FA, B0, wB, FB, redB, isoB, gPi; repeat split;
      [exact DA | exact DB | exists j; exact gPi
      | apply (iso_self (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi)))].
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PiDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* The same at the other formers.  At nat, prop and Prf the canonical family
   exists at EVERY level, so nothing has to be lifted and no cast appears:
   `natFam k` is the reading of `nat_ k`, full stop. *)
Definition NatDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | nat_ _ => iso (kAt F) (kAt (natFam k))
  | _ => unit
  end.

Lemma NatDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  NatDec rho t k w F -> NatDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [NatDec] in H |- *; try exact tt.
  exact (iso_trans _ _ _ (iso_sym _ _ P) H).
Qed.

Lemma ity_nat_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> NatDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - apply (iso_self (natFam k)).
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (NatDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Definition PropDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | prop _ => iso (kAt F) (kAt (propFam k))
  | _ => unit
  end.

Lemma PropDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  PropDec rho t k w F -> PropDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PropDec] in H |- *; try exact tt.
  exact (iso_trans _ _ _ (iso_sym _ _ P) H).
Qed.

Lemma ity_prop_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PropDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - apply (iso_self (propFam k)).
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PropDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Prf: the level j at which the PROPOSITION was read is existential -- a
   proposition lives at its own level, below the Prf's -- and it does not enter
   the family, which only wants the proposition's truth value and realiser. *)
Definition PrfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | prf _ p =>
      { j : nat & { wp : etm & { xp : kElAt (propFam j) wp &
        (ITm rho p j eprop (propFam j) wp xp * iso (kAt F) (kAt (prfF k xp)))%type } } }
  | _ => unit
  end.

Lemma PrfDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  PrfDec rho t k w F -> PrfDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PrfDec] in H |- *; try exact tt.
  destruct H as [j [wp [xp [Dp Hiso]]]]; exists j, wp, xp; split;
    [exact Dp | exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso)].
Qed.

Lemma ity_prf_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PrfDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - exists j, wp, xp; split; [exact Dp | apply (iso_self (prfF k xp))].
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PrfDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a universe, in two steps.  The family's type mentions the
   level, so "F is the universe family" cannot even be stated before the level
   is known; but the level equation is at nat, so it is free.  `univ kk j` is
   read at kk and its value is the (kk - S j)-fold lift of the universe that
   level S j adds, which is the shape of the ity_univ clause. *)
Definition UnivLvl (t : tm) (k : nat) : Prop :=
  match t with
  | univ kk m => k = kk /\ m < kk
  | _ => True
  end.

Lemma ity_univ_lvl rho t k w (F : kUFam k w) : ITy rho t k w F -> UnivLvl t k.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact I.
  - exact I.
  - split; [reflexivity | lia].
  - destruct p; exact I.
  - exact I.
  - exact I.
  - destruct A; exact I.
  - destruct A; cbn in nf; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

Definition UnivIso (t : tm) (k : nat) (w : etm) : kUFam k w -> Type :=
  match t return kUFam k w -> Type with
  | univ _ m =>
      fun F0 => { d : nat & { E : d + S m = k &
                  iso (kAt (lvlCast (eq_sym E) F0))
                      (kAt (famLiftN d (univFam m))) } }
  | _ => fun _ => unit
  end.

Lemma UnivIso_iso t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  UnivIso t k w F -> UnivIso t k w F'.
Proof.
  intros H; destruct t; cbn [UnivIso] in H |- *; try exact tt.
  destruct H as [d [E H]]; exists d, E; destruct E; cbn [lvlCast eq_sym] in H |- *.
  exact (iso_trans _ _ _ (iso_sym _ _ P) H).
Qed.

Lemma ity_univ_iso rho t k w (F : kUFam k w) : ITy rho t k w F -> UnivIso t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exists d, eq_refl; cbn [lvlCast eq_sym]; apply iso_self.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (UnivIso_iso A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a term that is NOT a former: the only clause that can have
   produced it is ity_of, so the family IS the decoding of a universe
   element.  The equality is on the nose, which is what makes it usable --
   ity_of's family is literally `elFam v`. *)
Definition OfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi _ _ _ => unit
  | sig_ _ _ _ => unit
  | nat_ _ => unit
  | prop _ => unit
  | univ _ _ => unit
  | prf _ _ => unit
  | up _ _ => unit
  | _ => { v : kElAt (univFam k) w &
           (ITm rho t (S k) (euniv k) (univFam k) w v *
            iso (kAt F) (kAt (elFam v)))%type }
  end.

Lemma OfDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  OfDec rho t k w F -> OfDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [OfDec] in H |- *; try exact tt.
  all: (destruct H as [v [Dv Hiso]]; exists v; split;
        [exact Dv | exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso)]).
Qed.

Lemma ity_of_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> OfDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct A; cbn in nf;
      try (exists v; split; [exact Dv | apply iso_self]); destruct nf.
  - exact (OfDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at the universe lift.  As at the universe itself the level has
   to be matched on, so that the lifted family and the one in hand are seen
   at the same level. *)
Definition UpDec (rho : Env) (t : tm) (k : nat) (w : etm) : kUFam k w -> Type :=
  match t, k return kUFam k w -> Type with
  | up j A, S i =>
      fun F0 => { F1 : kUFam i w &
                  ((j = i) * ITy rho A i w F1 *
                   iso (kAt F0) (kAt (famLiftK F1)))%type }
  | _, _ => fun _ => unit
  end.

Lemma UpDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  UpDec rho t k w F -> UpDec rho t k w F'.
Proof.
  destruct t; destruct k; cbn [UpDec]; try (exact (fun _ => tt)).
  intros [F1 [[Ej DA] Hiso]]; exists F1; split;
    [split; [exact Ej | exact DA] | exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso)].
Qed.

Lemma ity_up_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> UpDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - exists F; split; [split; [reflexivity | exact DA] | apply iso_self].
  - destruct A; cbn in nf; try (destruct k; exact tt); destruct nf.
  - exact (UpDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* The level a type former is read at, off the syntax alone.  Every clause of
   ITy but ity_of fixes it outright, now that every former carries its level;
   ity_of takes it from the term's own derivation, so that is the only case the
   level-uniqueness induction has to recurse in. *)
Definition LvlDec (t : tm) (k : nat) : Prop :=
  match t with
  | nat_ kk => k = kk
  | prop kk => k = kk
  | prf kk _ => k = kk
  | univ kk _ => k = kk
  | pi kk _ _ => k = kk
  | sig_ kk _ _ => k = kk
  | up j _ => k = S j
  | _ => True
  end.

Lemma ity_lvl_dec rho t k w (F : kUFam k w) : ITy rho t k w F -> LvlDec t k.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct A; cbn in nf |- *; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

(* ------------------------------------------------------------------ *)
(* One packaged isomorphism, at Prf: two readings of one proposition   *)
(* give isomorphic Prf-families as soon as their truth values agree.   *)
(* The two propositions may have been read at DIFFERENT levels -- a    *)
(* Prf at level k says nothing about where its proposition lives -- and *)
(* neither level enters the Prf-code, which carries only the realiser   *)
(* and the Prop.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma prfFam_iso k j j' u (x : kElAt (propFam j) u) u' (x' : kElAt (propFam j') u') :
  tyeq (eprf u) (eprf u') -> (propVal x <-> propVal x') ->
  iso (kAt (prfF k x)) (kAt (prfF k x')).
Proof. intros Hty Hiff; exact (conj Hty Hiff). Qed.

(* ------------------------------------------------------------------ *)
(* The same at Sigma.                                                 *)
(* ------------------------------------------------------------------ *)

Definition SigData (rho : Env) (A B : tm) (d j : nat) (w : etm)
  (F : kUFam (d + j) w) : Type :=
  { wA : etm & { FA : kUFam j wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (x : kElAt FA u), kUFam j (wB u x) &
  { redB : forall u x, reds (eapp B0 u) (wB u x) &
  { isoB : forall u x u' x', kEqAt FA u x u' x' ->
             iso (kAt (FB u' x')) (kAt (FB u x)) &
  { gSig : eqty j (esig wA B0) (esig wA B0) &
    ((ITy rho A j wA FA) *
     (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) *
     tyeq w (esig wA B0) *
     iso (kAt F)
         (kAt (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig))))%type } } } } } } } }.

Definition SigDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | sig_ _ A B =>
      { d : nat & { j : nat & { E : d + j = k &
        SigData rho A B d j w (lvlCast (eq_sym E) F) } } }
  | _ => unit
  end.

Lemma SigDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  SigDec rho t k w F -> SigDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [SigDec] in H |- *; try exact tt.
  destruct H as [d [j [E Hd]]]; exists d, j, E; destruct E.
  cbn [lvlCast eq_sym] in Hd |- *.
  destruct Hd as [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hw] Hiso]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig.
  split; [split; [split; [exact DA | exact DB] | exact Hw] |].
  exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso).
Qed.

Lemma ity_sig_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> SigDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exists d, j, eq_refl; cbn [lvlCast eq_sym].
    exists wA, FA, B0, wB, FB, redB, isoB, gSig; repeat split;
      [exact DA | exact DB | exists j; exact gSig
      | apply (iso_self (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig)))].
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (SigDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.
