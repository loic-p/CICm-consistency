From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.PiFam Interp.SigFam Interp.WFam Interp.Univ Interp.Env Interp.Elem
  Interp.PiEl Interp.SigEl Interp.WEl Interp.Rec Interp.Lift Interp.LiftN
  Interp.Def.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* Inversion of the interpretation at a type.

   This is what the fundamental lemma needs everywhere a rule eliminates a
   type: the family the induction hypothesis hands over has to be decomposed
   into the families of the type's components.  It is the reason ITy is a
   judgement of its own (see Interp/Def.v's header).

   The shape is passed as a MOTIVE -- a match on the term index -- rather than
   as an equation on the term, so that `destruct` on the derivation specialises
   the term and the family in one go and no equation is ever produced, hence
   none can be lost.  Since the realiser is a free index of ITy, the family's
   type does not mention the term and the match need not be dependent.

   Against v1: no `lvlCast` appears in any decoder.  v1 read `pi (d + j) A B`
   at the level `d + j` and its family was the d-fold lift of a level-j
   Pi-family, so the family in hand lived at a level that was only provably
   the sum; in v2 the former is read at its annotation k outright, and the
   casts sit inside the COMPONENTS (`upF`), which the decoded data carries.
   What the decoders gained instead is the second gap: the two components have
   independent levels. *)

(* composing one more equality of families, which is what travelling along
   ity_conv costs each decoder *)
Lemma ceq_of {k u u'} (F F' : kUFam k u) (G : kUFam k u') :
  kceq (kAt F) (kAt F') -> kceq (kAt F) (kAt G) -> kceq (kAt F') (kAt G).
Proof.
  intros P H.
  eapply ktrU;
    [ exact (famAtWf F') | exact (famAtWf F) | exact (famAtWf G)
    | apply knsymU; exact P | exact H ].
Qed.

Ltac ity_cases D :=
  destruct D as
    [ rho k w Ew | rho k w Ew | rho k d j E w Ew
    | rho k j p wp xp Dp
    | rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gPi Ew DA DB
    | rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gSig Ew DA DB
    | rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gW Ew DA DB
    | rho A k w F DA
    | rho A k w v nf Dv
    | rho A k w Fc Fc' Pc Dc ].

(* ------------------------------------------------------------------ *)
(* The binder formers.  The decoded data is exactly the clause's: two  *)
(* component levels, two gaps with their equations, the components and *)
(* their readings, and an equality to the canonical family.            *)
(* ------------------------------------------------------------------ *)

Definition PiData (rho : Env) (A B : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  { i : nat & { j : nat & { dA : nat & { dB : nat &
  { EA : dA + i = k & { EB : dB + j = k &
  { wA : etm & { FA : kUFam i wA & { B0 : etm &
  { wB : forall u, kElAt (upF dA k EA FA) u -> etm &
  { FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x) &
  { redB : forall u x, reds (eapp B0 u) (wB u x) &
  { cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
             kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))) &
  { gPi : eqty k (epi wA B0) (epi wA B0) &
    ((ITy rho A i wA FA) *
     (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) *
     tyeq w (epi wA B0) *
     kceq (kAt F)
          (kAt (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                  redB cohB gPi)))%type
  } } } } } } } } } } } } } }.

Definition PiDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi _ A B => PiData rho A B k w F
  | _ => unit
  end.

Lemma PiDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  PiDec rho t k w F -> PiDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PiDec] in H |- *; try exact tt.
  destruct H as [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB
    [gPi [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gPi.
  split; [split; [split; [exact DA | exact DB] | exact Hw] |].
  exact (ceq_of F F' _ P Hc).
Qed.

Lemma ity_pi_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PiDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gPi.
    repeat split; [exact DA | exact DB | exists k; exact gPi | apply famAtSelf].
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PiDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Definition SigData (rho : Env) (A B : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  { i : nat & { j : nat & { dA : nat & { dB : nat &
  { EA : dA + i = k & { EB : dB + j = k &
  { wA : etm & { FA : kUFam i wA & { B0 : etm &
  { wB : forall u, kElAt (upF dA k EA FA) u -> etm &
  { FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x) &
  { redB : forall u x, reds (eapp B0 u) (wB u x) &
  { cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
             kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))) &
  { gSig : eqty k (esig wA B0) (esig wA B0) &
    ((ITy rho A i wA FA) *
     (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) *
     tyeq w (esig wA B0) *
     kceq (kAt F)
          (kAt (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                  redB cohB gSig)))%type
  } } } } } } } } } } } } } }.

Definition SigDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | sig_ _ A B => SigData rho A B k w F
  | _ => unit
  end.

Lemma SigDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  SigDec rho t k w F -> SigDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [SigDec] in H |- *; try exact tt.
  destruct H as [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB
    [gSig [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gSig.
  split; [split; [split; [exact DA | exact DB] | exact Hw] |].
  exact (ceq_of F F' _ P Hc).
Qed.

Lemma ity_sig_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> SigDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gSig.
    repeat split; [exact DA | exact DB | exists k; exact gSig | apply famAtSelf].
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (SigDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Definition WData (rho : Env) (A B : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  { i : nat & { j : nat & { dA : nat & { dB : nat &
  { EA : dA + i = k & { EB : dB + j = k &
  { wA : etm & { FA : kUFam i wA & { B0 : etm &
  { wB : forall u, kElAt (upF dA k EA FA) u -> etm &
  { FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x) &
  { redB : forall u x, reds (eapp B0 u) (wB u x) &
  { cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
             kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))) &
  { gW : eqty k (ew wA B0) (ew wA B0) &
    ((ITy rho A i wA FA) *
     (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) *
     tyeq w (ew wA B0) *
     kceq (kAt F)
          (kAt (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                  redB cohB gW)))%type
  } } } } } } } } } } } } } }.

Definition WDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | wt _ A B => WData rho A B k w F
  | _ => unit
  end.

Lemma WDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  WDec rho t k w F -> WDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [WDec] in H |- *; try exact tt.
  destruct H as [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB
    [gW [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gW.
  split; [split; [split; [exact DA | exact DB] | exact Hw] |].
  exact (ceq_of F F' _ P Hc).
Qed.

Lemma ity_w_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> WDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - exists i, j, dA, dB, EA, EB, wA, FA, B0, wB, FB, redB, cohB, gW.
    repeat split; [exact DA | exact DB | exists k; exact gW | apply famAtSelf].
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (WDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* ------------------------------------------------------------------ *)
(* The component-free formers.  At nat, prop and Prf the canonical     *)
(* family exists at EVERY level, so nothing has to be lifted and no    *)
(* gap appears: `natFam k` is the reading of `nat_ k`, full stop.      *)
(* ------------------------------------------------------------------ *)

Definition NatDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | nat_ _ => kceq (kAt F) (kAt (natFam k))
  | _ => unit
  end.

Lemma NatDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  NatDec rho t k w F -> NatDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [NatDec] in H |- *; try exact tt.
  exact (ceq_of F F' (natFam k) P H).
Qed.

Lemma ity_nat_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> NatDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - apply famAtSelf.
  - exact tt.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (NatDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Definition PropDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | prop _ => kceq (kAt F) (kAt (propFam k))
  | _ => unit
  end.

Lemma PropDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  PropDec rho t k w F -> PropDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PropDec] in H |- *; try exact tt.
  exact (ceq_of F F' (propFam k) P H).
Qed.

Lemma ity_prop_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PropDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - apply famAtSelf.
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PropDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Prf: the level j at which the PROPOSITION was read is existential -- a
   proposition lives at its own level, below the Prf's -- and it does not enter
   the family, which only wants the proposition's truth value and realiser. *)
Definition PrfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | prf _ p =>
      { j : nat & { wp : etm & { xp : kElAt (propFam j) wp &
        (ITm rho p j eprop (propFam j) wp xp *
         kceq (kAt F) (kAt (prfF k xp)))%type } } }
  | _ => unit
  end.

Lemma PrfDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  PrfDec rho t k w F -> PrfDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PrfDec] in H |- *; try exact tt.
  destruct H as [j [wp [xp [Dp Hc]]]]; exists j, wp, xp; split;
    [exact Dp | exact (ceq_of F F' (prfF k xp) P Hc)].
Qed.

Lemma ity_prf_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PrfDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - exists j, wp, xp; split; [exact Dp | apply famAtSelf].
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PrfDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a universe, in two steps.  The family's type mentions the
   level, so "F is the universe family" cannot even be stated before the level
   is known; but the level equation is at nat, so it is free. *)
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
  - exact I.
  - destruct A; exact I.
  - destruct A; cbn in nf; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

Definition UnivCeq (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | univ _ m => { d : nat & { E : d + S m = k &
                  kceq (kAt F) (kAt (upF d k E (univFam m))) } }
  | _ => unit
  end.

Lemma UnivCeq_ceq t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  UnivCeq t k w F -> UnivCeq t k w F'.
Proof.
  intros H; destruct t; cbn [UnivCeq] in H |- *; try exact tt.
  destruct H as [d [E H]]; exists d, E; exact (ceq_of F F' _ P H).
Qed.

Lemma ity_univ_ceq rho t k w (F : kUFam k w) : ITy rho t k w F -> UnivCeq t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exists d, E; apply famAtSelf.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (UnivCeq_ceq A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a term that is NOT a former: the only clause that can have
   produced it is ity_of, so the family IS the decoding of a universe
   element.  The equality is on the nose, which is what makes it usable. *)
Definition OfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi _ _ _ => unit
  | sig_ _ _ _ => unit
  | wt _ _ _ => unit
  | nat_ _ => unit
  | prop _ => unit
  | univ _ _ => unit
  | prf _ _ => unit
  | up _ _ => unit
  | _ => { v : kElAt (univFam k) w &
           (ITm rho t (S k) (euniv k) (univFam k) w v *
            kceq (kAt F) (kAt (elFam v)))%type }
  end.

Lemma OfDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  OfDec rho t k w F -> OfDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [OfDec] in H |- *; try exact tt.
  all: (destruct H as [v [Dv Hc]]; exists v; split;
        [exact Dv | exact (ceq_of F F' (elFam v) P Hc)]).
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
  - exact tt.
  - destruct A; cbn in nf;
      try (exists v; split; [exact Dv | apply famAtSelf]); destruct nf.
  - exact (OfDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at the universe lift.  As at the universe itself the level has
   to be matched on, so that the lifted family and the one in hand are seen
   at the same level. *)
Definition UpDec (rho : Env) (t : tm) (k : nat) (w : etm) : kUFam k w -> Type :=
  match t, k return kUFam k w -> Type with
  | up j A, S i =>
      fun F0 => { F1 : kUFam i w &
                  ((j = i) * ITy rho A i w F1 *
                   kceq (kAt F0) (kAt (famLiftK F1)))%type }
  | _, _ => fun _ => unit
  end.

Lemma UpDec_ceq rho t k w (F F' : kUFam k w) (P : kceq (kAt F) (kAt F')) :
  UpDec rho t k w F -> UpDec rho t k w F'.
Proof.
  destruct t; destruct k; cbn [UpDec]; try (exact (fun _ => tt)).
  intros [F1 [[Ej DA] Hc]]; exists F1; split;
    [split; [exact Ej | exact DA] | exact (ceq_of F F' (famLiftK F1) P Hc)].
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
  - exact tt.
  - exists F; split; [split; [reflexivity | exact DA] | apply famAtSelf].
  - destruct A; cbn in nf; try (destruct k; exact tt); destruct nf.
  - exact (UpDec_ceq rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* The level a type former is read at, off the syntax alone.  Every clause of
   ITy but ity_of fixes it outright, now that every former carries its level;
   ity_of takes it from the term's own derivation, so that is the only case
   the level-uniqueness induction has to recurse in. *)
Definition LvlDec (t : tm) (k : nat) : Prop :=
  match t with
  | nat_ kk => k = kk
  | prop kk => k = kk
  | prf kk _ => k = kk
  | univ kk _ => k = kk
  | pi kk _ _ => k = kk
  | sig_ kk _ _ => k = kk
  | wt kk _ _ => k = kk
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
  - reflexivity.
  - destruct A; cbn in nf |- *; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

(* ------------------------------------------------------------------ *)
(* One packaged equality, at Prf: two readings of one proposition give *)
(* EQUAL Prf-families as soon as their truth values agree.  The two    *)
(* propositions may have been read at DIFFERENT levels -- a Prf at     *)
(* level k says nothing about where its proposition lives -- and       *)
(* neither level enters the Prf-code, which carries only the realiser  *)
(* and the Prop.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma prfFam_ceq k j j' u (x : kElAt (propFam j) u) u' (x' : kElAt (propFam j') u') :
  tyeq (eprf u) (eprf u') -> (propVal x <-> propVal x') ->
  kceq (kAt (prfF k x)) (kAt (prfF k x')).
Proof. intros Hty Hiff; exact (conj Hty Hiff). Qed.
