From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift Interp.Def.
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
   dependent: that is one more place where the free-realiser form pays. *)

Definition PiDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi A B =>
      { wA : etm & { FA : kUFam k wA & { B0 : etm &
      { wB : forall u, kElAt FA u -> etm &
      { FB : forall u (x : kElAt FA u), kUFam k (wB u x) &
      { redB : forall u x, reds (eapp B0 u) (wB u x) &
      { isoB : forall u x u' x', kEqAt FA u x u' x' ->
                 iso (kAt (FB u' x')) (kAt (FB u x)) &
      { gPi : eqty k (epi wA B0) (epi wA B0) &
        ((ITy rho A k wA FA) *
         (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) *
         tyeq w (epi wA B0) *
         iso (kAt F) (kAt (piFam k wA B0 FA wB FB redB isoB gPi)))%type } } } } } } } }
  | _ => unit
  end.

Ltac ity_cases D :=
  destruct D as
    [ rho w Ew | rho w Ew | rho m w Ew
    | rho p wp xp Dp
    | rho A B k wA FA B0 wB FB redB isoB gPi Ew DA DB
    | rho A B k wA FA B0 wB FB redB isoB gSig Ew DA DB
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
  destruct H as [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hw] Hiso]]]]]]]]].
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
  - exists wA, FA, B0, wB, FB, redB, isoB, gPi; repeat split;
      [exact DA | exact DB | exists k; exact gPi
      | apply (iso_self (piFam k wA B0 FA wB FB redB isoB gPi))].
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PiDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* The same at the other formers. *)
Definition NatDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | nat_ => iso (kAt F) (kAt (natFam k))
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
  - apply (iso_self (natFam 0)).
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
  | prop => iso (kAt F) (kAt (propFam k))
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
  - apply (iso_self (propFam 0)).
  - exact tt.
  - destruct p; exact tt.
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PropDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Definition PrfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | prf p =>
      { wp : etm & { xp : kElAt (propFam 0) wp &
        (ITm rho p 0 eprop (propFam 0) wp xp * iso (kAt F) (kAt (prfF k xp)))%type } }
  | _ => unit
  end.

Lemma PrfDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  PrfDec rho t k w F -> PrfDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [PrfDec] in H |- *; try exact tt.
  destruct H as [wp [xp [Dp Hiso]]]; exists wp, xp; split;
    [exact Dp | exact (iso_trans _ _ _ (iso_sym _ _ P) Hiso)].
Qed.

Lemma ity_prf_inv rho t k w (F : kUFam k w) : ITy rho t k w F -> PrfDec rho t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - exact tt.
  - exists wp, xp; split; [exact Dp | apply (iso_self (prfF 0 xp))].
  - exact tt.
  - exact tt.
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (PrfDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a universe, in two steps.  The family's type mentions the
   level, so "F is the universe family" cannot even be stated before the level
   is known; but the level equation is at nat, so it is free.  Splitting the
   two is what keeps both statements CAST-FREE: the second matches on the level
   as well as on the term, so that `univFam j` and `F` are seen to live at the
   same level without any eq_rect. *)
Definition UnivLvl (t : tm) (k : nat) : Prop :=
  match t with
  | univ m => k = S m
  | _ => True
  end.

Lemma ity_univ_lvl rho t k w (F : kUFam k w) : ITy rho t k w F -> UnivLvl t k.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact I.
  - exact I.
  - reflexivity.
  - destruct p; exact I.
  - exact I.
  - exact I.
  - destruct A; exact I.
  - destruct A; cbn in nf; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

Definition UnivIso (t : tm) (k : nat) (w : etm) : kUFam k w -> Type :=
  match t, k return kUFam k w -> Type with
  | univ m, S j => fun F0 => iso (kAt F0) (kAt (univFam j))
  | _, _ => fun _ => unit
  end.

Lemma UnivIso_iso t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  UnivIso t k w F -> UnivIso t k w F'.
Proof.
  intros H; destruct t; destruct k; cbn [UnivIso] in H |- *; try exact tt.
  exact (iso_trans _ _ _ (iso_sym _ _ P) H).
Qed.

Lemma ity_univ_iso rho t k w (F : kUFam k w) : ITy rho t k w F -> UnivIso t k w F.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - exact tt.
  - exact tt.
  - apply iso_self.
  - exact tt.
  - destruct k; exact tt.
  - destruct k; exact tt.
  - destruct A; destruct k; exact tt.
  - destruct A; cbn in nf; try (destruct k; exact tt); destruct nf.
  - exact (UnivIso_iso A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* Inversion at a term that is NOT a former: the only clause that can have
   produced it is ity_of, so the family IS the decoding of a universe
   element.  The equality is on the nose, which is what makes it usable --
   ity_of's family is literally `elFam v`. *)
Definition OfDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | pi _ _ => unit
  | sig_ _ _ => unit
  | nat_ => unit
  | prop => unit
  | univ _ => unit
  | prf _ => unit
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
  | up (univ j) A, S i =>
      fun F0 => { F1 : kUFam i w &
                  ((j = S i) * ITy rho A i w F1 *
                   iso (kAt F0) (kAt (famLiftK F1)))%type }
  | _, _ => fun _ => unit
  end.

Lemma UpDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  UpDec rho t k w F -> UpDec rho t k w F'.
Proof.
  (* The annotation has to be named: UpDec's pattern `up (univ j) A` compiles
     to a match on it, which `destruct t` leaves stuck.  The hypothesis is
     introduced only once every match has been resolved, so that no renaming
     by destruct can lose it. *)
  destruct t as
    [ i | A0 B0 t0 | A0 t0 | A0 B0 f0 a0 | f0 a0 | A0 B0 t0 a0 | A0 B0 p0
    | A0 B0 p0 | A0 B0 | A0 B0 | | | n0 | C0 z0 s0 n0 | m0 | Au A0 | A0 t0
    | | p0 | A0 p0 | | T0 e0 | A0 t0 a0 | A0 a0 | A0 B0 t0 a0 e0 b0 ];
    destruct k; cbn [UpDec]; try (exact (fun _ => tt)).
  all: (destruct Au; cbn [UpDec]; try (exact (fun _ => tt))).
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
  - destruct k; exact tt.
  - destruct k; exact tt.
  - exists F; split; [split; [reflexivity | exact DA] | apply iso_self].
  - destruct A; cbn in nf; try (destruct k; exact tt); destruct nf.
  - exact (UpDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

(* The level a type former is read at, off the syntax alone.  Every clause of
   ITy but ity_pi, ity_sig and ity_of fixes it outright; the two formers take it
   from their domain and ity_of from the term's own derivation, so those are the
   only cases the level-uniqueness induction has to recurse in. *)
Definition LvlDec (t : tm) (k : nat) : Prop :=
  match t with
  | nat_ => k = 0
  | prop => k = 0
  | prf _ => k = 0
  | univ m => k = S m
  | up Au _ => match Au with univ j => k = j | _ => True end
  | _ => True
  end.

Lemma ity_lvl_dec rho t k w (F : kUFam k w) : ITy rho t k w F -> LvlDec t k.
Proof.
  revert rho t k w F; fix IH 6; intros rho t k w F D; ity_cases D.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact I.
  - exact I.
  - reflexivity.
  - destruct A; cbn in nf |- *; try exact I; destruct nf.
  - exact (IH rho A k w Fc Dc).
Qed.

(* ------------------------------------------------------------------ *)
(* Functionality on types.  Stated ACROSS TWO RELATED ENVIRONMENTS,    *)
(* which is the only form under which the Pi case composes: the two    *)
(* derivations decompose the type with different domain families, so   *)
(* the codomains are interpreted in different extended environments.   *)
(* ------------------------------------------------------------------ *)

Lemma prfFam_iso k u (x : kElAt (propFam 0) u) u' (x' : kElAt (propFam 0) u') :
  tyeq (eprf u) (eprf u') -> (propVal x <-> propVal x') ->
  iso (kAt (prfF k x)) (kAt (prfF k x')).
Proof. intros Hty Hiff; exact (conj Hty Hiff). Qed.

Lemma ity_nat_fun rho rho' k w w' (F : kUFam k w) (F' : kUFam k w') :
  ITy rho nat_ k w F -> ITy rho' nat_ k w' F' -> iso (kAt F) (kAt F').
Proof.
  intros D D'; eapply iso_trans;
    [exact (ity_nat_inv rho nat_ k w F D)
    | apply iso_sym, (ity_nat_inv rho' nat_ k w' F' D')].
Qed.

Lemma ity_prop_fun rho rho' k w w' (F : kUFam k w) (F' : kUFam k w') :
  ITy rho prop k w F -> ITy rho' prop k w' F' -> iso (kAt F) (kAt F').
Proof.
  intros D D'; eapply iso_trans;
    [exact (ity_prop_inv rho prop k w F D)
    | apply iso_sym, (ity_prop_inv rho' prop k w' F' D')].
Qed.

Lemma ity_prf_fun rho rho' p k w w' (F : kUFam k w) (F' : kUFam k w')
  (Hp : forall wp xp wp' xp', ITm rho p 0 eprop (propFam 0) wp xp ->
          ITm rho' p 0 eprop (propFam 0) wp' xp' ->
          tyeq (eprf wp) (eprf wp') /\ (propVal xp <-> propVal xp')) :
  ITy rho (prf p) k w F -> ITy rho' (prf p) k w' F' -> iso (kAt F) (kAt F').
Proof.
  intros D D'.
  destruct (ity_prf_inv rho (prf p) k w F D) as [wp [xp [Dp Hiso]]].
  destruct (ity_prf_inv rho' (prf p) k w' F' D') as [wp' [xp' [Dp' Hiso']]].
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  destruct (Hp wp xp wp' xp' Dp Dp') as [H1 H2]; apply prfFam_iso; assumption.
Qed.

Lemma ity_pi_fun rho rho' A B k w w' (F : kUFam k w) (F' : kUFam k w')
  (Hty : tyeq w w')
  (HA : forall wA (FA : kUFam k wA) wA' (FA' : kUFam k wA'),
          ITy rho A k wA FA -> ITy rho' A k wA' FA' -> iso (kAt FA) (kAt FA'))
  (HB : forall wA (FA : kUFam k wA) wA' (FA' : kUFam k wA')
               u x u' x' wBx (FBx : kUFam k wBx) wBx' (FBx' : kUFam k wBx'),
          kRel FA FA' u x u' x' ->
          ITy (ext rho FA u x) B k wBx FBx -> ITy (ext rho' FA' u' x') B k wBx' FBx' ->
          iso (kAt FBx) (kAt FBx')) :
  ITy rho (pi A B) k w F -> ITy rho' (pi A B) k w' F' -> iso (kAt F) (kAt F').
Proof.
  intros D D'.
  destruct (ity_pi_inv rho (pi A B) k w F D)
    as [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hw] Hiso]]]]]]]]].
  destruct (ity_pi_inv rho' (pi A B) k w' F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply piFam_iso.
  - (* the two Pi-realisers are layer-1 equal: each is equal to the family's
       own realiser, and those are equal by hypothesis *)
    eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact Hty | exact Hw'].
  - apply (HA wA FA wA' FA'); [exact DA | exact DA'].
  - intros u x u' x' Hrel.
    apply (HB wA FA wA' FA' u x u' x'); [exact Hrel | apply DB | apply DB'].
Qed.

(* ------------------------------------------------------------------ *)
(* The same at Sigma.                                                 *)
(* ------------------------------------------------------------------ *)

Definition SigDec (rho : Env) (t : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  match t with
  | sig_ A B =>
      { wA : etm & { FA : kUFam k wA & { B0 : etm &
      { wB : forall u, kElAt FA u -> etm &
      { FB : forall u (x : kElAt FA u), kUFam k (wB u x) &
      { redB : forall u x, reds (eapp B0 u) (wB u x) &
      { isoB : forall u x u' x', kEqAt FA u x u' x' ->
                 iso (kAt (FB u' x')) (kAt (FB u x)) &
      { gSig : eqty k (esig wA B0) (esig wA B0) &
        ((ITy rho A k wA FA) *
         (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) *
         tyeq w (esig wA B0) *
         iso (kAt F) (kAt (sigFam k wA B0 FA wB FB redB isoB gSig)))%type } } } } } } } }
  | _ => unit
  end.

Lemma SigDec_iso rho t k w (F F' : kUFam k w) (P : iso (kAt F) (kAt F')) :
  SigDec rho t k w F -> SigDec rho t k w F'.
Proof.
  intros H; destruct t; cbn [SigDec] in H |- *; try exact tt.
  destruct H as [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hw] Hiso]]]]]]]]].
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
  - exists wA, FA, B0, wB, FB, redB, isoB, gSig; repeat split;
      [exact DA | exact DB | exists k; exact gSig
      | apply (iso_self (sigFam k wA B0 FA wB FB redB isoB gSig))].
  - destruct A; exact tt.
  - destruct A; cbn in nf; try exact tt; destruct nf.
  - exact (SigDec_iso rho A k w Fc Fc' Pc (IH rho A k w Fc Dc)).
Qed.

Lemma ity_sig_fun rho rho' A B k w w' (F : kUFam k w) (F' : kUFam k w')
  (Hty : tyeq w w')
  (HA : forall wA (FA : kUFam k wA) wA' (FA' : kUFam k wA'),
          ITy rho A k wA FA -> ITy rho' A k wA' FA' -> iso (kAt FA) (kAt FA'))
  (HB : forall wA (FA : kUFam k wA) wA' (FA' : kUFam k wA')
               u x u' x' wBx (FBx : kUFam k wBx) wBx' (FBx' : kUFam k wBx'),
          kRel FA FA' u x u' x' ->
          ITy (ext rho FA u x) B k wBx FBx -> ITy (ext rho' FA' u' x') B k wBx' FBx' ->
          iso (kAt FBx) (kAt FBx')) :
  ITy rho (sig_ A B) k w F -> ITy rho' (sig_ A B) k w' F' -> iso (kAt F) (kAt F').
Proof.
  intros D D'.
  destruct (ity_sig_inv rho (sig_ A B) k w F D)
    as [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hw] Hiso]]]]]]]]].
  destruct (ity_sig_inv rho' (sig_ A B) k w' F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply sigFam_iso.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact Hty | exact Hw'].
  - apply (HA wA FA wA' FA'); [exact DA | exact DA'].
  - intros u x u' x' Hrel.
    apply (HB wA FA wA' FA' u x u' x'); [exact Hrel | apply DB | apply DB'].
Qed.
