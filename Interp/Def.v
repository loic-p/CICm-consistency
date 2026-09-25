From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift Interp.LiftN.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* Blueprint 9.1: the interpretation, as an inductive relation on raw syntax
   and an environment.

   TWO judgements, mutually defined:

     ITy rho A k F      "the value of the TYPE A in rho is the family F"
     ITm rho t k Sy F x "the value of t in rho is x, an element of F, which is
                         the value of t's type -- a level-k family with
                         realiser Sy"

   and two clauses bridge them: `i_ty` reads a family as an element of the
   universe, `ity_of` reads an element of the universe as a family.  A type is
   a term of a universe, so ONE relation would do mathematically; the split is
   forced by inversion, and that is worth spelling out, because it is the only
   structural constraint the proofs impose on this definition.

   Rocq's `inversion` states an equation for an index only when the index's
   type does not itself depend on an index still being equated.  In ITm the
   value x has type `kElAt F (ers rho t)`, which depends on the family index
   F; inversion therefore packs (k, Sy, F, x) into an existT and can peel it
   only as far as the components with decidable equality -- nat and etm.
   Recovering x would need injectivity of existT at `kUFam k Sy`, i.e. UIP at
   a type of records containing functions, which is not available.  In ITy the
   family IS the last index and its type `kUFam k (ers rho A)` depends only on
   rho, A and k, so inversion delivers `F = piF ...` outright.  Every
   inversion the fundamental lemma needs is at a TYPE -- the typing rules
   expose the type's former whenever they eliminate it -- so the split is
   exactly enough.

   Note what this means for functionality: the interpretation is functional up
   to isomorphism ON TYPES, and that is all that is used.  It is NOT functional
   on terms without fixing the type: `lam A t` has a value at the Pi-family of
   `pi A (prf p)` and another at the Prf-family of `prf (all A p)`, and those
   two families are not isomorphic.

   THE REALISERS ARE FREE INDICES, pinned by one equation premise per clause
   (`Ew : w = ers rho t`), rather than computed as `ers rho t`.  This is not a
   matter of taste.  With the realiser computed, weakening and substitution
   have to transport the family along an equality of realisers -- and a cast in
   a family's TYPE propagates into every component indexed by that family: the
   codomain family FB has to be precomposed with the inverse cast, and then
   isoB, gPi, xt, FB3 and isoStep follow.  With the realiser free, weakening and
   substitution keep the family, the value and the realiser UNCHANGED and only
   rewrite the pinning equation, which no data depends on.  Equations do not
   propagate; casts do.

   THE LEVELS ARE THE SYNTAX'S.  Every former carries the level it lives at,
   its components live at any level BELOW it, and the level of a reading is the
   annotation -- `nat_ k` only ever reads at k, `pi (d + j) A B` only at d + j.
   The one exception is a proof term, whose level is that of its Prf type and
   so is not determined by the term at all; Interp/Fun.v's level functionality
   is therefore restricted to readings at a UNIVERSE family, which is all it
   was ever applied to, and the proof clause is refuted there by the shape
   mismatch of a universe code and a Prf code.

   Reconciling a former's level with its components' is what makes the universe
   lift's computation rules hold.  A Pi-code is built from component codes at
   its own level, so the value of `pi (d + j) A B`, whose components live at j,
   is the d-FOLD LIFT of the level-j Pi-family (Interp/LiftN.v).  Then

     up (d + j) (pi (d + j) A B)   and   pi (S d + j) A B

   have literally the same value: `famLiftK (famLiftN d X)` IS
   `famLiftN (S d) X`.  No isomorphism of two Pi-codes is ever needed -- that
   would ask for the naturality square of Codes/Iso.v's isoRefine -- and the
   eliminators pay for it with one `elUnliftN`, which is the equivalence's
   other half.  The component-free formers keep their canonical family at every
   level and their lift commutations are the three one-liners at the bottom of
   Interp/LiftN.v.

   Deliberate omissions, each for a reason recorded elsewhere:
   - `absurd`, because it needs NO clause: its case in the fundamental lemma
     is vacuous, the interpretation of Prf False having no elements.  A
     neutral type has an empty decoding, so there is nothing to say.
   - Eq, which is not in the theory (Layer1/BadTransp.v). *)

(* A type that is not headed by a former.  The clause ity_of, which reads any
   term of a universe as a family, is restricted to these: for a former-headed
   type the former's own clause applies, and excluding the overlap is what
   makes inversion at a type a single case. *)
Definition notFormer (A : tm) : Prop :=
  match A with
  | pi _ _ _ => False
  | nat_ _ => False
  | prop _ => False
  | univ _ _ => False
  | prf _ _ => False
  | up _ _ => False
  | sig_ _ _ _ => False
  | _ => True
  end.

(* The family of Prf p, read off the value of p: the truth value is the Prop
   the value of p carries, and the layer-1 side condition is its goodness.
   The Prf's own level k is unrelated to the level j at which the proposition
   was read -- a proposition is a proposition at every level, and only its
   truth value and its realiser enter here. *)
Definition prfF (k : nat) {j u} (x : kElAt (propFam j) u) : kUFam k (eprf u) :=
  prfFam k u (Rel_prop_elim eprop u u ev_prop (propGood x)) (propVal x).

(* The family of a Pi-type, and semantic application, with the erased
   codomain of the syntax plugged in: piFam and piApp with the substitution
   bookkeeping done once.  `d` is the gap between the components' level and the
   annotation; the family at the annotation's level is the d-fold lift. *)
Definition piF (rho : Env) (A B : tm) (d j : nat)
  (FA : kUFam j (ers rho A))
  (FB : forall u (x : kElAt FA u), kUFam j (ers (ext rho FA u x) B))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty j (ers rho (pi (d + j) A B)) (ers rho (pi (d + j) A B)))
  : kUFam (d + j) (ers rho (pi (d + j) A B)) :=
  famLiftN d
    (piFam j (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B))) FA
           (fun u x => ers (ext rho FA u x) B) FB
           (fun u x => reds_lam_app (er B) (rsub rho) u) isoB gPi).

Definition piAp (rho : Env) (A B : tm) (d j : nat)
  (FA : kUFam j (ers rho A))
  (FB : forall u (x : kElAt FA u), kUFam j (ers (ext rho FA u x) B))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty j (ers rho (pi (d + j) A B)) (ers rho (pi (d + j) A B)))
  u (x : kElAt (piF rho A B d j FA FB isoB gPi) u) u' (y : kElAt FA u')
  : kElAt (FB u' y) (eapp u u') :=
  piApp j (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B))) FA
        (fun u0 x0 => ers (ext rho FA u0 x0) B) FB
        (fun u0 x0 => reds_lam_app (er B) (rsub rho) u0) isoB gPi u
        (elUnliftN d _ u x) u' y.

(* The erased step of a natrec.  `er (natrec C z s n)` is
   `enatrec (er z) (elam (elam (er s))) (er n)`, and `elam (elam (er s))` is
   `er (lam _ _ _ (lam _ _ _ s))` for ANY annotations, since erasure drops
   them.  Writing the pin that way is what lets it travel under weakening and
   substitution with ers_upnr and ers_upn, with no new lemmas: the wrapper's
   renaming IS the wrapper of the renaming at depth +2. *)
Definition stepWrap (s : tm) : tm :=
  lam 0 (nat_ 0) (nat_ 0) (lam 0 (nat_ 0) (nat_ 0) s).

Lemma er_stepWrap s : er (stepWrap s) = elam (elam (er s)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The two judgements.                                                *)
(* ------------------------------------------------------------------ *)

Inductive ITy : forall (rho : Env) (A : tm) (k : nat) (w : etm), kUFam k w -> Type :=
(* The type formers, each at THE level its annotation gives it.  The levels
   used to be free here -- natFam k for every k -- and that slack made the
   interpretation of a type level-ambiguous, which is fatal for the fundamental
   lemma at a variable: ITm pins a variable's level to its environment entry's
   (i_var0 reads the entry's own family, and i_varS and i_conv preserve the
   level), so a statement quantifying over every level at which the type can be
   read is not provable there. *)
| ity_nat rho k w : w = ers rho (nat_ k) -> ITy rho (nat_ k) k enat (natFam k)
| ity_prop rho k w : w = ers rho (prop k) -> ITy rho (prop k) k eprop (propFam k)
(* A universe: `univ k j` is legal exactly when j < k, i.e. k = d + S j, and
   its value is the d-fold lift of the universe that level S j adds.  Written
   this way the lift computation `up (d + S j) (univ (d + S j) j)` == 
   `univ (S d + S j) j` is DEFINITIONAL, and at d = 0 the family is univFam j
   itself, which is the one the universe bridge of Interp/Univ.v speaks of. *)
| ity_univ rho d j w : w = ers rho (univ (d + S j) j) ->
    ITy rho (univ (d + S j) j) (d + S j) (euniv j) (famLiftN d (univFam j))
| ity_prf rho k j p wp (xp : kElAt (propFam j) wp) :
    ITm rho p j eprop (propFam j) wp xp ->
    ITy rho (prf k p) k (eprf wp) (prfF k xp)
| ity_pi rho A B d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty j (epi wA B0) (epi wA B0)) :
    epi wA B0 = ers rho (pi (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITy rho (pi (d + j) A B) (d + j) (epi wA B0)
        (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi))
(* Sigma: the same premises as Pi -- a Sigma-family is built from exactly the
   same data -- with esig for epi. *)
| ity_sig rho A B d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty j (esig wA B0) (esig wA B0)) :
    esig wA B0 = ers rho (sig_ (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITy rho (sig_ (d + j) A B) (d + j) (esig wA B0)
        (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig))
(* the universe lift.  The realiser is unchanged -- up erases to its subject
   -- so the only thing that moves is the level of the codes, by
   Interp/Lift.v.  It is a type FORMER as far as notFormer is concerned, so
   that inversion at a type stays single-case.  At a FORMER subject the lifted
   family is, up to ity_conv, the same former one level up: definitionally so
   at Pi, Sigma and univ, and by Interp/LiftN.v's three isomorphisms at nat,
   prop and prf. *)
| ity_up rho A k w (F : kUFam k w) :
    ITy rho A k w F ->
    ITy rho (up k A) (S k) w (famLiftK F)
(* and any other type: a term of a universe IS a family (Interp/Univ.v).
   This is what covers a type headed by an application, a recursor or a
   variable -- large elimination, in other words. *)
| ity_of rho A k w (v : kElAt (univFam k) w) :
    notFormer A ->
    ITm rho A (S k) (euniv k) (univFam k) w v ->
    ITy rho A k w (elFam v)
(* ---- conversion of a type's FAMILY.  ITy has to be closed under iso for the
     same reason ITm is (i_conv), and the semantic substitution lemma is what
     forces it: substituting a term for a variable puts the term's value at
     the family that value NAMES (`elFam v`), and that family is only
     isomorphic to the canonical one -- a reading of `nat_` at a universe may
     have travelled through i_conv.  Without this clause Interp/Subst.v's
     SubUniv is unprovable as soon as the substituted term is a type former,
     and the substitution lemma is unusable exactly where 9.2 needs it.
     Inversion stays single-case: every *Dec of Interp/Inv.v already concludes
     with an ISOMORPHISM to the canonical family, so this clause only composes
     one more.  It is also what lets `up k (nat_ k)` and `nat_ (S k)` have a
     common reading. ---- *)
| ity_conv rho A k w (F F' : kUFam k w) :
    iso (kAt F) (kAt F') ->
    ITy rho A k w F ->
    ITy rho A k w F'

with ITm : forall (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy) (w : etm),
    kElAt F w -> Type :=

(* ---- a type, as a term of the universe above it ---- *)
| i_ty rho A k w (F : kUFam k w) :
    ITy rho A k w F ->
    ITm rho A (S k) (euniv k) (univFam k) w (famEl F)

(* ---- variables ---- *)
| i_var0 rho k Sy (F : kUFam k Sy) w (x : kElAt F w) :
    ITm (ext rho F w x) (var_tm 0) k Sy F w x
| i_varS rho en i k Sy (F : kUFam k Sy) w (x : kElAt F w) :
    ITm rho (var_tm i) k Sy F w x ->
    ITm (en :: rho) (var_tm (S i)) k Sy F w x

(* ---- N ---- *)
| i_zero rho k :
    ITm rho (zero k) k enat (natFam k) ezero (natE 0 NatAt_zero)
| i_succ rho k n wn (x : kElAt (natFam k) wn) :
    ITm rho n k enat (natFam k) wn x ->
    ITm rho (succ n) k enat (natFam k) (esucc wn) (natSucc x)

(* ---- Pi.  The subject's value lives at the lifted family, and its
     behaviour is read off the level-j one, which is what elUnliftN brings it
     back to. ---- *)
| i_lam rho A B t d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty j (epi wA B0) (epi wA B0))
    w (x : kElAt (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi)) w)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y)) :
    w = ers rho (lam (d + j) A B t) ->
    epi wA B0 = ers rho (pi (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u y, ITy (ext rho FA u y) B j (wB u y) (FB u y)) ->
    (forall u y, ITm (ext rho FA u y) t j (wB u y) (FB u y) (wt u y) (xt u y)) ->
    (* the value is determined by its behaviour, up to the beta step that
       separates the two realisers *)
    (forall u y, kEqAt (FB u y) (eapp w u)
        (piApp j wA B0 FA wB FB redB isoB gPi w
           (elUnliftN d (piFam j wA B0 FA wB FB redB isoB gPi) w x) u y)
        (wt u y) (xt u y)) ->
    ITm rho (lam (d + j) A B t) (d + j) (epi wA B0)
        (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi)) w x

| i_app rho A B f a d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty j (epi wA B0) (epi wA B0))
    wf (xf : kElAt (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi)) wf)
    wa (xa : kElAt FA wa) :
    epi wA B0 = ers rho (pi (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITm rho f (d + j) (epi wA B0)
        (famLiftN d (piFam j wA B0 FA wB FB redB isoB gPi)) wf xf ->
    ITm rho a j wA FA wa xa ->
    ITm rho (app A B f a) j (wB wa xa) (FB wa xa) (eapp wf wa)
        (piApp j wA B0 FA wB FB redB isoB gPi wf
           (elUnliftN d (piFam j wA B0 FA wB FB redB isoB gPi) wf xf) wa xa)

(* ---- Sigma.  No pinning equation anywhere: the realiser of a pair is the
     pair of its components' realisers, and the realiser of a projection is
     the projection of its subject's, so all three are built from the
     subderivations'.  The layer-1 goodness of the pair is a premise, as it is
     for every introduction whose realiser is a value (Interp/Elem.v): it
     comes from Layer1/Elim.v's Rel_sig_intro. ---- *)
| i_pair rho A B t a d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty j (esig wA B0) (esig wA B0))
    wt (xt : kElAt FA wt) wa (xa : kElAt (FB wt xt) wa)
    (g : Good (esig wA B0) (epair wt wa)) :
    esig wA B0 = ers rho (sig_ (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITm rho t j wA FA wt xt ->
    ITm rho a j (wB wt xt) (FB wt xt) wa xa ->
    ITm rho (pair (d + j) A B t a) (d + j) (esig wA B0)
        (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig))
        (epair wt wa)
        (elLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig) (epair wt wa)
           (sigPair j wA B0 FA wB FB redB isoB gSig wt wa xt xa g))

| i_fst rho A B p d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty j (esig wA B0) (esig wA B0))
    wp (xp : kElAt (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig)) wp) :
    esig wA B0 = ers rho (sig_ (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITm rho p (d + j) (esig wA B0)
        (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig)) wp xp ->
    ITm rho (fst A B p) j wA FA (efst wp)
        (sigFst j wA B0 FA wB FB redB isoB gSig wp
           (elUnliftN d (sigFam j wA B0 FA wB FB redB isoB gSig) wp xp))

| i_snd rho A B p d j wA (FA : kUFam j wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty j (esig wA B0) (esig wA B0))
    wp (xp : kElAt (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig)) wp) :
    esig wA B0 = ers rho (sig_ (d + j) A B) ->
    ITy rho A j wA FA ->
    (forall u x, ITy (ext rho FA u x) B j (wB u x) (FB u x)) ->
    ITm rho p (d + j) (esig wA B0)
        (famLiftN d (sigFam j wA B0 FA wB FB redB isoB gSig)) wp xp ->
    ITm rho (snd A B p) j
        (wB (efst wp)
           (sigFst j wA B0 FA wB FB redB isoB gSig wp
              (elUnliftN d (sigFam j wA B0 FA wB FB redB isoB gSig) wp xp)))
        (FB (efst wp)
           (sigFst j wA B0 FA wB FB redB isoB gSig wp
              (elUnliftN d (sigFam j wA B0 FA wB FB redB isoB gSig) wp xp)))
        (esnd wp)
        (sigSnd j wA B0 FA wB FB redB isoB gSig wp
           (elUnliftN d (sigFam j wA B0 FA wB FB redB isoB gSig) wp xp))

(* ---- large elimination of N.  The step term carries its own two binders, so
     its semantic content is, for every scrutinee value and every value of the
     motive at it, a value of the motive at the successor: no Pi-type, no
     nrec_step, no double application, and no isoStep.  Its realiser is a free
     index tied to the erased step S0 by redS, exactly as ity_pi ties its
     codomain realisers to B0 -- the two beta-steps that the erased recursor's
     computation rule leaves behind are absorbed by expansion, which is what
     moveTo does.

     The scrutinee's family is natFam j, the annotation on its type, and the
     motive is read at its own level k in an environment extended by an entry
     at j. ---- *)
| i_natrec rho C z s n k j
    (SC : etm -> etm)
    (FC : forall m (x : kElAt (natFam j) m), kUFam k (SC m))
    (isoC : forall m x m' x', kEqAt (natFam j) m x m' x' ->
              iso (kAt (FC m x)) (kAt (FC m' x')))
    S0
    wz (xz : kElAt (FC ezero (natE 0 NatAt_zero)) wz)
    (ws : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w), etm)
    (xs : forall m x w y, kElAt (FC (esucc m) (natSucc x)) (ws m x w y))
    (redS : forall m x w y, reds (eapp (eapp S0 m) w) (ws m x w y))
    wn (xn : kElAt (natFam j) wn) :
    S0 = ers rho (stepWrap s) ->
    (forall m x, ITy (ext rho (natFam j) m x) C k (SC m) (FC m x)) ->
    ITm rho z k (SC ezero) (FC ezero (natE 0 NatAt_zero)) wz xz ->
    (forall m x w y,
       ITm (ext (ext rho (natFam j) m x) (FC m x) w y) s k
           (SC (esucc m)) (FC (esucc m) (natSucc x)) (ws m x w y) (xs m x w y)) ->
    ITm rho n j enat (natFam j) wn xn ->
    ITm rho (natrec C z s n) k (SC wn) (FC wn (natE (natIdx xn) (natSpec xn)))
        (enatrec wz S0 wn)
        (semrec k j SC FC isoC wz S0 xz
           (fun m x w y =>
              moveTo (FC (esucc m) (natSucc x)) (FC (esucc m) (natSucc x))
                (iso_self (FC (esucc m) (natSucc x)))
                (ws m x w y) (xs m x w y) (eapp (eapp S0 m) w) (redS m x w y))
           (natIdx xn) wn (natSpec xn))

(* ---- propositions ---- *)
| i_false rho k w (g : Good eprop efalse) :
    w = ers rho (false_ k) ->
    ITm rho (false_ k) k eprop (propFam k) efalse (propElem efalse False g)
(* The impredicative forall.  Its LEVEL is its own annotation, not something
     read off the premises: the premise about p is quantified over the domain's
     elements and says nothing when the domain is empty, so without the
     annotation a forall over an empty type would be interpretable at every
     level and no reading of a proposition would have a determined level.  The
     domain may live at ANY level k -- that is the impredicativity. *)
| i_all rho j A p k wA (FA : kUFam k wA)
    (wp : forall u, kElAt FA u -> etm)
    (xp : forall u (y : kElAt FA u), kElAt (propFam j) (wp u y))
    w (g : Good eprop w) :
    w = ers rho (all j A p) ->
    ITy rho A k wA FA ->
    (forall u y, ITm (ext rho FA u y) p j eprop (propFam j) (wp u y) (xp u y)) ->
    ITm rho (all j A p) j eprop (propFam j) w
        (propElem w (forall u (y : kElAt FA u), propVal (xp u y)) g)

(* ---- proof terms: ONE clause, because the decoding of Prf p relates all of
     its elements.  That is proof irrelevance, and it is why the clause says
     nothing about t beyond the truth of p and the layer-1 goodness of its
     erasure.  It subsumes forall-introduction, forall-elimination, and every
     proof variable or application.

     This is the one clause whose LEVEL is free: `prf k p` lives at every k
     above the proposition's own level, and the term does not record which.
     Nothing needs it to be pinned -- Interp/Fun.v's level functionality is
     about readings at a universe family, and a Prf family is not one. ---- *)
| i_proof rho t p k j wp (xp : kElAt (propFam j) wp)
    (h : propVal xp) w (g : Good (eprf wp) w) :
    w = ers rho t ->
    ITm rho p j eprop (propFam j) wp xp ->
    ITm rho t k (eprf wp) (prfF k xp) w (prfElem w h g)

(* ---- the universe lift on terms.  Same realiser, same value up to the
     lift of the decoding; no pinning equation is needed, because both the
     realiser and the family are inherited from the subderivation. ---- *)
| i_up_tm rho A t k Sy (F : kUFam k Sy) w (x : kElAt F w) :
    ITy rho A k Sy F ->
    ITm rho t k Sy F w x ->
    ITm rho (uptm A t) (S k) Sy (famLiftK F) w (elLift F w x)

(* ---- conversion of the TYPE.  The interpretation has to be closed under it:
     t_conv moves a term to a convertible type, and its value has to move with
     it, along the isomorphism of the two types' families.  This is the one
     clause that is not directed by the subject's syntax, and without it the
     fundamental lemma's conversion case is not provable at all -- the value
     produced by the induction hypothesis lives in the family of the OLD type
     and there is nothing else that relates the two.

     It costs nothing elsewhere.  Nothing inverts ITm (see the note on the two
     judgements above), so the extra clause is invisible to every consumer;
     and the two lemmas that traverse the relation -- weakening and
     substitution -- gain one line each, because a conversion touches neither
     the realiser nor the environment.  Note that ITy gets NO such clause:
     types are interpreted up to isomorphism already (Interp/Inv.v), and
     adding one there would put ity_of in the way of inversion at a former. *)
| i_conv rho t k Sy (F : kUFam k Sy) Sy' (F' : kUFam k Sy') w (x : kElAt F w)
    (P : iso (kAt F) (kAt F')) :
    ITm rho t k Sy F w x ->
    ITm rho t k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
