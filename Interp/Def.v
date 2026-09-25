From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift.
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
  | pi _ _ => False
  | nat_ => False
  | prop => False
  | univ _ => False
  | prf _ => False
  | up _ _ => False
  | sig_ _ _ => False
  | _ => True
  end.

(* The family of Prf p, read off the value of p: the truth value is the Prop
   the value of p carries, and the layer-1 side condition is its goodness. *)
Definition prfF (k : nat) {u} (x : kElAt (propFam 0) u) : kUFam k (eprf u) :=
  prfFam k u (Rel_prop_elim eprop u u ev_prop (propGood x)) (propVal x).

(* The family of a Pi-type, and semantic application, with the erased
   codomain of the syntax plugged in: piFam and piApp with the substitution
   bookkeeping done once. *)
Definition piF (rho : Env) (A B : tm) (k : nat)
  (FA : kUFam k (ers rho A))
  (FB : forall u (x : kElAt FA u), kUFam k (ers (ext rho FA u x) B))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (ers rho (pi A B)) (ers rho (pi A B)))
  : kUFam k (ers rho (pi A B)) :=
  piFam k (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B))) FA
        (fun u x => ers (ext rho FA u x) B) FB
        (fun u x => reds_lam_app (er B) (rsub rho) u) isoB gPi.

Definition piAp (rho : Env) (A B : tm) (k : nat)
  (FA : kUFam k (ers rho A))
  (FB : forall u (x : kElAt FA u), kUFam k (ers (ext rho FA u x) B))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (ers rho (pi A B)) (ers rho (pi A B)))
  u (x : kElAt (piF rho A B k FA FB isoB gPi) u) u' (y : kElAt FA u')
  : kElAt (FB u' y) (eapp u u') :=
  piApp k (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B))) FA
        (fun u0 x0 => ers (ext rho FA u0 x0) B) FB
        (fun u0 x0 => reds_lam_app (er B) (rsub rho) u0) isoB gPi u x u' y.

(* The erased step of a natrec.  `er (natrec C z s n)` is
   `enatrec (er z) (elam (elam (er s))) (er n)`, and `elam (elam (er s))` is
   `er (lam _ _ (lam _ _ s))` for ANY annotations, since erasure drops them.
   Writing the pin that way is what lets it travel under weakening and
   substitution with ers_upnr and ers_upn, with no new lemmas: the wrapper's
   renaming IS the wrapper of the renaming at depth +2. *)
Definition stepWrap (s : tm) : tm := lam nat_ nat_ (lam nat_ nat_ s).

Lemma er_stepWrap s : er (stepWrap s) = elam (elam (er s)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The two judgements.                                                *)
(* ------------------------------------------------------------------ *)

Inductive ITy : forall (rho : Env) (A : tm) (k : nat) (w : etm), kUFam k w -> Type :=
(* The type formers, each at THE level the syntax gives it: nat_, prop and
   prf p at 0, univ m and up (univ k) . one above their argument, Pi and Sigma
   at their components'.  The levels used to be free here -- natFam k for every
   k -- and that slack made the interpretation of a type level-ambiguous, which
   is fatal for the fundamental lemma at a variable: ITm pins a variable's
   level to its environment entry's (i_var0 reads the entry's own family, and
   i_varS and i_conv preserve the level), so a statement quantifying over every
   level at which the type can be read is not provable there.  Nothing wanted
   the slack except the old i_natrec, whose step term's Pi-type forced N at the
   motive's level; with the step carrying its own binders that is gone. *)
| ity_nat rho w : w = ers rho nat_ -> ITy rho nat_ 0 enat (natFam 0)
| ity_prop rho w : w = ers rho prop -> ITy rho prop 0 eprop (propFam 0)
| ity_univ rho m w : w = ers rho (univ m) -> ITy rho (univ m) (S m) (euniv m) (univFam m)
| ity_prf rho p wp (xp : kElAt (propFam 0) wp) :
    ITm rho p 0 eprop (propFam 0) wp xp ->
    ITy rho (prf p) 0 (eprf wp) (prfF 0 xp)
| ity_pi rho A B k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty k (epi wA B0) (epi wA B0)) :
    epi wA B0 = ers rho (pi A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITy rho (pi A B) k (epi wA B0) (piFam k wA B0 FA wB FB redB isoB gPi)
(* Sigma: the same premises as Pi -- a Sigma-family is built from exactly the
   same data -- with esig for epi. *)
| ity_sig rho A B k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty k (esig wA B0) (esig wA B0)) :
    esig wA B0 = ers rho (sig_ A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITy rho (sig_ A B) k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig)
(* the universe lift.  The realiser is unchanged -- up erases to its subject
   -- so the only thing that moves is the level of the codes, by
   Interp/Lift.v.  It is a type FORMER as far as notFormer is concerned, so
   that inversion at a type stays single-case. *)
| ity_up rho A k w (F : kUFam k w) :
    ITy rho A k w F ->
    ITy rho (up (univ (S k)) A) (S k) w (famLiftK F)
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
     one more. ---- *)
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
| i_zero rho :
    ITm rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
| i_succ rho n wn (x : kElAt (natFam 0) wn) :
    ITm rho n 0 enat (natFam 0) wn x ->
    ITm rho (succ n) 0 enat (natFam 0) (esucc wn) (natSucc x)

(* ---- Pi ---- *)
| i_lam rho A B t k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty k (epi wA B0) (epi wA B0))
    w (x : kElAt (piFam k wA B0 FA wB FB redB isoB gPi) w)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y)) :
    w = ers rho (lam A B t) ->
    epi wA B0 = ers rho (pi A B) ->
    ITy rho A k wA FA ->
    (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) ->
    (forall u y, ITm (ext rho FA u y) t k (wB u y) (FB u y) (wt u y) (xt u y)) ->
    (* the value is determined by its behaviour, up to the beta step that
       separates the two realisers *)
    (forall u y, kEqAt (FB u y) (eapp w u)
        (piApp k wA B0 FA wB FB redB isoB gPi w x u y) (wt u y) (xt u y)) ->
    ITm rho (lam A B t) k (epi wA B0) (piFam k wA B0 FA wB FB redB isoB gPi) w x

| i_app rho A B f a k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gPi : eqty k (epi wA B0) (epi wA B0))
    wf (xf : kElAt (piFam k wA B0 FA wB FB redB isoB gPi) wf)
    wa (xa : kElAt FA wa) :
    epi wA B0 = ers rho (pi A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITm rho f k (epi wA B0) (piFam k wA B0 FA wB FB redB isoB gPi) wf xf ->
    ITm rho a k wA FA wa xa ->
    ITm rho (app A B f a) k (wB wa xa) (FB wa xa) (eapp wf wa)
        (piApp k wA B0 FA wB FB redB isoB gPi wf xf wa xa)

(* ---- Sigma.  No pinning equation anywhere: the realiser of a pair is the
     pair of its components' realisers, and the realiser of a projection is
     the projection of its subject's, so all three are built from the
     subderivations'.  The layer-1 goodness of the pair is a premise, as it is
     for every introduction whose realiser is a value (Interp/Elem.v): it
     comes from Layer1/Elim.v's Rel_sig_intro. ---- *)
| i_pair rho A B t a k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wt (xt : kElAt FA wt) wa (xa : kElAt (FB wt xt) wa)
    (g : Good (esig wA B0) (epair wt wa)) :
    esig wA B0 = ers rho (sig_ A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITm rho t k wA FA wt xt ->
    ITm rho a k (wB wt xt) (FB wt xt) wa xa ->
    ITm rho (pair A B t a) k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig)
        (epair wt wa) (sigPair k wA B0 FA wB FB redB isoB gSig wt wa xt xa g)

| i_fst rho A B p k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wp (xp : kElAt (sigFam k wA B0 FA wB FB redB isoB gSig) wp) :
    esig wA B0 = ers rho (sig_ A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITm rho p k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig) wp xp ->
    ITm rho (fst A B p) k wA FA (efst wp)
        (sigFst k wA B0 FA wB FB redB isoB gSig wp xp)

| i_snd rho A B p k wA (FA : kUFam k wA) B0
    (wB : forall u, kElAt FA u -> etm)
    (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wp (xp : kElAt (sigFam k wA B0 FA wB FB redB isoB gSig) wp) :
    esig wA B0 = ers rho (sig_ A B) ->
    ITy rho A k wA FA ->
    (forall u x, ITy (ext rho FA u x) B k (wB u x) (FB u x)) ->
    ITm rho p k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig) wp xp ->
    ITm rho (snd A B p) k
        (wB (efst wp) (sigFst k wA B0 FA wB FB redB isoB gSig wp xp))
        (FB (efst wp) (sigFst k wA B0 FA wB FB redB isoB gSig wp xp))
        (esnd wp) (sigSnd k wA B0 FA wB FB redB isoB gSig wp xp)

(* ---- large elimination of N.  The step term carries its own two binders, so
     its semantic content is, for every scrutinee value and every value of the
     motive at it, a value of the motive at the successor: no Pi-type, no
     nrec_step, no double application, and no isoStep.  Its realiser is a free
     index tied to the erased step S0 by redS, exactly as ity_pi ties its
     codomain realisers to B0 -- the two beta-steps that the erased recursor's
     computation rule leaves behind are absorbed by expansion, which is what
     moveTo does.

     The scrutinee's family is natFam 0, the syntactic level of nat_, and the
     motive is read in an environment extended by an entry at that level. ---- *)
| i_natrec rho C z s n k
    (SC : etm -> etm)
    (FC : forall m (x : kElAt (natFam 0) m), kUFam k (SC m))
    (isoC : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
              iso (kAt (FC m x)) (kAt (FC m' x')))
    S0
    wz (xz : kElAt (FC ezero (natE 0 NatAt_zero)) wz)
    (ws : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w), etm)
    (xs : forall m x w y, kElAt (FC (esucc m) (natSucc x)) (ws m x w y))
    (redS : forall m x w y, reds (eapp (eapp S0 m) w) (ws m x w y))
    wn (xn : kElAt (natFam 0) wn) :
    S0 = ers rho (stepWrap s) ->
    (forall m x, ITy (ext rho (natFam 0) m x) C k (SC m) (FC m x)) ->
    ITm rho z k (SC ezero) (FC ezero (natE 0 NatAt_zero)) wz xz ->
    (forall m x w y,
       ITm (ext (ext rho (natFam 0) m x) (FC m x) w y) s k
           (SC (esucc m)) (FC (esucc m) (natSucc x)) (ws m x w y) (xs m x w y)) ->
    ITm rho n 0 enat (natFam 0) wn xn ->
    ITm rho (natrec C z s n) k (SC wn) (FC wn (natE (natIdx xn) (natSpec xn)))
        (enatrec wz S0 wn)
        (semrec k 0 SC FC isoC wz S0 xz
           (fun m x w y =>
              moveTo (FC (esucc m) (natSucc x)) (FC (esucc m) (natSucc x))
                (iso_self (FC (esucc m) (natSucc x)))
                (ws m x w y) (xs m x w y) (eapp (eapp S0 m) w) (redS m x w y))
           (natIdx xn) wn (natSpec xn))

(* ---- propositions ---- *)
| i_false rho w (g : Good eprop efalse) :
    w = ers rho false_ ->
    ITm rho false_ 0 eprop (propFam 0) efalse (propElem efalse False g)
| i_all rho A p k wA (FA : kUFam k wA)
    (wp : forall u, kElAt FA u -> etm)
    (xp : forall u (y : kElAt FA u), kElAt (propFam 0) (wp u y))
    w (g : Good eprop w) :
    w = ers rho (all A p) ->
    ITy rho A k wA FA ->
    (forall u y, ITm (ext rho FA u y) p 0 eprop (propFam 0) (wp u y) (xp u y)) ->
    ITm rho (all A p) 0 eprop (propFam 0) w
        (propElem w (forall u (y : kElAt FA u), propVal (xp u y)) g)

(* ---- proof terms: ONE clause, because the decoding of Prf p relates all of
     its elements.  That is proof irrelevance, and it is why the clause says
     nothing about t beyond the truth of p and the layer-1 goodness of its
     erasure.  It subsumes forall-introduction, forall-elimination, and every
     proof variable or application. ---- *)
| i_proof rho t p wp (xp : kElAt (propFam 0) wp)
    (h : propVal xp) w (g : Good (eprf wp) w) :
    w = ers rho t ->
    ITm rho p 0 eprop (propFam 0) wp xp ->
    ITm rho t 0 (eprf wp) (prfF 0 xp) w (prfElem w h g)

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
