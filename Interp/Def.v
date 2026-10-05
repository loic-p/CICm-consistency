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
  Interp.PiEl Interp.SigEl Interp.WEl Interp.Rec Interp.Lift Interp.LiftN.
From Stdlib Require Import Arith Lia.

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
   rho, A and k, so inversion delivers `F = piFam ...` outright.  Every
   inversion the fundamental lemma needs is at a TYPE -- the typing rules
   expose the type's former whenever they eliminate it -- so the split is
   exactly enough.

   THE REALISERS ARE FREE INDICES, pinned by one equation premise per clause
   (`Ew : w = ers rho t`), rather than computed as `ers rho t`.  This is not a
   matter of taste.  With the realiser computed, weakening and substitution
   have to transport the family along an equality of realisers -- and a cast in
   a family's TYPE propagates into every component indexed by that family.
   With the realiser free, weakening and substitution keep the family, the
   value and the realiser UNCHANGED and only rewrite the pinning equation,
   which no data depends on.  Equations do not propagate; casts do.

   THE LEVELS ARE THE SYNTAX'S, AND THE COMPONENTS' ARE INDEPENDENT.  Every
   former carries the level it lives at, and in v2 its components live at any
   levels BELOW it, separately: `pi k A B` with A : U_i, B : U_j and only
   i <= k, j <= k.  A Pi-code is built from component codes at ITS OWN level,
   so each component is read at its own level and then lifted the remaining
   way: the gap is a `d` with `d + i = k`, carried as an equation premise and
   consumed by `upF` (Interp/LiftN.v).  The eliminators pay for it with one
   `dnEl` on the RESULT -- an application of `f : pi k A B` is read at B's own
   level j, which is where the typing rule puts it.

   v1 had a single component level j <= k and could lift the whole former's
   family d times; that is not available here, and heterogeneity is not
   optional: the W of Aczel sets (Tests/Aczel.v) has its label type one level
   above its branching type.

   Deliberate omissions, each for a reason recorded elsewhere:
   - `absurd`, because it needs NO clause: its case in the fundamental lemma
     is vacuous, the interpretation of Prf False having no elements.
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
  | wt _ _ _ => False
  | _ => True
  end.

(* The family of Prf p, read off the value of p: the truth value is the Prop
   the value of p carries, and the layer-1 side condition is its goodness.
   The Prf's own level k is unrelated to the level j at which the proposition
   was read -- a proposition is a proposition at every level, and only its
   truth value and its realiser enter here. *)
Definition prfF (k : nat) {j u} (x : kElAt (propFam j) u) : kUFam k (eprf u) :=
  prfFam k u (Rel_prop_elim eprop u u ev_prop (propGood x)) (propVal x).

(* The erased step of a natrec.  `er (natrec C z s n)` is
   `enatrec (er z) (elam (elam (er s))) (er n)`, and `elam (elam (er s))` is
   `er (lam _ _ _ (lam _ _ _ s))` for ANY annotations, since erasure drops
   them.  Writing the pin that way is what lets it travel under weakening and
   substitution with no new lemmas: the wrapper's renaming IS the wrapper of
   the renaming at depth +2.  `wrec`'s step has three binders, hence the
   second wrapper. *)
Definition stepWrap (s : tm) : tm :=
  lam 0 (nat_ 0) (nat_ 0) (lam 0 (nat_ 0) (nat_ 0) s).

Definition stepWrap3 (s : tm) : tm :=
  lam 0 (nat_ 0) (nat_ 0) (lam 0 (nat_ 0) (nat_ 0) (lam 0 (nat_ 0) (nat_ 0) s)).

Lemma er_stepWrap s : er (stepWrap s) = elam (elam (er s)).
Proof. reflexivity. Qed.

Lemma er_stepWrap3 s : er (stepWrap3 s) = elam (elam (elam (er s))).
Proof. reflexivity. Qed.

(* The erased realiser of the induction hypothesis a W-recursion's step is
   handed: the function sending a branch to the recursion on the subtree
   there.  It is the same term WEl.v's RecS section abbreviates. *)
Definition ihR (Sr f : etm) : etm :=
  elam (ewrec (ren_etm rshift Sr) (eapp (ren_etm rshift f) (var_etm 0))).

(* ------------------------------------------------------------------ *)
(* THE STEP OF A W-RECURSION.                                          *)
(*                                                                    *)
(* `wrec`'s step is typed in a three-entry context -- the label, the     *)
(* branching function, the induction hypothesis -- and the last two are  *)
(* Pi-typed, so the interpretation has to turn the semantic branching    *)
(* function and the semantic induction hypothesis into ELEMENTS of Pi    *)
(* families.  That is what PiEl.v's introduction `piLam` is for; this    *)
(* section is the bookkeeping around it.  `natrec` needs none of it: its *)
(* step's two binders range over a natural and a value of the motive.    *)
(* ------------------------------------------------------------------ *)

Section WStep.
  (* the W type, exactly as the W clause reads it *)
  Context (k i j dA dB : nat) (EA : dA + i = k) (EB : dB + j = k).
  Context (wA : etm) (FA : kUFam i wA) (B0 : etm).
  Context (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
          (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
          (redB : forall u x, reds (eapp B0 u) (wB u x))
          (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
             kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
          (gW : eqty k (ew wA B0) (ew wA B0)).

  Local Notation WF :=
    (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x)) redB cohB gW).

  (* the motive *)
  (* The motive's REALISER does not depend on the element: it is the erasure
     of C under the entry, and an erasure sees only realisers.  natrec's
     clause has had `etm -> etm` from the start; W's used to carry the
     element, and that made the induction hypothesis's codomain reduction
     (`Bih_red`) quantify over an element of the branching family -- which
     the recognition of `wih`'s erasure cannot supply, since it has only
     layer-1 related realisers to hand. *)
  Context (m : nat) (SC : etm -> etm)
          (FC : forall w (x : kElAt WF w), kUFam m (SC w))
          (cohC : forall w x w' x', kEqAt WF w x WF w' x' ->
             kceq (kAt (FC w x)) (kAt (FC w' x'))).

  (* ---- the branching function's type ----

     A Pi at the W's own level, whose domain is the branching type at the
     label and whose codomain is constantly the tree type.  Its erased
     codomain is a free index pinned only by the beta step: nothing here needs
     to know its shape. *)
  Context (Bbr : etm) (redBbr : forall v, reds (eapp Bbr v) (ew wA B0))
          (gBr : forall u0 (z : kElAt (upF dA k EA FA) u0),
             eqty k (epi (wB u0 z) Bbr) (epi (wB u0 z) Bbr)).

  Definition brFam u0 (z : kElAt (upF dA k EA FA) u0)
    : kUFam k (epi (wB u0 z) Bbr) :=
    piFam k (wB u0 z) Bbr (upF dB k EB (FB u0 z))
      (fun v _ => ew wA B0) (fun v _ => WF) (fun v _ => redBbr v)
      (fun v y v' y' _ => famAtSelf WF) (gBr u0 z).

  Definition brEl u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
    (sub : forall v (y : kElAt (upF dB k EB (FB u0 z)) v), kElAt WF (eapp f v))
    (subext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                  (upF dB k EB (FB u0 z)) v' y' ->
       kEqAt WF (eapp f v) (sub v y) WF (eapp f v') (sub v' y'))
    (gf : Good (epi (wB u0 z) Bbr) f) : kElAt (brFam u0 z) f :=
    piLam k (wB u0 z) Bbr (upF dB k EB (FB u0 z)) (fun v _ => ew wA B0)
      (fun v _ => WF) (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
      (gBr u0 z) f (fun v _ => eapp f v) sub (fun v y => reds_refl (eapp f v))
      subext gf.


  (* and what such an element does: this is the branching function of a sup,
     and the data `wSup` asks for *)
  Definition brApp u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
    (xf : kElAt (brFam u0 z) f) v (y : kElAt (upF dB k EB (FB u0 z)) v)
    : kElAt WF (eapp f v) :=
    piApp k (wB u0 z) Bbr (upF dB k EB (FB u0 z)) (fun v0 _ => ew wA B0)
      (fun v0 _ => WF) (fun v0 _ => redBbr v0)
      (fun v0 y0 v0' y0' _ => famAtSelf WF) (gBr u0 z) f xf v y.

  Lemma brApp_eq u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
    (xf : kElAt (brFam u0 z) f) v y v' y' :
    kEqAt (upF dB k EB (FB u0 z)) v y (upF dB k EB (FB u0 z)) v' y' ->
    kEqAt WF (eapp f v) (brApp u0 z f xf v y)
          WF (eapp f v') (brApp u0 z f xf v' y').
  Proof.
    intros H.
    exact (kRel_at
             (piApp_eq k (wB u0 z) Bbr (upF dB k EB (FB u0 z)) (fun v0 _ => ew wA B0)
                (fun v0 _ => WF) (fun v0 _ => redBbr v0)
                (fun v0 y0 v0' y0' _ => famAtSelf WF) (gBr u0 z)
                f xf f xf v y v' y' (kEqAt_refl (brFam u0 z) f xf) H)).
  Qed.

  (* ---- the induction hypothesis's type ----

     A Pi at ITS own level n, whose domain is the branching type (level j,
     lifted to n) and whose codomain is the motive at the subtree (level m,
     lifted to n).  Both gaps are independent of the W's own, which is what
     `t_wrec`'s j <= n and m <= n say, and an index therefore travels between
     the two levels at which the branching type is presented (`ihIdx`). *)
  Context (n dBn dC : nat) (EBn : dBn + j = n) (EC : dC + m = n).
  Context (Bih : forall u0 (z : kElAt (upF dA k EA FA) u0) (f : etm), etm)
          (* guarded by the node's goodness, as gf and gih below are and for
             the same reason: at a junk branching function the induction
             hypothesis's type is junk and need not be a type at all *)
          (gIh : forall u0 (z : kElAt (upF dA k EA FA) u0) (f : etm),
             Good (ew wA B0) (esup u0 f) ->
             eqty n (epi (wB u0 z) (Bih u0 z f)) (epi (wB u0 z) (Bih u0 z f))).

  Definition ihIdx u0 (z : kElAt (upF dA k EA FA) u0) v
    (y : kElAt (upF dBn n EBn (FB u0 z)) v) : kElAt (upF dB k EB (FB u0 z)) v :=
    reLvl (FB u0 z) dB k EB dBn n EBn v y.

  Lemma ihIdx_eq u0 (z : kElAt (upF dA k EA FA) u0) v y v' y' :
    kEqAt (upF dBn n EBn (FB u0 z)) v y (upF dBn n EBn (FB u0 z)) v' y' ->
    kEqAt (upF dB k EB (FB u0 z)) v (ihIdx u0 z v y)
          (upF dB k EB (FB u0 z)) v' (ihIdx u0 z v' y').
  Proof.
    intros H; exact (reLvl_eq (FB u0 z) (FB u0 z) dB k EB dBn n EBn v y v' y'
                       (famAtSelf (FB u0 z)) H).
  Qed.

  Context (Bih_red : forall u0 (z : kElAt (upF dA k EA FA) u0) f v,
             reds (eapp (Bih u0 z f) v) (SC (eapp f v))).

  Definition ihFam u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
    (gd : Good (ew wA B0) (esup u0 f))
    (sub : forall v (y : kElAt (upF dB k EB (FB u0 z)) v), kElAt WF (eapp f v))
    (subext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                  (upF dB k EB (FB u0 z)) v' y' ->
       kEqAt WF (eapp f v) (sub v y) WF (eapp f v') (sub v' y'))
    : kUFam n (epi (wB u0 z) (Bih u0 z f)) :=
    piFam n (wB u0 z) (Bih u0 z f) (upF dBn n EBn (FB u0 z))
      (fun v _ => SC (eapp f v))
      (fun v y => upF dC n EC (FC (eapp f v) (sub v (ihIdx u0 z v y))))
      (fun v _ => Bih_red u0 z f v)
      (fun v y v' y' H => upF_ceq dC n EC
         (FC (eapp f v) (sub v (ihIdx u0 z v y)))
         (FC (eapp f v') (sub v' (ihIdx u0 z v' y')))
         (cohC (eapp f v) (sub v (ihIdx u0 z v y))
               (eapp f v') (sub v' (ihIdx u0 z v' y'))
               (subext v (ihIdx u0 z v y) v' (ihIdx u0 z v' y')
                  (ihIdx_eq u0 z v y v' y' H))))
      (gIh u0 z f gd).

  Context (Sr : etm).

  Definition ihEl u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
    (gd : Good (ew wA B0) (esup u0 f))
    (sub : forall v (y : kElAt (upF dB k EB (FB u0 z)) v), kElAt WF (eapp f v))
    (subext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                  (upF dB k EB (FB u0 z)) v' y' ->
       kEqAt WF (eapp f v) (sub v y) WF (eapp f v') (sub v' y'))
    (ih : forall v y, kElAt (FC (eapp f v) (sub v y)) (eapp (ihR Sr f) v))
    (ihext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                 (upF dB k EB (FB u0 z)) v' y' ->
       kRel (FC (eapp f v) (sub v y)) (eapp (ihR Sr f) v) (ih v y)
            (FC (eapp f v') (sub v' y')) (eapp (ihR Sr f) v') (ih v' y'))
    (gih : Good (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f))
    : kElAt (ihFam u0 z f gd sub subext) (ihR Sr f) :=
    piLam n (wB u0 z) (Bih u0 z f) (upF dBn n EBn (FB u0 z))
      (fun v _ => SC (eapp f v))
      (fun v y => upF dC n EC (FC (eapp f v) (sub v (ihIdx u0 z v y))))
      (fun v _ => Bih_red u0 z f v)
      (fun v y v' y' H => upF_ceq dC n EC _ _
         (cohC _ _ _ _ (subext v (ihIdx u0 z v y) v' (ihIdx u0 z v' y')
                          (ihIdx_eq u0 z v y v' y' H))))
      (gIh u0 z f gd) (ihR Sr f) (fun v _ => eapp (ihR Sr f) v)
      (fun v y => upEl dC n EC (FC (eapp f v) (sub v (ihIdx u0 z v y)))
                    (eapp (ihR Sr f) v) (ih v (ihIdx u0 z v y)))
      (fun v y => reds_refl (eapp (ihR Sr f) v))
      (fun v y v' y' H =>
         upEl_eq dC n EC (FC (eapp f v) (sub v (ihIdx u0 z v y)))
           (eapp (ihR Sr f) v) (ih v (ihIdx u0 z v y))
           (FC (eapp f v') (sub v' (ihIdx u0 z v' y')))
           (eapp (ihR Sr f) v') (ih v' (ihIdx u0 z v' y'))
           (kRel_ceq (ihext v (ihIdx u0 z v y) v' (ihIdx u0 z v' y')
                        (ihIdx_eq u0 z v y v' y' H)))
           (kRel_at (ihext v (ihIdx u0 z v y) v' (ihIdx u0 z v' y')
                       (ihIdx_eq u0 z v y v' y' H))))
      gih.

  (* the layer-1 goodness of the two Pi-typed entries' realisers: as for every
     introduction whose realiser is a value, it is given, and the fundamental
     lemma supplies it from layer 1.

     GUARDED BY THE NODE'S OWN GOODNESS.  Unguarded these would be false: `f`
     ranges over all realisers here, and only the branching function of an
     actual tree is a good element of the branching Pi -- so an unguarded
     premise would make the clause unsatisfiable, and the interpretation of
     `wrec` vacuous.  Everywhere the interpretation needs them the node's
     `gd` is to hand, and the two halves of the fundamental lemma supply
     them from it: `Rel_w_br2` + `Rel_pi_intro` for the branching function,
     and layer 1's own recursor lemma `sem_wrec` for the induction
     hypothesis. *)
  Context (gf : forall u0 (z : kElAt (upF dA k EA FA) u0) f,
             Good (ew wA B0) (esup u0 f) -> Good (epi (wB u0 z) Bbr) f)
          (gih : forall u0 (z : kElAt (upF dA k EA FA) u0) f,
             Good (ew wA B0) (esup u0 f) ->
             Good (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f)).

  (* ---- and the step itself, in the shape `wRecS` consumes: the reading of
     the step term, expanded along the three beta steps the erased recursor's
     computation rule leaves behind.  This is `i_natrec`'s `ws`/`xs`/`redS`,
     with three binders instead of two.

     The five types are NAMED, because the W-recursion clause of the
     interpretation and its canonical-form decoder (Interp/Fun.v) both carry
     them and neither is readable with them written out. ---- *)

  Definition WsTy : Type :=
    forall u0 (z : kElAt (upF dA k EA FA) u0) (f : etm)
      (sub : forall v (y : kElAt (upF dB k EB (FB u0 z)) v), kElAt WF (eapp f v))
      (subext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                    (upF dB k EB (FB u0 z)) v' y' ->
         kEqAt WF (eapp f v) (sub v y) WF (eapp f v') (sub v' y'))
      (gd : Good (ew wA B0) (esup u0 f))
      (ih : forall v y, kElAt (FC (eapp f v) (sub v y)) (eapp (ihR Sr f) v))
      (ihext : forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                                   (upF dB k EB (FB u0 z)) v' y' ->
         kRel (FC (eapp f v) (sub v y)) (eapp (ihR Sr f) v) (ih v y)
              (FC (eapp f v') (sub v' y')) (eapp (ihR Sr f) v') (ih v' y')),
      etm.

  Definition XsTy (ws : WsTy) : Type :=
    forall u0 z f sub subext gd ih ihext,
      kElAt (FC (esup u0 f)
               (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                  redB cohB gW u0 f z sub subext gd))
            (ws u0 z f sub subext gd ih ihext).

  Definition RedSTy (ws : WsTy) : Type :=
    forall u0 z f sub subext gd ih ihext,
      reds (eapp (eapp (eapp Sr u0) f) (ihR Sr f))
           (ws u0 z f sub subext gd ih ihext).

  Context (ws : WsTy) (xs : XsTy ws) (redS : RedSTy ws).

  Definition stepOf u0 z f sub subext gd ih ihext
    : kElAt (FC (esup u0 f)
               (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                  redB cohB gW u0 f z sub subext gd))
            (eapp (eapp (eapp Sr u0) f) (ihR Sr f)) :=
    famExp (FC (esup u0 f)
              (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                 redB cohB gW u0 f z sub subext gd))
      (eapp (eapp (eapp Sr u0) f) (ihR Sr f)) (ws u0 z f sub subext gd ih ihext)
      (redS u0 z f sub subext gd ih ihext) (xs u0 z f sub subext gd ih ihext).

  (* the congruence of that step, which `wRecS` needs for its definition *)
  Definition StepRelTy : Type :=
    forall u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext',
      kEqAt (upF dA k EA FA) u0 z (upF dA k EA FA) u0' z' ->
      (forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                           (upF dB k EB (FB u0' z')) v' y' ->
         kEqAt WF (eapp f v) (sub v y) WF (eapp f' v') (sub' v' y')) ->
      Rel (ew wA B0) (esup u0 f) (esup u0' f') ->
      (forall v y v' y', kEqAt (upF dB k EB (FB u0 z)) v y
                           (upF dB k EB (FB u0' z')) v' y' ->
         kRel (FC (eapp f v) (sub v y)) (eapp (ihR Sr f) v) (ih v y)
              (FC (eapp f' v') (sub' v' y')) (eapp (ihR Sr f') v') (ih' v' y')) ->
      kRel (FC (esup u0 f)
              (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                 redB cohB gW u0 f z sub subext gd))
           (eapp (eapp (eapp Sr u0) f) (ihR Sr f))
           (stepOf u0 z f sub subext gd ih ihext)
           (FC (esup u0' f')
              (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                 redB cohB gW u0' f' z' sub' subext' gd'))
           (eapp (eapp (eapp Sr u0') f') (ihR Sr f'))
           (stepOf u0' z' f' sub' subext' gd' ih' ihext').

End WStep.

(* ------------------------------------------------------------------ *)
(* The two judgements.                                                *)
(* ------------------------------------------------------------------ *)

Inductive ITy : forall (rho : Env) (A : tm) (k : nat) (w : etm), kUFam k w -> Type :=
(* The type formers, each at THE level its annotation gives it.  The levels
   used to be free here -- natFam k for every k -- and that slack made the
   interpretation of a type level-ambiguous, which is fatal for the fundamental
   lemma at a variable: ITm pins a variable's level to its environment entry's,
   so a statement quantifying over every level at which the type can be read is
   not provable there. *)
| ity_nat rho k w : w = ers rho (nat_ k) -> ITy rho (nat_ k) k enat (natFam k)
| ity_prop rho k w : w = ers rho (prop k) -> ITy rho (prop k) k eprop (propFam k)
(* A universe: `univ k j` is legal exactly when j < k, i.e. k = d + S j, and
   its value is the d-fold lift of the universe that level S j adds.  At
   d = 0 the family is univFam j itself -- the one the universe bridge of
   Interp/Univ.v speaks of -- and the cast is the identity. *)
| ity_univ rho k d j (E : d + S j = k) w : w = ers rho (univ k j) ->
    ITy rho (univ k j) k (euniv j) (upF d k E (univFam j))
| ity_prf rho k j p wp (xp : kElAt (propFam j) wp) :
    ITm rho p j eprop (propFam j) wp xp ->
    ITy rho (prf k p) k (eprf wp) (prfF k xp)
(* Pi, Sigma and W: the same premises -- the three codes are built from
   exactly the same data -- with epi, esig and ew for each other.  The two
   components are read at their own levels i and j and lifted to the
   annotation k; the codomain family is indexed by elements of the LIFTED
   domain, and the environment the codomain is read in carries the unlifted
   one, which is where the typing rule puts the variable. *)
| ity_pi rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gPi : eqty k (epi wA B0) (epi wA B0)) :
    epi wA B0 = ers rho (pi k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITy rho (pi k A B) k (epi wA B0)
        (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gPi)
| ity_sig rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gSig : eqty k (esig wA B0) (esig wA B0)) :
    esig wA B0 = ers rho (sig_ k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITy rho (sig_ k A B) k (esig wA B0)
        (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig)
| ity_w rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gW : eqty k (ew wA B0) (ew wA B0)) :
    ew wA B0 = ers rho (wt k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITy rho (wt k A B) k (ew wA B0)
        (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW)
(* the universe lift.  The realiser is unchanged -- up erases to its subject
   -- so the only thing that moves is the level of the codes, by
   Interp/Lift.v.  It is a type FORMER as far as notFormer is concerned, so
   that inversion at a type stays single-case. *)
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
(* ---- conversion of a type's FAMILY.  ITy has to be closed under the
     equality for the same reason ITm is (i_conv), and the semantic
     substitution lemma is what forces it: substituting a term for a variable
     puts the term's value at the family that value NAMES (`elFam v`), and
     that family is only EQUAL to the canonical one.  It is also what lets
     `up k (nat_ k)` and `nat_ (S k)` have a common reading. ---- *)
| ity_conv rho A k w (F F' : kUFam k w) :
    kceq (kAt F) (kAt F') ->
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

(* ---- Pi.  The value of a lambda is BUILT from its behaviour, by PiEl.v's
     introduction `piLam`: v1 carried the element as an index together with an
     equation saying what it did, because it had no introduction. ---- *)
| i_lam rho A B t k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gPi : eqty k (epi wA B0) (epi wA B0))
    w (wt : forall u, kElAt (upF dA k EA FA) u -> etm)
    (xt : forall u x, kElAt (FB u x) (wt u x))
    (redt : forall u x, reds (eapp w u) (wt u x))
    (xtext : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kEqAt (upF dB k EB (FB u x)) (wt u x)
               (upEl dB k EB (FB u x) (wt u x) (xt u x))
             (upF dB k EB (FB u' x')) (wt u' x')
               (upEl dB k EB (FB u' x') (wt u' x') (xt u' x')))
    (gd : Good (epi wA B0) w) :
    w = ers rho (lam k A B t) ->
    epi wA B0 = ers rho (pi k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    (forall u x, ITm (ext rho FA u (dnEl dA k EA FA u x)) t j (wB u x) (FB u x)
                   (wt u x) (xt u x)) ->
    ITm rho (lam k A B t) k (epi wA B0)
        (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gPi) w
        (piLam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gPi w wt
           (fun u x => upEl dB k EB (FB u x) (wt u x) (xt u x)) redt xtext gd)

(* ---- and an application is read at the CODOMAIN's own level, which is
     where t_app puts it: one `dnEl` on the result. ---- *)
| i_app rho A B f a k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gPi : eqty k (epi wA B0) (epi wA B0))
    wf (xf : kElAt (piFam k wA B0 (upF dA k EA FA) wB
                      (fun u x => upF dB k EB (FB u x)) redB cohB gPi) wf)
    wa (xa : kElAt FA wa) :
    epi wA B0 = ers rho (pi k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITm rho f k (epi wA B0)
        (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gPi) wf xf ->
    ITm rho a i wA FA wa xa ->
    ITm rho (app A B f a) j
        (wB wa (upEl dA k EA FA wa xa)) (FB wa (upEl dA k EA FA wa xa))
        (eapp wf wa)
        (dnEl dB k EB (FB wa (upEl dA k EA FA wa xa)) (eapp wf wa)
           (piApp k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
              redB cohB gPi wf xf wa (upEl dA k EA FA wa xa)))

(* ---- Sigma.  No pinning equation anywhere: the realiser of a pair is the
     pair of its components' realisers, and the realiser of a projection is
     the projection of its subject's.  The layer-1 goodness of the pair is a
     premise, as it is for every introduction whose realiser is a value. ---- *)
| i_pair rho A B t a k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wt (xt : kElAt FA wt) wa (xa : kElAt (FB wt (upEl dA k EA FA wt xt)) wa)
    (g : Good (esig wA B0) (epair wt wa)) :
    esig wA B0 = ers rho (sig_ k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITm rho t i wA FA wt xt ->
    ITm rho a j (wB wt (upEl dA k EA FA wt xt)) (FB wt (upEl dA k EA FA wt xt)) wa xa ->
    ITm rho (pair k A B t a) k (esig wA B0)
        (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig)
        (epair wt wa)
        (sigPair k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig wt wa (upEl dA k EA FA wt xt)
           (upEl dB k EB (FB wt (upEl dA k EA FA wt xt)) wa xa) g)

| i_fst rho A B p k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wp (xp : kElAt (sigFam k wA B0 (upF dA k EA FA) wB
                      (fun u x => upF dB k EB (FB u x)) redB cohB gSig) wp) :
    esig wA B0 = ers rho (sig_ k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITm rho p k (esig wA B0)
        (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig) wp xp ->
    ITm rho (fst A B p) i wA FA (efst wp)
        (dnEl dA k EA FA (efst wp)
           (sigFst k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
              redB cohB gSig wp xp))

| i_snd rho A B p k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gSig : eqty k (esig wA B0) (esig wA B0))
    wp (xp : kElAt (sigFam k wA B0 (upF dA k EA FA) wB
                      (fun u x => upF dB k EB (FB u x)) redB cohB gSig) wp) :
    esig wA B0 = ers rho (sig_ k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITm rho p k (esig wA B0)
        (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig) wp xp ->
    ITm rho (snd A B p) j
        (wB (efst wp)
           (sigFst k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
              redB cohB gSig wp xp))
        (FB (efst wp)
           (sigFst k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
              redB cohB gSig wp xp))
        (esnd wp)
        (dnEl dB k EB
           (FB (efst wp)
              (sigFst k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                 redB cohB gSig wp xp))
           (esnd wp)
           (sigSnd k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
              redB cohB gSig wp xp))


(* ---- W: a tree, and the recursion on it ----

   A sup's label is read at the label type's own level and lifted; its
   branching function is read at the Pi type `t_sup` gives it, whose domain is
   the branching type at the label and whose codomain is constantly the tree
   type, and `brApp` reads the branches off it.  `wSup` then asks for exactly
   that, plus the layer-1 goodness of the sup, which is a premise as it is for
   every introduction whose realiser is a value. ---- *)
| i_sup rho A B a f k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gW : eqty k (ew wA B0) (ew wA B0))
    Bbr (redBbr : forall v, reds (eapp Bbr v) (ew wA B0))
    (gBr : forall u0 (z : kElAt (upF dA k EA FA) u0),
       eqty k (epi (wB u0 z) Bbr) (epi (wB u0 z) Bbr))
    wa (xa : kElAt FA wa)
    wf (xf : kElAt (brFam k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
                      Bbr redBbr gBr wa (upEl dA k EA FA wa xa)) wf)
    (gd : Good (ew wA B0) (esup wa wf)) :
    (* only the TYPE's realiser is pinned: a sup's own realiser is the pair
       of its label's and its branching function's, and the Pi the branching
       function lives at needs no pin, since the clause reads f at a family
       it is given (which is how `i_pair` treats its second component too) *)
    ew wA B0 = ers rho (wt k A B) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    ITm rho a i wA FA wa xa ->
    ITm rho f k (epi (wB wa (upEl dA k EA FA wa xa)) Bbr)
        (brFam k i j dA dB EA EB wA FA B0 wB FB redB cohB gW Bbr redBbr gBr
           wa (upEl dA k EA FA wa xa)) wf xf ->
    ITm rho (sup k A B a f) k (ew wA B0)
        (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW)
        (esup wa wf)
        (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW wa wf (upEl dA k EA FA wa xa)
           (brApp k i j dA dB EA EB wA FA B0 wB FB redB cohB gW Bbr redBbr gBr
              wa (upEl dA k EA FA wa xa) wf xf)
           (brApp_eq k i j dA dB EA EB wA FA B0 wB FB redB cohB gW Bbr redBbr gBr
              wa (upEl dA k EA FA wa xa) wf xf)
           gd)

(* ---- the recursion.  The step is read in its three-entry context -- the
   label, the branching function, the induction hypothesis -- and the last two
   entries are elements of Pi families, built from the semantic data by
   `brEl` and `ihEl` (PiEl.v's `piLam`).  Its realiser is a free index tied to
   the erased step by `redS`, exactly as `i_natrec`'s is, with three beta
   steps instead of two.

   The step's congruence is a PREMISE, because `wRecS`'s definition depends on
   it: the recursor is built from its graph, and the graph's extensionality is
   what supplies the induction hypothesis's own (see Interp/WEl.v).  It is the
   functionality of the step's reading, which is what Interp/Fun.v proves. ---- *)
| i_wrec rho A B C s w k i j m n dA dB dBn dC
    (EA : dA + i = k) (EB : dB + j = k) (EBn : dBn + j = n) (EC : dC + m = n)
    (* the induction hypothesis is read at the LEAST level that accommodates
       both its domain (the branching type, at j) and its codomain (the motive
       at the subtree, at m).  Without this pin the clause would leave `n`
       free, and two readings of one `wrec` could put their IH entries at
       different levels -- which `EnvRel` cannot relate, so functionality at
       the step would not even be statable. *)
    (En : n = Nat.max j m)
    wA (FA : kUFam i wA) B0
    (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
    (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
    (redB : forall u x, reds (eapp B0 u) (wB u x))
    (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
       kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
    (gW : eqty k (ew wA B0) (ew wA B0))
    (SC : etm -> etm)
    (FC : forall w0 x, kUFam m (SC w0))
    (cohC : forall w0 x w0' x',
       kEqAt (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                redB cohB gW) w0 x
             (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                redB cohB gW) w0' x' ->
       kceq (kAt (FC w0 x)) (kAt (FC w0' x')))
    Bbr (redBbr : forall v, reds (eapp Bbr v) (ew wA B0))
    (gBr : forall u0 (z : kElAt (upF dA k EA FA) u0),
       eqty k (epi (wB u0 z) Bbr) (epi (wB u0 z) Bbr))
    Bih (gIh : forall u0 (z : kElAt (upF dA k EA FA) u0) (f : etm),
           Good (ew wA B0) (esup u0 f) ->
           eqty n (epi (wB u0 z) (Bih u0 z f)) (epi (wB u0 z) (Bih u0 z f)))
    (Bih_red : forall u0 z f v, reds (eapp (Bih u0 z f) v) (SC (eapp f v)))
    Sr
    (gf : forall u0 (z : kElAt (upF dA k EA FA) u0) f,
       Good (ew wA B0) (esup u0 f) -> Good (epi (wB u0 z) Bbr) f)
    (gih : forall u0 (z : kElAt (upF dA k EA FA) u0) f,
       Good (ew wA B0) (esup u0 f) ->
       Good (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f))
    (ws : WsTy k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC Sr)
    (xs : XsTy k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC Sr ws)
    (redS : RedSTy k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC Sr ws)
    (stepSrel : StepRelTy k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
                  m SC FC Sr ws xs redS)
    ww (xw : kElAt (wFam k wA B0 (upF dA k EA FA) wB
                      (fun u x => upF dB k EB (FB u x)) redB cohB gW) ww) :
    Sr = ers rho (stepWrap3 s) ->
    ew wA B0 = ers rho (wt k A B) ->
    (* and the motive's realiser is pinned too.  `DC` ties it to the erasure
       of C only at realisers that carry an ELEMENT of the tree family, and
       the induction hypothesis's type has to be recognised at layer-1
       related realisers, where no element is to hand -- so the pin is stated
       directly.  It is what the totality direction builds anyway, and with
       `SC : etm -> etm` it is an equation between erasures and nothing
       more. *)
    (forall w1, SC w1 = subst_etm (scons w1 (rsub rho)) (er C)) ->
    ITy rho A i wA FA ->
    (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) ->
    (forall u x, ITy (ext rho (wFam k wA B0 (upF dA k EA FA) wB
                                 (fun u0 x0 => upF dB k EB (FB u0 x0)) redB cohB gW)
                        u x) C m (SC u) (FC u x)) ->
    (* the step's reading, in the three-entry environment *)
    (forall u0 z f sub subext gd ih ihext,
       ITm (ext (ext (ext rho FA u0 (dnEl dA k EA FA u0 z))
                  (brFam k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
                     Bbr redBbr gBr u0 z) f
                  (brEl k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
                     Bbr redBbr gBr u0 z f sub subext (gf u0 z f gd)))
              (ihFam k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                 n dBn dC EBn EC Bih gIh Bih_red u0 z f gd sub subext)
              (ihR Sr f)
              (ihEl k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                 n dBn dC EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                 (gih u0 z f gd)))
           s m
           (SC (esup u0 f))
           (FC (esup u0 f)
              (wSup k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
                 redB cohB gW u0 f z sub subext gd))
           (ws u0 z f sub subext gd ih ihext)
           (xs u0 z f sub subext gd ih ihext)) ->
    ITm rho w k (ew wA B0)
        (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW) ww xw ->
    ITm rho (wrec A B C s w) m (SC ww) (FC ww xw) (ewrec Sr ww)
        (wRecS k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW m Sr (fun w0 _ => SC w0) FC cohC
           (stepOf k i j dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC Sr
              ws xs redS)
           stepSrel ww xw)

(* ---- large elimination of N.  The step term carries its own two binders, so
     its semantic content is, for every scrutinee value and every value of the
     motive at it, a value of the motive at the successor: no Pi-type, no
     nrec_step, no double application.  Its realiser is a free index tied to
     the erased step S0 by redS -- the two beta-steps that the erased
     recursor's computation rule leaves behind are absorbed by expansion,
     which is what moveTo does.

     The scrutinee's family is natFam j, the annotation on its type, and the
     motive is read at its own level k in an environment extended by an entry
     at j. ---- *)
| i_natrec rho C z s n k j
    (SC : etm -> etm)
    (FC : forall m (x : kElAt (natFam j) m), kUFam k (SC m))
    (cohC : forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
              kceq (kAt (FC m x)) (kAt (FC m' x')))
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
        (semrec k j SC FC cohC wz S0 xz
           (fun m x w y =>
              moveTo (FC (esucc m) (natSucc x)) (FC (esucc m) (natSucc x))
                (famAtSelf (FC (esucc m) (natSucc x)))
                (ws m x w y) (xs m x w y) (eapp (eapp S0 m) w) (redS m x w y))
           (natIdx xn) wn (natSpec xn))

(* ---- propositions ---- *)
| i_false rho k w (g : Good eprop efalse) :
    w = ers rho (false_ k) ->
    ITm rho (false_ k) k eprop (propFam k) efalse (propElem efalse False g)
(* The impredicative forall.  Its LEVEL is its own annotation, not something
     read off the premises: the premise about p is quantified over the
     domain's elements and says nothing when the domain is empty, so without
     the annotation a forall over an empty type would be interpretable at
     every level.  The domain may live at ANY level k -- that is the
     impredicativity. *)
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
     proof variable or application. ---- *)
| i_proof rho t p k j wp (xp : kElAt (propFam j) wp)
    (h : propVal xp) w (g : Good (eprf wp) w) :
    w = ers rho t ->
    ITm rho p j eprop (propFam j) wp xp ->
    ITm rho t k (eprf wp) (prfF k xp) w (prfElem w h g)

(* ---- the universe lift on terms.  Same realiser, same value up to the
     lift of the decoding. ---- *)
| i_up_tm rho A t k Sy (F : kUFam k Sy) w (x : kElAt F w) :
    ITy rho A k Sy F ->
    ITm rho t k Sy F w x ->
    ITm rho (uptm A t) (S k) Sy (famLiftK F) w (elLift F w x)

(* ---- conversion of the TYPE.  The interpretation has to be closed under
     it: t_conv moves a term to a convertible type, and its value has to move
     with it, along the equality of the two types' families.  Without it the
     fundamental lemma's conversion case is not provable at all.  Note that
     ITy gets its own clause (ity_conv) for the same reason. ---- *)
| i_conv rho t k Sy (F : kUFam k Sy) Sy' (F' : kUFam k Sy') w (x : kElAt F w)
    (P : kceq (kAt F) (kAt F')) :
    ITm rho t k Sy F w x ->
    ITm rho t k Sy' F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
