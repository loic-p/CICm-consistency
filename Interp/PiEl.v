From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.Univ Interp.Env Interp.Elem.
From Stdlib Require Import Arith Lia.

(* Semantic application: the elimination side of the Pi-family.

   A Pi-code's decoding is a function on the elements of the DOMAIN CODE at
   the node the Pi-code lives at, whereas the interpretation has an element of
   the domain FAMILY.  The two are different instances of one family, so the
   argument goes in through `famFrom` and the value comes back through
   `famTo`, and the round trip is not the identity -- only related to it
   (`pArg_eq`).  Since the codomain family is indexed by the argument, the
   value lands at `FB u' (pArg y)` rather than at `FB u' y`, and one coercion
   along `cohB` brings it home.

   That coercion is the only content of this file; everything else is
   placement, which is definitional.  In v1 this was the same shape but with
   `ctoK` (the canonical transport) and the `hetC` algebra on top of it, and
   with `isoB` stated backwards so every use needed `kEqAt_sym` first.

   Performance note: nothing below unfolds a coercion.  `xto` is sealed in
   Interp/Codes.v, and every statement is an equality of elements, so the
   conversion checker never looks inside one.  v1's analogue of this file took
   tens of seconds; this one takes under two. *)

Section PiEl.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  Local Notation PF := (piFam k A0 B0 FA SB FB redB cohB gPi).

  (* The argument, after its round trip through the domain code. *)
  Definition pArg v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    u' (y : kElAt FA u') : kElAt FA u' :=
    pxc k A0 B0 FA v fT pf u'
        (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y).

  Lemma pArg_eq v fT pf u' y : kEqAt FA u' (pArg v fT pf u' y) FA u' y.
  Proof. unfold pArg, pxc; apply famTo_famFrom. Qed.

  (* the raw application, at the instance the code's decoding gives it *)
  Definition pRaw v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    u (x : kElC (pcode k A0 B0 FA SB FB redB v fT pf) u) u' (y : kElAt FA u')
    : kElC (pcB k A0 B0 FA SB FB redB v fT pf u'
              (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y)) (eapp u u') :=
    proj1_sig (Datatypes.fst x) u'
      (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y).

  (* Application at one instance of the family: bring the raw value to the
     canonical instance of FB at the round-tripped argument, then coerce along
     cohB to FB at the argument itself. *)
  Definition pApp v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    u (x : kElC (pcode k A0 B0 FA SB FB redB v fT pf) u)
    u' (y : kElAt FA u') : kElAt (FB u' y) (eapp u u') :=
    kto (kAt (FB u' (pArg v fT pf u' y))) (kAt (FB u' y))
      (famAtWf (FB u' (pArg v fT pf u' y))) (famAtWf (FB u' y))
      (cohB u' (pArg v fT pf u' y) u' y (pArg_eq v fT pf u' y)) (eapp u u')
      (famTo (FB u' (pArg v fT pf u' y)) (eapp B0 u') _ _ (eapp u u')
         (pRaw v fT pf u x u' y)).

  (* the value is related to the raw one, across the two codes *)
  Lemma pApp_coh v fT pf u x u' y :
    kcel (pcB k A0 B0 FA SB FB redB v fT pf u'
            (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y))
         (eapp u u') (pRaw v fT pf u x u' y)
         (kAt (FB u' y)) (eapp u u') (pApp v fT pf u x u' y).
  Proof.
    unfold pApp.
    eapply ktrE;
      [ exact (famWf (FB u' (pArg v fT pf u' y)) _ _ _)
      | exact (famAtWf (FB u' (pArg v fT pf u' y)))
      | exact (famAtWf (FB u' y))
      | exact (uf_coh (FB u' (pArg v fT pf u' y)) _ _ _ _ _ _)
      | exact (famTo_coh (FB u' (pArg v fT pf u' y)) _ _ _ (eapp u u')
                 (pRaw v fT pf u x u' y))
      | apply kto_coh ].
  Qed.

  (* Application at the canonical instance, which is the one the
     interpretation uses.  The accessibility proof has to be destructed for
     the family's code to unfold at all. *)
  Definition piApp u (x : kElAt PF u) u' (y : kElAt FA u') : kElAt (FB u' y) (eapp u u').
  Proof.
    revert x; unfold kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT]; intros x.
    exact (pApp (epi A0 B0) fT (evalAg_refl (epi A0 B0)) u x u' y).
  Defined.

  (* ---- INTRODUCTION: a function from its behaviour ----

     The dual of `piApp`, and the one thing v1 never built: v1's `i_lam`
     carried the Pi-element as an index together with an equation saying what
     it did, so the fundamental lemma had to be handed one from outside.  v2
     needs the introduction for real, because the step of `wrec` is typed in
     a context whose entries are a branching FUNCTION and an induction
     hypothesis -- both Pi-typed -- so the interpretation has to turn a
     semantic family of values into an element of a Pi family.

     The data is exactly a lambda's: for every argument a value of the
     codomain at that argument, extensional in the argument, with the
     subject's realiser reducing to the value's.  The construction is one
     expansion (the beta step the erasure leaves behind) and one coercion
     into the placed codomain. *)

  Definition pLamF v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    u1 (x1 : kElS (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf) (pcA k A0 B0 FA v fT pf)) u1)
    : kElC (pcB k A0 B0 FA SB FB redB v fT pf u1 x1) (eapp w u1) :=
    kto (kAt (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
        (pcB k A0 B0 FA SB FB redB v fT pf u1 x1)
        (famAtWf (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
        (pwfB k A0 B0 FA SB FB redB v fT pf u1 x1)
        (knsymU (pcB k A0 B0 FA SB FB redB v fT pf u1 x1)
           (kAt (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
           (pcB_at k A0 B0 FA SB FB redB v fT pf u1 x1))
        (eapp w u1)
        (famExp (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)) (eapp w u1)
           (wt u1 (pxc k A0 B0 FA v fT pf u1 x1))
           (redt u1 (pxc k A0 B0 FA v fT pf u1 x1))
           (xt u1 (pxc k A0 B0 FA v fT pf u1 x1))).

  (* the value is related to the behaviour it was built from *)
  Lemma pLamF_coh v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y)) u1 x1 :
    kcel (pcB k A0 B0 FA SB FB redB v fT pf u1 x1) (eapp w u1)
           (pLamF v fT pf w wt xt redt u1 x1)
         (kAt (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
           (wt u1 (pxc k A0 B0 FA v fT pf u1 x1))
           (xt u1 (pxc k A0 B0 FA v fT pf u1 x1)).
  Proof.
    unfold pLamF.
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB v fT pf u1 x1)
      | exact (famAtWf (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
      | exact (famAtWf (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
      | exact (pcB_at k A0 B0 FA SB FB redB v fT pf u1 x1)
      | apply knsym; apply kto_coh
      | apply famExp_rel ].
  Qed.

  (* and it is extensional, which is what the decoding asks of it *)
  Lemma pLamF_ext v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    (xtext : forall u y u' y', kEqAt FA u y FA u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB u' y') (wt u' y') (xt u' y'))
    u1 x1 u1' x1' :
    kcEl (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf) (pcA k A0 B0 FA v fT pf)) u1 x1
         (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf) (pcA k A0 B0 FA v fT pf)) u1' x1' ->
    kcel (pcB k A0 B0 FA SB FB redB v fT pf u1 x1) (eapp w u1)
           (pLamF v fT pf w wt xt redt u1 x1)
         (pcB k A0 B0 FA SB FB redB v fT pf u1' x1') (eapp w u1')
           (pLamF v fT pf w wt xt redt u1' x1').
  Proof.
    intros H.
    assert (Ha : kEqAt FA u1 (pxc k A0 B0 FA v fT pf u1 x1)
                   FA u1' (pxc k A0 B0 FA v fT pf u1' x1'))
      by (apply famTo_eq; exact H).
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB v fT pf u1 x1)
      | exact (famAtWf (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
      | exact (pwfB k A0 B0 FA SB FB redB v fT pf u1' x1')
      | exact (pcB_at k A0 B0 FA SB FB redB v fT pf u1 x1)
      | exact (pLamF_coh v fT pf w wt xt redt u1 x1) |].
    eapply ktrE;
      [ exact (famAtWf (FB u1 (pxc k A0 B0 FA v fT pf u1 x1)))
      | exact (famAtWf (FB u1' (pxc k A0 B0 FA v fT pf u1' x1')))
      | exact (pwfB k A0 B0 FA SB FB redB v fT pf u1' x1')
      | exact (cohB u1 (pxc k A0 B0 FA v fT pf u1 x1)
                 u1' (pxc k A0 B0 FA v fT pf u1' x1') Ha)
      | exact (xtext u1 (pxc k A0 B0 FA v fT pf u1 x1)
                 u1' (pxc k A0 B0 FA v fT pf u1' x1') Ha)
      | apply knsym; exact (pLamF_coh v fT pf w wt xt redt u1' x1') ].
  Qed.

  Definition pLam v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    (xtext : forall u y u' y', kEqAt FA u y FA u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB u' y') (wt u' y') (xt u' y'))
    (gd : Good v w)
    : kElC (pcode k A0 B0 FA SB FB redB v fT pf) w :=
    (exist _ (pLamF v fT pf w wt xt redt) (pLamF_ext v fT pf w wt xt redt xtext), gd).

  Definition piLam (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    (xtext : forall u y u' y', kEqAt FA u y FA u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB u' y') (wt u' y') (xt u' y'))
    (gd : Good (epi A0 B0) w) : kElAt PF w.
  Proof.
    unfold kElAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT].
    exact (pLam (epi A0 B0) fT (evalAg_refl (epi A0 B0)) w wt xt redt xtext gd).
  Defined.
End PiEl.

(* ------------------------------------------------------------------ *)
(* The law: application respects the equalities.                        *)
(*                                                                    *)
(* The middle step is the equality of the two Pi-elements, which IS      *)
(* "related arguments give related values" -- one application, where v1  *)
(* had to flip an isomorphism, build the transport `pisoB` and reconcile  *)
(* two `hetC`s.                                                         *)
(* ------------------------------------------------------------------ *)

Section PiElLaw.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  Local Notation PF := (piFam k A0 B0 FA SB FB redB cohB gPi).
  Local Notation pA := (pArg k A0 B0 FA).

  (* the code of the instance the raw value lands at is equal to the canonical
     code of FB at any argument related to the round-tripped one *)
  Lemma pcB_ceq v fT pf u' y u'' y1 :
    kEqAt FA u' y FA u'' y1 ->
    kceq (pcB k A0 B0 FA SB FB redB v fT pf u'
            (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y))
         (kAt (FB u'' y1)).
  Proof.
    intros H.
    eapply ktrU;
      [ exact (pwfB k A0 B0 FA SB FB redB v fT pf u'
                 (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y))
      | exact (famAtWf (FB u' (pA v fT pf u' y)))
      | exact (famAtWf (FB u'' y1))
      | exact (pcB_at k A0 B0 FA SB FB redB v fT pf u'
                 (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y)) |].
    apply cohB.
    eapply kEqAt_trans;
      [ exact (famAtSelf FA)
      | exact (pArg_eq k A0 B0 FA v fT pf u' y)
      | exact H ].
  Qed.

  Lemma piApp_eq u (x : kElAt PF u) u1 (x1 : kElAt PF u1)
    u' (y : kElAt FA u') u'' (y1 : kElAt FA u'') :
    kEqAt PF u x PF u1 x1 -> kEqAt FA u' y FA u'' y1 ->
    kRel (FB u' y) (eapp u u') (piApp k A0 B0 FA SB FB redB cohB gPi u x u' y)
         (FB u'' y1) (eapp u1 u'') (piApp k A0 B0 FA SB FB redB cohB gPi u1 x1 u'' y1).
  Proof.
    revert x x1; unfold piApp, kElAt, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT]; intros x x1 Hx Hy.
    set (pf := evalAg_refl (epi A0 B0)).
    set (z := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u' y).
    set (z1 := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u'' y1).
    split; [exact (cohB u' y u'' y1 Hy) |].
    (* the three relations: into the raw value, across the two functions, and
       back out of the raw value *)
    assert (H1 : kcel (kAt (FB u' y)) (eapp u u')
                   (pApp k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u x u' y)
                   (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z) (eapp u u')
                   (pRaw k A0 B0 FA SB FB redB (epi A0 B0) fT pf u x u' y))
      by (apply knsym;
          exact (pApp_coh k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u x u' y)).
    assert (H2 : kcel (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z) (eapp u u')
                   (pRaw k A0 B0 FA SB FB redB (epi A0 B0) fT pf u x u' y)
                   (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1) (eapp u1 u'')
                   (pRaw k A0 B0 FA SB FB redB (epi A0 B0) fT pf u1 x1 u'' y1))
      by (apply (proj1 Hx); apply famFrom_eq; exact Hy).
    assert (H3 : kcel (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1) (eapp u1 u'')
                   (pRaw k A0 B0 FA SB FB redB (epi A0 B0) fT pf u1 x1 u'' y1)
                   (kAt (FB u'' y1)) (eapp u1 u'')
                   (pApp k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u1 x1 u'' y1))
      by exact (pApp_coh k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u1 x1 u'' y1).
    (* and the code equalities the two compositions need *)
    assert (E1 : kceq (kAt (FB u' y))
                   (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z))
      by (apply knsymU; exact (pcB_ceq (epi A0 B0) fT pf u' y u' y (kEqAt_refl FA u' y))).
    assert (E2 : kceq (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
                   (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1)).
    { eapply ktrU;
        [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
        | exact (famAtWf (FB u'' y1))
        | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1)
        | exact (pcB_ceq (epi A0 B0) fT pf u' y u'' y1 Hy)
        | apply knsymU;
          exact (pcB_ceq (epi A0 B0) fT pf u'' y1 u'' y1 (kEqAt_refl FA u'' y1)) ]. }
    eapply ktrE;
      [ exact (famAtWf (FB u' y))
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
      | exact (famAtWf (FB u'' y1))
      | exact E1 | exact H1 |].
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1)
      | exact (famAtWf (FB u'' y1))
      | exact E2 | exact H2 | exact H3 ].
  Qed.

  (* ---- EXTENSIONALITY: two Pi elements are equal as soon as their
     applications are.  This IS the Pi code's element relation (`mkPi_eq`),
     read through the placement: the only work is the argument's round trip
     through the domain code, which the function's own extensionality
     absorbs.  It is the converse of piApp_eq, and the eta rule needs it. ---- *)

  Lemma piEl_ext u (x : kElAt PF u) u1 (x1 : kElAt PF u1) :
    Rel (epi A0 B0) u u1 ->
    (forall v (y : kElAt FA v) v' (y' : kElAt FA v'), kEqAt FA v y FA v' y' ->
       kEqAt (FB v y) (eapp u v)
               (piApp k A0 B0 FA SB FB redB cohB gPi u x v y)
             (FB v' y') (eapp u1 v')
               (piApp k A0 B0 FA SB FB redB cohB gPi u1 x1 v' y')) ->
    kEqAt PF u x PF u1 x1.
  Proof.
    revert x x1; unfold piApp, kElAt, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT]; intros x x1 HR Hb.
    set (pf := evalAg_refl (epi A0 B0)).
    split; [| split; [exists k; exact gPi | exact HR]].
    intros v1 z1 v1' z1' r.
    (* each side: the raw application IS the family-level one, once the
       argument's round trip is absorbed by the function's extensionality *)
    assert (Hside : forall w1 t1 uu
                      (xx : kElC (pcode k A0 B0 FA SB FB redB (epi A0 B0) fT pf)
                              uu),
               kcel (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 t1)
                      (eapp uu w1) (proj1_sig (Datatypes.fst xx) w1 t1)
                    (kAt (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)))
                      (eapp uu w1)
                      (pApp k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf uu xx w1
                         (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1))).
    { intros w1 t1 uu xx.
      set (zz := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) w1
                   (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)).
      assert (q : kcel (pcA k A0 B0 FA (epi A0 B0) fT pf) w1 zz
                       (pcA k A0 B0 FA (epi A0 B0) fT pf) w1 t1)
        by exact (famFrom_famTo FA A0 (pAcc A0 B0 (epi A0 B0) fT pf)
                    (evalAg_refl A0) w1 t1).
      (* the function respects the domain code's relation *)
      pose proof (proj2_sig (Datatypes.fst xx) w1 zz w1 t1 q) as Hfx.
      eapply ktrE;
        [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 t1)
        | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 zz)
        | exact (famAtWf (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)))
        | (* the two instances' codes are equal, through their canonical ones *)
          eapply ktrU;
          [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 t1)
          | exact (famAtWf (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)))
          | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 zz)
          | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 t1) |];
          eapply ktrU;
          [ exact (famAtWf (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)))
          | exact (famAtWf (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 zz)))
          | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 zz)
          | apply cohB; apply famTo_eq; apply knsym; exact q
          | apply knsymU;
            exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 zz) ]
        | apply knsym; exact Hfx
        | exact (pApp_coh k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf uu xx w1
                   (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)) ]. }
    (* the two arguments, read as elements of the domain family *)
    pose proof (famTo_eq FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0)
                  v1 z1 A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0)
                  v1' z1' r) as Hy.
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1 z1)
      | exact (famAtWf (FB v1 (pxc k A0 B0 FA (epi A0 B0) fT pf v1 z1)))
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1' z1')
      | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1 z1)
      | exact (Hside v1 z1 u x) |].
    eapply ktrE;
      [ exact (famAtWf (FB v1 (pxc k A0 B0 FA (epi A0 B0) fT pf v1 z1)))
      | exact (famAtWf (FB v1' (pxc k A0 B0 FA (epi A0 B0) fT pf v1' z1')))
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1' z1')
      | exact (cohB _ _ _ _ Hy)
      | exact (Hb v1 (pxc k A0 B0 FA (epi A0 B0) fT pf v1 z1)
                 v1' (pxc k A0 B0 FA (epi A0 B0) fT pf v1' z1') Hy)
      | apply knsym; exact (Hside v1' z1' u1 x1) ].
  Qed.

  (* ---- and the law of the introduction: what a `piLam` does is what it was
     built to do.  This is the equation v1's `i_lam` had to carry as a
     premise. ---- *)
  Lemma piLam_app (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    (xtext : forall u y u' y', kEqAt FA u y FA u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB u' y') (wt u' y') (xt u' y'))
    (gd : Good (epi A0 B0) w) u (y : kElAt FA u) :
    kEqAt (FB u y) (eapp w u)
      (piApp k A0 B0 FA SB FB redB cohB gPi w
         (piLam k A0 B0 FA SB FB redB cohB gPi w wt xt redt xtext gd) u y)
      (FB u y) (wt u y) (xt u y).
  Proof.
    unfold piApp, piLam, kElAt, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT].
    set (pf := evalAg_refl (epi A0 B0)).
    set (z := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u y).
    eapply ktrE;
      [ exact (famAtWf (FB u y))
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u z)
      | exact (famAtWf (FB u y))
      | apply knsymU;
        exact (pcB_ceq (epi A0 B0) fT pf u y u y (kEqAt_refl FA u y))
      | (* out of the application, into the raw value, which IS the pLamF *)
        apply knsym;
        exact (pApp_coh k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf w
                 (pLam k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf w wt xt redt xtext gd)
                 u y) |].
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u z)
      | exact (famAtWf (FB u (pA (epi A0 B0) fT pf u y)))
      | exact (famAtWf (FB u y))
      | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT pf u z)
      | exact (pLamF_coh k A0 B0 FA SB FB redB (epi A0 B0) fT pf w wt xt redt u z)
      | exact (xtext u (pA (epi A0 B0) fT pf u y) u y
                 (pArg_eq k A0 B0 FA (epi A0 B0) fT pf u y)) ].
  Qed.
End PiElLaw.

(* ------------------------------------------------------------------ *)
(* Two Pi-families with equal components, and application across them.  *)
(*                                                                    *)
(* This is where v1 paid the most.  Its `piApp_to` had to unfold the     *)
(* coercion at a Pi code (`toRefine_pi_app`), reconcile the pullback the  *)
(* coercion applies the function at with the argument in hand             *)
(* (`pull_of_to`), and compose two `hetC`s -- and it is the file whose     *)
(* conversion checks made v1's Interp slow.  Here the coercion is never    *)
(* unfolded: `piApp_to` is the heterogeneous application law applied to     *)
(* `xto_coh`, so the kernel only ever sees equalities of elements.          *)
(* ------------------------------------------------------------------ *)

Section PiElX.
  Context (k : nat).
  Context (A0 B0 : etm) (FA : kUFam k A0)
          (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x))
          (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x')))
          (gPi : eqty k (epi A0 B0) (epi A0 B0)).
  Context (A0' B0' : etm) (FA' : kUFam k A0')
          (SB' : forall u, kElAt FA' u -> etm)
          (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
          (redB' : forall u x, reds (eapp B0' u) (SB' u x))
          (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
             kceq (kAt (FB' u x)) (kAt (FB' u' x')))
          (gPi' : eqty k (epi A0' B0') (epi A0' B0')).
  (* what relates the two families componentwise *)
  Context (Hty : tyeq (epi A0 B0) (epi A0' B0'))
          (HA : kceq (kAt FA) (kAt FA'))
          (HB : forall u x u' x', kEqAt FA u x FA' u' x' ->
             kceq (kAt (FB u x)) (kAt (FB' u' x'))).

  Local Notation PF := (piFam k A0 B0 FA SB FB redB cohB gPi).
  Local Notation PF' := (piFam k A0' B0' FA' SB' FB' redB' cohB' gPi').

  (* The two families are equal: buildPi_ceq, with the components' equalities
     read through the placement. *)
  Lemma piFam_ceq : kceq (kAt PF) (kAt PF').
  Proof.
    unfold kAt, uf_at, kAcc.
    generalize (uf_acc PF') as h'; generalize (uf_acc PF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT'].
    apply (buildPi_ceq k (epi A0 B0) A0 B0 fT (epi A0' B0') A0' B0' fT' Hty
             (pEv A0 B0 (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
             (pEv A0' B0' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
             (pcA k A0 B0 FA (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
             (peA k A0 B0 FA (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
             (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
             (peB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
             (pcA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
             (peA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
             (pcB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                (evalAg_refl (epi A0' B0')))
             (peB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                (evalAg_refl (epi A0' B0')))).
    - (* domains *)
      apply famCeq_all; exact HA.
    - (* codomains, at corresponding arguments *)
      intros u x u' y r.
      eapply ktrU;
        [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT
                   (evalAg_refl (epi A0 B0)) u x)
        | exact (famAtWf (FB u (pxc k A0 B0 FA (epi A0 B0) fT
                                  (evalAg_refl (epi A0 B0)) u x)))
        | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                   (evalAg_refl (epi A0' B0')) u' y)
        | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT
                   (evalAg_refl (epi A0 B0)) u x) |].
      eapply ktrU;
        [ exact (famAtWf (FB u (pxc k A0 B0 FA (epi A0 B0) fT
                                  (evalAg_refl (epi A0 B0)) u x)))
        | exact (famAtWf (FB' u' (pxc k A0' B0' FA' (epi A0' B0') fT'
                                    (evalAg_refl (epi A0' B0')) u' y)))
        | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                   (evalAg_refl (epi A0' B0')) u' y)
        | | apply knsymU;
            exact (pcB_at k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                     (evalAg_refl (epi A0' B0')) u' y) ].
      apply HB.
      exact (famTo_eqX FA A0 (pAcc A0 B0 (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
               (evalAg_refl A0) u x FA' A0'
               (pAcc A0' B0' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
               (evalAg_refl A0') u' y
               (famCeq_all FA FA' HA A0
                  (pAcc A0 B0 (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
                  (evalAg_refl A0) A0'
                  (pAcc A0' B0' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
                  (evalAg_refl A0')) r).
  Qed.
  (* Application across the two families: the same chain as `piApp_eq`, with
     the primed family on the right.  The middle step is again the equality of
     the two function elements, which at a Pi code IS "related arguments give
     related values" -- and it is heterogeneous in the code, which is the
     whole reason this lemma needs no transport. *)
  Lemma piApp_eqX u (x : kElAt PF u) u1 (x1 : kElAt PF' u1)
    u' (y : kElAt FA u') u'' (y1 : kElAt FA' u'') :
    kEqAt PF u x PF' u1 x1 -> kEqAt FA u' y FA' u'' y1 ->
    kRel (FB u' y) (eapp u u') (piApp k A0 B0 FA SB FB redB cohB gPi u x u' y)
         (FB' u'' y1) (eapp u1 u'')
         (piApp k A0' B0' FA' SB' FB' redB' cohB' gPi' u1 x1 u'' y1).
  Proof.
    revert x x1; unfold piApp, kElAt, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF') as h'; generalize (uf_acc PF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT']; intros x x1 Hx Hy.
    set (pf := evalAg_refl (epi A0 B0)).
    set (pf' := evalAg_refl (epi A0' B0')).
    set (z := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u' y).
    set (z1 := famFrom FA' A0' (pAcc A0' B0' (epi A0' B0') fT' pf')
                 (evalAg_refl A0') u'' y1).
    split; [exact (HB u' y u'' y1 Hy) |].
    assert (Hz : kcel (pcA k A0 B0 FA (epi A0 B0) fT pf) u' z
                      (pcA k A0' B0' FA' (epi A0' B0') fT' pf') u'' z1)
      by (apply (famFrom_eqX FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0)
                   u' y FA' A0' (pAcc A0' B0' (epi A0' B0') fT' pf')
                   (evalAg_refl A0') u'' y1);
          [ exact HA | exact Hy ]).
    assert (HBz : kceq (kAt (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z)))
                       (kAt (FB' u'' (pxc k A0' B0' FA' (epi A0' B0') fT' pf' u'' z1))))
      by (apply HB;
          exact (famTo_eqX FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u' z
                   FA' A0' (pAcc A0' B0' (epi A0' B0') fT' pf') (evalAg_refl A0') u'' z1
                   (famCeq_all FA FA' HA A0 (pAcc A0 B0 (epi A0 B0) fT pf)
                      (evalAg_refl A0) A0'
                      (pAcc A0' B0' (epi A0' B0') fT' pf') (evalAg_refl A0')) Hz)).
    assert (E1 : kceq (kAt (FB u' y)) (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z))
      by (apply knsymU;
          exact (pcB_ceq k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u' y u' y
                   (kEqAt_refl FA u' y))).
    assert (E2 : kceq (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
                      (pcB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' pf' u'' z1)).
    { eapply ktrU;
        [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
        | exact (famAtWf (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z)))
        | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' pf' u'' z1)
        | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z) |].
      eapply ktrU;
        [ exact (famAtWf (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z)))
        | exact (famAtWf (FB' u'' (pxc k A0' B0' FA' (epi A0' B0') fT' pf' u'' z1)))
        | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' pf' u'' z1)
        | exact HBz
        | apply knsymU;
          exact (pcB_at k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' pf' u'' z1) ]. }
    eapply ktrE;
      [ exact (famAtWf (FB u' y))
      | exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
      | exact (famAtWf (FB' u'' y1))
      | exact E1
      | apply knsym;
        exact (pApp_coh k A0 B0 FA SB FB redB cohB (epi A0 B0) fT pf u x u' y) |].
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
      | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' pf' u'' z1)
      | exact (famAtWf (FB' u'' y1))
      | exact E2
      | apply (proj1 Hx); exact Hz
      | exact (pApp_coh k A0' B0' FA' SB' FB' redB' cohB' (epi A0' B0') fT' pf'
                 u1 x1 u'' y1) ].
  Qed.

  (* ---- the congruence of the INTRODUCTION: two lambdas with related
     behaviours have related values.  The Pi-element equality IS pointwise
     agreement on related arguments, so this is the behaviour hypothesis, with
     one `pLamF_coh` on either side to get at it.  v1 had no introduction at
     all, so it had no need of this; v2 does, because `i_lam` builds its value
     and the step of a W-recursion builds two Pi elements. ---- *)
  Lemma piLam_eq (w : etm)
    (wt : forall u, kElAt FA u -> etm)
    (xt : forall u y, kElAt (FB u y) (wt u y))
    (redt : forall u y, reds (eapp w u) (wt u y))
    (xtext : forall u y u' y', kEqAt FA u y FA u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB u' y') (wt u' y') (xt u' y'))
    (gd : Good (epi A0 B0) w)
    (w' : etm)
    (wt' : forall u, kElAt FA' u -> etm)
    (xt' : forall u y, kElAt (FB' u y) (wt' u y))
    (redt' : forall u y, reds (eapp w' u) (wt' u y))
    (xtext' : forall u y u' y', kEqAt FA' u y FA' u' y' ->
       kEqAt (FB' u y) (wt' u y) (xt' u y) (FB' u' y') (wt' u' y') (xt' u' y'))
    (gd' : Good (epi A0' B0') w')
    (HR : Rel (epi A0 B0) w w')
    (Hb : forall u y u' y', kEqAt FA u y FA' u' y' ->
       kEqAt (FB u y) (wt u y) (xt u y) (FB' u' y') (wt' u' y') (xt' u' y')) :
    kEqAt PF w (piLam k A0 B0 FA SB FB redB cohB gPi w wt xt redt xtext gd)
          PF' w' (piLam k A0' B0' FA' SB' FB' redB' cohB' gPi' w' wt' xt' redt'
                    xtext' gd').
  Proof.
    unfold piLam, kEqAt, kElAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF') as h'; generalize (uf_acc PF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT'].
    split; [| split; [exact Hty | exact HR]].
    intros u1 x1 u1' x1' Hx.
    (* the two arguments, read in the two domain families *)
    assert (Ha : kEqAt FA u1
                   (pxc k A0 B0 FA (epi A0 B0) fT (evalAg_refl (epi A0 B0)) u1 x1)
                   FA' u1'
                   (pxc k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl (epi A0' B0'))
                      u1' x1')).
    { apply (famTo_eqX FA A0
               (pAcc A0 B0 (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
               (evalAg_refl A0) u1 x1
               FA' A0'
               (pAcc A0' B0' (epi A0' B0') fT' (evalAg_refl (epi A0' B0')))
               (evalAg_refl A0') u1' x1');
        [ exact (famCeq_all FA FA' HA _ _ _ _ _ _) | exact Hx ]. }
    eapply ktrE;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT
                 (evalAg_refl (epi A0 B0)) u1 x1)
      | exact (famAtWf (FB u1 (pxc k A0 B0 FA (epi A0 B0) fT
                                 (evalAg_refl (epi A0 B0)) u1 x1)))
      | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                 (evalAg_refl (epi A0' B0')) u1' x1')
      | exact (pcB_at k A0 B0 FA SB FB redB (epi A0 B0) fT
                 (evalAg_refl (epi A0 B0)) u1 x1)
      | exact (pLamF_coh k A0 B0 FA SB FB redB (epi A0 B0) fT
                 (evalAg_refl (epi A0 B0)) w wt xt redt u1 x1) |].
    eapply ktrE;
      [ exact (famAtWf (FB u1 (pxc k A0 B0 FA (epi A0 B0) fT
                                 (evalAg_refl (epi A0 B0)) u1 x1)))
      | exact (famAtWf (FB' u1' (pxc k A0' B0' FA' (epi A0' B0') fT'
                                   (evalAg_refl (epi A0' B0')) u1' x1')))
      | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                 (evalAg_refl (epi A0' B0')) u1' x1')
      | exact (HB _ _ _ _ Ha)
      | exact (Hb _ _ _ _ Ha)
      | apply knsym;
        exact (pLamF_coh k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT'
                 (evalAg_refl (epi A0' B0')) w' wt' xt' redt' u1' x1') ].
  Qed.

  (* and the commutation with the coercion, which v1 proved by unfolding the
     coercion at a Pi code *)
  Lemma piApp_to (P : kceq (kAt PF) (kAt PF')) (Q : kceq (kAt FA) (kAt FA'))
    u (x : kElAt PF u) v (y : kElAt FA v) :
    kRel (FB v y) (eapp u v) (piApp k A0 B0 FA SB FB redB cohB gPi u x v y)
         (FB' v (kto (kAt FA) (kAt FA') (famAtWf FA) (famAtWf FA') Q v y)) (eapp u v)
         (piApp k A0' B0' FA' SB' FB' redB' cohB' gPi' u
            (kto (kAt PF) (kAt PF') (famAtWf PF) (famAtWf PF') P u x) v
            (kto (kAt FA) (kAt FA') (famAtWf FA) (famAtWf FA') Q v y)).
  Proof. apply piApp_eqX; apply kto_coh. Qed.
End PiElX.
