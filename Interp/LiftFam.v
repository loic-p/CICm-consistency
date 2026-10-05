From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift Codes.Mor.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.PiFam Interp.SigFam Interp.WFam Interp.Lift Interp.LiftN.
From Stdlib Require Import Arith Lia.

(* ------------------------------------------------------------------ *)
(* THE LIFT AGAINST THE BINDER FORMERS.                                *)
(*                                                                    *)
(* `up k (pi k A B) ≡ pi (S k) A B` is a conversion rule of the        *)
(* theory, and its semantic content is this file: the lift of a Pi      *)
(* FAMILY is the Pi family of the lifted components.  At nat, prop and  *)
(* Prf the same fact is three lines (Interp/Lift.v), because those      *)
(* codes carry no components; here the code's components are placed at  *)
(* nodes BELOW the former's, and the lift acts on them through the      *)
(* cone's dispatch.                                                    *)
(*                                                                    *)
(* Two things make it work.  First, `Codes/Lift.v`'s `liftSub_place`    *)
(* and friends: the lift of a placed component is the placed lift,      *)
(* definitionally -- which is why `datSucc` there is written with the   *)
(* projections of its argument rather than by destructing it.  Second,  *)
(* `mapRefine` keeps the clause, so the lifted code IS an `r_pi` once   *)
(* its well-formedness proof is destructed, and `kceq` at two `r_pi`s   *)
(* is the conjunction of the shadows' layer-1 equality, the domains'    *)
(* equality and the codomains' at related arguments.                   *)
(*                                                                    *)
(* MEASURED COST, 2026-10-04 (all with `Time`, on this machine):
     - `refine (conj _ (conj _ _))`, i.e. the whole reduction of
       `kceq (liftCode k (pcode ...) W) (pcode (S k) ...)` to eqU's
       three-component conjunction: 0 s.  The head unfolding is FREE.
     - the shadow component: 0 s.
     - the domain component as an explicit term: 0.025 s (as `apply
       liftCode_ceq` + `exact`, 0.4 s).
     - the codomain component as an explicit term: 64 s -- and it does
       TERMINATE, which with `apply`-style tactics it did not (killed at 600 s
       and at 30 min).  `Qed` after it is still over 85 s.
     - the same codomain conjunct supplied as a HYPOTHESIS, so that nothing is
       left to unification: 0 s, with `Qed` at 0.19 s.
   So the cost is neither the head unfolding nor the components themselves: it
   is the UNIFICATION of the arguments this file leaves as `_` (the two node
   triples of `famCeq_all`, and the right-hand well-formedness proof), each of
   which makes the unifier convert `pcB (S k) ...`-shaped terms.  The next
   step is to spell those six node arguments out -- they are exactly what
   `pcB`'s own definition uses -- after which nothing is left to guess.
   Two rules learned the hard way, both recorded in STATUS-v2.md:
     - state a lemma's hypothesis AND conclusion in the vocabulary the
       CALLER's goal prints (`sm_from` of the cone's morphism, `pxc`), and do
       the translation inside the lemma, where it is binder-free and costs
       0.05 s; the same conversion at the application, under the codomain's
       four binders, is what never terminated;
     - prefer one explicit term to a chain of `apply`s: the evars an `apply`
       leaves are instantiated by conversions on these terms, and that is
       where the time goes.

   The codomain's argument needs care: the lifted code reads its        *)
(* codomain at the argument PULLED BACK along the lift (that is point 1 *)
(* of Codes/DESIGN.md §12), while the level-(S k) family reads it at    *)
(* the argument unlifted through `elUnlift`.  The two agree, and        *)
(* `arg_down` below is that agreement: unlifting and changing node      *)
(* commute, because both are coercions and the coherences compose.      *)
(* ------------------------------------------------------------------ *)

(* The unifier must never try to unfold the cone's dispatch: the conversions
   this file needs are all shallow (the `place` identities of Codes/Lift.v),
   while unfolding `morOf`/`datD`/`dat` normalises the rank tree.  Measured:
   with this declaration the codomain component costs 1.9 s and `Qed` 1.5 s;
   without it the same proof took 64 s and `Qed` did not finish in 20 min. *)
Strategy 10000 [ morOf datD datS dat datSucc datSup nodeMorOf presL
                 liftSub liftSubEl unliftSubEl liftS liftSE unliftSE ].

Section LiftComp.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).

  (* ---- the lifted components ---- *)

  Definition liftSB : forall u, kElAt (famLiftK FA) u -> etm :=
    fun u x => SB u (elUnlift FA u x).
  Definition liftFB
    : forall u (x : kElAt (famLiftK FA) u), kUFam (S k) (liftSB u x) :=
    fun u x => famLiftK (FB u (elUnlift FA u x)).
  Definition liftredB : forall u x, reds (eapp B0 u) (liftSB u x) :=
    fun u x => redB u (elUnlift FA u x).

  Lemma liftcohB : forall u x u' x',
    kEqAt (famLiftK FA) u x (famLiftK FA) u' x' ->
    kceq (kAt (liftFB u x)) (kAt (liftFB u' x')).
  Proof.
    intros u x u' x' H; unfold liftFB; apply famLiftK_ceq; apply cohB.
    apply elUnlift_eq; [apply famAtSelf | exact H].
  Qed.

End LiftComp.

Section PiLift.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  Lemma liftgPi : eqty (S k) (epi A0 B0) (epi A0 B0).
  Proof. apply (eqty_cumul k (S k)); [apply Nat.le_succ_diag_r | exact gPi]. Qed.

  (* ---- the argument, read down into the domain family in the two ways the
       two codes read it ---- *)

  Lemma arg_down v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0))
    (wa : wfsub (lU (lvl k)) (lUEq (lvl k)) (lOK (lvl k)) (rk v (hT v fT))
            (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf)
               (pcA k A0 B0 FA v fT pf)))
    u x u' x'
    (H :
      cEl
      (xcmp (kU (S k)) (kUEq (S k)) (kOK (S k)) (rk v (hT v fT))
      (rk v (hT v fT)))
      (sm_map
      (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (rk v (hT v fT))
      (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
      (ltrans (lvl k)) (lrefl (lvl (S k)))
      (lsym (lvl (S k))) (ltrans (lvl (S k)))
      (rk v (hT v fT))))
      (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf) (pcA k A0 B0 FA v fT pf))
      wa)
      u x
      (placeDom (S k) v A0 B0 fT (pEv A0 B0 v fT pf)
      (pcA (S k) A0 B0 (famLiftK FA) v fT pf))
      u' x') :
    kEqAt FA u
    (pxc k A0 B0 FA v fT pf u
    (sm_from
    (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (rk v (hT v fT))
    (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
    (ltrans (lvl k)) (lrefl (lvl (S k)))
    (lsym (lvl (S k))) (ltrans (lvl (S k)))
    (rk v (hT v fT))))
    (placeDom k v A0 B0 fT (pEv A0 B0 v fT pf) (pcA k A0 B0 FA v fT pf))
    wa u x))
    FA u' (elUnlift FA u' (pxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')).
  Proof.
    (* Both the hypothesis and the conclusion are stated in the vocabulary the
       CALLER's goal uses (`sm_from` of the cone's morphism, `pxc`), and the
       translation into the vocabulary this proof works in happens here, where
       it is binder-free and costs a twentieth of a second.  Letting the caller
       do it instead -- i.e. stating this lemma with `unliftEl`/`famTo` and
       converting at the application -- is the same conversion under the
       codomain's four binders, and that does not terminate in any reasonable
       time. *)
    change (kcel (liftCode k (pcA k A0 B0 FA v fT pf) wa) u x
                 (liftCode k (pcA k A0 B0 FA v fT pf)
                    (pwfA k A0 B0 FA v fT pf)) u' x') in H.
    change (kEqAt FA u (famTo FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u
                          (unliftEl k (pcA k A0 B0 FA v fT pf) wa u x))
                  FA u' (elUnlift FA u'
                           (famTo (famLiftK FA) A0 (pAcc A0 B0 v fT pf)
                              (evalAg_refl A0) u' x'))).
    (* the two lifted codes the two elements live at are equal *)
    assert (Hc : kceq (pcA k A0 B0 FA v fT pf) (kAt FA))
      by exact (uf_coh FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0)
                  A0 (kAcc FA) (evalAg_refl A0)).
    (* x' travels to the canonical node, and back down into the lifted code
       there: that is what elUnlift reads it at *)
    assert (Hxz : kcel (liftCode k (pcA k A0 B0 FA v fT pf) wa) u x
                    (liftCode k (kAt FA) (famAtWf FA)) u'
                    (famFrom (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0) u'
                       (famTo (famLiftK FA) A0 (pAcc A0 B0 v fT pf)
                          (evalAg_refl A0) u' x'))).
    { eapply ktrE;
        [ exact (liftCode_wf k _ wa)
        | exact (liftCode_wf k _ (pwfA k A0 B0 FA v fT pf))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (liftCode_ceq k _ _ wa (pwfA k A0 B0 FA v fT pf)
                   (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _))
        | exact H |].
      eapply ktrE;
        [ exact (liftCode_wf k _ (pwfA k A0 B0 FA v fT pf))
        | exact (famAtWf (famLiftK FA))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (uf_coh (famLiftK FA) A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0)
                   A0 (kAcc (famLiftK FA)) (evalAg_refl A0))
        | exact (famTo_coh (famLiftK FA) A0 (pAcc A0 B0 v fT pf)
                   (evalAg_refl A0) u' x')
        | exact (famFrom_coh (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0)
                   u' _) ]. }
    (* so their unlifts are related, at the two codes of FA *)
    pose proof (unliftEl_cel k (pcA k A0 B0 FA v fT pf) (kAt FA) wa (famAtWf FA)
                  Hc u x u' _ Hxz) as Hdown.
    (* and the first one's move to the canonical node is its own coherence *)
    eapply ktrE;
      [ exact (famAtWf FA)
      | exact (famWf FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famAtWf FA)
      | apply knsymU; exact Hc
      | apply knsym;
        exact (famTo_coh FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u _)
      | exact Hdown ].
  Qed.

  (* ---- the two codes at one node ---- *)

  Lemma pcode_lift v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) :
    kceq (liftCode k (pcode k A0 B0 FA SB FB redB v fT pf)
            (pcode_wf k A0 B0 FA SB FB redB cohB gPi v fT pf))
         (pcode (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB) v fT pf).
  Proof.
    generalize (pcode_wf k A0 B0 FA SB FB redB cohB gPi v fT pf) as W; intros W.
    destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    Time refine (conj _ (conj _ _)).
    - Time (exists k; exact (eqty_refl_l k v (epi A0 B0)
                               (pcode_sh k A0 B0 gPi v fT pf))).
    - Time exact (liftCode_ceq k (pcA k A0 B0 FA v fT pf)
                    (pcA k A0 B0 FA v fT pf) wa (pwfA k A0 B0 FA v fT pf)
                    (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _)).
    - Time intros u x u' x' H.
      Time exact (liftCode_ceq k _ _
                    (wb u (unliftEl k (pcA k A0 B0 FA v fT pf) wa u x)) _
                    (famCeq_all
                       (FB u (pxc k A0 B0 FA v fT pf u
                                (unliftEl k (pcA k A0 B0 FA v fT pf) wa u x)))
                       (FB u' (elUnlift FA u'
                                 (pxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')))
                       (cohB _ _ _ _ (arg_down v fT pf wa u x u' x' H))
                       _ _ _ _ _ _)).
  Time Qed.

  Lemma famLiftK_piFam :
    kceq (kAt (famLiftK (piFam k A0 B0 FA SB FB redB cohB gPi)))
         (kAt (piFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                 (liftcohB k A0 FA SB FB cohB) liftgPi)).
  Proof.
    assert (Hn : forall v (h : Acc prec v) (pf : evalAg v (epi A0 B0)),
               kceq (uf_c (famLiftK (piFam k A0 B0 FA SB FB redB cohB gPi)) v h pf)
                    (uf_c (piFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                             (liftcohB k A0 FA SB FB cohB) liftgPi) v h pf)).
    { intros v h pf; destruct h as [fT]; exact (pcode_lift v fT pf). }
    exact (famCeq_of _ _ (epi A0 B0)
             (kAcc (piFam k A0 B0 FA SB FB redB cohB gPi)) (evalAg_refl (epi A0 B0))
             (epi A0 B0)
             (kAcc (piFam k A0 B0 FA SB FB redB cohB gPi)) (evalAg_refl (epi A0 B0))
             (Hn _ _ _)).
  Qed.
End PiLift.

Section SigLift.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gSig : eqty k (esig A0 B0) (esig A0 B0)).

  Lemma liftgSig : eqty (S k) (esig A0 B0) (esig A0 B0).
  Proof. apply (eqty_cumul k (S k)); [apply Nat.le_succ_diag_r | exact gSig]. Qed.

  (* ---- the argument, read down into the domain family in the two ways the
       two codes read it ---- *)

  Lemma arg_down_sig v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0))
    (wa : wfsub (lU (lvl k)) (lUEq (lvl k)) (lOK (lvl k)) (rk v (hT v fT))
            (placeSDom k v A0 B0 fT (sEv A0 B0 v fT pf)
               (scA k A0 B0 FA v fT pf)))
    u x u' x'
    (H :
      cEl
      (xcmp (kU (S k)) (kUEq (S k)) (kOK (S k)) (rk v (hT v fT))
      (rk v (hT v fT)))
      (sm_map
      (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (rk v (hT v fT))
      (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
      (ltrans (lvl k)) (lrefl (lvl (S k)))
      (lsym (lvl (S k))) (ltrans (lvl (S k)))
      (rk v (hT v fT))))
      (placeSDom k v A0 B0 fT (sEv A0 B0 v fT pf) (scA k A0 B0 FA v fT pf))
      wa)
      u x
      (placeSDom (S k) v A0 B0 fT (sEv A0 B0 v fT pf)
      (scA (S k) A0 B0 (famLiftK FA) v fT pf))
      u' x') :
    kEqAt FA u
    (sxc k A0 B0 FA v fT pf u
    (sm_from
    (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (rk v (hT v fT))
    (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
    (ltrans (lvl k)) (lrefl (lvl (S k)))
    (lsym (lvl (S k))) (ltrans (lvl (S k)))
    (rk v (hT v fT))))
    (placeSDom k v A0 B0 fT (sEv A0 B0 v fT pf) (scA k A0 B0 FA v fT pf))
    wa u x))
    FA u' (elUnlift FA u' (sxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')).
  Proof.
    (* Both the hypothesis and the conclusion are stated in the vocabulary the
       CALLER's goal uses (`sm_from` of the cone's morphism, `sxc`), and the
       translation into the vocabulary this proof works in happens here, where
       it is binder-free and costs a twentieth of a second.  Letting the caller
       do it instead -- i.e. stating this lemma with `unliftEl`/`famTo` and
       converting at the application -- is the same conversion under the
       codomain's four binders, and that does not terminate in any reasonable
       time. *)
    change (kcel (liftCode k (scA k A0 B0 FA v fT pf) wa) u x
                 (liftCode k (scA k A0 B0 FA v fT pf)
                    (swfA k A0 B0 FA v fT pf)) u' x') in H.
    change (kEqAt FA u (famTo FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) u
                          (unliftEl k (scA k A0 B0 FA v fT pf) wa u x))
                  FA u' (elUnlift FA u'
                           (famTo (famLiftK FA) A0 (sAcc A0 B0 v fT pf)
                              (evalAg_refl A0) u' x'))).
    (* the two lifted codes the two elements live at are equal *)
    assert (Hc : kceq (scA k A0 B0 FA v fT pf) (kAt FA))
      by exact (uf_coh FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0)
                  A0 (kAcc FA) (evalAg_refl A0)).
    (* x' travels to the canonical node, and back down into the lifted code
       there: that is what elUnlift reads it at *)
    assert (Hxz : kcel (liftCode k (scA k A0 B0 FA v fT pf) wa) u x
                    (liftCode k (kAt FA) (famAtWf FA)) u'
                    (famFrom (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0) u'
                       (famTo (famLiftK FA) A0 (sAcc A0 B0 v fT pf)
                          (evalAg_refl A0) u' x'))).
    { eapply ktrE;
        [ exact (liftCode_wf k _ wa)
        | exact (liftCode_wf k _ (swfA k A0 B0 FA v fT pf))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (liftCode_ceq k _ _ wa (swfA k A0 B0 FA v fT pf)
                   (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _))
        | exact H |].
      eapply ktrE;
        [ exact (liftCode_wf k _ (swfA k A0 B0 FA v fT pf))
        | exact (famAtWf (famLiftK FA))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (uf_coh (famLiftK FA) A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0)
                   A0 (kAcc (famLiftK FA)) (evalAg_refl A0))
        | exact (famTo_coh (famLiftK FA) A0 (sAcc A0 B0 v fT pf)
                   (evalAg_refl A0) u' x')
        | exact (famFrom_coh (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0)
                   u' _) ]. }
    (* so their unlifts are related, at the two codes of FA *)
    pose proof (unliftEl_cel k (scA k A0 B0 FA v fT pf) (kAt FA) wa (famAtWf FA)
                  Hc u x u' _ Hxz) as Hdown.
    (* and the first one's move to the canonical node is its own coherence *)
    eapply ktrE;
      [ exact (famAtWf FA)
      | exact (famWf FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famAtWf FA)
      | apply knsymU; exact Hc
      | apply knsym;
        exact (famTo_coh FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) u _)
      | exact Hdown ].
  Qed.

  (* ---- the two codes at one node ---- *)

  Lemma scode_lift v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) :
    kceq (liftCode k (scode k A0 B0 FA SB FB redB v fT pf)
            (scode_wf k A0 B0 FA SB FB redB cohB gSig v fT pf))
         (scode (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB) v fT pf).
  Proof.
    generalize (scode_wf k A0 B0 FA SB FB redB cohB gSig v fT pf) as W; intros W.
    destruct W as [[wa [wb wcoh]] [ety [eaa coh]]].
    Time refine (conj _ (conj _ _)).
    - Time (exists k; exact (eqty_refl_l k v (esig A0 B0)
                               (scode_sh k A0 B0 gSig v fT pf))).
    - Time exact (liftCode_ceq k (scA k A0 B0 FA v fT pf)
                    (scA k A0 B0 FA v fT pf) wa (swfA k A0 B0 FA v fT pf)
                    (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _)).
    - Time intros u x u' x' H.
      Time exact (liftCode_ceq k _ _
                    (wb u (unliftEl k (scA k A0 B0 FA v fT pf) wa u x)) _
                    (famCeq_all
                       (FB u (sxc k A0 B0 FA v fT pf u
                                (unliftEl k (scA k A0 B0 FA v fT pf) wa u x)))
                       (FB u' (elUnlift FA u'
                                 (sxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')))
                       (cohB _ _ _ _ (arg_down_sig v fT pf wa u x u' x' H))
                       _ _ _ _ _ _)).
  Time Qed.

  Lemma famLiftK_sigFam :
    kceq (kAt (famLiftK (sigFam k A0 B0 FA SB FB redB cohB gSig)))
         (kAt (sigFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                 (liftcohB k A0 FA SB FB cohB) liftgSig)).
  Proof.
    assert (Hn : forall v (h : Acc prec v) (pf : evalAg v (esig A0 B0)),
               kceq (uf_c (famLiftK (sigFam k A0 B0 FA SB FB redB cohB gSig)) v h pf)
                    (uf_c (sigFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                             (liftcohB k A0 FA SB FB cohB) liftgSig) v h pf)).
    { intros v h pf; destruct h as [fT]; exact (scode_lift v fT pf). }
    exact (famCeq_of _ _ (esig A0 B0)
             (kAcc (sigFam k A0 B0 FA SB FB redB cohB gSig)) (evalAg_refl (esig A0 B0))
             (esig A0 B0)
             (kAcc (sigFam k A0 B0 FA SB FB redB cohB gSig)) (evalAg_refl (esig A0 B0))
             (Hn _ _ _)).
  Qed.
End SigLift.

Section WLift.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gW : eqty k (ew A0 B0) (ew A0 B0)).

  Lemma liftgW : eqty (S k) (ew A0 B0) (ew A0 B0).
  Proof. apply (eqty_cumul k (S k)); [apply Nat.le_succ_diag_r | exact gW]. Qed.

  (* ---- the argument, read down into the domain family in the two ways the
       two codes read it ---- *)

  Lemma arg_down_w v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0))
    (wa : wfsub (lU (lvl k)) (lUEq (lvl k)) (lOK (lvl k)) (rk v (hT v fT))
            (placeWDom k v A0 B0 fT (wEv A0 B0 v fT pf)
               (wcA k A0 B0 FA v fT pf)))
    u x u' x'
    (H :
      cEl
      (xcmp (kU (S k)) (kUEq (S k)) (kOK (S k)) (rk v (hT v fT))
      (rk v (hT v fT)))
      (sm_map
      (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (rk v (hT v fT))
      (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
      (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
      (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
      (ltrans (lvl k)) (lrefl (lvl (S k)))
      (lsym (lvl (S k))) (ltrans (lvl (S k)))
      (rk v (hT v fT))))
      (placeWDom k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf))
      wa)
      u x
      (placeWDom (S k) v A0 B0 fT (wEv A0 B0 v fT pf)
      (wcA (S k) A0 B0 (famLiftK FA) v fT pf))
      u' x') :
    kEqAt FA u
    (wxc k A0 B0 FA v fT pf u
    (sm_from
    (morOf (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (rk v (hT v fT))
    (datD (lU (lvl k)) (lU (lvl (S k))) (lUEq (lvl k))
    (lUEq (lvl (S k))) (lOK (lvl k)) (lOK (lvl (S k)))
    (lvlUM k) (lrefl (lvl k)) (lsym (lvl k))
    (ltrans (lvl k)) (lrefl (lvl (S k)))
    (lsym (lvl (S k))) (ltrans (lvl (S k)))
    (rk v (hT v fT))))
    (placeWDom k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf))
    wa u x))
    FA u' (elUnlift FA u' (wxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')).
  Proof.
    (* Both the hypothesis and the conclusion are stated in the vocabulary the
       CALLER's goal uses (`sm_from` of the cone's morphism, `wxc`), and the
       translation into the vocabulary this proof works in happens here, where
       it is binder-free and costs a twentieth of a second.  Letting the caller
       do it instead -- i.e. stating this lemma with `unliftEl`/`famTo` and
       converting at the application -- is the same conversion under the
       codomain's four binders, and that does not terminate in any reasonable
       time. *)
    change (kcel (liftCode k (wcA k A0 B0 FA v fT pf) wa) u x
                 (liftCode k (wcA k A0 B0 FA v fT pf)
                    (wwfA k A0 B0 FA v fT pf)) u' x') in H.
    change (kEqAt FA u (famTo FA A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0) u
                          (unliftEl k (wcA k A0 B0 FA v fT pf) wa u x))
                  FA u' (elUnlift FA u'
                           (famTo (famLiftK FA) A0 (wAccA A0 B0 v fT pf)
                              (evalAg_refl A0) u' x'))).
    (* the two lifted codes the two elements live at are equal *)
    assert (Hc : kceq (wcA k A0 B0 FA v fT pf) (kAt FA))
      by exact (uf_coh FA A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0)
                  A0 (kAcc FA) (evalAg_refl A0)).
    (* x' travels to the canonical node, and back down into the lifted code
       there: that is what elUnlift reads it at *)
    assert (Hxz : kcel (liftCode k (wcA k A0 B0 FA v fT pf) wa) u x
                    (liftCode k (kAt FA) (famAtWf FA)) u'
                    (famFrom (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0) u'
                       (famTo (famLiftK FA) A0 (wAccA A0 B0 v fT pf)
                          (evalAg_refl A0) u' x'))).
    { eapply ktrE;
        [ exact (liftCode_wf k _ wa)
        | exact (liftCode_wf k _ (wwfA k A0 B0 FA v fT pf))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (liftCode_ceq k _ _ wa (wwfA k A0 B0 FA v fT pf)
                   (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _))
        | exact H |].
      eapply ktrE;
        [ exact (liftCode_wf k _ (wwfA k A0 B0 FA v fT pf))
        | exact (famAtWf (famLiftK FA))
        | exact (liftCode_wf k _ (famAtWf FA))
        | exact (uf_coh (famLiftK FA) A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0)
                   A0 (kAcc (famLiftK FA)) (evalAg_refl A0))
        | exact (famTo_coh (famLiftK FA) A0 (wAccA A0 B0 v fT pf)
                   (evalAg_refl A0) u' x')
        | exact (famFrom_coh (famLiftK FA) A0 (kAcc FA) (evalAg_refl A0)
                   u' _) ]. }
    (* so their unlifts are related, at the two codes of FA *)
    pose proof (unliftEl_cel k (wcA k A0 B0 FA v fT pf) (kAt FA) wa (famAtWf FA)
                  Hc u x u' _ Hxz) as Hdown.
    (* and the first one's move to the canonical node is its own coherence *)
    eapply ktrE;
      [ exact (famAtWf FA)
      | exact (famWf FA A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famAtWf FA)
      | apply knsymU; exact Hc
      | apply knsym;
        exact (famTo_coh FA A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0) u _)
      | exact Hdown ].
  Qed.

  (* ---- the two codes at one node ---- *)

  Lemma wcode_lift v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) :
    kceq (liftCode k (wcode k A0 B0 FA SB FB redB v fT pf)
            (wcode_wf k A0 B0 FA SB FB redB cohB gW v fT pf))
         (wcode (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB) v fT pf).
  Proof.
    generalize (wcode_wf k A0 B0 FA SB FB redB cohB gW v fT pf) as W; intros W.
    destruct W as [[wa [wb [aeqc beqc]]] [ety [eaa coh]]].
    Time refine (conj _ (conj _ _)).
    - Time (exists k; exact (eqty_refl_l k v (ew A0 B0)
                               (wcode_sh k A0 B0 gW v fT pf))).
    - Time exact (liftCode_ceq k (wcA k A0 B0 FA v fT pf)
                    (wcA k A0 B0 FA v fT pf) wa (wwfA k A0 B0 FA v fT pf)
                    (famCeq_all FA FA (famAtSelf FA) _ _ _ _ _ _)).
    - Time intros u x u' x' H.
      Time exact (liftCode_ceq k _ _
                    (wb u (unliftEl k (wcA k A0 B0 FA v fT pf) wa u x)) _
                    (famCeq_all
                       (FB u (wxc k A0 B0 FA v fT pf u
                                (unliftEl k (wcA k A0 B0 FA v fT pf) wa u x)))
                       (FB u' (elUnlift FA u'
                                 (wxc (S k) A0 B0 (famLiftK FA) v fT pf u' x')))
                       (cohB _ _ _ _ (arg_down_w v fT pf wa u x u' x' H))
                       _ _ _ _ _ _)).
  Time Qed.

  Lemma famLiftK_wFam :
    kceq (kAt (famLiftK (wFam k A0 B0 FA SB FB redB cohB gW)))
         (kAt (wFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                 (liftcohB k A0 FA SB FB cohB) liftgW)).
  Proof.
    assert (Hn : forall v (h : Acc prec v) (pf : evalAg v (ew A0 B0)),
               kceq (uf_c (famLiftK (wFam k A0 B0 FA SB FB redB cohB gW)) v h pf)
                    (uf_c (wFam (S k) A0 B0 (famLiftK FA) (liftSB k A0 FA SB) (liftFB k A0 FA SB FB) (liftredB k A0 B0 FA SB redB)
                             (liftcohB k A0 FA SB FB cohB) liftgW) v h pf)).
    { intros v h pf; destruct h as [fT]; exact (wcode_lift v fT pf). }
    exact (famCeq_of _ _ (ew A0 B0)
             (kAcc (wFam k A0 B0 FA SB FB redB cohB gW)) (evalAg_refl (ew A0 B0))
             (ew A0 B0)
             (kAcc (wFam k A0 B0 FA SB FB redB cohB gW)) (evalAg_refl (ew A0 B0))
             (Hn _ _ _)).
  Qed.
End WLift.


(* ------------------------------------------------------------------ *)
(* The lift against `upF`: one more lift of a component presented at a *)
(* former's annotation is the same component presented at the next      *)
(* annotation, with its gap one bigger.  Both sides are the same        *)
(* iterated lift under two level casts, so the equations come out by    *)
(* elimination.                                                        *)
(* ------------------------------------------------------------------ *)

Lemma famLiftK_upF {i u} (d k : nat) (E : d + i = k) (E' : S d + i = S k)
  (F : kUFam i u) :
  kceq (kAt (famLiftK (upF d k E F))) (kAt (upF (S d) (S k) E' F)).
Proof.
  revert E'; destruct E; intros E'.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec E' eq_refl).
  unfold upF; rewrite !lvlCast_refl.
  apply famAtSelf.
Qed.

(* ------------------------------------------------------------------ *)
(* The gap bookkeeping the up-rules need.                              *)
(*                                                                    *)
(* A component read at level i appears in `pi kk A B` through the gap   *)
(* `kk - i` and in `pi (S kk) A B` through `S kk - i`, and the lift     *)
(* takes the first presentation to the second.  On ELEMENTS: unlifting  *)
(* once (out of the lift) and then down the gap is unlifting down the    *)
(* bigger gap -- definitionally, once the two gap equations are         *)
(* eliminated, because `elUnliftN (S d)` IS `elUnliftN d` after one      *)
(* `elUnlift`.                                                         *)
(* ------------------------------------------------------------------ *)

Lemma dnEl_famLiftK {i u u'} (d k : nat) (E : d + i = k) (E' : S d + i = S k)
  (F : kUFam i u) (F' : kUFam i u') (Q : kceq (kAt F) (kAt F'))
  w (x : kElAt (famLiftK (upF d k E F)) w)
  w' (x' : kElAt (upF (S d) (S k) E' F') w')
  (H : kEqAt (famLiftK (upF d k E F)) w x (upF (S d) (S k) E' F') w' x') :
  kEqAt F w (dnEl d k E F w (elUnlift (upF d k E F) w x))
        F' w' (dnEl (S d) (S k) E' F' w' x').
Proof.
  revert x x' H; destruct E.
  rewrite (Eqdep_dec.UIP_dec Nat.eq_dec E' eq_refl).
  intros x x' H.
  exact (elUnliftN_eq (S d) F w x F' w' x' Q H).
Qed.
