From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.SigFam
  Interp.Univ Interp.Env Interp.Elem Interp.PiEl.
From Stdlib Require Import Arith Lia.

(* The elements of a Sigma-family: the two projections, the pair, and the laws
   the conversion rules for Sigma need.

   A Sigma-code's decoding is a dependent PAIR over the elements of the DOMAIN
   CODE at the node the Sigma-code lives at, whereas the interpretation has
   elements of the domain FAMILY, so -- as at Pi -- the components travel
   through famTo/famFrom.  The difference from Pi is that the realisers move
   too: the first component's realiser is `efst u` and the second's `esnd u`,
   and at a pair those only REDUCE to the components' own realisers, so the
   expansion closure of the decoding (Interp/Elem.v) does the work that the
   argument round trip does at Pi.

   This was v1's most expensive file by far (~500s to type-check, against
   under three seconds here).  The reason is the one DESIGN.md sec. 11
   predicted: v1's laws had to unfold the canonical TRANSPORT at a Sigma code
   and reconcile two composites of transports, and the terms being compared
   mention the Brouwer tree `rk` produces.  In v2 no law unfolds a coercion:
   each is a chain of `xto_coh` and transitivity, and `xto` is sealed. *)

(* PERFORMANCE.  This file is v1's most expensive by far -- ~500s there
   against ~14s here -- and what remains of the cost is all in the
   transitivity chains below: `kcel` at a component's code has to be unified
   with `ktrE`'s conclusion, and a component's code carries Brouwer ordinals
   built from `rk`.  Two rules keep that bounded, and both matter:

   - the COERCION is sealed (Interp/Codes.v), so no chain ever looks inside
     one -- this is what made v1's `sigFst_to`/`sigSnd_to` expensive;
   - every step is a named lemma whose statement already mentions the code
     (`scB_at`, `sSnd_coh`, `sPair_snd_rel`), so the unifier is never asked to
     discover that a component's code IS an instance of a family.

   Sealing the component projections themselves (`Opaque scA scB sxc`) does
   NOT work: the chains need `scB` to unfold to `uf_c (FB ...) ...`. *)

(* The two reductions a pair's realisers make. *)
Lemma reds_fst_pair t u : reds (efst (epair t u)) t.
Proof. eapply reds_step; [apply red_fst | apply reds_refl]. Qed.

Lemma reds_snd_pair t u : reds (esnd (epair t u)) u.
Proof. eapply reds_step; [apply red_snd | apply reds_refl]. Qed.

Section SigEl.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gSig : eqty k (esig A0 B0) (esig A0 B0)).

  Local Notation SF := (sigFam k A0 B0 FA SB FB redB cohB gSig).
  Local Notation SC v fT pf := (scode k A0 B0 FA SB FB redB v fT pf).

  (* ---- the projections at one instance ---- *)

  Definition sFst v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    u (x : kElC (SC v fT pf) u) : kElAt FA (efst u) :=
    sxc k A0 B0 FA v fT pf (efst u) (projT1 (Datatypes.fst x)).

  Definition sSnd v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    u (x : kElC (SC v fT pf) u) : kElAt (FB (efst u) (sFst v fT pf u x)) (esnd u) :=
    famTo (FB (efst u) (sFst v fT pf u x)) (eapp B0 (efst u)) _ _ (esnd u)
      (projT2 (Datatypes.fst x)).

  (* the raw second component is related to the one sSnd returns *)
  Lemma sSnd_coh v fT pf u (x : kElC (SC v fT pf) u) :
    kcel (scB k A0 B0 FA SB FB redB v fT pf (efst u) (projT1 (Datatypes.fst x)))
         (esnd u) (projT2 (Datatypes.fst x))
         (kAt (FB (efst u) (sFst v fT pf u x))) (esnd u) (sSnd v fT pf u x).
  Proof. apply famTo_coh. Qed.

  (* ---- the pair at one instance ---- *)

  Definition sPairFst v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) wa wb (x : kElAt FA wa)
    : kElC (scA k A0 B0 FA v fT pf) (efst (epair wa wb)) :=
    cExp (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k) (lexp (lvl k))
      (scA k A0 B0 FA v fT pf) (swfA k A0 B0 FA v fT pf)
      (efst (epair wa wb)) wa (reds_fst_pair wa wb)
      (famFrom FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) wa x).

  Lemma sPairFst_rel v fT pf wa wb (x : kElAt FA wa) :
    kEqAt FA (efst (epair wa wb))
      (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) (sPairFst v fT pf wa wb x))
      FA wa x.
  Proof.
    eapply ktrE;
      [ exact (famAtWf FA) | exact (famWf FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famAtWf FA)
      | apply knsymU; exact (uf_coh FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0)
                               A0 (kAcc FA) (evalAg_refl A0))
      | apply knsym; exact (famTo_coh FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0)
                              (efst (epair wa wb)) (sPairFst v fT pf wa wb x)) |].
    eapply ktrE;
      [ exact (famWf FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famWf FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0))
      | exact (famAtWf FA)
      | exact (proj2 (famWf FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0)))
      | exact (cExp_rel (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k)
                 (lexp (lvl k)) (scA k A0 B0 FA v fT pf) (swfA k A0 B0 FA v fT pf)
                 (efst (epair wa wb)) wa (reds_fst_pair wa wb)
                 (famFrom FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) wa x))
      | apply knsym;
        exact (famFrom_coh FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) wa x) ].
  Qed.

  Definition sPair v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb)
    (g : Good v (epair wa wb)) : kElC (SC v fT pf) (epair wa wb) :=
    (existT _ (sPairFst v fT pf wa wb x)
       (famFrom (FB (efst (epair wa wb))
                    (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                       (sPairFst v fT pf wa wb x)))
          (eapp B0 (efst (epair wa wb))) _ _ (esnd (epair wa wb))
          (famExp _ (esnd (epair wa wb)) wb (reds_snd_pair wa wb)
             (kto (kAt (FB wa x))
                (kAt (FB (efst (epair wa wb))
                         (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                            (sPairFst v fT pf wa wb x))))
                (famAtWf (FB wa x))
                (famAtWf (FB (efst (epair wa wb))
                             (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                                (sPairFst v fT pf wa wb x))))
                (cohB wa x (efst (epair wa wb))
                   (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                      (sPairFst v fT pf wa wb x))
                   (kEqAt_sym FA (efst (epair wa wb)) _ FA wa x
                      (sPairFst_rel v fT pf wa wb x)))
                wb y))), g).

  (* ---- and at the canonical instance, which is what the interpretation
     uses.  The two projections are packed into one definition so that a
     single destruction of the accessibility proof serves both: sigSnd's TYPE
     mentions sigFst. ---- *)

  Definition sigEl u (x : kElAt SF u)
    : { z : kElAt FA (efst u) & kElAt (FB (efst u) z) (esnd u) }.
  Proof.
    revert x; unfold kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x.
    exact (existT _ (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)
                    (sSnd (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)).
  Defined.

  Definition sigFst u (x : kElAt SF u) : kElAt FA (efst u) := projT1 (sigEl u x).

  Definition sigSnd u (x : kElAt SF u) : kElAt (FB (efst u) (sigFst u x)) (esnd u) :=
    projT2 (sigEl u x).

  Definition sigPair wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb)
    (g : Good (esig A0 B0) (epair wa wb)) : kElAt SF (epair wa wb).
  Proof.
    unfold kElAt, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT].
    exact (sPair (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x y g).
  Defined.

  Lemma sigGood u (x : kElAt SF u) : Good (esig A0 B0) u.
  Proof.
    revert x; unfold kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x.
    exact (Datatypes.snd x).
  Qed.

  (* The pair's second component is related to the component it was built
     from: out of famFrom, out of the expansion, out of the coercion.  This is
     v1's `sPair_snd_het`, and it is what makes the two remaining laws short. *)
  Lemma sPair_snd_rel v fT pf wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb)
    (g : Good v (epair wa wb)) :
    kcel (scB k A0 B0 FA SB FB redB v fT pf (efst (epair wa wb))
            (sPairFst v fT pf wa wb x))
         (esnd (epair wa wb))
         (projT2 (Datatypes.fst (sPair v fT pf wa wb x y g)))
         (kAt (FB wa x)) wb y.
  Proof.
    set (p1 := sPairFst v fT pf wa wb x).
    set (C1 := kAt (FB (efst (epair wa wb))
                       (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) p1))).
    eapply ktrE;
      [ exact (swfB k A0 B0 FA SB FB redB v fT pf (efst (epair wa wb)) p1)
      | exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB wa x))
      | exact (scB_at k A0 B0 FA SB FB redB v fT pf (efst (epair wa wb)) p1)
      | apply knsym; apply famFrom_coh |].
    eapply ktrE;
      [ exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB wa x))
      | exact (famAtSelf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) p1)))
      | apply famExp_rel
      | apply knsym; apply kto_coh ].
  Qed.

  (* ---- the two projections respect the equality ---- *)

  Lemma sigFst_eq u (x : kElAt SF u) u' (x' : kElAt SF u') :
    kEqAt SF u x SF u' x' ->
    kEqAt FA (efst u) (sigFst u x) FA (efst u') (sigFst u' x').
  Proof.
    revert x x'; unfold sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x x' H.
    apply (famTo_eq FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (evalAg_refl A0)).
    exact (proj1 H).
  Qed.

  Lemma sigSnd_eq u (x : kElAt SF u) u' (x' : kElAt SF u') :
    kEqAt SF u x SF u' x' ->
    kRel (FB (efst u) (sigFst u x)) (esnd u) (sigSnd u x)
         (FB (efst u') (sigFst u' x')) (esnd u') (sigSnd u' x').
  Proof.
    intros H0; split; [exact (cohB _ _ _ _ (sigFst_eq u x u' x' H0)) |].
    revert H0; revert x x';
      unfold sigSnd, sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x x' H.
    set (pf := evalAg_refl (esig A0 B0)).
    set (z := projT1 (Datatypes.fst x)).
    set (z' := projT1 (Datatypes.fst x')).
    eapply ktrE;
      [ exact (famAtWf (FB (efst u) (sFst (esig A0 B0) fT pf u x)))
      | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | exact (famAtWf (FB (efst u') (sFst (esig A0 B0) fT pf u' x')))
      | apply knsymU; exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | apply knsym; exact (sSnd_coh (esig A0 B0) fT pf u x) |].
    eapply ktrE;
      [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u') z')
      | exact (famAtWf (FB (efst u') (sFst (esig A0 B0) fT pf u' x')))
      | exact (scohB k A0 B0 FA SB FB redB cohB (esig A0 B0) fT pf
                 (efst u) z (efst u') z' (proj1 H))
      | exact (proj1 (proj2 H))
      | exact (sSnd_coh (esig A0 B0) fT pf u' x') ].
  Qed.

  (* ---- the two beta laws: the projections of a pair are its components ---- *)

  Lemma sigFst_pair wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) g :
    kEqAt FA (efst (epair wa wb)) (sigFst (epair wa wb) (sigPair wa wb x y g)) FA wa x.
  Proof.
    unfold sigFst, sigEl, sigPair, kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT].
    apply sPairFst_rel.
  Qed.

  Lemma sigSnd_pair wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) g :
    kRel (FB (efst (epair wa wb)) (sigFst (epair wa wb) (sigPair wa wb x y g)))
         (esnd (epair wa wb)) (sigSnd (epair wa wb) (sigPair wa wb x y g))
         (FB wa x) wb y.
  Proof.
    split; [exact (cohB _ _ _ _ (sigFst_pair wa wb x y g)) |].
    revert g; unfold sigSnd, sigFst, sigEl, sigPair, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros g.
    set (pf := evalAg_refl (esig A0 B0)).
    set (p1 := sPairFst (esig A0 B0) fT pf wa wb x).
    set (C1 := kAt (FB (efst (epair wa wb))
                       (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1))).
    (* out of famTo, out of famFrom, out of the expansion, out of the coercion *)
    eapply ktrE;
      [ exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1)))
      | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa wb)) p1)
      | exact (famAtWf (FB wa x))
      | apply knsymU;
        exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa wb)) p1)
      | apply knsym; apply famTo_coh |].
    eapply ktrE;
      [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa wb)) p1)
      | exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB wa x))
      | exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa wb)) p1)
      | apply knsym; apply famFrom_coh |].
    eapply ktrE;
      [ exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1)))
      | exact (famAtWf (FB wa x))
      | exact (famAtSelf (FB (efst (epair wa wb))
                 (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb)) p1)))
      | apply famExp_rel
      | apply knsym; apply kto_coh ].
  Qed.

  (* ---- surjective pairing, and the congruence for pairs ---- *)

  (* Rebuilding an element from its projections gives one RELATED to it.  The
     two side conditions -- that the pair of the projections realises the type
     and is related to the subject -- come from Layer1/Elim.v's
     Rel_sig_intro/elim, so they are hypotheses. *)
  Lemma sigPair_surj u (x : kElAt SF u)
    (g : Good (esig A0 B0) (epair (efst u) (esnd u)))
    (gr : Rel (esig A0 B0) (epair (efst u) (esnd u)) u) :
    kEqAt SF (epair (efst u) (esnd u))
      (sigPair (efst u) (esnd u) (sigFst u x) (sigSnd u x) g) SF u x.
  Proof.
    revert g; revert x.
    unfold sigPair, sigFst, sigSnd, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x g.
    set (pf := evalAg_refl (esig A0 B0)).
    set (z := projT1 (Datatypes.fst x)).
    split.
    - (* first components *)
      eapply ktrE;
        [ exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (proj2 (swfA k A0 B0 FA (esig A0 B0) fT pf))
        | exact (cExp_rel (kU k) (kUEq k) (kOK k) (krefl k) (ksym k) (ktrans k)
                   (lexp (lvl k)) (scA k A0 B0 FA (esig A0 B0) fT pf)
                   (swfA k A0 B0 FA (esig A0 B0) fT pf)
                   (efst (epair (efst u) (esnd u))) (efst u)
                   (reds_fst_pair (efst u) (esnd u))
                   (famFrom FA A0 (sAcc A0 B0 (esig A0 B0) fT pf) (evalAg_refl A0)
                      (efst u) (sFst (esig A0 B0) fT pf u x)))
        | exact (famFrom_famTo FA A0 (sAcc A0 B0 (esig A0 B0) fT pf)
                   (evalAg_refl A0) (efst u) z) ].
    - split; [| split; [exists k; exact gSig | exact gr]].
      (* second components *)
      eapply ktrE;
        [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf
                   (efst (epair (efst u) (esnd u)))
                   (sPairFst (esig A0 B0) fT pf (efst u) (esnd u)
                      (sFst (esig A0 B0) fT pf u x)))
        | exact (famAtWf (FB (efst u) (sFst (esig A0 B0) fT pf u x)))
        | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
        | eapply ktrU;
            [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf
                       (efst (epair (efst u) (esnd u)))
                       (sPairFst (esig A0 B0) fT pf (efst u) (esnd u)
                          (sFst (esig A0 B0) fT pf u x)))
            | exact (famAtWf (FB (efst (epair (efst u) (esnd u)))
                       (sxc k A0 B0 FA (esig A0 B0) fT pf
                          (efst (epair (efst u) (esnd u)))
                          (sPairFst (esig A0 B0) fT pf (efst u) (esnd u)
                             (sFst (esig A0 B0) fT pf u x)))))
            | exact (famAtWf (FB (efst u) (sFst (esig A0 B0) fT pf u x)))
            | exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf
                       (efst (epair (efst u) (esnd u)))
                       (sPairFst (esig A0 B0) fT pf (efst u) (esnd u)
                          (sFst (esig A0 B0) fT pf u x)))
            | apply cohB;
              exact (sPairFst_rel (esig A0 B0) fT pf (efst u) (esnd u)
                       (sFst (esig A0 B0) fT pf u x)) ]
        | exact (sPair_snd_rel (esig A0 B0) fT pf (efst u) (esnd u)
                   (sFst (esig A0 B0) fT pf u x) (sSnd (esig A0 B0) fT pf u x) g)
        | apply knsym; exact (sSnd_coh (esig A0 B0) fT pf u x) ].
  Qed.

  (* congruence: pairs of related components are related *)
  Lemma sigPair_eq wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb)
    (g : Good (esig A0 B0) (epair wa wb))
    wa' wb' (x' : kElAt FA wa') (y' : kElAt (FB wa' x') wb')
    (g' : Good (esig A0 B0) (epair wa' wb')) :
    Rel (esig A0 B0) (epair wa wb) (epair wa' wb') ->
    kEqAt FA wa x FA wa' x' -> kRel (FB wa x) wb y (FB wa' x') wb' y' ->
    kEqAt SF (epair wa wb) (sigPair wa wb x y g)
          SF (epair wa' wb') (sigPair wa' wb' x' y' g').
  Proof.
    unfold sigPair, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros gr Hx Hy.
    set (pf := evalAg_refl (esig A0 B0)).
    split.
    - (* first components: out of the expansion, across, back in *)
      eapply ktrE;
        [ exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (proj2 (swfA k A0 B0 FA (esig A0 B0) fT pf))
        | apply cExp_rel |].
      eapply ktrE;
        [ exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (swfA k A0 B0 FA (esig A0 B0) fT pf)
        | exact (proj2 (swfA k A0 B0 FA (esig A0 B0) fT pf))
        | exact (famFrom_eq FA A0 (sAcc A0 B0 (esig A0 B0) fT pf) (evalAg_refl A0)
                   wa x wa' x' Hx)
        | apply knsym; apply cExp_rel ].
    - split; [| split; [exists k; exact gSig | exact gr]].
      (* second components: out of the pair, across, back into the pair *)
      eapply ktrE;
        [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa wb))
                   (sPairFst (esig A0 B0) fT pf wa wb x))
        | exact (famAtWf (FB wa x))
        | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa' wb'))
                   (sPairFst (esig A0 B0) fT pf wa' wb' x'))
        | eapply ktrU;
            [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf
                       (efst (epair wa wb)) (sPairFst (esig A0 B0) fT pf wa wb x))
            | exact (famAtWf (FB (efst (epair wa wb))
                       (sxc k A0 B0 FA (esig A0 B0) fT pf (efst (epair wa wb))
                          (sPairFst (esig A0 B0) fT pf wa wb x))))
            | exact (famAtWf (FB wa x))
            | exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf
                       (efst (epair wa wb)) (sPairFst (esig A0 B0) fT pf wa wb x))
            | apply cohB; exact (sPairFst_rel (esig A0 B0) fT pf wa wb x) ]
        | exact (sPair_snd_rel (esig A0 B0) fT pf wa wb x y g) |].
      eapply ktrE;
        [ exact (famAtWf (FB wa x))
        | exact (famAtWf (FB wa' x'))
        | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst (epair wa' wb'))
                   (sPairFst (esig A0 B0) fT pf wa' wb' x'))
        | exact (kRel_ceq Hy)
        | exact (kRel_at Hy)
        | apply knsym;
          exact (sPair_snd_rel (esig A0 B0) fT pf wa' wb' x' y' g') ].
  Qed.
End SigEl.

(* ------------------------------------------------------------------ *)
(* Two Sigma-families with equal components, and the projections across *)
(* them.  v1's `sigFst_to`/`sigSnd_to` had to unfold the coercion at a   *)
(* Sigma code; here they are the heterogeneous laws applied to            *)
(* `xto_coh`.                                                            *)
(* ------------------------------------------------------------------ *)

Section SigElX.
  Context (k : nat).
  Context (A0 B0 : etm) (FA : kUFam k A0)
          (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x))
          (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x')))
          (gSig : eqty k (esig A0 B0) (esig A0 B0)).
  Context (A0' B0' : etm) (FA' : kUFam k A0')
          (SB' : forall u, kElAt FA' u -> etm)
          (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
          (redB' : forall u x, reds (eapp B0' u) (SB' u x))
          (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
             kceq (kAt (FB' u x)) (kAt (FB' u' x')))
          (gSig' : eqty k (esig A0' B0') (esig A0' B0')).
  Context (Hty : tyeq (esig A0 B0) (esig A0' B0'))
          (HA : kceq (kAt FA) (kAt FA'))
          (HB : forall u x u' x', kEqAt FA u x FA' u' x' ->
             kceq (kAt (FB u x)) (kAt (FB' u' x'))).

  Local Notation SF := (sigFam k A0 B0 FA SB FB redB cohB gSig).
  Local Notation SF' := (sigFam k A0' B0' FA' SB' FB' redB' cohB' gSig').

  (* The two families are equal: buildSig_ceq, with the components' equalities
     read through the placement. *)
  Lemma sigFam_ceq : kceq (kAt SF) (kAt SF').
  Proof.
    unfold kAt, uf_at, kAcc.
    generalize (uf_acc SF') as h'; generalize (uf_acc SF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT'].
    apply (buildSig_ceq k (esig A0 B0) A0 B0 fT (esig A0' B0') A0' B0' fT' Hty
             (sEv A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (sEv A0' B0' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
             (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (seA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (seB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (scA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
             (seA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
             (scB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT'
                (evalAg_refl (esig A0' B0')))
             (seB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT'
                (evalAg_refl (esig A0' B0')))).
    - (* domains *)
      apply famCeq_all; exact HA.
    - (* codomains, at corresponding arguments *)
      intros u x u' y r.
      eapply ktrU;
        [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT
                   (evalAg_refl (esig A0 B0)) u x)
        | exact (famAtWf (FB u (sxc k A0 B0 FA (esig A0 B0) fT
                                  (evalAg_refl (esig A0 B0)) u x)))
        | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT'
                   (evalAg_refl (esig A0' B0')) u' y)
        | exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT
                   (evalAg_refl (esig A0 B0)) u x) |].
      eapply ktrU;
        [ exact (famAtWf (FB u (sxc k A0 B0 FA (esig A0 B0) fT
                                  (evalAg_refl (esig A0 B0)) u x)))
        | exact (famAtWf (FB' u' (sxc k A0' B0' FA' (esig A0' B0') fT'
                                    (evalAg_refl (esig A0' B0')) u' y)))
        | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT'
                   (evalAg_refl (esig A0' B0')) u' y)
        | | apply knsymU;
            exact (scB_at k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT'
                     (evalAg_refl (esig A0' B0')) u' y) ].
      apply HB.
      exact (famTo_eqX FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
               (evalAg_refl A0) u x FA' A0'
               (sAcc A0' B0' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
               (evalAg_refl A0') u' y
               (famCeq_all FA FA' HA A0
                  (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
                  (evalAg_refl A0) A0'
                  (sAcc A0' B0' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
                  (evalAg_refl A0')) r).
  Qed.

  (* the first projection across the two families *)
  Lemma sigFst_eqX u (x : kElAt SF u) u' (x' : kElAt SF' u') :
    kEqAt SF u x SF' u' x' ->
    kEqAt FA (efst u) (sigFst k A0 B0 FA SB FB redB cohB gSig u x)
          FA' (efst u') (sigFst k A0' B0' FA' SB' FB' redB' cohB' gSig' u' x').
  Proof.
    revert x x'; unfold sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF') as h'; generalize (uf_acc SF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT']; intros x x' H.
    apply (famTo_eqX FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (evalAg_refl A0) (efst u) _
             FA' A0' (sAcc A0' B0' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
             (evalAg_refl A0') (efst u') _);
      [ exact (famCeq_all FA FA' HA A0
                 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
                 (evalAg_refl A0) A0'
                 (sAcc A0' B0' (esig A0' B0') fT' (evalAg_refl (esig A0' B0')))
                 (evalAg_refl A0'))
      | exact (proj1 H) ].
  Qed.

  (* and the second *)
  Lemma sigSnd_eqX u (x : kElAt SF u) u' (x' : kElAt SF' u') :
    kEqAt SF u x SF' u' x' ->
    kRel (FB (efst u) (sigFst k A0 B0 FA SB FB redB cohB gSig u x)) (esnd u)
         (sigSnd k A0 B0 FA SB FB redB cohB gSig u x)
         (FB' (efst u') (sigFst k A0' B0' FA' SB' FB' redB' cohB' gSig' u' x'))
         (esnd u') (sigSnd k A0' B0' FA' SB' FB' redB' cohB' gSig' u' x').
  Proof.
    intros H0; split; [exact (HB _ _ _ _ (sigFst_eqX u x u' x' H0)) |].
    revert H0; revert x x';
      unfold sigSnd, sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF') as h'; generalize (uf_acc SF) as h.
    intros h h'; destruct h as [fT]; destruct h' as [fT']; intros x x' H.
    set (pf := evalAg_refl (esig A0 B0)).
    set (pf' := evalAg_refl (esig A0' B0')).
    set (z := projT1 (Datatypes.fst x)).
    set (z' := projT1 (Datatypes.fst x')).
    assert (Hz : kEqAt FA (efst u) (sxc k A0 B0 FA (esig A0 B0) fT pf (efst u) z)
                   FA' (efst u') (sxc k A0' B0' FA' (esig A0' B0') fT' pf' (efst u') z'))
      by (apply (famTo_eqX FA A0 (sAcc A0 B0 (esig A0 B0) fT pf) (evalAg_refl A0)
                   (efst u) z FA' A0'
                   (sAcc A0' B0' (esig A0' B0') fT' pf') (evalAg_refl A0') (efst u') z');
          [ exact (famCeq_all FA FA' HA A0 (sAcc A0 B0 (esig A0 B0) fT pf)
                     (evalAg_refl A0) A0'
                     (sAcc A0' B0' (esig A0' B0') fT' pf') (evalAg_refl A0'))
          | exact (proj1 H) ]).
    eapply ktrE;
      [ exact (famAtWf (FB (efst u) (sFst k A0 B0 FA SB FB redB (esig A0 B0) fT pf u x)))
      | exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | exact (famAtWf (FB' (efst u')
                 (sFst k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf' u' x')))
      | apply knsymU; exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | apply knsym; exact (sSnd_coh k A0 B0 FA SB FB redB (esig A0 B0) fT pf u x) |].
    eapply ktrE;
      [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
      | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf' (efst u') z')
      | exact (famAtWf (FB' (efst u')
                 (sFst k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf' u' x')))
      | eapply ktrU;
          [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
          | exact (famAtWf (FB' (efst u')
                     (sxc k A0' B0' FA' (esig A0' B0') fT' pf' (efst u') z')))
          | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf' (efst u') z')
          | eapply ktrU;
              [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
              | exact (famAtWf (FB (efst u)
                         (sxc k A0 B0 FA (esig A0 B0) fT pf (efst u) z)))
              | exact (famAtWf (FB' (efst u')
                         (sxc k A0' B0' FA' (esig A0' B0') fT' pf' (efst u') z')))
              | exact (scB_at k A0 B0 FA SB FB redB (esig A0 B0) fT pf (efst u) z)
              | exact (HB _ _ _ _ Hz) ]
          | apply knsymU;
            exact (scB_at k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf'
                     (efst u') z') ]
      | exact (proj1 (proj2 H))
      | exact (sSnd_coh k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' pf' u' x') ].
  Qed.

  (* the coercion commutations, which v1 proved by unfolding the coercion *)
  Lemma sigFst_to (P : kceq (kAt SF) (kAt SF')) u (x : kElAt SF u) :
    kEqAt FA (efst u) (sigFst k A0 B0 FA SB FB redB cohB gSig u x)
          FA' (efst u) (sigFst k A0' B0' FA' SB' FB' redB' cohB' gSig' u
                          (kto (kAt SF) (kAt SF') (famAtWf SF) (famAtWf SF') P u x)).
  Proof. apply sigFst_eqX; apply kto_coh. Qed.

  Lemma sigSnd_to (P : kceq (kAt SF) (kAt SF')) u (x : kElAt SF u) :
    kRel (FB (efst u) (sigFst k A0 B0 FA SB FB redB cohB gSig u x)) (esnd u)
         (sigSnd k A0 B0 FA SB FB redB cohB gSig u x)
         (FB' (efst u) (sigFst k A0' B0' FA' SB' FB' redB' cohB' gSig' u
                           (kto (kAt SF) (kAt SF') (famAtWf SF) (famAtWf SF') P u x)))
         (esnd u)
         (sigSnd k A0' B0' FA' SB' FB' redB' cohB' gSig' u
            (kto (kAt SF) (kAt SF') (famAtWf SF) (famAtWf SF') P u x)).
  Proof. apply sigSnd_eqX; apply kto_coh. Qed.
End SigElX.
