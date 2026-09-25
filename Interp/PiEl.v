From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.Univ Interp.Env Interp.Elem.
From Stdlib Require Import Arith Lia.

(* Semantic application: the elimination side of the Pi-family.

   A Pi-code's decoding is a function on the elements of the DOMAIN CODE at
   the node the Pi-code lives at, whereas the interpretation has an element
   of the domain FAMILY.  The two are different instances of one family, so
   the argument goes in through famFrom and comes back out through famTo,
   and the round trip is not the identity -- only related to it (pArg_eq).
   Since the codomain family is indexed by the argument, the value therefore
   lands at FB u' (pArg y) rather than at FB u' y, and one transport along
   isoB brings it home.  That transport is the only content of this file;
   everything else is placement, which is definitional. *)

(* The round trip through an instance of a family is the identity, up to the
   family's own equality.  This is functoriality of the canonical transport
   plus the identity property at a self-isomorphism. *)
Lemma famTo_famFrom {k u} (F : kUFam k u) v h pf w (y : kElAt F w) :
  kEqAt F w (famTo F v h pf w (famFrom F v h pf w y)) w y.
Proof.
  eapply kEqC_trans;
    [ apply kEqC_sym,
        (ctoK_fun (kAt F) (uf_c F v h pf) (kAt F)
           (uf_coh F u (kAcc F) (evalAg_refl u) v h pf)
           (uf_coh F v h pf u (kAcc F) (evalAg_refl u))
           (iso_self F) w y)
    | apply (uf_idp F u (kAcc F) (evalAg_refl u) (iso_self F) w y) ].
Qed.

Section PiEl.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  Local Notation PF := (piFam k A0 B0 FA SB FB redB isoB gPi).

  (* The argument, after its round trip through the domain code. *)
  Definition pArg v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    u' (y : kElAt FA u') : kElAt FA u' :=
    pxc k A0 B0 FA v fT pf u'
        (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y).

  Lemma pArg_eq v fT pf u' y : kEqAt FA u' (pArg v fT pf u' y) u' y.
  Proof. unfold pArg, pxc; apply famTo_famFrom. Qed.

  (* Application at one instance of the family. *)
  Definition pApp v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    u (x : kElC (pcode k A0 B0 FA SB FB redB isoB v fT pf) u)
    u' (y : kElAt FA u') : kElAt (FB u' y) (eapp u u').
  Proof.
    refine (ctoK (kAt (FB u' (pArg v fT pf u' y))) (kAt (FB u' y))
              (isoB u' y u' (pArg v fT pf u' y)
                 (kEqAt_sym FA u' (pArg v fT pf u' y) u' y (pArg_eq v fT pf u' y)))
              (eapp u u') _).
    refine (famTo (FB u' (pArg v fT pf u' y)) _ _ _ (eapp u u') _).
    exact (Datatypes.fst (proj1_sig x) u'
             (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y)).
  Defined.

  (* Application at the canonical instance, which is the one the
     interpretation uses.  The accessibility proof has to be destructed for
     the family's code to unfold at all. *)
  Definition piApp u (x : kElAt PF u) u' (y : kElAt FA u') : kElAt (FB u' y) (eapp u u').
  Proof.
    revert x; unfold kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT]; intros x.
    exact (pApp (epi A0 B0) fT (evalAg_refl (epi A0 B0)) u x u' y).
  Defined.
End PiEl.

(* ------------------------------------------------------------------ *)
(* The law: application respects the equalities.  Everything below is  *)
(* the hetC algebra -- no transport is ever unfolded, because the      *)
(* placement of a component is transparent (place_to) and any two      *)
(* canonical transports between the same codes agree (ctoK_irr).       *)
(* ------------------------------------------------------------------ *)

Section PiElLaw.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  Local Notation PF := (piFam k A0 B0 FA SB FB redB isoB gPi).

  (* The value of pApp is related to the raw code-level application. *)
  Lemma pApp_het v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
    (u : etm) (x : kElC (pcode k A0 B0 FA SB FB redB isoB v fT pf) u)
    (u' : etm) (y : kElAt FA u') :
    hetC (pcB k A0 B0 FA SB FB redB v fT pf u'
            (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y))
         (kAt (FB u' y))
         (eapp u u')
         (Datatypes.fst (proj1_sig x) u'
            (famFrom FA A0 (pAcc A0 B0 v fT pf) (evalAg_refl A0) u' y))
         (eapp u u') (pApp k A0 B0 FA SB FB redB isoB v fT pf u x u' y).
  Proof.
    unfold pApp, famTo.
    eapply hetC_trans; [apply hetC_to | apply hetC_to].
  Qed.

  Lemma piApp_eq u (x : kElAt PF u) u1 (x1 : kElAt PF u1)
    u' (y : kElAt FA u') u'' (y1 : kElAt FA u'') :
    kEqAt PF u x u1 x1 -> kEqAt FA u' y u'' y1 ->
    kRel (FB u' y) (FB u'' y1)
         (eapp u u') (piApp k A0 B0 FA SB FB redB isoB gPi u x u' y)
         (eapp u1 u'') (piApp k A0 B0 FA SB FB redB isoB gPi u1 x1 u'' y1).
  Proof.
    revert x x1; unfold piApp, kElAt, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc PF) as h; intros h; destruct h as [fT]; intros x x1 Hx Hy.
    set (pf := evalAg_refl (epi A0 B0)).
    set (z := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u' y).
    set (z1 := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) u'' y1).
    assert (r : kEqC (pcA k A0 B0 FA (epi A0 B0) fT pf) u' z u'' z1)
      by (apply ctoK_eq; exact Hy).
    assert (r' : kEqC (pcA k A0 B0 FA (epi A0 B0) fT pf) u'' z1 u' z)
      by (apply kEqC_sym; exact r).
    destruct Hx as [Hfun _].
    assert (Hhet : hetC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
                        (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u'' z1)
                        (eapp u u') (Datatypes.fst (proj1_sig x) u' z)
                        (eapp u1 u'') (Datatypes.fst (proj1_sig x1) u'' z1)).
    { apply hetC_sym.
      exists (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf u' z u'' z1 r).
      apply kEqC_sym, (proj1 (Hfun u' z u'' z1 r r')). }
    eapply hetC_trans; [apply hetC_sym, pApp_het |].
    eapply hetC_trans; [exact Hhet | apply pApp_het].
  Qed.
End PiElLaw.

(* ------------------------------------------------------------------ *)
(* Two Pi-families with isomorphic components are isomorphic.  This is *)
(* buildPi_iso lifted from codes to families: the same argument as      *)
(* piFam's own coherence field, but between two DIFFERENT families,     *)
(* which is what functionality of the interpretation on types needs.    *)
(* ------------------------------------------------------------------ *)

Lemma pxc_het (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (A0' B0' : etm) (FA' : kUFam k A0')
  v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0))
  v' (fT' : forall y, prec y v' -> Acc prec y) (pf' : evalAg v' (epi A0' B0'))
  u x u' y :
  hetC (pcA k A0 B0 FA v fT pf) (pcA k A0' B0' FA' v' fT' pf') u x u' y ->
  kRel FA FA' u (pxc k A0 B0 FA v fT pf u x) u' (pxc k A0' B0' FA' v' fT' pf' u' y).
Proof.
  intros H; unfold kRel, pxc, famTo.
  eapply hetC_trans; [apply hetC_sym, hetC_to |].
  eapply hetC_trans; [exact H | apply hetC_to].
Qed.

Lemma piFam_iso (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (epi A0 B0) (epi A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (isoB' : forall u x u' x', kEqAt FA' u x u' x' -> iso (kAt (FB' u' x')) (kAt (FB' u x)))
  (gPi' : eqty k (epi A0' B0') (epi A0' B0'))
  (Hty : tyeq (epi A0 B0) (epi A0' B0'))
  (HA : iso (kAt FA) (kAt FA'))
  (HB : forall u x u' x', kRel FA FA' u x u' x' -> iso (kAt (FB u x)) (kAt (FB' u' x'))) :
  iso (kAt (piFam k A0 B0 FA SB FB redB isoB gPi))
      (kAt (piFam k A0' B0' FA' SB' FB' redB' isoB' gPi')).
Proof.
  unfold kAt, uf_at, kAcc.
  generalize (uf_acc (piFam k A0' B0' FA' SB' FB' redB' isoB' gPi')) as h'.
  generalize (uf_acc (piFam k A0 B0 FA SB FB redB isoB gPi)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT'].
  apply (buildPi_iso k
           (epi A0 B0) A0 B0 fT (pEv A0 B0 (epi A0 B0) fT (evalAg_refl _))
             (pcA k A0 B0 FA (epi A0 B0) fT (evalAg_refl _))
             (peA k A0 B0 FA (epi A0 B0) fT (evalAg_refl _))
             (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _))
             (peB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _))
             (pidB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _))
             (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT (evalAg_refl _))
           (epi A0' B0') A0' B0' fT' (pEv A0' B0' (epi A0' B0') fT' (evalAg_refl _))
             (pcA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
             (peA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
             (pcB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _))
             (peB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _))
             (pidB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _))
             (pisoB k A0' B0' FA' SB' FB' redB' isoB' (epi A0' B0') fT' (evalAg_refl _))).
  - exact Hty.
  - (* the domains: the two families' instances, through their coherences *)
    eapply iso_trans; [apply uf_coh |].
    eapply iso_trans; [exact HA | apply uf_coh].
  - (* the codomains, at related arguments *)
    intros u x u' y Hxy.
    eapply iso_trans; [apply uf_coh |].
    eapply iso_trans; [| apply uf_coh].
    apply HB, pxc_het, Hxy.
Qed.

(* The transported function applied at the transported argument is the transport
   of the application.  This is what functionality on terms needs at app and at
   lam, and it is the one transport law with content: toRefine's r_pi branch
   applies the function at an hj_pull-ed argument, so the proof has to reconcile
   that pullback with the argument in hand (pull_of_to) and then move the
   application across the domain's equality, which the Pi-code's decoding
   respects by construction (the first component of the value's own
   self-relatedness, exactly as in piApp_eq). *)
Lemma piApp_to (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (epi A0 B0) (epi A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (isoB' : forall u x u' x', kEqAt FA' u x u' x' -> iso (kAt (FB' u' x')) (kAt (FB' u x)))
  (gPi' : eqty k (epi A0' B0') (epi A0' B0')) :
  forall (P : iso (kAt (piFam k A0 B0 FA SB FB redB isoB gPi))
                  (kAt (piFam k A0' B0' FA' SB' FB' redB' isoB' gPi')))
    (Q : iso (kAt FA) (kAt FA'))
    u (x : kElAt (piFam k A0 B0 FA SB FB redB isoB gPi) u)
    (Hx : kEqAt (piFam k A0 B0 FA SB FB redB isoB gPi) u x u x)
    v (y : kElAt FA v),
  kRel (FB v y) (FB' v (ctoK _ _ Q v y))
       (eapp u v) (piApp k A0 B0 FA SB FB redB isoB gPi u x v y)
       (eapp u v) (piApp k A0' B0' FA' SB' FB' redB' isoB' gPi' u
                     (ctoK _ _ P u x) v (ctoK _ _ Q v y)).
Proof.
  unfold piApp, kEqAt at 1, kElAt at 1 2, kAt, uf_at, kAcc.
  generalize (uf_acc (piFam k A0' B0' FA' SB' FB' redB' isoB' gPi')) as h'.
  generalize (uf_acc (piFam k A0 B0 FA SB FB redB isoB gPi)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT']; intros P Q u x Hx v y.
  eapply hetC_trans; [apply hetC_sym; apply pApp_het |].
  eapply hetC_trans; [| apply pApp_het].
  cbn [uf_c piFam] in *; unfold ctoK in *.
  rewrite (cto_refine (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)).
  unfold pcode, mkCode, buildPi, mkPi, kstage, hT; cbn [projT2].
  rewrite toRefine_pi_app.
  unfold bb, placeCod; rewrite place_to_het.
  match goal with
  | |- hetC (pcB _ _ _ _ _ _ _ _ _ _ _ ?z) _ _ _ _
           (ctoK (pcB _ _ _ _ _ _ _ _ _ _ _ ?zp) _ _ _ _) =>
      assert (HA : kEqC (pcA k A0 B0 FA (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
                        v zp v z) by apply pull_of_to;
      assert (HA' : kEqC (pcA k A0 B0 FA (epi A0 B0) fT (evalAg_refl (epi A0 B0)))
                         v z v zp) by (apply kEqC_sym; exact HA);
      assert (HB : hetC
                     (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT
                        (evalAg_refl (epi A0 B0)) v z)
                     (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT
                        (evalAg_refl (epi A0 B0)) v zp)
                     (eapp u v) (Datatypes.fst (proj1_sig x) v z)
                     (eapp u v) (Datatypes.fst (proj1_sig x) v zp));
      [ destruct Hx as [Hfun _]; apply hetC_sym;
        exists (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT
                  (evalAg_refl (epi A0 B0)) v z v zp HA');
        apply kEqC_sym, (proj1 (Hfun v z v zp HA' HA))
      | eapply hetC_trans; [exact HB | apply hetC_to] ]
  end.
Qed.
