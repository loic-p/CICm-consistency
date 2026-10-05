From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The Pi family: the semantic value of a Pi-type, assembled from the semantic
   values of its domain and of its codomain instances.  This is the clause of
   the interpretation at Pi, stripped of the syntax.

   The layer-1 goodness of the Pi-type is a hypothesis: layer 1's Pi clause
   asks for the codomain to be reducible at EVERY pair of related realisers,
   whereas the semantic data only covers realisers that carry an element, so
   it cannot be recovered here.  It comes from the layer-1 fundamental lemma.

   Against v1: the codomain's input is `cohB`, "related arguments give EQUAL
   codomain families", in the natural direction -- v1's `isoB` was an
   isomorphism, stated backwards because the transport it induced had to go
   that way, and this file then had to flip it with `kEqAt_sym` and compose
   `famTo_het`'s two transports. *)

Section PiFam.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  (* The data at one instance of the family.  All of v, fT and pf are explicit
     arguments rather than section variables, so that the argument lists of
     these auxiliary definitions are predictable. *)
  Definition pEv v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : eval v (epi A0 B0) :=
    pf (epi A0 B0) (eval_whnf _ (whnf_pi A0 B0)).

  Definition pAcc v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : Acc prec A0 :=
    accAt v fT (pdom v A0 B0 (pEv v fT pf)).

  Definition pcA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : Code k (domNode v A0 B0 fT (pEv v fT pf)) :=
    uf_c FA A0 (pAcc v fT pf) (evalAg_refl A0).

  Definition peA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : tyeq (projT1 (pcA v fT pf)) A0 :=
    ex_intro _ k (uf_sh FA A0 (pAcc v fT pf) (evalAg_refl A0)).

  Definition pwfA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : wfn (pcA v fT pf) :=
    uf_wf FA A0 (pAcc v fT pf) (evalAg_refl A0).

  (* an element of the placed domain, read as an element of the domain family *)
  Definition pxc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u
    (x : kElS (placeDom k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)) u) : kElAt FA u :=
    famTo FA A0 (pAcc v fT pf) (evalAg_refl A0) u x.

  Definition pag u (x : kElAt FA u) : evalAg (eapp B0 u) (SB u x) :=
    fun w H => eval_reds _ _ _ (redB u x) H.

  Definition pcB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) u x
    : Code k (codNode v A0 B0 fT (pEv v fT pf) u
                (argGood k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf) u x)) :=
    uf_c (FB u (pxc v fT pf u x)) (eapp B0 u)
         (accAt v fT (pcod v A0 B0 (pEv v fT pf) u
                        (argGood k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)
                           (peA v fT pf) u x)))
         (pag u (pxc v fT pf u x)).

  Definition peB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) u x : tyeq (projT1 (pcB v fT pf u x)) (eapp B0 u).
  Proof.
    exists k; eapply eqty_exp; [apply reds_refl | apply redB | apply uf_sh].
  Defined.

  Definition pwfB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) u x : wfn (pcB v fT pf u x) :=
    uf_wf (FB u (pxc v fT pf u x)) _ _ _.

  (* the instance the codomain code sits at is equal to the canonical code of
     the codomain family at the round-tripped argument.  Named here, with all
     the instance arguments in scope, so that no caller has to spell them. *)
  Lemma pcB_at v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) u x :
    kceq (pcB v fT pf u x) (kAt (FB u (pxc v fT pf u x))).
  Proof.
    exact (uf_coh (FB u (pxc v fT pf u x)) (eapp B0 u)
             (accAt v fT (pcod v A0 B0 (pEv v fT pf) u
                            (argGood k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)
                               (peA v fT pf) u x)))
             (pag u (pxc v fT pf u x))
             (SB u (pxc v fT pf u x)) (kAcc (FB u (pxc v fT pf u x)))
             (evalAg_refl (SB u (pxc v fT pf u x)))).
  Qed.

  (* the coherence a Pi-code asks for, at one instance.  Read the two placed
     arguments as elements of the domain family, apply `cohB`, and transport
     the resulting equality of canonical instances to the instances at hand --
     three steps, all of them equalities. *)
  Definition pcohB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) u x u' x'
    (r : kcEl (placeDom k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)) u x
               (placeDom k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)) u' x')
    : kceq (pcB v fT pf u x) (pcB v fT pf u' x').
  Proof.
    apply famCeq_all.
    apply cohB.
    apply famTo_eq; exact r.
  Defined.

  Definition pcode v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : Code k (rk v (hT v fT)) :=
    mkCode (buildPi k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf)
              (pcB v fT pf) (peB v fT pf)).

  Lemma pcode_sh v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : eqty k v (epi A0 B0).
  Proof. eapply eqty_exp; [exact (proj1 (pEv v fT pf)) | apply reds_refl | exact gPi]. Qed.

  Lemma pcode_wf v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : wfn (pcode v fT pf).
  Proof.
    exact (buildPi_wf k v A0 B0 fT (pEv v fT pf)
             (ex_intro _ k (eqty_refl_l k v (epi A0 B0) (pcode_sh v fT pf)))
             (pcA v fT pf) (peA v fT pf) (pwfA v fT pf)
             (pcB v fT pf) (peB v fT pf) (pwfB v fT pf) (pcohB v fT pf)).
  Qed.

  Definition piFam : kUFam k (epi A0 B0).
  Proof.
    unshelve refine (Build_UFam (lvl k) k (epi A0 B0) _ gPi _ _ _).
    - intros v h pf; destruct h as [fT]; exact (pcode v fT pf).
    - intros v h pf; destruct h as [fT]; exact (pcode_sh v fT pf).
    - intros v h pf; destruct h as [fT]; exact (pcode_wf v fT pf).
    - intros v h pf v' h' pf'; destruct h as [fT]; destruct h' as [fT'].
      apply (buildPi_ceq k
               v A0 B0 fT v' A0 B0 fT'
               (* the two shadows are layer-1 equal *)
               (ex_intro _ k (eqty_trans k v (epi A0 B0) v' (pcode_sh v fT pf)
                                (eqty_sym k v' (epi A0 B0) (pcode_sh v' fT' pf'))))
               (pEv v fT pf) (pEv v' fT' pf')
               (pcA v fT pf) (peA v fT pf) (pcB v fT pf) (peB v fT pf)
               (pcA v' fT' pf') (peA v' fT' pf') (pcB v' fT' pf') (peB v' fT' pf')).
      + (* the domains are equal *)
        apply uf_coh.
      + (* the codomains are equal at corresponding arguments *)
        intros u x u' y r.
        apply famCeq_all; apply cohB.
        apply (famTo_eqX FA A0 (pAcc v fT pf) (evalAg_refl A0) u x
                 FA A0 (pAcc v' fT' pf') (evalAg_refl A0) u' y);
          [apply uf_coh | exact r].
  Defined.
End PiFam.

(* ------------------------------------------------------------------ *)
(* Two Pi families are EQUAL as soon as their components are: the      *)
(* shadows layer-1 equal, the domains equal, and the codomains equal at *)
(* related arguments.  This is what functionality at a Pi-type needs,   *)
(* and it is `buildPi_ceq` with the two canonical instances' coherences *)
(* composed on either side.                                            *)
(* ------------------------------------------------------------------ *)

Lemma piFam_ceq (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
     kceq (kAt (FB u x)) (kAt (FB u' x')))
  (gPi : eqty k (epi A0 B0) (epi A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
     kceq (kAt (FB' u x)) (kAt (FB' u' x')))
  (gPi' : eqty k (epi A0' B0') (epi A0' B0'))
  (Hty : tyeq (epi A0 B0) (epi A0' B0'))
  (HA : kceq (kAt FA) (kAt FA'))
  (HB : forall u x u' x', kEqAt FA u x FA' u' x' ->
     kceq (kAt (FB u x)) (kAt (FB' u' x'))) :
  kceq (kAt (piFam k A0 B0 FA SB FB redB cohB gPi))
       (kAt (piFam k A0' B0' FA' SB' FB' redB' cohB' gPi')).
Proof.
  unfold kAt, uf_at, kAcc.
  generalize (uf_acc (piFam k A0' B0' FA' SB' FB' redB' cohB' gPi')) as h'.
  generalize (uf_acc (piFam k A0 B0 FA SB FB redB cohB gPi)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT'].
  apply (buildPi_ceq k
           (epi A0 B0) A0 B0 fT (epi A0' B0') A0' B0' fT' Hty
           (pEv A0 B0 (epi A0 B0) fT (evalAg_refl _))
           (pEv A0' B0' (epi A0' B0') fT' (evalAg_refl _))
           (pcA k A0 B0 FA (epi A0 B0) fT (evalAg_refl _))
           (peA k A0 B0 FA (epi A0 B0) fT (evalAg_refl _))
           (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _))
           (peB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _))
           (pcA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
           (peA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
           (pcB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _))
           (peB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _))).
  - (* the domains, through the two families' coherences *)
    eapply ktrU;
      [ exact (pwfA k A0 B0 FA (epi A0 B0) fT (evalAg_refl _))
      | exact (famAtWf FA) | exact (pwfA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
      | apply uf_coh |].
    eapply ktrU;
      [ exact (famAtWf FA) | exact (famAtWf FA')
      | exact (pwfA k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _))
      | exact HA | apply knsymU; apply uf_coh ].
  - (* the codomains, at related arguments *)
    intros u x u' y r.
    eapply ktrU;
      [ exact (pwfB k A0 B0 FA SB FB redB (epi A0 B0) fT (evalAg_refl _) u x)
      | exact (famAtWf (FB u (pxc k A0 B0 FA (epi A0 B0) fT (evalAg_refl _) u x)))
      | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _) u' y)
      | apply pcB_at |].
    eapply ktrU;
      [ exact (famAtWf (FB u (pxc k A0 B0 FA (epi A0 B0) fT (evalAg_refl _) u x)))
      | exact (famAtWf (FB' u' (pxc k A0' B0' FA' (epi A0' B0') fT' (evalAg_refl _) u' y)))
      | exact (pwfB k A0' B0' FA' SB' FB' redB' (epi A0' B0') fT' (evalAg_refl _) u' y)
      | | apply knsymU; apply pcB_at ].
    apply HB.
    apply (famTo_eqX FA A0 (pAcc A0 B0 (epi A0 B0) fT (evalAg_refl _))
             (evalAg_refl A0) u x
             FA' A0' (pAcc A0' B0' (epi A0' B0') fT' (evalAg_refl _))
             (evalAg_refl A0') u' y);
      [ exact (famCeq_all FA FA' HA _ _ _ _ _ _) | exact r ].
Qed.
