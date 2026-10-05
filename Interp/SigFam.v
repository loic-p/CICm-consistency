From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The Sigma family: component for component the same as the Pi one.  A
   Sigma-code carries no condition on its decoding, but it carries the same
   components and the same coherence, so this file is PiFam.v with `esig` in
   place of `epi` and the Sigma witnesses in place of the Pi ones. *)

Section SigFam.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gSig : eqty k (esig A0 B0) (esig A0 B0)).

  (* The data at one instance of the family.  All of v, fT and pf are explicit
     arguments rather than section variables, so that the argument lists of
     these auxiliary definitions are predictable. *)
  Definition sEv v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : eval v (esig A0 B0) :=
    pf (esig A0 B0) (eval_whnf _ (whnf_sig A0 B0)).

  Definition sAcc v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : Acc prec A0 :=
    accAt v fT (sdom v A0 B0 (sEv v fT pf)).

  Definition scA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : Code k (sdomNode v A0 B0 fT (sEv v fT pf)) :=
    uf_c FA A0 (sAcc v fT pf) (evalAg_refl A0).

  Definition seA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : tyeq (projT1 (scA v fT pf)) A0 :=
    ex_intro _ k (uf_sh FA A0 (sAcc v fT pf) (evalAg_refl A0)).

  Definition swfA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : wfn (scA v fT pf) :=
    uf_wf FA A0 (sAcc v fT pf) (evalAg_refl A0).

  (* an element of the placed domain, read as an element of the domain family *)
  Definition sxc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u
    (x : kElS (placeSDom k v A0 B0 fT (sEv v fT pf) (scA v fT pf)) u) : kElAt FA u :=
    famTo FA A0 (sAcc v fT pf) (evalAg_refl A0) u x.

  Definition sag u (x : kElAt FA u) : evalAg (eapp B0 u) (SB u x) :=
    fun w H => eval_reds _ _ _ (redB u x) H.

  Definition scB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) u x
    : Code k (scodNode v A0 B0 fT (sEv v fT pf) u
                (sargGood k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf) u x)) :=
    uf_c (FB u (sxc v fT pf u x)) (eapp B0 u)
         (accAt v fT (scod v A0 B0 (sEv v fT pf) u
                        (sargGood k v A0 B0 fT (sEv v fT pf) (scA v fT pf)
                           (seA v fT pf) u x)))
         (sag u (sxc v fT pf u x)).

  Definition seB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) u x : tyeq (projT1 (scB v fT pf u x)) (eapp B0 u).
  Proof.
    exists k; eapply eqty_exp; [apply reds_refl | apply redB | apply uf_sh].
  Defined.

  Definition swfB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) u x : wfn (scB v fT pf u x) :=
    uf_wf (FB u (sxc v fT pf u x)) _ _ _.

  (* the instance the codomain code sits at is equal to the canonical code of
     the codomain family at the round-tripped argument.  Named here, with all
     the instance arguments in scope, so that no caller has to spell them. *)
  Lemma scB_at v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) u x :
    kceq (scB v fT pf u x) (kAt (FB u (sxc v fT pf u x))).
  Proof.
    exact (uf_coh (FB u (sxc v fT pf u x)) (eapp B0 u)
             (accAt v fT (scod v A0 B0 (sEv v fT pf) u
                            (sargGood k v A0 B0 fT (sEv v fT pf) (scA v fT pf)
                               (seA v fT pf) u x)))
             (sag u (sxc v fT pf u x))
             (SB u (sxc v fT pf u x)) (kAcc (FB u (sxc v fT pf u x)))
             (evalAg_refl (SB u (sxc v fT pf u x)))).
  Qed.

  (* the coherence a Pi-code asks for, at one instance.  Read the two placed
     arguments as elements of the domain family, apply `cohB`, and transport
     the resulting equality of canonical instances to the instances at hand --
     three steps, all of them equalities. *)
  Definition scohB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) u x u' x'
    (r : kcEl (placeSDom k v A0 B0 fT (sEv v fT pf) (scA v fT pf)) u x
               (placeSDom k v A0 B0 fT (sEv v fT pf) (scA v fT pf)) u' x')
    : kceq (scB v fT pf u x) (scB v fT pf u' x').
  Proof.
    apply famCeq_all.
    apply cohB.
    apply famTo_eq; exact r.
  Defined.

  Definition scode v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : Code k (rk v (hT v fT)) :=
    mkCode (buildSig k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf)
              (scB v fT pf) (seB v fT pf)).

  Lemma scode_sh v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : eqty k v (esig A0 B0).
  Proof. eapply eqty_exp; [exact (proj1 (sEv v fT pf)) | apply reds_refl | exact gSig]. Qed.

  Lemma scode_wf v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : wfn (scode v fT pf).
  Proof.
    exact (buildSig_wf k v A0 B0 fT (sEv v fT pf)
             (ex_intro _ k (eqty_refl_l k v (esig A0 B0) (scode_sh v fT pf)))
             (scA v fT pf) (seA v fT pf) (swfA v fT pf)
             (scB v fT pf) (seB v fT pf) (swfB v fT pf) (scohB v fT pf)).
  Qed.

  Definition sigFam : kUFam k (esig A0 B0).
  Proof.
    unshelve refine (Build_UFam (lvl k) k (esig A0 B0) _ gSig _ _ _).
    - intros v h pf; destruct h as [fT]; exact (scode v fT pf).
    - intros v h pf; destruct h as [fT]; exact (scode_sh v fT pf).
    - intros v h pf; destruct h as [fT]; exact (scode_wf v fT pf).
    - intros v h pf v' h' pf'; destruct h as [fT]; destruct h' as [fT'].
      apply (buildSig_ceq k
               v A0 B0 fT v' A0 B0 fT'
               (* the two shadows are layer-1 equal *)
               (ex_intro _ k (eqty_trans k v (esig A0 B0) v' (scode_sh v fT pf)
                                (eqty_sym k v' (esig A0 B0) (scode_sh v' fT' pf'))))
               (sEv v fT pf) (sEv v' fT' pf')
               (scA v fT pf) (seA v fT pf) (scB v fT pf) (seB v fT pf)
               (scA v' fT' pf') (seA v' fT' pf') (scB v' fT' pf') (seB v' fT' pf')).
      + (* the domains are equal *)
        apply uf_coh.
      + (* the codomains are equal at corresponding arguments *)
        intros u x u' y r.
        apply famCeq_all; apply cohB.
        apply (famTo_eqX FA A0 (sAcc v fT pf) (evalAg_refl A0) u x
                 FA A0 (sAcc v' fT' pf') (evalAg_refl A0) u' y);
          [apply uf_coh | exact r].
  Defined.
End SigFam.

(* ------------------------------------------------------------------ *)
(* Two Sigma families are EQUAL as soon as their components are: the      *)
(* shadows layer-1 equal, the domains equal, and the codomains equal at *)
(* related arguments.  This is what functionality at a Sigma-type needs,   *)
(* and it is `buildSig_ceq` with the two canonical instances' coherences *)
(* composed on either side.                                            *)
(* ------------------------------------------------------------------ *)

Lemma sigFam_ceq (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
     kceq (kAt (FB u x)) (kAt (FB u' x')))
  (gSig : eqty k (esig A0 B0) (esig A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
     kceq (kAt (FB' u x)) (kAt (FB' u' x')))
  (gSig' : eqty k (esig A0' B0') (esig A0' B0'))
  (Hty : tyeq (esig A0 B0) (esig A0' B0'))
  (HA : kceq (kAt FA) (kAt FA'))
  (HB : forall u x u' x', kEqAt FA u x FA' u' x' ->
     kceq (kAt (FB u x)) (kAt (FB' u' x'))) :
  kceq (kAt (sigFam k A0 B0 FA SB FB redB cohB gSig))
       (kAt (sigFam k A0' B0' FA' SB' FB' redB' cohB' gSig')).
Proof.
  unfold kAt, uf_at, kAcc.
  generalize (uf_acc (sigFam k A0' B0' FA' SB' FB' redB' cohB' gSig')) as h'.
  generalize (uf_acc (sigFam k A0 B0 FA SB FB redB cohB gSig)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT'].
  apply (buildSig_ceq k
           (esig A0 B0) A0 B0 fT (esig A0' B0') A0' B0' fT' Hty
           (sEv A0 B0 (esig A0 B0) fT (evalAg_refl _))
           (sEv A0' B0' (esig A0' B0') fT' (evalAg_refl _))
           (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl _))
           (seA k A0 B0 FA (esig A0 B0) fT (evalAg_refl _))
           (scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _))
           (seB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _))
           (scA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
           (seA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
           (scB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _))
           (seB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _))).
  - (* the domains, through the two families' coherences *)
    eapply ktrU;
      [ exact (swfA k A0 B0 FA (esig A0 B0) fT (evalAg_refl _))
      | exact (famAtWf FA) | exact (swfA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
      | apply uf_coh |].
    eapply ktrU;
      [ exact (famAtWf FA) | exact (famAtWf FA')
      | exact (swfA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
      | exact HA | apply knsymU; apply uf_coh ].
  - (* the codomains, at related arguments *)
    intros u x u' y r.
    eapply ktrU;
      [ exact (swfB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _) u x)
      | exact (famAtWf (FB u (sxc k A0 B0 FA (esig A0 B0) fT (evalAg_refl _) u x)))
      | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _) u' y)
      | apply scB_at |].
    eapply ktrU;
      [ exact (famAtWf (FB u (sxc k A0 B0 FA (esig A0 B0) fT (evalAg_refl _) u x)))
      | exact (famAtWf (FB' u' (sxc k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _) u' y)))
      | exact (swfB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _) u' y)
      | | apply knsymU; apply scB_at ].
    apply HB.
    apply (famTo_eqX FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl _))
             (evalAg_refl A0) u x
             FA' A0' (sAcc A0' B0' (esig A0' B0') fT' (evalAg_refl _))
             (evalAg_refl A0') u' y);
      [ exact (famCeq_all FA FA' HA _ _ _ _ _ _) | exact r ].
Qed.
