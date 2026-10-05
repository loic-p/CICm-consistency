From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The W family: new in v2, and component for component the same as the Pi
   one.  A W-code carries the same two components and the same coherence -- the
   label type and the branching family, with "related labels give equal
   branching families" -- so this file is PiFam.v with `ew` in place of `epi`
   and the W witnesses in place of the Pi ones.  What differs is the DECODING
   (trees rather than functions), and that lives in Interp/Codes.v. *)

Section WFam.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gW : eqty k (ew A0 B0) (ew A0 B0)).

  (* The data at one instance of the family.  All of v, fT and pf are explicit
     arguments rather than section variables, so that the argument lists of
     these auxiliary definitions are predictable. *)
  Definition wEv v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : eval v (ew A0 B0) :=
    pf (ew A0 B0) (eval_whnf _ (whnf_w A0 B0)).

  Definition wAccA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : Acc prec A0 :=
    accAt v fT (wdom v A0 B0 (wEv v fT pf)).

  Definition wcA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : Code k (wdomNode v A0 B0 fT (wEv v fT pf)) :=
    uf_c FA A0 (wAccA v fT pf) (evalAg_refl A0).

  Definition weA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : tyeq (projT1 (wcA v fT pf)) A0 :=
    ex_intro _ k (uf_sh FA A0 (wAccA v fT pf) (evalAg_refl A0)).

  Definition wwfA v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : wfn (wcA v fT pf) :=
    uf_wf FA A0 (wAccA v fT pf) (evalAg_refl A0).

  (* an element of the placed domain, read as an element of the domain family *)
  Definition wxc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (ew A0 B0)) u
    (x : kElS (placeWDom k v A0 B0 fT (wEv v fT pf) (wcA v fT pf)) u) : kElAt FA u :=
    famTo FA A0 (wAccA v fT pf) (evalAg_refl A0) u x.

  Definition wag u (x : kElAt FA u) : evalAg (eapp B0 u) (SB u x) :=
    fun w H => eval_reds _ _ _ (redB u x) H.

  Definition wcB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) u x
    : Code k (wcodNode v A0 B0 fT (wEv v fT pf) u
                (wargGood k v A0 B0 fT (wEv v fT pf) (wcA v fT pf) (weA v fT pf) u x)) :=
    uf_c (FB u (wxc v fT pf u x)) (eapp B0 u)
         (accAt v fT (wcod v A0 B0 (wEv v fT pf) u
                        (wargGood k v A0 B0 fT (wEv v fT pf) (wcA v fT pf)
                           (weA v fT pf) u x)))
         (wag u (wxc v fT pf u x)).

  Definition weB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) u x : tyeq (projT1 (wcB v fT pf u x)) (eapp B0 u).
  Proof.
    exists k; eapply eqty_exp; [apply reds_refl | apply redB | apply uf_sh].
  Defined.

  Definition wwfB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) u x : wfn (wcB v fT pf u x) :=
    uf_wf (FB u (wxc v fT pf u x)) _ _ _.

  (* the instance the codomain code sits at is equal to the canonical code of
     the codomain family at the round-tripped argument.  Named here, with all
     the instance arguments in scope, so that no caller has to spell them. *)
  Lemma wcB_at v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) u x :
    kceq (wcB v fT pf u x) (kAt (FB u (wxc v fT pf u x))).
  Proof.
    exact (uf_coh (FB u (wxc v fT pf u x)) (eapp B0 u)
             (accAt v fT (wcod v A0 B0 (wEv v fT pf) u
                            (wargGood k v A0 B0 fT (wEv v fT pf) (wcA v fT pf)
                               (weA v fT pf) u x)))
             (wag u (wxc v fT pf u x))
             (SB u (wxc v fT pf u x)) (kAcc (FB u (wxc v fT pf u x)))
             (evalAg_refl (SB u (wxc v fT pf u x)))).
  Qed.

  (* the coherence a Pi-code asks for, at one instance.  Read the two placed
     arguments as elements of the domain family, apply `cohB`, and transport
     the resulting equality of canonical instances to the instances at hand --
     three steps, all of them equalities. *)
  Definition wcohB v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) u x u' x'
    (r : kcEl (placeWDom k v A0 B0 fT (wEv v fT pf) (wcA v fT pf)) u x
               (placeWDom k v A0 B0 fT (wEv v fT pf) (wcA v fT pf)) u' x')
    : kceq (wcB v fT pf u x) (wcB v fT pf u' x').
  Proof.
    apply famCeq_all.
    apply cohB.
    apply famTo_eq; exact r.
  Defined.

  Definition wcode v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : Code k (rk v (hT v fT)) :=
    mkCode (buildW k v A0 B0 fT (wEv v fT pf) (wcA v fT pf) (weA v fT pf)
              (wcB v fT pf) (weB v fT pf)).

  Lemma wcode_sh v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : eqty k v (ew A0 B0).
  Proof. eapply eqty_exp; [exact (proj1 (wEv v fT pf)) | apply reds_refl | exact gW]. Qed.

  Lemma wcode_wf v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (ew A0 B0)) : wfn (wcode v fT pf).
  Proof.
    exact (buildW_wf k v A0 B0 fT (wEv v fT pf)
             (ex_intro _ k (eqty_refl_l k v (ew A0 B0) (wcode_sh v fT pf)))
             (wcA v fT pf) (weA v fT pf) (wwfA v fT pf)
             (wcB v fT pf) (weB v fT pf) (wwfB v fT pf) (wcohB v fT pf)).
  Qed.

  Definition wFam : kUFam k (ew A0 B0).
  Proof.
    unshelve refine (Build_UFam (lvl k) k (ew A0 B0) _ gW _ _ _).
    - intros v h pf; destruct h as [fT]; exact (wcode v fT pf).
    - intros v h pf; destruct h as [fT]; exact (wcode_sh v fT pf).
    - intros v h pf; destruct h as [fT]; exact (wcode_wf v fT pf).
    - intros v h pf v' h' pf'; destruct h as [fT]; destruct h' as [fT'].
      apply (buildW_ceq k
               v A0 B0 fT v' A0 B0 fT'
               (* the two shadows are layer-1 equal *)
               (ex_intro _ k (eqty_trans k v (ew A0 B0) v' (wcode_sh v fT pf)
                                (eqty_sym k v' (ew A0 B0) (wcode_sh v' fT' pf'))))
               (wEv v fT pf) (wEv v' fT' pf')
               (wcA v fT pf) (weA v fT pf) (wcB v fT pf) (weB v fT pf)
               (wcA v' fT' pf') (weA v' fT' pf') (wcB v' fT' pf') (weB v' fT' pf')).
      + (* the domains are equal *)
        apply uf_coh.
      + (* the codomains are equal at corresponding arguments *)
        intros u x u' y r.
        apply famCeq_all; apply cohB.
        apply (famTo_eqX FA A0 (wAccA v fT pf) (evalAg_refl A0) u x
                 FA A0 (wAccA v' fT' pf') (evalAg_refl A0) u' y);
          [apply uf_coh | exact r].
  Defined.
End WFam.

(* ------------------------------------------------------------------ *)
(* Two W families are EQUAL as soon as their components are: the      *)
(* shadows layer-1 equal, the domains equal, and the codomains equal at *)
(* related arguments.  This is what functionality at a W-type needs,   *)
(* and it is `buildW_ceq` with the two canonical instances' coherences *)
(* composed on either side.                                            *)
(* ------------------------------------------------------------------ *)

Lemma wFam_ceq (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
     kceq (kAt (FB u x)) (kAt (FB u' x')))
  (gW : eqty k (ew A0 B0) (ew A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
     kceq (kAt (FB' u x)) (kAt (FB' u' x')))
  (gW' : eqty k (ew A0' B0') (ew A0' B0'))
  (Hty : tyeq (ew A0 B0) (ew A0' B0'))
  (HA : kceq (kAt FA) (kAt FA'))
  (HB : forall u x u' x', kEqAt FA u x FA' u' x' ->
     kceq (kAt (FB u x)) (kAt (FB' u' x'))) :
  kceq (kAt (wFam k A0 B0 FA SB FB redB cohB gW))
       (kAt (wFam k A0' B0' FA' SB' FB' redB' cohB' gW')).
Proof.
  unfold kAt, uf_at, kAcc.
  generalize (uf_acc (wFam k A0' B0' FA' SB' FB' redB' cohB' gW')) as h'.
  generalize (uf_acc (wFam k A0 B0 FA SB FB redB cohB gW)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT'].
  apply (buildW_ceq k
           (ew A0 B0) A0 B0 fT (ew A0' B0') A0' B0' fT' Hty
           (wEv A0 B0 (ew A0 B0) fT (evalAg_refl _))
           (wEv A0' B0' (ew A0' B0') fT' (evalAg_refl _))
           (wcA k A0 B0 FA (ew A0 B0) fT (evalAg_refl _))
           (weA k A0 B0 FA (ew A0 B0) fT (evalAg_refl _))
           (wcB k A0 B0 FA SB FB redB (ew A0 B0) fT (evalAg_refl _))
           (weB k A0 B0 FA SB FB redB (ew A0 B0) fT (evalAg_refl _))
           (wcA k A0' B0' FA' (ew A0' B0') fT' (evalAg_refl _))
           (weA k A0' B0' FA' (ew A0' B0') fT' (evalAg_refl _))
           (wcB k A0' B0' FA' SB' FB' redB' (ew A0' B0') fT' (evalAg_refl _))
           (weB k A0' B0' FA' SB' FB' redB' (ew A0' B0') fT' (evalAg_refl _))).
  - (* the domains, through the two families' coherences *)
    eapply ktrU;
      [ exact (wwfA k A0 B0 FA (ew A0 B0) fT (evalAg_refl _))
      | exact (famAtWf FA) | exact (wwfA k A0' B0' FA' (ew A0' B0') fT' (evalAg_refl _))
      | apply uf_coh |].
    eapply ktrU;
      [ exact (famAtWf FA) | exact (famAtWf FA')
      | exact (wwfA k A0' B0' FA' (ew A0' B0') fT' (evalAg_refl _))
      | exact HA | apply knsymU; apply uf_coh ].
  - (* the codomains, at related arguments *)
    intros u x u' y r.
    eapply ktrU;
      [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) fT (evalAg_refl _) u x)
      | exact (famAtWf (FB u (wxc k A0 B0 FA (ew A0 B0) fT (evalAg_refl _) u x)))
      | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') fT' (evalAg_refl _) u' y)
      | apply wcB_at |].
    eapply ktrU;
      [ exact (famAtWf (FB u (wxc k A0 B0 FA (ew A0 B0) fT (evalAg_refl _) u x)))
      | exact (famAtWf (FB' u' (wxc k A0' B0' FA' (ew A0' B0') fT' (evalAg_refl _) u' y)))
      | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') fT' (evalAg_refl _) u' y)
      | | apply knsymU; apply wcB_at ].
    apply HB.
    apply (famTo_eqX FA A0 (wAccA A0 B0 (ew A0 B0) fT (evalAg_refl _))
             (evalAg_refl A0) u x
             FA' A0' (wAccA A0' B0' (ew A0' B0') fT' (evalAg_refl _))
             (evalAg_refl A0') u' y);
      [ exact (famCeq_all FA FA' HA _ _ _ _ _ _) | exact r ].
Qed.
