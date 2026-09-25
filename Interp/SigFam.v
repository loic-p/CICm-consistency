From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The Sigma family: the semantic value of a Sigma-type, assembled from the semantic
   values of its domain and of its codomain instances.  This is the clause of
   the interpretation at Sigma, stripped of the syntax.

   The layer-1 goodness of the Sigma-type is a hypothesis: layer 1's Sigma clause
   asks for the codomain to be reducible at EVERY pair of related realisers,
   whereas the semantic data only covers realisers that carry an element, so
   it cannot be recovered here.  It comes from the layer-1 fundamental lemma. *)

Section SigFam.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x))).
  Context (gSig : eqty k (esig A0 B0) (esig A0 B0)).

  (* The data at one instance of the family.  All three of v, fT and pf are
     explicit arguments rather than section variables, so that the argument
     lists of these auxiliary definitions are predictable. *)
  Definition sEv v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) : eval v (esig A0 B0) :=
    pf (esig A0 B0) (eval_whnf _ (whnf_sig A0 B0)).

  Definition sAcc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : Acc prec A0 := accAt v fT (sdom v A0 B0 (sEv v fT pf)).

  Definition scA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : Code k (sdomNode v A0 B0 fT (sEv v fT pf)) :=
    uf_c FA A0 (sAcc v fT pf) (evalAg_refl A0).

  Definition seA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : tyeq (projT1 (scA v fT pf)) A0 :=
    ex_intro _ k (uf_sh FA A0 (sAcc v fT pf) (evalAg_refl A0)).

  Definition sidA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : LIdP (scA v fT pf) :=
    uf_idp FA A0 (sAcc v fT pf) (evalAg_refl A0).

  Definition sxc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u
    (x : kElS (placeSDom k v A0 B0 fT (sEv v fT pf) (scA v fT pf)) u) : kElAt FA u :=
    famTo FA A0 (sAcc v fT pf) (evalAg_refl A0) u x.

  Definition sag u (x : kElAt FA u) : evalAg (eapp B0 u) (SB u x) :=
    fun w H => eval_reds _ _ _ (redB u x) H.

  Definition scB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u x
    : Code k (scodNode v A0 B0 fT (sEv v fT pf) u
                (sargGood k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf) u x)) :=
    uf_c (FB u (sxc v fT pf u x)) (eapp B0 u)
         (accAt v fT (scod v A0 B0 (sEv v fT pf) u
                        (sargGood k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf) u x)))
         (sag u (sxc v fT pf u x)).

  Definition seB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u x : tyeq (projT1 (scB v fT pf u x)) (eapp B0 u).
  Proof.
    exists k; eapply eqty_exp; [apply reds_refl | apply redB | apply uf_sh].
  Defined.

  Definition sidB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u x : LIdP (scB v fT pf u x) :=
    uf_idp (FB u (sxc v fT pf u x)) _ _ _.

  Definition sisoB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) u x u' x'
    (r : kEqS (placeSDom k v A0 B0 fT (sEv v fT pf) (scA v fT pf)) u x u' x')
    : iso (scB v fT pf u' x') (scB v fT pf u x).
  Proof.
    eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)); [ apply uf_coh |].
    eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
      [ apply (isoB u (sxc v fT pf u x) u' (sxc v fT pf u' x'));
        apply famTo_eq; exact r
      | apply uf_coh ].
  Defined.

  Definition scode v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : Code k (rk v (hT v fT)) :=
    mkCode (buildSig k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf)
              (scB v fT pf) (seB v fT pf) (sidB v fT pf) (sisoB v fT pf)).

  Lemma scode_sh v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : eqty k v (esig A0 B0).
  Proof. eapply eqty_exp; [exact (proj1 (sEv v fT pf)) | apply reds_refl | exact gSig]. Qed.

  Lemma scode_idp v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0)) : LIdP (scode v fT pf).
  Proof.
    exact (buildSig_idp k v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf) (sidA v fT pf)
             (scB v fT pf) (seB v fT pf) (sidB v fT pf) (sisoB v fT pf)).
  Qed.

  Definition sigFam : kUFam k (esig A0 B0).
  Proof.
    unshelve refine (Build_UFam (lvl k) k (esig A0 B0) _ gSig _ _ _).
    - intros v h pf; destruct h as [fT]; exact (scode v fT pf).
    - intros v h pf; destruct h as [fT]; exact (scode_sh v fT pf).
    - intros v h pf v' h' pf'; destruct h as [fT]; destruct h' as [fT'].
      apply (buildSig_iso k
               v A0 B0 fT (sEv v fT pf) (scA v fT pf) (seA v fT pf)
                 (scB v fT pf) (seB v fT pf) (sidB v fT pf) (sisoB v fT pf)
               v' A0 B0 fT' (sEv v' fT' pf') (scA v' fT' pf') (seA v' fT' pf')
                 (scB v' fT' pf') (seB v' fT' pf') (sidB v' fT' pf') (sisoB v' fT' pf')).
      + (* the two shadows are layer-1 equal *)
        exists k; eapply eqty_trans;
          [ exact (scode_sh v fT pf) | apply eqty_sym; exact (scode_sh v' fT' pf') ].
      + (* the domains are isomorphic *)
        apply uf_coh.
      + (* the codomains are isomorphic at corresponding arguments *)
        intros u x u' y [P HP].
        eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
          [ apply uf_coh |].
        eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
          [ | apply uf_coh ].
        apply (isoB u' (sxc v' fT' pf' u' y) u (sxc v fT pf u x)).
        apply kEqAt_sym.
        exact (famTo_het FA A0 (sAcc v fT pf) (evalAg_refl A0)
                 A0 (sAcc v' fT' pf') (evalAg_refl A0) u x u' y P HP).
    - intros v h pf; destruct h as [fT]; exact (scode_idp v fT pf).
  Defined.
End SigFam.
