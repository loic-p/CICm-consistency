From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* The Pi family: the semantic value of a Pi-type, assembled from the semantic
   values of its domain and of its codomain instances.  This is the clause of
   the interpretation at Pi, stripped of the syntax.

   The layer-1 goodness of the Pi-type is a hypothesis: layer 1's Pi clause
   asks for the codomain to be reducible at EVERY pair of related realisers,
   whereas the semantic data only covers realisers that carry an element, so
   it cannot be recovered here.  It comes from the layer-1 fundamental lemma. *)

Section PiFam.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x))).
  Context (gPi : eqty k (epi A0 B0) (epi A0 B0)).

  (* The data at one instance of the family.  All three of v, fT and pf are
     explicit arguments rather than section variables, so that the argument
     lists of these auxiliary definitions are predictable. *)
  Definition pEv v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (epi A0 B0)) : eval v (epi A0 B0) :=
    pf (epi A0 B0) (eval_whnf _ (whnf_pi A0 B0)).

  Definition pAcc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : Acc prec A0 := accAt v fT (pdom v A0 B0 (pEv v fT pf)).

  Definition pcA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : Code k (domNode v A0 B0 fT (pEv v fT pf)) :=
    uf_c FA A0 (pAcc v fT pf) (evalAg_refl A0).

  Definition peA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : tyeq (projT1 (pcA v fT pf)) A0 :=
    ex_intro _ k (uf_sh FA A0 (pAcc v fT pf) (evalAg_refl A0)).

  Definition pidA v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : LIdP (pcA v fT pf) :=
    uf_idp FA A0 (pAcc v fT pf) (evalAg_refl A0).

  Definition pxc v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u
    (x : kElS (placeDom k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)) u) : kElAt FA u :=
    famTo FA A0 (pAcc v fT pf) (evalAg_refl A0) u x.

  Definition pag u (x : kElAt FA u) : evalAg (eapp B0 u) (SB u x) :=
    fun w H => eval_reds _ _ _ (redB u x) H.

  Definition pcB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u x
    : Code k (codNode v A0 B0 fT (pEv v fT pf) u
                (argGood k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf) u x)) :=
    uf_c (FB u (pxc v fT pf u x)) (eapp B0 u)
         (accAt v fT (pcod v A0 B0 (pEv v fT pf) u
                        (argGood k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf) u x)))
         (pag u (pxc v fT pf u x)).

  Definition peB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u x : tyeq (projT1 (pcB v fT pf u x)) (eapp B0 u).
  Proof.
    exists k; eapply eqty_exp; [apply reds_refl | apply redB | apply uf_sh].
  Defined.

  Definition pidB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u x : LIdP (pcB v fT pf u x) :=
    uf_idp (FB u (pxc v fT pf u x)) _ _ _.

  Definition pisoB v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) u x u' x'
    (r : kEqS (placeDom k v A0 B0 fT (pEv v fT pf) (pcA v fT pf)) u x u' x')
    : iso (pcB v fT pf u' x') (pcB v fT pf u x).
  Proof.
    eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)); [ apply uf_coh |].
    eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
      [ apply (isoB u (pxc v fT pf u x) u' (pxc v fT pf u' x'));
        apply famTo_eq; exact r
      | apply uf_coh ].
  Defined.

  Definition pcode v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : Code k (rk v (hT v fT)) :=
    mkCode (buildPi k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf)
              (pcB v fT pf) (peB v fT pf) (pidB v fT pf) (pisoB v fT pf)).

  Lemma pcode_sh v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : eqty k v (epi A0 B0).
  Proof. eapply eqty_exp; [exact (proj1 (pEv v fT pf)) | apply reds_refl | exact gPi]. Qed.

  Lemma pcode_idp v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (epi A0 B0)) : LIdP (pcode v fT pf).
  Proof.
    exact (buildPi_idp k v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf) (pidA v fT pf)
             (pcB v fT pf) (peB v fT pf) (pidB v fT pf) (pisoB v fT pf)).
  Qed.

  Definition piFam : kUFam k (epi A0 B0).
  Proof.
    unshelve refine (Build_UFam (lvl k) k (epi A0 B0) _ gPi _ _ _).
    - intros v h pf; destruct h as [fT]; exact (pcode v fT pf).
    - intros v h pf; destruct h as [fT]; exact (pcode_sh v fT pf).
    - intros v h pf v' h' pf'; destruct h as [fT]; destruct h' as [fT'].
      apply (buildPi_iso k
               v A0 B0 fT (pEv v fT pf) (pcA v fT pf) (peA v fT pf)
                 (pcB v fT pf) (peB v fT pf) (pidB v fT pf) (pisoB v fT pf)
               v' A0 B0 fT' (pEv v' fT' pf') (pcA v' fT' pf') (peA v' fT' pf')
                 (pcB v' fT' pf') (peB v' fT' pf') (pidB v' fT' pf') (pisoB v' fT' pf')).
      + (* the two shadows are layer-1 equal *)
        exists k; eapply eqty_trans;
          [ exact (pcode_sh v fT pf) | apply eqty_sym; exact (pcode_sh v' fT' pf') ].
      + (* the domains are isomorphic *)
        apply uf_coh.
      + (* the codomains are isomorphic at corresponding arguments *)
        intros u x u' y [P HP].
        eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
          [ apply uf_coh |].
        eapply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k));
          [ | apply uf_coh ].
        apply (isoB u' (pxc v' fT' pf' u' y) u (pxc v fT pf u x)).
        apply kEqAt_sym.
        exact (famTo_het FA A0 (pAcc v fT pf) (evalAg_refl A0)
                 A0 (pAcc v' fT' pf') (evalAg_refl A0) u x u' y P HP).
    - intros v h pf; destruct h as [fT]; exact (pcode_idp v fT pf).
  Defined.
End PiFam.
