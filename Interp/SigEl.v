From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.SigFam
  Interp.Univ Interp.Env Interp.Elem Interp.PiEl.
From Stdlib Require Import Arith Lia.

(* The elements of a Sigma-family: the two projections, the pair, and the
   three laws that the conversion rules for Sigma need.

   A Sigma-code's decoding is a dependent PAIR over the elements of the
   DOMAIN CODE at the node the Sigma-code lives at, whereas the
   interpretation has elements of the domain FAMILY, so -- as at Pi -- the
   components travel through famTo/famFrom.  The difference from Pi is that
   here the realisers move too: the first component's realiser is `efst u`
   and the second's is `esnd u`, and at a pair those only REDUCE to the
   components' own realisers.  So the expansion closure of the decoding
   (Interp/Elem.v) does the work that the argument round trip does at Pi. *)

Lemma sxc_het (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (A0' B0' : etm) (FA' : kUFam k A0')
  v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
  v' (fT' : forall y, prec y v' -> Acc prec y) (pf' : evalAg v' (esig A0' B0'))
  u x u' y :
  hetC (scA k A0 B0 FA v fT pf) (scA k A0' B0' FA' v' fT' pf') u x u' y ->
  kRel FA FA' u (sxc k A0 B0 FA v fT pf u x) u' (sxc k A0' B0' FA' v' fT' pf' u' y).
Proof.
  intros H; unfold kRel, sxc, famTo.
  eapply hetC_trans; [apply hetC_sym, hetC_to |].
  eapply hetC_trans; [exact H | apply hetC_to].
Qed.

Lemma sigFam_iso (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gSig : eqty k (esig A0 B0) (esig A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (isoB' : forall u x u' x', kEqAt FA' u x u' x' -> iso (kAt (FB' u' x')) (kAt (FB' u x)))
  (gSig' : eqty k (esig A0' B0') (esig A0' B0'))
  (Hty : tyeq (esig A0 B0) (esig A0' B0'))
  (HA : iso (kAt FA) (kAt FA'))
  (HB : forall u x u' x', kRel FA FA' u x u' x' -> iso (kAt (FB u x)) (kAt (FB' u' x'))) :
  iso (kAt (sigFam k A0 B0 FA SB FB redB isoB gSig))
      (kAt (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')).
Proof.
  unfold kAt, uf_at, kAcc.
  generalize (uf_acc (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')) as h'.
  generalize (uf_acc (sigFam k A0 B0 FA SB FB redB isoB gSig)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT'].
  apply (buildSig_iso k
           (esig A0 B0) A0 B0 fT (sEv A0 B0 (esig A0 B0) fT (evalAg_refl _))
             (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl _))
             (seA k A0 B0 FA (esig A0 B0) fT (evalAg_refl _))
             (scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _))
             (seB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _))
             (sidB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl _))
             (sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT (evalAg_refl _))
           (esig A0' B0') A0' B0' fT' (sEv A0' B0' (esig A0' B0') fT' (evalAg_refl _))
             (scA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
             (seA k A0' B0' FA' (esig A0' B0') fT' (evalAg_refl _))
             (scB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _))
             (seB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _))
             (sidB k A0' B0' FA' SB' FB' redB' (esig A0' B0') fT' (evalAg_refl _))
             (sisoB k A0' B0' FA' SB' FB' redB' isoB' (esig A0' B0') fT' (evalAg_refl _))).
  - exact Hty.
  - (* the domains: the two families' instances, through their coherences *)
    eapply iso_trans; [apply uf_coh |].
    eapply iso_trans; [exact HA | apply uf_coh].
  - (* the codomains, at related arguments *)
    intros u x u' y Hxy.
    eapply iso_trans; [apply uf_coh |].
    eapply iso_trans; [| apply uf_coh].
    apply HB, sxc_het, Hxy.
Qed.

(* ------------------------------------------------------------------ *)
(* Elements: the two projections and the pair.                        *)
(* ------------------------------------------------------------------ *)

Lemma reds_fst_pair t u : reds (efst (epair t u)) t.
Proof. eapply reds_step; [apply red_fst | apply reds_refl]. Qed.

Lemma reds_snd_pair t u : reds (esnd (epair t u)) u.
Proof. eapply reds_step; [apply red_snd | apply reds_refl]. Qed.

(* The round trip the other way round: famFrom after famTo.  famTo_famFrom
   (Interp/PiEl.v) is the one at the family's canonical instance; this is the
   one at the instance, and the Sigma pair needs both. *)
Lemma famFrom_famTo {k u} (F : kUFam k u) v h pf w (z : kElC (uf_c F v h pf) w) :
  kEqC (uf_c F v h pf) w (famFrom F v h pf w (famTo F v h pf w z)) w z.
Proof.
  eapply kEqC_trans;
    [ apply kEqC_sym,
        (ctoK_fun (uf_c F v h pf) (kAt F) (uf_c F v h pf)
           (uf_coh F v h pf u (kAcc F) (evalAg_refl u))
           (uf_coh F u (kAcc F) (evalAg_refl u) v h pf)
           (uf_coh F v h pf v h pf) w z)
    | apply (uf_idp F v h pf (uf_coh F v h pf v h pf) w z) ].
Qed.

Section SigEl.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x))).
  Context (gSig : eqty k (esig A0 B0) (esig A0 B0)).

  Local Notation SF := (sigFam k A0 B0 FA SB FB redB isoB gSig).
  Local Notation SC v fT pf := (scode k A0 B0 FA SB FB redB isoB v fT pf).

  (* The projections at one instance.  The first component of the decoding is
     an element of the domain CODE, so it comes out through famTo; the second
     is an element of the codomain code at that very element, so nothing has
     to be transported. *)
  Definition sFst v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    u (x : kElC (SC v fT pf) u) : kElAt FA (efst u) :=
    sxc k A0 B0 FA v fT pf (efst u) (projT1 (Datatypes.fst (proj1_sig x))).

  Definition sSnd v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    u (x : kElC (SC v fT pf) u) : kElAt (FB (efst u) (sFst v fT pf u x)) (esnd u).
  Proof.
    refine (famTo (FB (efst u) (sFst v fT pf u x)) _ _ _ (esnd u) _).
    exact (projT2 (Datatypes.fst (proj1_sig x))).
  Defined.

  (* The pair at one instance.  Both realisers only REDUCE to the components'
     own, so the expansion closure of the decoding moves them, and one
     transport along isoB brings the second component to the codomain instance
     that the expanded first component names. *)
  Definition sPairFst v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    wa wb (x : kElAt FA wa)
    : kElC (scA k A0 B0 FA v fT pf) (efst (epair wa wb)) :=
    se_exp (kexp k _) (scA k A0 B0 FA v fT pf) (efst (epair wa wb)) wa
      (reds_fst_pair wa wb)
      (famFrom FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0) wa x).

  Lemma sPairFst_rel v fT pf wa wb (x : kElAt FA wa) :
    kEqAt FA (efst (epair wa wb))
      (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) (sPairFst v fT pf wa wb x)) wa x.
  Proof.
    eapply kEqAt_trans;
      [ apply (famTo_eq FA A0 (sAcc A0 B0 v fT pf) (evalAg_refl A0));
        apply (se_exp_rel (kexp k _))
      | apply famTo_famFrom ].
  Qed.

  Definition sPair v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) (g : Good v (epair wa wb))
    : kElC (SC v fT pf) (epair wa wb).
  Proof.
    refine (mkSigEl k _ v A0 B0 _
              (placeSDom k v A0 B0 fT (sEv A0 B0 v fT pf) (scA k A0 B0 FA v fT pf))
              _ _ _ _ _ (epair wa wb) (sPairFst v fT pf wa wb x) _ g).
    refine (famFrom (FB (efst (epair wa wb))
                        (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                           (sPairFst v fT pf wa wb x))) _ _ _ (esnd (epair wa wb)) _).
    refine (famExp _ (esnd (epair wa wb)) wb (reds_snd_pair wa wb) _).
    exact (ctoK (kAt (FB wa x)) _
             (isoB (efst (epair wa wb))
                (sxc k A0 B0 FA v fT pf (efst (epair wa wb)) (sPairFst v fT pf wa wb x))
                wa x (sPairFst_rel v fT pf wa wb x)) wb y).
  Defined.

  (* And at the canonical instance, which is the one the interpretation uses.
     The two projections are packed into one definition so that a single
     destruction of the accessibility proof serves both -- sigSnd's TYPE
     mentions sigFst, so they cannot be introduced separately. *)
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

  (* The raw second component and the one sSnd returns are heterogeneously
     related: sSnd is famTo, and famTo IS a canonical transport. *)
  Lemma sSnd_het v (fT : forall y, prec y v -> Acc prec y) (pf : evalAg v (esig A0 B0))
    u (x : kElC (SC v fT pf) u) :
    hetC (scB k A0 B0 FA SB FB redB v fT pf (efst u)
            (projT1 (Datatypes.fst (proj1_sig x))))
         (kAt (FB (efst u) (sFst v fT pf u x)))
         (esnd u) (projT2 (Datatypes.fst (proj1_sig x)))
         (esnd u) (sSnd v fT pf u x).
  Proof. unfold sSnd, famTo; apply hetC_to. Qed.

  Lemma sigGood u (x : kElAt SF u) : Good (esig A0 B0) u.
  Proof.
    revert x; unfold kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x.
    exact (Datatypes.snd (proj1_sig x)).
  Qed.

  (* ---- the two projections respect the equality ---- *)

  Lemma sigFst_eq u (x : kElAt SF u) u' (x' : kElAt SF u') :
    kEqAt SF u x u' x' ->
    kEqAt FA (efst u) (sigFst u x) (efst u') (sigFst u' x').
  Proof.
    revert x x'; unfold sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x x' H.
    destruct H as [[r E] _].
    apply (famTo_eq FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0)))
             (evalAg_refl A0)).
    exact r.
  Qed.

  Lemma sigSnd_eq u (x : kElAt SF u) u' (x' : kElAt SF u') :
    kEqAt SF u x u' x' ->
    kRel (FB (efst u) (sigFst u x)) (FB (efst u') (sigFst u' x'))
         (esnd u) (sigSnd u x) (esnd u') (sigSnd u' x').
  Proof.
    revert x x'; unfold kRel, sigSnd, sigFst, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x x' H.
    pose proof H as H0; destruct H as [[r E] [[r' E'] _]].
    eapply hetC_trans; [apply hetC_sym; apply sSnd_het |].
    eapply hetC_trans; [| apply sSnd_het].
    apply hetC_sym.
    exists (sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT
              (evalAg_refl (esig A0 B0)) _ _ _ _ r).
    apply kEqC_sym; exact E.
  Qed.

  (* The second component the pair carries is heterogeneously the one it was
     built from: the expansion of the realiser and the transport along isoB
     are both identities of the heterogeneous relation. *)
  Lemma sPair_snd_het v (fT : forall y, prec y v -> Acc prec y)
    (pf : evalAg v (esig A0 B0)) wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb)
    (g : Good v (epair wa wb)) :
    hetC (kAt (FB wa x))
         (scB k A0 B0 FA SB FB redB v fT pf (efst (epair wa wb))
            (sPairFst v fT pf wa wb x))
         wb y (esnd (epair wa wb))
         (projT2 (Datatypes.fst (proj1_sig (sPair v fT pf wa wb x y g)))).
  Proof.
    unfold sPair, mkSigEl; cbn [proj1_sig Datatypes.fst projT2].
    unfold famFrom.
    eapply hetC_trans;
      [ eapply hetC_eq_r;
          [ apply hetC_to
          | apply kEqC_sym;
            apply (famExp_rel (FB (efst (epair wa wb))
                     (sxc k A0 B0 FA v fT pf (efst (epair wa wb))
                        (sPairFst v fT pf wa wb x)))) ]
      | apply hetC_to ].
  Qed.

  (* ---- the two beta laws: the projections of a pair are its components ---- *)

  Lemma sigFst_pair wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) g :
    kEqAt FA (efst (epair wa wb)) (sigFst (epair wa wb) (sigPair wa wb x y g)) wa x.
  Proof.
    unfold sigFst, sigEl, sigPair, kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT].
    apply sPairFst_rel.
  Qed.

  Lemma sigSnd_pair wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) g :
    kRel (FB (efst (epair wa wb)) (sigFst (epair wa wb) (sigPair wa wb x y g))) (FB wa x)
         (esnd (epair wa wb)) (sigSnd (epair wa wb) (sigPair wa wb x y g)) wb y.
  Proof.
    unfold kRel, sigSnd, sigFst, sigEl, sigPair, kElAt at 1, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT].
    eapply hetC_eq_l; [ apply famTo_famFrom |].
    eapply hetC_eq_l; [ apply famExp_rel |].
    apply hetC_sym; apply hetC_to.
  Qed.

  (* ---- surjective pairing.  The layer-1 facts -- that the pair of the
     projections realises the type and is related to the subject -- come from
     Layer1/Elim.v's Rel_sig_intro/elim, so they are hypotheses. ---- *)
  Lemma sigPair_surj u (x : kElAt SF u)
    (g : Good (esig A0 B0) (epair (efst u) (esnd u)))
    (gr : Rel (esig A0 B0) (epair (efst u) (esnd u)) u) :
    kEqAt SF (epair (efst u) (esnd u)) (sigPair (efst u) (esnd u) (sigFst u x) (sigSnd u x) g) u x.
  Proof.
    revert g; revert x.
    unfold sigPair, sigFst, sigSnd, sigEl, kEqAt, kElAt at 1 2, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros x g.
    assert (r : kEqC (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair (efst u) (esnd u))) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)) (efst u) (projT1 (Datatypes.fst (proj1_sig x)))).
    { eapply kEqC_trans;
        [ apply (se_exp_rel (kexp k _) (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair (efst u) (esnd u))) (efst u)
                   (reds_fst_pair (efst u) (esnd u)))
        | apply (famFrom_famTo FA A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (evalAg_refl A0)) ]. }
    assert (Hhet : hetC ((scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst u) (projT1 (Datatypes.fst (proj1_sig x)))) ((scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair (efst u) (esnd u))) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)))
                        (esnd u) (projT2 (Datatypes.fst (proj1_sig x))) (esnd (epair (efst u) (esnd u)))
                        (projT2 (Datatypes.fst (proj1_sig
                           (sPair (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x) (sSnd (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x) g))))).
    { eapply hetC_trans;
        [ apply (sSnd_het (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)
        | apply (sPair_snd_het (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x) (sSnd (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x) g) ]. }
    split; [| split; [| exact gr]].
    - exists r.
      apply kEqC_sym.
      apply (hetC_at _ _ ((sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair (efst u) (esnd u))) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)) (efst u) (projT1 (Datatypes.fst (proj1_sig x))) r)).
      exact Hhet.
    - exists (kEqC_sym (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) _ _ _ _ r).
      apply kEqC_sym.
      apply (hetC_at _ _ ((sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst u) (projT1 (Datatypes.fst (proj1_sig x))) (efst (epair (efst u) (esnd u))) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) (efst u) (esnd u) (sFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) u x)) (kEqC_sym (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) _ _ _ _ r))).
      apply hetC_sym; exact Hhet.
  Qed.

  (* ---- congruence: pairs of related components are related ---- *)
  Lemma sigPair_eq wa wb (x : kElAt FA wa) (y : kElAt (FB wa x) wb) (g : Good (esig A0 B0) (epair wa wb))
    wa' wb' (x' : kElAt FA wa') (y' : kElAt (FB wa' x') wb') (g' : Good (esig A0 B0) (epair wa' wb')) :
    Rel (esig A0 B0) (epair wa wb) (epair wa' wb') ->
    kEqAt FA wa x wa' x' -> kRel (FB wa x) (FB wa' x') wb y wb' y' ->
    kEqAt SF (epair wa wb) (sigPair wa wb x y g) (epair wa' wb') (sigPair wa' wb' x' y' g').
  Proof.
    unfold sigPair, kEqAt, kAt, uf_at, kAcc.
    generalize (uf_acc SF) as h; intros h; destruct h as [fT]; intros gr Hx Hy.
    assert (r : kEqC (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa wb)) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x) (efst (epair wa' wb')) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x')).
    { eapply kEqC_trans;
        [ apply (se_exp_rel (kexp k _) (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa wb)) wa (reds_fst_pair wa wb)) |].
      eapply kEqC_trans;
        [ apply (ctoK_eq (kAt FA) _ (uf_coh FA A0 (kAcc FA) (evalAg_refl A0)
                   A0 (sAcc A0 B0 (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (evalAg_refl A0)) wa x wa' x' Hx)
        | apply kEqC_sym;
          apply (se_exp_rel (kexp k _) (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa' wb')) wa' (reds_fst_pair wa' wb')) ]. }
    assert (Hhet : hetC ((scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa wb)) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x)) ((scB k A0 B0 FA SB FB redB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa' wb')) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x'))
                        (esnd (epair wa wb))
                        (projT2 (Datatypes.fst (proj1_sig
                           (sPair (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x y g))))
                        (esnd (epair wa' wb'))
                        (projT2 (Datatypes.fst (proj1_sig
                           (sPair (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x' y' g'))))).
    { eapply hetC_trans;
        [ apply hetC_sym; apply (sPair_snd_het (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x y g) |].
      eapply hetC_trans;
        [ exact Hy | apply (sPair_snd_het (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x' y' g') ]. }
    split; [| split; [| exact gr]].
    - exists r.
      apply kEqC_sym.
      apply (hetC_at _ _ ((sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa wb)) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x) (efst (epair wa' wb')) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x') r)).
      apply hetC_sym; exact Hhet.
    - exists (kEqC_sym (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) _ _ _ _ r).
      apply kEqC_sym.
      apply (hetC_at _ _ ((sisoB k A0 B0 FA SB FB redB isoB (esig A0 B0) fT (evalAg_refl (esig A0 B0))) (efst (epair wa' wb')) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa' wb' x') (efst (epair wa wb)) (sPairFst (esig A0 B0) fT (evalAg_refl (esig A0 B0)) wa wb x)
                            (kEqC_sym (scA k A0 B0 FA (esig A0 B0) fT (evalAg_refl (esig A0 B0))) _ _ _ _ r))).
      exact Hhet.
  Qed.
End SigEl.

(* The transport at a Sigma-code is componentwise -- toRefine's r_sig branch
   pushes the first component forward with hj_to and needs no pullback -- so the
   first projection of a transported pair IS the transport of the first
   projection.  That is what functionality on terms needs at fst: it lets the
   HETEROGENEOUS comparison of two readings factor through the homogeneous
   sigFst_eq at the second reading's family. *)
Lemma sigFst_to (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gSig : eqty k (esig A0 B0) (esig A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (isoB' : forall u x u' x', kEqAt FA' u x u' x' -> iso (kAt (FB' u' x')) (kAt (FB' u x)))
  (gSig' : eqty k (esig A0' B0') (esig A0' B0')) :
  forall (P : iso (kAt (sigFam k A0 B0 FA SB FB redB isoB gSig))
                  (kAt (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')))
    u (x : kElAt (sigFam k A0 B0 FA SB FB redB isoB gSig) u),
  kRel FA FA' (efst u) (sigFst k A0 B0 FA SB FB redB isoB gSig u x)
              (efst u) (sigFst k A0' B0' FA' SB' FB' redB' isoB' gSig' u
                          (ctoK _ _ P u x)).
Proof.
  unfold sigFst, sigEl, ctoK, kElAt at 1 2, kAt, uf_at, kAcc.
  generalize (uf_acc (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')) as h'.
  generalize (uf_acc (sigFam k A0 B0 FA SB FB redB isoB gSig)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT']; intros P u x.
  apply sxc_het.
  apply hetC_to.
Qed.

(* The second projection of a transported pair is the transport of the second
   projection, along the codomains' isomorphism at the transported first
   component.  Unlike sigFst_to this cannot be left to `apply`: the codomain
   codes depend on the transported first component, so the unifier would have to
   reduce `cto` at a Brouwer tree built from rk.  The three-step recipe instead
   INSTANTIATES the componentwise law: cto_refine brings the code-level
   transport down to the refinement level, toRefine_sig_snd is the law there
   (reflexivity, because the two stages are variables), and place_to_het undoes
   the placement.  Nothing is reduced. *)
Lemma sigSnd_to (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gSig : eqty k (esig A0 B0) (esig A0 B0))
  (A0' B0' : etm) (FA' : kUFam k A0')
  (SB' : forall u, kElAt FA' u -> etm)
  (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
  (redB' : forall u x, reds (eapp B0' u) (SB' u x))
  (isoB' : forall u x u' x', kEqAt FA' u x u' x' -> iso (kAt (FB' u' x')) (kAt (FB' u x)))
  (gSig' : eqty k (esig A0' B0') (esig A0' B0')) :
  forall (P : iso (kAt (sigFam k A0 B0 FA SB FB redB isoB gSig))
                  (kAt (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')))
    u (x : kElAt (sigFam k A0 B0 FA SB FB redB isoB gSig) u),
  kRel (FB (efst u) (sigFst k A0 B0 FA SB FB redB isoB gSig u x))
       (FB' (efst u) (sigFst k A0' B0' FA' SB' FB' redB' isoB' gSig' u (ctoK _ _ P u x)))
       (esnd u) (sigSnd k A0 B0 FA SB FB redB isoB gSig u x)
       (esnd u) (sigSnd k A0' B0' FA' SB' FB' redB' isoB' gSig' u (ctoK _ _ P u x)).
Proof.
  unfold sigSnd, sigFst, sigEl, ctoK, kElAt at 1 2, kAt, uf_at, kAcc.
  generalize (uf_acc (sigFam k A0' B0' FA' SB' FB' redB' isoB' gSig')) as h'.
  generalize (uf_acc (sigFam k A0 B0 FA SB FB redB isoB gSig)) as h.
  intros h h'; destruct h as [fT]; destruct h' as [fT']; intros P u x.
  eapply hetC_trans; [apply hetC_sym; apply sSnd_het |].
  eapply hetC_trans; [| apply sSnd_het].
  cbn [uf_c sigFam] in *.
  rewrite (cto_refine (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)).
  unfold scode, mkCode, buildSig, mkSig, kstage, hT; cbn [projT2].
  rewrite toRefine_sig_snd.
  unfold sbb, placeSCod; rewrite place_to_het.
  apply hetC_to.
Qed.
