From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.WFam
  Interp.Univ Interp.Env Interp.Elem Interp.PiEl.
From Stdlib Require Import Arith Lia.

(* The elements of a W-family: `sup`, and the recursor.

   New in v2 -- v1's calculus had no W -- and it is the one place where the
   interpretation meets an INDUCTIVE decoding: an element of a W-code is a
   tree together with the statement that its branching is hereditarily
   extensional, which is `WRel t t`.

   The shape is the Pi one twice over.  A tree's branches are indexed by
   elements of the branching code at the node the W-code lives at, whereas the
   interpretation has elements of the branching FAMILY, so an index goes in
   through `famFrom` and comes back through `famTo` exactly as an argument
   does at Pi (`wIdx` below is `pArg` with the coercion along `cohB` folded
   in).  And the recursor is `semrec` with the recursion on the TREE rather
   than on a numeral: each step moves the step function's value to the motive
   instance the goal asks for and expands the realiser along the computation
   rule, which is one `moveTo`. *)

(* The layer-1 fact a tree node carries: its branching function takes related
   indices to related subtree realisers.  It is inside `Good T w` -- layer 1's
   W-relation at a sup says exactly that -- and `Rel_w_elim` is how one gets it
   out, with the stuck case refuted because a sup is a value. *)
Lemma Rel_w_br2 T A0 B0 : Good_ty T -> eval T (ew A0 B0) ->
  forall x y, Rel T x y ->
  forall a0 f0 a1 f1, eval x (esup a0 f0) -> eval y (esup a1 f1) ->
  forall u u', Rel (eapp B0 a0) u u' -> Rel T (eapp f0 u) (eapp f1 u').
Proof.
  intros gT eT.
  apply (Rel_w_elim T A0 B0
           (fun x y => forall a0 f0 a1 f1,
              eval x (esup a0 f0) -> eval y (esup a1 f1) ->
              forall u u', Rel (eapp B0 a0) u u' -> Rel T (eapp f0 u) (eapp f1 u'))
           gT eT).
  - intros w1 w1' a' a'' f' f'' e1 e1' H1 Ha Hbr _ a0 f0 a1 f1 e0 e0' u u' Hu.
    assert (E0 := eval_det _ _ _ e0 e1); injection E0; intros; subst a0 f0.
    assert (E1 := eval_det _ _ _ e0' e1'); injection E1; intros; subst a1 f1.
    apply Hbr; exact Hu.
  - intros w1 w1' H1 Hs Hs' a0 f0 a1 f1 e0 e0' u u' Hu.
    exfalso; exact (stuckv_not_value w1 (esup a0 f0) Hs e0 (v_sup a0 f0)).
Qed.

Lemma Rel_w_br T A0 B0 w a f :
  Good_ty T -> eval T (ew A0 B0) -> Rel T w w -> eval w (esup a f) ->
  forall u u', Rel (eapp B0 a) u u' -> Rel T (eapp f u) (eapp f u').
Proof.
  intros gT eT Hw ew0.
  exact (Rel_w_br2 T A0 B0 gT eT w w Hw a f a f ew0 ew0).
Qed.

Section WEl.
  Context (k : nat) (A0 B0 : etm).
  Context (FA : kUFam k A0).
  Context (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x)).
  Context (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x'))).
  Context (gW : eqty k (ew A0 B0) (ew A0 B0)).

  Local Notation WF := (wFam k A0 B0 FA SB FB redB cohB gW).

  (* ---- reading a placed branch index in the branching family ---- *)

  Section Inst.
    Context (v : etm) (fT : forall y, prec y v -> Acc prec y)
            (pf : evalAg v (ew A0 B0)).

    Local Notation aa := (placeWDom k v A0 B0 fT (wEv A0 B0 v fT pf)
                            (wcA k A0 B0 FA v fT pf)).

    (* the label, placed *)
    Definition wLab u0 (z : kElAt FA u0) : kElS aa u0 :=
      famFrom FA A0 (wAccA A0 B0 v fT pf) (evalAg_refl A0) u0 z.

    Lemma wLab_eq u0 (z : kElAt FA u0) :
      kEqAt FA u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z)) FA u0 z.
    Proof. unfold wLab, wxc; apply famTo_famFrom. Qed.

    (* a branch index of the placed tree, read in the branching family *)
    Definition wIdx u0 (z : kElAt FA u0) v0
      (y : kElC (wcB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z)) v0)
      : kElAt (FB u0 z) v0 :=
      kto (kAt (FB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z)))) (kAt (FB u0 z))
        (famAtWf (FB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z)))) (famAtWf (FB u0 z))
        (cohB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z)) u0 z (wLab_eq u0 z)) v0
        (famTo (FB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z))) (eapp B0 u0) _ _ v0 y).

    Lemma wIdx_rel u0 (z : kElAt FA u0) v0 y :
      kcel (wcB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z)) v0 y
           (kAt (FB u0 z)) v0 (wIdx u0 z v0 y).
    Proof.
      unfold wIdx.
      eapply ktrE;
        [ exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (famAtWf (FB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z))))
        | exact (famAtWf (FB u0 z))
        | exact (wcB_at k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | apply famTo_coh
        | apply kto_coh ].
    Qed.

    (* the instance the branches live at is equal to the canonical code of the
       branching family at the label *)
    Lemma wcB_ceq u0 (z : kElAt FA u0) :
      kceq (wcB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z)) (kAt (FB u0 z)).
    Proof.
      eapply ktrU;
        [ exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (famAtWf (FB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z))))
        | exact (famAtWf (FB u0 z))
        | exact (wcB_at k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (cohB u0 (wxc k A0 B0 FA v fT pf u0 (wLab u0 z)) u0 z (wLab_eq u0 z)) ].
    Qed.

    (* ---- sup at one instance ---- *)

    Definition wSupI (u0 f : etm) (z : kElAt FA u0)
      (sub : forall v0 (y : kElAt (FB u0 z) v0),
               kElC (wcode k A0 B0 FA SB FB redB v fT pf) (eapp f v0))
      (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
          kcel (wcode k A0 B0 FA SB FB redB v fT pf) (eapp f v0) (sub v0 y)
               (wcode k A0 B0 FA SB FB redB v fT pf) (eapp f v0') (sub v0' y'))
      (gd : Good v (esup u0 f))
      : kElC (wcode k A0 B0 FA SB FB redB v fT pf) (esup u0 f).
    Proof.
      refine (mkWsup k (rk v (hT v fT)) v A0 B0 (wEv A0 B0 v fT pf)
                aa (wea_holds k v A0 B0 fT (wEv A0 B0 v fT pf)
                      (wcA k A0 B0 FA v fT pf) (weA k A0 B0 FA v fT pf))
                (wwfA k A0 B0 FA v fT pf)
                (wbb k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf)
                   (weA k A0 B0 FA v fT pf) (wcB k A0 B0 FA SB FB redB v fT pf))
                (web_holds k v A0 B0 fT (wEv A0 B0 v fT pf)
                   (wcA k A0 B0 FA v fT pf) (weA k A0 B0 FA v fT pf)
                   (wcB k A0 B0 FA SB FB redB v fT pf)
                   (weB k A0 B0 FA SB FB redB v fT pf))
                (esup u0 f) u0 f (wLab u0 z)
                (eval_whnf _ (or_introl (v_sup u0 f))) gd
                (fun v0 y => sub v0 (wIdx u0 z v0 y)) _).
      intros v0 y v0' y' Hy; apply subext.
      eapply ktrE;
        [ exact (famAtWf (FB u0 z))
        | exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (famAtWf (FB u0 z))
        | apply knsymU; exact (wcB_ceq u0 z)
        | apply knsym; exact (wIdx_rel u0 z v0 y) |].
      eapply ktrE;
        [ exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z))
        | exact (famAtWf (FB u0 z))
        | exact (proj2 (wwfB k A0 B0 FA SB FB redB v fT pf u0 (wLab u0 z)))
        | exact Hy
        | exact (wIdx_rel u0 z v0' y') ].
    Defined.

    (* ---- a tree at this instance, read as an element of the family ---- *)

    Definition wOf w (t : kWEl k (rk v (hT v fT)) v
                        (placeWDom k v A0 B0 fT (wEv A0 B0 v fT pf)
                           (wcA k A0 B0 FA v fT pf))
                        (wbb k v A0 B0 fT (wEv A0 B0 v fT pf)
                           (wcA k A0 B0 FA v fT pf) (weA k A0 B0 FA v fT pf)
                           (wcB k A0 B0 FA SB FB redB v fT pf)) w)
      (tr : kWRel k (rk v (hT v fT)) v _ _ t t) (gd : Good v w) : kElAt WF w :=
      famTo WF v (Acc_intro v fT) pf w
        (mkWel k (rk v (hT v fT)) v A0 B0 (wEv A0 B0 v fT pf) _
           (wea_holds k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf)
              (weA k A0 B0 FA v fT pf)) _
           (web_holds k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf)
              (weA k A0 B0 FA v fT pf) (wcB k A0 B0 FA SB FB redB v fT pf)
              (weB k A0 B0 FA SB FB redB v fT pf))
           w t tr gd).

    (* two trees whose relation holds give related elements *)
    Lemma wOf_eq w t tr gd w' t' tr' gd' :
      kWRel k (rk v (hT v fT)) v _ _ t t' ->
      Rel v w w' -> kEqAt WF w (wOf w t tr gd) WF w' (wOf w' t' tr' gd').
    Proof.
      intros H HR; apply famTo_eq.
      apply (mkW_eq k (rk v (hT v fT)) v A0 B0 (wEv A0 B0 v fT pf)
               (ex_intro _ k (eqty_refl_l k v (ew A0 B0)
                                (wcode_sh k A0 B0 gW v fT pf))));
        [ exact H | exact HR ].
    Qed.

    (* ---- the branches of a tree node, read in the family ---- *)

    Local Notation bb u0 z := (wbb k v A0 B0 fT (wEv A0 B0 v fT pf)
                                 (wcA k A0 B0 FA v fT pf) (weA k A0 B0 FA v fT pf)
                                 (wcB k A0 B0 FA SB FB redB v fT pf) u0 z).

    (* a placed index, from a family-level one at the tree's own label *)
    Definition wIdxBack u0 (z : kElS aa u0) v0
      (y : kElAt (FB u0 (wxc k A0 B0 FA v fT pf u0 z)) v0) : kElS (bb u0 z) v0 :=
      famFrom (FB u0 (wxc k A0 B0 FA v fT pf u0 z)) (eapp B0 u0) _ _ v0 y.

    Lemma wIdxBack_rel u0 (z : kElS aa u0) v0 y :
      kcel (kAt (FB u0 (wxc k A0 B0 FA v fT pf u0 z))) v0 y
           (wcB k A0 B0 FA SB FB redB v fT pf u0 z) v0 (wIdxBack u0 z v0 y).
    Proof. apply famFrom_coh. Qed.

    (* the branch elements of a node, and their extensionality *)
    Definition wBr u0 (z : kElS aa u0) (f : etm)
      (sub : forall v0, kElS (bb u0 z) v0 -> kWEl k (rk v (hT v fT)) v aa _ (eapp f v0))
      (trs : forall v0 y v0' y', kcEl (bb u0 z) v0 y (bb u0 z) v0' y' ->
          kWRel k (rk v (hT v fT)) v aa _ (sub v0 y) (sub v0' y'))
      v0 (y : kElAt (FB u0 (wxc k A0 B0 FA v fT pf u0 z)) v0)
      : kElC (wcode k A0 B0 FA SB FB redB v fT pf) (eapp f v0) :=
      mkWel k (rk v (hT v fT)) v A0 B0 (wEv A0 B0 v fT pf) aa
        (wea_holds k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf)
           (weA k A0 B0 FA v fT pf)) _
        (web_holds k v A0 B0 fT (wEv A0 B0 v fT pf) (wcA k A0 B0 FA v fT pf)
           (weA k A0 B0 FA v fT pf) (wcB k A0 B0 FA SB FB redB v fT pf)
           (weB k A0 B0 FA SB FB redB v fT pf))
        (eapp f v0) (sub v0 (wIdxBack u0 z v0 y))
        (trs v0 (wIdxBack u0 z v0 y) v0 (wIdxBack u0 z v0 y)
           (kselfE (bb u0 z) (wwfB k A0 B0 FA SB FB redB v fT pf u0 z) v0
              (wIdxBack u0 z v0 y)))
        (kWgood k (rk v (hT v fT)) v aa _ (sub v0 (wIdxBack u0 z v0 y))).

    (* the two index conversions compose to the identity, up to the equality:
       this is what reconciles a rebuilt sup with the node it came from *)
    Lemma wIdx_roundtrip u0 (z : kElS aa u0) v0
      (y : kElC (wcB k A0 B0 FA SB FB redB v fT pf u0
                   (wLab u0 (wxc k A0 B0 FA v fT pf u0 z))) v0) :
      kcel (wcB k A0 B0 FA SB FB redB v fT pf u0 z) v0
             (wIdxBack u0 z v0 (wIdx u0 (wxc k A0 B0 FA v fT pf u0 z) v0 y))
           (wcB k A0 B0 FA SB FB redB v fT pf u0
              (wLab u0 (wxc k A0 B0 FA v fT pf u0 z))) v0 y.
    Proof.
      eapply ktrE;
        [ exact (wwfB k A0 B0 FA SB FB redB v fT pf u0 z)
        | exact (famAtWf (FB u0 (wxc k A0 B0 FA v fT pf u0 z)))
        | exact (wwfB k A0 B0 FA SB FB redB v fT pf u0
                   (wLab u0 (wxc k A0 B0 FA v fT pf u0 z)))
        | exact (wcB_at k A0 B0 FA SB FB redB v fT pf u0 z)
        | apply knsym;
          exact (wIdxBack_rel u0 z v0 (wIdx u0 (wxc k A0 B0 FA v fT pf u0 z) v0 y))
        | apply knsym; exact (wIdx_rel u0 (wxc k A0 B0 FA v fT pf u0 z) v0 y) ].
    Qed.
  End Inst.



  (* ---- the canonical instance, with its accessibility proof in constructor
     form.                                                               ----

     `rk v h` only unfolds once h is an `Acc_intro`, so the W code's shape --
     and with it the tree structure of its elements -- is invisible at the
     canonical instance `uf_acc WF`.  Destructing that proof inside a lemma
     does not help: a statement that mentions `wSup` cannot then reduce it,
     because the destruction applies to a COPY.  So instead of destructing,
     rebuild: `Acc_intro _ (Acc_inv (kAcc WF))` is an accessibility proof of
     the same realiser, in constructor form, and the family's own coherence
     moves elements between the two instances.  Nothing below destructs an
     accessibility proof. *)

  Definition wfC : forall y, prec y (ew A0 B0) -> Acc prec y :=
    fun y hy => Acc_inv (kAcc WF) hy.
  Definition wpf : evalAg (ew A0 B0) (ew A0 B0) := evalAg_refl (ew A0 B0).

  (* abbreviations for the constructor-form instance *)
  Local Notation nodeC := (rk (ew A0 B0) (hT (ew A0 B0) wfC)).
  Local Notation WCc := (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf).
  Local Notation aaC := (placeWDom k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                           (wcA k A0 B0 FA (ew A0 B0) wfC wpf)).
  Local Notation bbC := (wbb k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                           (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                           (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                           (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)).
  Local Notation mkWelC := (mkWel k nodeC (ew A0 B0) A0 B0
                              (wEv A0 B0 (ew A0 B0) wfC wpf) aaC
                              (wea_holds k (ew A0 B0) A0 B0 wfC
                                 (wEv A0 B0 (ew A0 B0) wfC wpf)
                                 (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                                 (weA k A0 B0 FA (ew A0 B0) wfC wpf)) bbC
                              (web_holds k (ew A0 B0) A0 B0 wfC
                                 (wEv A0 B0 (ew A0 B0) wfC wpf)
                                 (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                                 (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                                 (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)
                                 (weB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf))).
  Local Notation tyC := (ex_intro (fun n => eqty n (ew A0 B0) (ew A0 B0)) k
                           (eqty_refl_l k (ew A0 B0) (ew A0 B0)
                              (wcode_sh k A0 B0 gW (ew A0 B0) wfC wpf))).

  Local Notation mkWtreeC := (mkWtree k nodeC (ew A0 B0) A0 B0
                                (wEv A0 B0 (ew A0 B0) wfC wpf) aaC
                                (wea_holds k (ew A0 B0) A0 B0 wfC
                                   (wEv A0 B0 (ew A0 B0) wfC wpf)
                                   (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                                   (weA k A0 B0 FA (ew A0 B0) wfC wpf)) bbC
                                (web_holds k (ew A0 B0) A0 B0 wfC
                                   (wEv A0 B0 (ew A0 B0) wfC wpf)
                                   (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                                   (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                                   (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)
                                   (weB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf))).
  Local Notation labC u0 z := (wLab (ew A0 B0) wfC wpf u0 z).
  Local Notation reLab u0 z :=
    (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 (wLab (ew A0 B0) wfC wpf u0 z)).
  Local Notation idxC u0 z v0 y := (wIdx (ew A0 B0) wfC wpf u0 z v0 y).
  Local Notation idxBackC u0 z v0 y := (wIdxBack (ew A0 B0) wfC wpf u0 z v0 y).

  Definition wUp w (x : kElC (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) w)
    : kElAt WF w :=
    famTo WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w x.

  Definition wDn w (x : kElAt WF w)
    : kElC (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) w :=
    famFrom WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w x.

  Lemma wUp_coh w x : kcel (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) w x
                           (kAt WF) w (wUp w x).
  Proof. exact (famTo_coh WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w x). Qed.

  Lemma wDn_coh w x : kEqAt WF w x WF w (wUp w (wDn w x)).
  Proof.
    eapply ktrE;
      [ exact (famAtWf WF)
      | exact (famWf WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf)
      | exact (famAtWf WF)
      | exact (uf_coh WF (ew A0 B0) (kAcc WF) (evalAg_refl (ew A0 B0))
                 (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf)
      | exact (famFrom_coh WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w x)
      | exact (famTo_coh WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w (wDn w x)) ].
  Qed.

  (* ---- sup at the canonical instance: what the interpretation uses ---- *)

  Definition wSup (u0 f : etm) (z : kElAt FA u0)
    (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
    (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
        kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
    (gd : Good (ew A0 B0) (esup u0 f)) : kElAt WF (esup u0 f) :=
    wUp (esup u0 f)
      (wSupI (ew A0 B0) wfC wpf u0 f z
         (fun v0 y => wDn (eapp f v0) (sub v0 y))
         (fun v0 y v0' y' H =>
            famFrom_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf
              (eapp f v0) (sub v0 y) (eapp f v0') (sub v0' y') (subext v0 y v0' y' H))
         gd).

  (* ---- the branches of a node, lifted to the canonical instance, are
     extensional: the tree's own relation gives the subtrees, and the layer-1
     branch relation comes out of the node's goodness (Rel_w_br) ---- *)

  Lemma wBr_ext w0 u0 (z : kElS (placeWDom k (ew A0 B0) A0 B0 wfC
                                   (wEv A0 B0 (ew A0 B0) wfC wpf)
                                   (wcA k A0 B0 FA (ew A0 B0) wfC wpf)) u0)
    (f : etm)
    (sub : forall v0, kElS (wbb k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                              (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                              (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                              (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) u0 z) v0 ->
             kWEl k (rk (ew A0 B0) (hT (ew A0 B0) wfC)) (ew A0 B0) _ _ (eapp f v0))
    (trs : forall v0 y v0' y',
        kcEl (wbb k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                 (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                 (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                 (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) u0 z) v0 y _ v0' y' ->
        kWRel k (rk (ew A0 B0) (hT (ew A0 B0) wfC)) (ew A0 B0) _ _ (sub v0 y) (sub v0' y'))
    (ev : eval w0 (esup u0 f)) (gd : Good (ew A0 B0) w0)
    v0 y v0' y' :
    kEqAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y
          (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0' y' ->
    kEqAt WF (eapp f v0) (wUp (eapp f v0) (wBr (ew A0 B0) wfC wpf u0 z f sub trs v0 y))
          WF (eapp f v0') (wUp (eapp f v0') (wBr (ew A0 B0) wfC wpf u0 z f sub trs v0' y')).
  Proof.
    intros H.
    apply (famTo_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
    apply (mkW_eq k (rk (ew A0 B0) (hT (ew A0 B0) wfC)) (ew A0 B0) A0 B0
             (wEv A0 B0 (ew A0 B0) wfC wpf)
             (ex_intro _ k (eqty_refl_l k (ew A0 B0) (ew A0 B0)
                              (wcode_sh k A0 B0 gW (ew A0 B0) wfC wpf)))).
    - apply trs.
      exact (famFrom_eq (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
               (eapp B0 u0) _ _ v0 y v0' y' H).
    - (* the two branch realisers are layer-1 related *)
      apply (Rel_w_br (ew A0 B0) A0 B0 w0 u0 f (kFam_good_ty WF)
               (eval_whnf _ (whnf_w A0 B0)) gd ev).
      eapply Rel_exp_ty;
        [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
        | exact (famEl_rel (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y _ v0' y' H) ].
  Qed.

  (* ---- the congruence law for sup ---- *)

  Lemma wSup_cong u0 (z : kElAt FA u0) f sub subext gd
    u0' (z' : kElAt FA u0') f' sub' subext' gd' :
    kEqAt FA u0 z FA u0' z' ->
    (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0' z') v0' y' ->
       kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f' v0') (sub' v0' y')) ->
    Rel (ew A0 B0) (esup u0 f) (esup u0' f') ->
    kEqAt WF (esup u0 f) (wSup u0 f z sub subext gd)
          WF (esup u0' f') (wSup u0' f' z' sub' subext' gd').
  Proof.
    intros Hz Hsub HR.
    unfold wSup; apply (famTo_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
    apply (mkW_eq k (rk (ew A0 B0) (hT (ew A0 B0) wfC)) (ew A0 B0) A0 B0
             (wEv A0 B0 (ew A0 B0) wfC wpf)
             (ex_intro _ k (eqty_refl_l k (ew A0 B0) (ew A0 B0)
                              (wcode_sh k A0 B0 gW (ew A0 B0) wfC wpf))));
      [| exact HR].
    split.
    - (* labels: the two placements of related elements are related *)
      exact (famFrom_eq FA A0 (wAccA A0 B0 (ew A0 B0) wfC wpf) (evalAg_refl A0)
               u0 z u0' z' Hz).
    - (* branches: read the two placed indices in the two branching families,
         then the hypothesis, then back down *)
      intros v0 y v0' y' Hy.
      apply (mkW_eq_inv k (rk (ew A0 B0) (hT (ew A0 B0) wfC)) (ew A0 B0) A0 B0
               (wEv A0 B0 (ew A0 B0) wfC wpf) _
               (wea_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)) _
               (web_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)
                  (weB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf))).
      apply (famFrom_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
      apply Hsub.
      (* the two indices, read in the branching families *)
      eapply ktrE;
        [ exact (famAtWf (FB u0 z))
        | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0
                   (wLab (ew A0 B0) wfC wpf u0 z))
        | exact (famAtWf (FB u0' z'))
        | apply knsymU; exact (wcB_ceq (ew A0 B0) wfC wpf u0 z)
        | apply knsym; exact (wIdx_rel (ew A0 B0) wfC wpf u0 z v0 y) |].
      eapply ktrE;
        [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0
                   (wLab (ew A0 B0) wfC wpf u0 z))
        | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0'
                   (wLab (ew A0 B0) wfC wpf u0' z'))
        | exact (famAtWf (FB u0' z'))
        | eapply ktrU;
            [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0
                       (wLab (ew A0 B0) wfC wpf u0 z))
            | exact (famAtWf (FB u0 z))
            | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0'
                       (wLab (ew A0 B0) wfC wpf u0' z'))
            | exact (wcB_ceq (ew A0 B0) wfC wpf u0 z)
            | eapply ktrU;
                [ exact (famAtWf (FB u0 z))
                | exact (famAtWf (FB u0' z'))
                | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0'
                           (wLab (ew A0 B0) wfC wpf u0' z'))
                | exact (cohB u0 z u0' z' Hz)
                | apply knsymU; exact (wcB_ceq (ew A0 B0) wfC wpf u0' z') ] ]
        | exact Hy
        | exact (wIdx_rel (ew A0 B0) wfC wpf u0' z' v0' y') ].
  Qed.

(* ------------------------------------------------------------------ *)
(* The recursor.                                                       *)
(*                                                                    *)
(* The recursion is on the TREE, and -- unlike every other eliminator   *)
(* in this development -- it needs no coercion at all: the motive        *)
(* instance at a node is the node's own element, so only the REALISER    *)
(* moves, by the two expansions the computation rule provides            *)
(* (`reds_wrec_sup` at the node, `reds_wih_beta` at each branch).        *)
(* ------------------------------------------------------------------ *)

  (* the self-relation and the goodness a node's subtree carries: named,
     because they appear in every statement about the recursor *)
  Definition subTr (w0 u0 : etm) (z : kElS aaC u0) (f : etm)
    (ev : eval w0 (esup u0 f)) (gd0 : Good (ew A0 B0) w0)
    (sub : forall v0, kElS (bbC u0 z) v0 -> kWEl k nodeC (ew A0 B0) aaC bbC (eapp f v0))
    (tr : kWRel k nodeC (ew A0 B0) aaC bbC
            (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0 u0 z f ev gd0 sub))
    v0 y : kWRel k nodeC (ew A0 B0) aaC bbC (sub v0 y) (sub v0 y) :=
    proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
             w0 u0 z f ev gd0 sub tr) v0 y v0 y
      (kselfE (bbC u0 z) (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z) v0 y).

  Definition subGd (w0 u0 : etm) (z : kElS aaC u0) (f : etm)
    (sub : forall v0, kElS (bbC u0 z) v0 -> kWEl k nodeC (ew A0 B0) aaC bbC (eapp f v0))
    v0 y : Good (ew A0 B0) (eapp f v0) :=
    kWgood k nodeC (ew A0 B0) aaC bbC (sub v0 y).

  Local Notation elOf w t tr gd := (wUp w (mkWelC w t tr gd)).

  (* ---- the crux: a sup rebuilt from a node's data IS the node ----

     The decoding of a W code is generated by `sup`, up to the equality.  The
     two trees differ at every branch by the round trip through the family
     (`wUp`/`wDn`, and the coercion inside `wIdx`), so each branch is
     reconciled by `wIdx_roundtrip` and the node's own relation supplies the
     subtrees.  This is what lets the recursor below take its step in the form
     the interpretation has it -- with semantic data -- rather than in the
     tree form the recursion produces. *)

  Lemma wSup_tree w0 u0 (z : kElS aaC u0) (f : etm)
    (ev : eval w0 (esup u0 f)) (gd0 : Good (ew A0 B0) w0)
    (sub : forall v0, kElS (bbC u0 z) v0 -> kWEl k nodeC (ew A0 B0) aaC bbC (eapp f v0))
    (tr : kWRel k nodeC (ew A0 B0) aaC bbC
            (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0 u0 z f ev gd0 sub))
    (gd : Good (ew A0 B0) w0) :
    kEqAt WF (esup u0 f)
      (wSup u0 f (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)
         (fun v0 y => wUp (eapp f v0)
            (wBr (ew A0 B0) wfC wpf u0 z f sub
               (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                         w0 u0 z f ev gd0 sub tr)) v0 y))
         (wBr_ext w0 u0 z f sub
            (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                      w0 u0 z f ev gd0 sub tr)) ev gd)
         (Good_red (ew A0 B0) w0 (esup u0 f) (proj1 ev) gd))
      WF w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd).
  Proof.
    set (trs := proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                         w0 u0 z f ev gd0 sub tr)).
    set (zs := wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z).
    unfold wSup; apply (famTo_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
    apply (mkW_eq k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) tyC);
      [| apply Rel_sym; exact (Rel_red_r (ew A0 B0) w0 (esup u0 f) (proj1 ev) gd)].
    split.
    - (* labels: the round trip through the domain family *)
      exact (famFrom_famTo FA A0 (wAccA A0 B0 (ew A0 B0) wfC wpf) (evalAg_refl A0) u0 z).
    - (* branches *)
      intros v0 y v0' y' Hy.
      (* the index of the rebuilt tree, brought back to the node's own *)
      assert (Hidx : kcEl (bbC u0 z) v0
                       (wIdxBack (ew A0 B0) wfC wpf u0 z v0
                          (wIdx (ew A0 B0) wfC wpf u0 zs v0 y))
                       (bbC u0 z) v0' y').
      { eapply ktrE;
          [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
          | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0
                     (wLab (ew A0 B0) wfC wpf u0 zs))
          | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
          | eapply ktrU;
              [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
              | exact (famAtWf (FB u0 zs))
              | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0
                         (wLab (ew A0 B0) wfC wpf u0 zs))
              | exact (wcB_at k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
              | apply knsymU; exact (wcB_ceq (ew A0 B0) wfC wpf u0 zs) ]
          | exact (wIdx_roundtrip (ew A0 B0) wfC wpf u0 z v0 y)
          | exact Hy ]. }
      (* and now the two subtrees, through the element relation *)
      apply (mkW_eq_inv k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) aaC
               (wea_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)) bbC
               (web_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)
                  (weB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf))
               (eapp f v0) _ (eapp f v0')
               (mkWelC (eapp f v0') (sub v0' y')
                  (trs v0' y' v0' y'
                     (kselfE (bbC u0 z)
                        (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z) v0' y'))
                  (kWgood k nodeC (ew A0 B0) aaC bbC (sub v0' y')))).
      eapply ktrE;
        [ exact (famWf WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf)
        | exact (famWf WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf)
        | exact (famWf WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf)
        | exact (proj2 (famWf WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf))
        | exact (famFrom_famTo WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf
                   (eapp f v0)
                   (wBr (ew A0 B0) wfC wpf u0 z f sub trs v0
                      (wIdx (ew A0 B0) wfC wpf u0 zs v0 y))) |].
      apply (mkW_eq k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) tyC).
      + exact (trs v0 _ v0' y' Hidx).
      + (* the two branch realisers are layer-1 related *)
        apply (Rel_w_br (ew A0 B0) A0 B0 w0 u0 f (kFam_good_ty WF)
                 (eval_whnf _ (whnf_w A0 B0)) gd ev).
        eapply Rel_exp_ty; [exact (redB u0 zs) |].
        eapply Rel_tyeq;
          [ exact (ex_intro (fun n => eqty n (kSh (bbC u0 z)) (SB u0 zs)) k
                     (uf_sh (FB u0 zs) (eapp B0 u0) _ _))
          | exact (krel k nodeC (bbC u0 z) v0 _ (bbC u0 z) v0' y' Hidx) ].
  Qed.

  (* ---- the data of a rebuilt sup ----

     The step of the computation rule is read on a NODE's data (`stepP`), so
     when the node is itself a rebuilt sup its label is the round trip
     `wxc (wLab z)` and its branch indices live in the branching family at
     that label.  These two lemmas undo the detour: `wIdx_fam_rt` brings an
     index back -- `wIdxBack` places it, `wIdx` reads it at the original
     label, and the composite is the identity up to the equality -- and
     `wSup_brC` then identifies the branch itself.  Both the relation and the
     goodness proof carried by the rebuilt branch are universally quantified,
     so that the caller's -- whatever `wRecI` filled its holes with -- match. *)

  Lemma wIdx_fam_rt u0 (z : kElAt FA u0) v0
    (y : kElAt (FB u0 (reLab u0 z)) v0) v0' (y' : kElAt (FB u0 z) v0') :
    kEqAt (FB u0 (reLab u0 z)) v0 y (FB u0 z) v0' y' ->
    kEqAt (FB u0 z) v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y))
          (FB u0 z) v0' y'.
  Proof.
    intros Hy.
    apply (kEqAt_trans (FB u0 z) v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y))
             (FB u0 (reLab u0 z)) v0 y (FB u0 z) v0' y'); [| | exact Hy].
    - apply knsymU;
        exact (cohB u0 (reLab u0 z) u0 z (wLab_eq (ew A0 B0) wfC wpf u0 z)).
    - apply kEqAt_sym.
      eapply ktrE;
        [ exact (famAtWf (FB u0 (reLab u0 z)))
        | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 (labC u0 z))
        | exact (famAtWf (FB u0 z))
        | apply knsymU;
          exact (wcB_at k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 (labC u0 z))
        | exact (wIdxBack_rel (ew A0 B0) wfC wpf u0 (labC u0 z) v0 y)
        | exact (wIdx_rel (ew A0 B0) wfC wpf u0 z v0
                   (idxBackC u0 (labC u0 z) v0 y)) ].
  Qed.

  Lemma wSup_brC u0 (z : kElAt FA u0) (f : etm)
    (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
    (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
        kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
    v0 (y : kElAt (FB u0 (reLab u0 z)) v0) v0' (y' : kElAt (FB u0 z) v0')
    (Hy : kEqAt (FB u0 (reLab u0 z)) v0 y (FB u0 z) v0' y') tr gd :
    kcel (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) (eapp f v0)
      (mkWelC (eapp f v0)
         (mkWtreeC (eapp f v0)
            (wDn (eapp f v0) (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))))
         tr gd)
      (wcode k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf) (eapp f v0')
      (wDn (eapp f v0') (sub v0' y')).
  Proof.
    assert (Hs : kEqAt WF (eapp f v0)
                   (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))
                   WF (eapp f v0') (sub v0' y'))
      by exact (subext v0 _ v0' y' (wIdx_fam_rt u0 z v0 y v0' y' Hy)).
    apply (mkW_eq k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) tyC).
    - apply (mkW_eq_inv k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) aaC
               (wea_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)) bbC
               (web_holds k (ew A0 B0) A0 B0 wfC (wEv A0 B0 (ew A0 B0) wfC wpf)
                  (wcA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (weA k A0 B0 FA (ew A0 B0) wfC wpf)
                  (wcB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf)
                  (weB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf))
               (eapp f v0)
               (wDn (eapp f v0)
                  (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y))))
               (eapp f v0') (wDn (eapp f v0') (sub v0' y'))).
      exact (famFrom_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf
               (eapp f v0) (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))
               (eapp f v0') (sub v0' y') Hs).
    - exact (famEl_rel WF (eapp f v0)
               (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))
               WF (eapp f v0') (sub v0' y') Hs).
  Qed.

  (* and the branch, read back at the canonical instance *)
  Lemma wSup_br u0 (z : kElAt FA u0) (f : etm)
    (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
    (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
        kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
    v0 (y : kElAt (FB u0 (reLab u0 z)) v0) v0' (y' : kElAt (FB u0 z) v0')
    (Hy : kEqAt (FB u0 (reLab u0 z)) v0 y (FB u0 z) v0' y') tr gd :
    kEqAt WF (eapp f v0)
      (elOf (eapp f v0)
         (mkWtreeC (eapp f v0)
            (wDn (eapp f v0) (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))))
         tr gd)
      WF (eapp f v0') (sub v0' y').
  Proof.
    apply (kEqAt_trans WF (eapp f v0)
             (elOf (eapp f v0)
                (mkWtreeC (eapp f v0)
                   (wDn (eapp f v0)
                      (sub v0 (idxC u0 z v0 (idxBackC u0 (labC u0 z) v0 y)))))
                tr gd)
             WF (eapp f v0') (wUp (eapp f v0') (wDn (eapp f v0') (sub v0' y')))
             WF (eapp f v0') (sub v0' y')).
    - exact (famAtSelf WF).
    - apply (famTo_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
      exact (wSup_brC u0 z f sub subext v0 y v0' y' Hy tr gd).
    - exact (kEqAt_sym WF (eapp f v0') (sub v0' y') WF (eapp f v0')
               (wUp (eapp f v0') (wDn (eapp f v0') (sub v0' y')))
               (wDn_coh (eapp f v0') (sub v0' y'))).
  Qed.


  (* ------------------------------------------------------------------ *)
  (* THE RECURSOR, BY ITS GRAPH.                                         *)
  (*                                                                    *)
  (* The step of a W-recursion receives its induction hypothesis as a     *)
  (* FUNCTION of the branch, and the interpretation has to read that      *)
  (* function as an element of a Pi family -- `wih n k A B C` is a Pi     *)
  (* type -- whose decoding consists of the EXTENSIONAL functions.  So    *)
  (* the step needs, besides the hypothesis, the proof that it respects   *)
  (* the equality.                                                       *)
  (*                                                                    *)
  (* That proof is not available to a structural recursion: at a node it  *)
  (* is a relation between the values at two SIBLING subtrees, which a    *)
  (* Fixpoint cannot produce while it is still defining them, and no      *)
  (* statement mentioning the function being defined can appear in its    *)
  (* own type.  The way out is the standard one: define the recursor by    *)
  (* its GRAPH, prove that the graph is extensional -- related trees have *)
  (* related values -- BEFORE proving it total, and read the function off *)
  (* the totality proof.  The extensionality of the hypothesis at a node  *)
  (* is then an instance of the graph's, which is already available.      *)
  (*                                                                    *)
  (* The step's congruence `stepRel` is therefore an assumption of the    *)
  (* whole section: the DEFINITION of the recursor depends on it, not     *)
  (* only its laws.                                                      *)
  (* ------------------------------------------------------------------ *)

  Section RecG.
    Context (m : nat) (Sr : etm).
    Local Notation ihR f :=
      (elam (ewrec (ren_etm rshift Sr) (eapp (ren_etm rshift f) (var_etm 0)))).
    Context (SC : forall w, kElAt WF w -> etm)
            (FC : forall w (x : kElAt WF w), kUFam m (SC w x))
            (cohC : forall w x w' x', kEqAt WF w x WF w' x' ->
               kceq (kAt (FC w x)) (kAt (FC w' x'))).

    (* the family the recursive result at one branch lives in *)
    Local Notation subC w0 u0 z f ev gd0 sub tr v0 y :=
      (FC (eapp f v0)
         (elOf (eapp f v0) (sub v0 y)
            (subTr w0 u0 z f ev gd0 sub tr v0 y)
            (subGd w0 u0 z f sub v0 y))).

    (* the induction hypothesis at a node, and its extensionality *)
    Local Notation IH w0 u0 z f ev gd0 sub tr :=
      (forall v0 (y : kElS (bbC u0 z) v0),
         kElAt (subC w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR f) v0)).
    Local Notation IHext w0 u0 z f ev gd0 sub tr ih :=
      (forall v0 y v0' y', kcEl (bbC u0 z) v0 y (bbC u0 z) v0' y' ->
         kRel (subC w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR f) v0) (ih v0 y)
              (subC w0 u0 z f ev gd0 sub tr v0' y') (eapp (ihR f) v0') (ih v0' y')).

    Context (step : forall w0 u0 z f ev gd0 sub tr gd
        (ih : IH w0 u0 z f ev gd0 sub tr) (ihext : IHext w0 u0 z f ev gd0 sub tr ih),
        kElAt (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
              (eapp (eapp (eapp Sr u0) f) (ihR f))).

    Context (stepRel : forall w0 u0 z f ev gd0 sub tr gd ih ihext
                              w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext',
       kWRel k nodeC (ew A0 B0) aaC bbC
         (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
       Rel (ew A0 B0) w0 w0' ->
       (forall v0 y v0' y', kcEl (bbC u0 z) v0 y (bbC u0' z') v0' y' ->
          kRel (subC w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR f) v0) (ih v0 y)
               (subC w0' u0' z' f' ev' gd0' sub' tr' v0' y') (eapp (ihR f') v0')
               (ih' v0' y')) ->
       kRel (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
            (eapp (eapp (eapp Sr u0) f) (ihR f))
            (step w0 u0 z f ev gd0 sub tr gd ih ihext)
            (FC w0' (elOf w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
            (eapp (eapp (eapp Sr u0') f') (ihR f'))
            (step w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext')).

    (* ---- the graph ----

       `wGr t tr gd x` says: x is A value of the recursion on t.  The two
       expansions are the computation rule's -- `reds_wrec_sup` at the node
       and `reds_wih_beta` at each branch -- and the value is pinned only up
       to the family's equality, which is what makes the graph closed under
       it (`wGr_eq`) and so usable at all. *)

    Fixpoint wGr {w} (t : kWEl k nodeC (ew A0 B0) aaC bbC w)
      : forall tr gd, kElAt (FC w (elOf w t tr gd)) (ewrec Sr w) -> Prop :=
      match t as t0 in WEl _ _ _ w0
        return forall tr gd, kElAt (FC w0 (elOf w0 t0 tr gd)) (ewrec Sr w0) -> Prop with
      | wel_sup w0 u0 z f ev gd0 sub => fun tr gd x =>
          exists (ih : IH w0 u0 z f ev gd0 sub tr)
                 (ihext : IHext w0 u0 z f ev gd0 sub tr ih),
            (forall v0 y,
               wGr (sub v0 y) (subTr w0 u0 z f ev gd0 sub tr v0 y)
                 (subGd w0 u0 z f sub v0 y)
                 (famRed (subC w0 u0 z f ev gd0 sub tr v0 y)
                    (eapp (ihR f) v0) (ewrec Sr (eapp f v0))
                    (reds_wih_beta Sr f v0) (ih v0 y)))
            /\ kEqAt (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                     (ewrec Sr w0) x
                     (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                     (ewrec Sr w0)
                     (famExp (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                        (ewrec Sr w0) (eapp (eapp (eapp Sr u0) f) (ihR f))
                        (reds_wrec_sup Sr w0 u0 f ev)
                        (step w0 u0 z f ev gd0 sub tr gd ih ihext))
      end.

    (* it is closed under the equality, which is all a value is determined to *)
    Lemma wGr_eq {w} (t : kWEl k nodeC (ew A0 B0) aaC bbC w) tr gd x x' :
      wGr t tr gd x ->
      kEqAt (FC w (elOf w t tr gd)) (ewrec Sr w) x
            (FC w (elOf w t tr gd)) (ewrec Sr w) x' ->
      wGr t tr gd x'.
    Proof.
      destruct t as [w0 u0 z f ev gd0 sub]; intros [ih [ihext [H1 H2]]] He.
      exists ih, ihext; split; [exact H1 |].
      eapply kEqAt_trans;
        [ exact (famAtSelf (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd)))
        | apply kEqAt_sym; exact He | exact H2 ].
    Qed.

    (* the round trip of the two moves along one reduction *)
    Lemma famRed_famExp {u} (F : kUFam m u) w w1 (H : reds w w1) y :
      kEqAt F w1 (famRed F w w1 H (famExp F w w1 H y)) F w1 y.
    Proof.
      eapply kEqAt_trans;
        [ exact (famAtSelf F)
        | apply kEqAt_sym; exact (famRed_rel F w w1 H (famExp F w w1 H y))
        | exact (famExp_rel F w w1 H y) ].
    Qed.

    (* ---- the graph is extensional: related trees have related values ----

       This is where the plain Fixpoint had to be given up: the proof is an
       induction on the first tree, and it is available BEFORE the recursor
       exists, because it speaks of the graph and not of any function. *)

    Lemma wGr_rel :
      forall w (t : kWEl k nodeC (ew A0 B0) aaC bbC w) tr gd x, wGr t tr gd x ->
      forall w' (t' : kWEl k nodeC (ew A0 B0) aaC bbC w') tr' gd' x', wGr t' tr' gd' x' ->
      kWRel k nodeC (ew A0 B0) aaC bbC t t' -> Rel (ew A0 B0) w w' ->
      kRel (FC w (elOf w t tr gd)) (ewrec Sr w) x
           (FC w' (elOf w' t' tr' gd')) (ewrec Sr w') x'.
    Proof.
      intros w t; induction t as [w0 u0 z f ev gd0 sub IHt].
      intros tr gd x [ih [ihext [Hsub Hx]]] w' t'.
      destruct t' as [w0' u0' z' f' ev' gd0' sub'].
      intros tr' gd' x' [ih' [ihext' [Hsub' Hx']]] H HR.
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); exact Hx |].
      eapply kRel_trans; [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); exact Hx'].
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
      eapply kRel_trans; [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel].
      apply (stepRel w0 u0 z f ev gd0 sub tr gd ih ihext
               w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext' H HR).
      (* the two hypotheses are related, by the induction hypothesis on the
         subtrees -- out of the branch expansion and back into it *)
      intros v0 y v0' y' Hy.
      eapply kRel_trans;
        [ apply (proj1 (kRel_same _ _ _ _ _)); apply famRed_rel |].
      eapply kRel_trans;
        [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famRed_rel ].
      apply (IHt v0 y _ _ _ (Hsub v0 y) (eapp f' v0') (sub' v0' y') _ _ _ (Hsub' v0' y')).
      - exact (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                        w0' u0' z' f' ev' gd0' sub' H) v0 y v0' y' Hy).
      - apply (Rel_w_br2 (ew A0 B0) A0 B0 (kFam_good_ty WF)
                 (eval_whnf _ (whnf_w A0 B0)) w0 w0' HR u0 f u0' f' ev ev').
        eapply Rel_exp_ty;
          [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) |].
        eapply Rel_tyeq;
          [ exact (ex_intro (fun n => eqty n (kSh (bbC u0 z))
                                        (SB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))) k
                     (uf_sh (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
                        (eapp B0 u0) _ _))
          | exact (krel k nodeC (bbC u0 z) v0 y (bbC u0' z') v0' y' Hy) ].
    Qed.

    (* ---- and it is total ----

       The recursion is on the tree; at a node the hypothesis is the family of
       values the recursive calls provide, and its extensionality is the
       graph's, which is now available. *)

    Definition wGr_tot : forall w (t : kWEl k nodeC (ew A0 B0) aaC bbC w) tr gd,
        { x : kElAt (FC w (elOf w t tr gd)) (ewrec Sr w) | wGr t tr gd x }.
    Proof.
      fix wGr_tot 2.
      intros w t; destruct t as [w0 u0 z f ev gd0 sub]; intros tr gd.
      (* the recursive results, read at the branch's own realiser *)
      pose (ih := fun v0 y =>
        famExp (subC w0 u0 z f ev gd0 sub tr v0 y)
          (eapp (ihR f) v0) (ewrec Sr (eapp f v0)) (reds_wih_beta Sr f v0)
          (proj1_sig (wGr_tot (eapp f v0) (sub v0 y)
                        (subTr w0 u0 z f ev gd0 sub tr v0 y)
                        (subGd w0 u0 z f sub v0 y)))).
      assert (Hsub : forall v0 y,
          wGr (sub v0 y) (subTr w0 u0 z f ev gd0 sub tr v0 y)
            (subGd w0 u0 z f sub v0 y)
            (famRed (subC w0 u0 z f ev gd0 sub tr v0 y)
               (eapp (ihR f) v0) (ewrec Sr (eapp f v0))
               (reds_wih_beta Sr f v0) (ih v0 y))).
      { intros v0 y; unfold ih.
        eapply wGr_eq;
          [ exact (proj2_sig (wGr_tot (eapp f v0) (sub v0 y)
                     (subTr w0 u0 z f ev gd0 sub tr v0 y)
                     (subGd w0 u0 z f sub v0 y)))
          | apply kEqAt_sym; apply famRed_famExp ]. }
      assert (ihext : IHext w0 u0 z f ev gd0 sub tr ih).
      { intros v0 y v0' y' Hy; unfold ih.
        eapply kRel_trans;
          [ apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
        eapply kRel_trans;
          [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel ].
        apply (wGr_rel (eapp f v0) (sub v0 y) _ _ _
                 (proj2_sig (wGr_tot (eapp f v0) (sub v0 y) _ _))
                 (eapp f v0') (sub v0' y') _ _ _
                 (proj2_sig (wGr_tot (eapp f v0') (sub v0' y') _ _))).
        - exact (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                          w0 u0 z f ev gd0 sub tr) v0 y v0' y' Hy).
        - apply (Rel_w_br (ew A0 B0) A0 B0 w0 u0 f (kFam_good_ty WF)
                   (eval_whnf _ (whnf_w A0 B0)) gd ev).
          eapply Rel_exp_ty;
            [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) |].
          eapply Rel_tyeq;
            [ exact (ex_intro (fun n => eqty n (kSh (bbC u0 z))
                                          (SB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))) k
                       (uf_sh (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
                          (eapp B0 u0) _ _))
            | exact (krel k nodeC (bbC u0 z) v0 y (bbC u0 z) v0' y' Hy) ]. }
      refine (exist _
        (famExp (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
           (ewrec Sr w0) (eapp (eapp (eapp Sr u0) f) (ihR f))
           (reds_wrec_sup Sr w0 u0 f ev)
           (step w0 u0 z f ev gd0 sub tr gd ih ihext)) _).
      exists ih, ihext; split; [exact Hsub | apply kEqAt_refl].
    Defined.

    (* the recursor at a node, and at an arbitrary element of the family *)
    Definition wRecN w (t : kWEl k nodeC (ew A0 B0) aaC bbC w) tr gd
      : kElAt (FC w (elOf w t tr gd)) (ewrec Sr w) :=
      proj1_sig (wGr_tot w t tr gd).

    Definition wRecOnG w (y : kElC WCc w) : kElAt (FC w (wUp w y)) (ewrec Sr w) :=
      match y with
      | (exist _ t tr, gd) => wRecN w t tr gd
      end.

    Definition wRecG w (x : kElAt WF w) : kElAt (FC w x) (ewrec Sr w) :=
      moveTo (FC w (wUp w (wDn w x))) (FC w x)
        (cohC _ _ _ _ (kEqAt_sym WF w x WF w (wUp w (wDn w x)) (wDn_coh w x)))
        (ewrec Sr w) (wRecOnG w (wDn w x)) (ewrec Sr w) (reds_refl (ewrec Sr w)).

    (* the graph at a node, exposed: this is the computation rule in the
       form the semantic layer consumes *)
    Lemma wRecN_sup w0 u0 z f ev gd0 sub tr gd :
      exists (ih : IH w0 u0 z f ev gd0 sub tr)
             (ihext : IHext w0 u0 z f ev gd0 sub tr ih),
        (forall v0 y,
           wGr (sub v0 y) (subTr w0 u0 z f ev gd0 sub tr v0 y)
             (subGd w0 u0 z f sub v0 y)
             (famRed (subC w0 u0 z f ev gd0 sub tr v0 y)
                (eapp (ihR f) v0) (ewrec Sr (eapp f v0))
                (reds_wih_beta Sr f v0) (ih v0 y)))
        /\ kEqAt (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                 (ewrec Sr w0) (wRecN w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd)
                 (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                 (ewrec Sr w0)
                 (famExp (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                    (ewrec Sr w0) (eapp (eapp (eapp Sr u0) f) (ihR f))
                    (reds_wrec_sup Sr w0 u0 f ev)
                    (step w0 u0 z f ev gd0 sub tr gd ih ihext)).
    Proof.
      exact (proj2_sig (wGr_tot w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd)).
    Qed.

    (* its congruence is the graph's *)
    Lemma wRecN_rel w t tr gd w' t' tr' gd' :
      kWRel k nodeC (ew A0 B0) aaC bbC t t' -> Rel (ew A0 B0) w w' ->
      kRel (FC w (elOf w t tr gd)) (ewrec Sr w) (wRecN w t tr gd)
           (FC w' (elOf w' t' tr' gd')) (ewrec Sr w') (wRecN w' t' tr' gd').
    Proof.
      intros H HR.
      exact (wGr_rel w t tr gd _ (proj2_sig (wGr_tot w t tr gd))
               w' t' tr' gd' _ (proj2_sig (wGr_tot w' t' tr' gd')) H HR).
    Qed.

    Lemma wRecOnG_rel w (y : kElC WCc w) w' (y' : kElC WCc w') :
      kcel WCc w y WCc w' y' ->
      kRel (FC w (wUp w y)) (ewrec Sr w) (wRecOnG w y)
           (FC w' (wUp w' y')) (ewrec Sr w') (wRecOnG w' y').
    Proof.
      destruct y as [[t tr] gd]; destruct y' as [[t' tr'] gd']; intros H.
      exact (wRecN_rel w t tr gd w' t' tr' gd' (proj1 H) (proj2 (proj2 H))).
    Qed.

    Lemma wRecG_rel w x w' x' :
      kEqAt WF w x WF w' x' ->
      kRel (FC w x) (ewrec Sr w) (wRecG w x) (FC w' x') (ewrec Sr w') (wRecG w' x').
    Proof.
      intros H; unfold wRecG.
      eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
      eapply kRel_trans; [| apply moveTo_rel].
      apply wRecOnG_rel.
      exact (famFrom_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf w x w' x' H).
    Qed.
    (* ---- the computation rule at a node ----

       The graph's hypothesis is existential, so the recursor at a node is the
       step applied to SOME extensional family of values of the subtrees; that
       family is pointwise related to the recursor's own, by the graph's
       extensionality, and `stepRel` replaces it.  This is the whole content
       of the computation rule; what the semantic layer adds is bookkeeping. *)

    Definition ihN w0 u0 z f ev gd0 sub tr : IH w0 u0 z f ev gd0 sub tr :=
      fun v0 y =>
        famExp (subC w0 u0 z f ev gd0 sub tr v0 y)
          (eapp (ihR f) v0) (ewrec Sr (eapp f v0)) (reds_wih_beta Sr f v0)
          (wRecN (eapp f v0) (sub v0 y)
             (subTr w0 u0 z f ev gd0 sub tr v0 y)
             (subGd w0 u0 z f sub v0 y)).

    (* the branch realisers of one node are layer-1 related, which every step
       of the computation rule needs *)
    Lemma wBrRel w0 u0 (z : kElS aaC u0) f (ev : eval w0 (esup u0 f))
      (gd : Good (ew A0 B0) w0) v0 y v0' y' :
      kcEl (bbC u0 z) v0 y (bbC u0 z) v0' y' -> Rel (ew A0 B0) (eapp f v0) (eapp f v0').
    Proof.
      intros Hy.
      apply (Rel_w_br (ew A0 B0) A0 B0 w0 u0 f (kFam_good_ty WF)
               (eval_whnf _ (whnf_w A0 B0)) gd ev).
      eapply Rel_exp_ty;
        [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) |].
      eapply Rel_tyeq;
        [ exact (ex_intro (fun n => eqty n (kSh (bbC u0 z))
                                      (SB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))) k
                   (uf_sh (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
                      (eapp B0 u0) _ _))
        | exact (krel k nodeC (bbC u0 z) v0 y (bbC u0 z) v0' y' Hy) ].
    Qed.

    Lemma ihN_ext w0 u0 z f ev gd0 sub tr (gd : Good (ew A0 B0) w0) :
      IHext w0 u0 z f ev gd0 sub tr (ihN w0 u0 z f ev gd0 sub tr).
    Proof.
      intros v0 y v0' y' Hy; unfold ihN.
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
      eapply kRel_trans;
        [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel ].
      apply wRecN_rel.
      - exact (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                        w0 u0 z f ev gd0 sub tr) v0 y v0' y' Hy).
      - exact (wBrRel w0 u0 z f ev gd v0 y v0' y' Hy).
    Qed.

    Lemma wRecN_step w0 u0 z f ev gd0 sub tr (gd : Good (ew A0 B0) w0) :
      kRel (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd)) (ewrec Sr w0)
           (wRecN w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd)
           (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
           (eapp (eapp (eapp Sr u0) f) (ihR f))
           (step w0 u0 z f ev gd0 sub tr gd (ihN w0 u0 z f ev gd0 sub tr)
              (ihN_ext w0 u0 z f ev gd0 sub tr gd)).
    Proof.
      destruct (wRecN_sup w0 u0 z f ev gd0 sub tr gd) as [ih0 [ihext0 [Hsub0 Heq0]]].
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); exact Heq0 |].
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
      apply (stepRel w0 u0 z f ev gd0 sub tr gd ih0 ihext0
               w0 u0 z f ev gd0 sub tr gd _ _ tr gd).
      (* the graph's hypothesis and the recursor's own are related *)
      intros v0 y v0' y' Hy; unfold ihN.
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famRed_rel |].
      eapply kRel_trans;
        [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel ].
      apply (wGr_rel (eapp f v0) (sub v0 y) _ _ _ (Hsub0 v0 y)
               (eapp f v0') (sub v0' y') _ _ _
               (proj2_sig (wGr_tot (eapp f v0') (sub v0' y') _ _))).
      - exact (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                        w0 u0 z f ev gd0 sub tr) v0 y v0' y' Hy).
      - exact (wBrRel w0 u0 z f ev gd v0 y v0' y' Hy).
    Qed.

  End RecG.



  (* ---- the same two facts across TWO nodes, which is what the step's
     congruence needs ---- *)

  Lemma wIdxBack_eq2 u0 (z : kElS aaC u0) u0' (z' : kElS aaC u0')
    (Q : kceq (kAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
              (kAt (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z'))))
    v0 y v0' y' :
    kEqAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y
          (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z')) v0' y' ->
    kcEl (bbC u0 z) v0 (wIdxBack (ew A0 B0) wfC wpf u0 z v0 y)
         (bbC u0' z') v0' (wIdxBack (ew A0 B0) wfC wpf u0' z' v0' y').
  Proof.
    intros H.
    eapply ktrE;
      [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | exact (famAtWf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0' z')
      | exact (wcB_at k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | apply knsym; exact (wIdxBack_rel (ew A0 B0) wfC wpf u0 z v0 y) |].
    eapply ktrE;
      [ exact (famAtWf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact (famAtWf (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z')))
      | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0' z')
      | exact Q
      | exact H
      | exact (wIdxBack_rel (ew A0 B0) wfC wpf u0' z' v0' y') ].
  Qed.

  Lemma wBr_ext2 w0 u0 (z : kElS aaC u0) f
    (sub : forall v0, kElS (bbC u0 z) v0 -> kWEl k nodeC (ew A0 B0) aaC bbC (eapp f v0))
    trs (ev : eval w0 (esup u0 f)) (gd : Good (ew A0 B0) w0)
    w0' u0' (z' : kElS aaC u0') f'
    (sub' : forall v0, kElS (bbC u0' z') v0 ->
              kWEl k nodeC (ew A0 B0) aaC bbC (eapp f' v0))
    trs' (ev' : eval w0' (esup u0' f')) (gd' : Good (ew A0 B0) w0')
    (Hbr : forall v0 y v0' y', kcEl (bbC u0 z) v0 y (bbC u0' z') v0' y' ->
       kWRel k nodeC (ew A0 B0) aaC bbC (sub v0 y) (sub' v0' y'))
    (HR : Rel (ew A0 B0) w0 w0')
    (Q : kceq (kAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
              (kAt (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z'))))
    v0 y v0' y' :
    kEqAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y
          (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z')) v0' y' ->
    kEqAt WF (eapp f v0) (wUp (eapp f v0) (wBr (ew A0 B0) wfC wpf u0 z f sub trs v0 y))
          WF (eapp f' v0')
             (wUp (eapp f' v0') (wBr (ew A0 B0) wfC wpf u0' z' f' sub' trs' v0' y')).
  Proof.
    intros H.
    apply (famTo_eq WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf).
    apply (mkW_eq k nodeC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) wfC wpf) tyC).
    - apply Hbr; exact (wIdxBack_eq2 u0 z u0' z' Q v0 y v0' y' H).
    - (* the two branch realisers are layer-1 related *)
      apply (Rel_w_br2 (ew A0 B0) A0 B0 (kFam_good_ty WF)
               (eval_whnf _ (whnf_w A0 B0)) w0 w0' HR u0 f u0' f' ev ev').
      eapply Rel_exp_ty;
        [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z))
        | exact (famEl_rel (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y
                   (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z')) v0' y' H) ].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The step at the SEMANTIC level, which is what the interpretation      *)
  (* supplies: it reads the label as an element of the domain family and   *)
  (* the branches as elements of the W family, where a node's own data is  *)
  (* placed.  `wSup_tree` -- a sup rebuilt from a node's data IS the node  *)
  (* -- is what moves between the two, and the index conversions carry the *)
  (* induction hypothesis and its extensionality across.                   *)
  (* ------------------------------------------------------------------ *)

  (* a family-level relation of branch indices, read on the node's own code *)
  Lemma wIdxBack_eq u0 (z : kElS aaC u0) v0 y v0' y' :
    kEqAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0 y
          (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)) v0' y' ->
    kcEl (bbC u0 z) v0 (wIdxBack (ew A0 B0) wfC wpf u0 z v0 y)
         (bbC u0 z) v0' (wIdxBack (ew A0 B0) wfC wpf u0 z v0' y').
  Proof.
    intros H.
    eapply ktrE;
      [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | exact (famAtWf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | exact (wcB_at k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | apply knsym; exact (wIdxBack_rel (ew A0 B0) wfC wpf u0 z v0 y) |].
    eapply ktrE;
      [ exact (famAtWf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact (famAtWf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) wfC wpf u0 z)
      | exact (famAtSelf (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
      | exact H
      | exact (wIdxBack_rel (ew A0 B0) wfC wpf u0 z v0' y') ].
  Qed.

  Section RecS.
    Context (m : nat) (Sr : etm).
    Local Notation ihR f :=
      (elam (ewrec (ren_etm rshift Sr) (eapp (ren_etm rshift f) (var_etm 0)))).
    Context (SC : forall w, kElAt WF w -> etm)
            (FC : forall w (x : kElAt WF w), kUFam m (SC w x))
            (cohC : forall w x w' x', kEqAt WF w x WF w' x' ->
               kceq (kAt (FC w x)) (kAt (FC w' x'))).
    Context (stepS : forall u0 (z : kElAt FA u0) f
               (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
               (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
                   kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
               (gd : Good (ew A0 B0) (esup u0 f))
               (ih : forall v0 y, kElAt (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0))
               (ihext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
                   kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0) (ih v0 y)
                        (FC (eapp f v0') (sub v0' y')) (eapp (ihR f) v0') (ih v0' y')),
               kElAt (FC (esup u0 f) (wSup u0 f z sub subext gd))
                     (eapp (eapp (eapp Sr u0) f) (ihR f))).

    Context (stepSrel : forall u0 z f sub subext gd ih ihext
                               u0' z' f' sub' subext' gd' ih' ihext',
       kEqAt FA u0 z FA u0' z' ->
       (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0' z') v0' y' ->
          kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f' v0') (sub' v0' y')) ->
       Rel (ew A0 B0) (esup u0 f) (esup u0' f') ->
       (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0' z') v0' y' ->
          kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0) (ih v0 y)
               (FC (eapp f' v0') (sub' v0' y')) (eapp (ihR f') v0') (ih' v0' y')) ->
       kRel (FC (esup u0 f) (wSup u0 f z sub subext gd))
            (eapp (eapp (eapp Sr u0) f) (ihR f))
            (stepS u0 z f sub subext gd ih ihext)
            (FC (esup u0' f') (wSup u0' f' z' sub' subext' gd'))
            (eapp (eapp (eapp Sr u0') f') (ihR f'))
            (stepS u0' z' f' sub' subext' gd' ih' ihext')).


    (* the same step, read on a node's placed data *)
    Definition stepP w0 u0 (z : kElS aaC u0) f ev gd0
      (sub : forall v0, kElS (bbC u0 z) v0 -> kWEl k nodeC (ew A0 B0) aaC bbC (eapp f v0))
      (tr : kWRel k nodeC (ew A0 B0) aaC bbC
              (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0 u0 z f ev gd0 sub))
      (gd : Good (ew A0 B0) w0)
      (ih : forall v0 y,
          kElAt (FC (eapp f v0)
                   (elOf (eapp f v0) (sub v0 y)
                      (subTr w0 u0 z f ev gd0 sub tr v0 y)
                      (subGd w0 u0 z f sub v0 y)))
                (eapp (ihR f) v0))
      (ihext : forall v0 y v0' y', kcEl (bbC u0 z) v0 y (bbC u0 z) v0' y' ->
          kRel (FC (eapp f v0)
                  (elOf (eapp f v0) (sub v0 y)
                     (subTr w0 u0 z f ev gd0 sub tr v0 y)
                     (subGd w0 u0 z f sub v0 y)))
               (eapp (ihR f) v0) (ih v0 y)
               (FC (eapp f v0')
                  (elOf (eapp f v0') (sub v0' y')
                     (subTr w0 u0 z f ev gd0 sub tr v0' y')
                     (subGd w0 u0 z f sub v0' y')))
               (eapp (ihR f) v0') (ih v0' y'))
      : kElAt (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
              (eapp (eapp (eapp Sr u0) f) (ihR f)) :=
      moveTo
        (FC (esup u0 f)
           (wSup u0 f (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)
              (fun v0 y => wUp (eapp f v0)
                 (wBr (ew A0 B0) wfC wpf u0 z f sub
                    (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                              w0 u0 z f ev gd0 sub tr)) v0 y))
              (wBr_ext w0 u0 z f sub
                 (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC w0 u0 z f ev gd0 sub
                           w0 u0 z f ev gd0 sub tr)) ev gd)
              (Good_red (ew A0 B0) w0 (esup u0 f) (proj1 ev) gd)))
        (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
        (cohC _ _ _ _ (wSup_tree w0 u0 z f ev gd0 sub tr gd))
        (eapp (eapp (eapp Sr u0) f) (ihR f))
        (stepS u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z) f _ _ _
           (fun v0 y => ih v0 (wIdxBack (ew A0 B0) wfC wpf u0 z v0 y))
           (fun v0 y v0' y' H =>
              ihext v0 (wIdxBack (ew A0 B0) wfC wpf u0 z v0 y)
                    v0' (wIdxBack (ew A0 B0) wfC wpf u0 z v0' y')
                    (wIdxBack_eq u0 z v0 y v0' y' H)))
        (eapp (eapp (eapp Sr u0) f) (ihR f)) (reds_refl _).

    (* ---- the step's congruence at a NODE, from its congruence at the
       semantic level.  `wRecG` needs this for its DEFINITION, not only for
       its laws, because the extensionality of the induction hypothesis is
       part of what the step consumes. ---- *)
    Lemma stepP_rel w0 u0 z f ev gd0 sub tr gd ih ihext
                    w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext' :
      kWRel k nodeC (ew A0 B0) aaC bbC
        (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
      Rel (ew A0 B0) w0 w0' ->
      (forall v0 y v0' y', kcEl (bbC u0 z) v0 y (bbC u0' z') v0' y' ->
         kRel (FC (eapp f v0)
                 (elOf (eapp f v0) (sub v0 y)
                    (subTr w0 u0 z f ev gd0 sub tr v0 y)
                    (subGd w0 u0 z f sub v0 y)))
              (eapp (ihR f) v0) (ih v0 y)
              (FC (eapp f' v0')
                 (elOf (eapp f' v0') (sub' v0' y')
                    (subTr w0' u0' z' f' ev' gd0' sub' tr' v0' y')
                    (subGd w0' u0' z' f' sub' v0' y')))
              (eapp (ihR f') v0') (ih' v0' y')) ->
      kRel (FC w0 (elOf w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
           (eapp (eapp (eapp Sr u0) f) (ihR f))
           (stepP w0 u0 z f ev gd0 sub tr gd ih ihext)
           (FC w0' (elOf w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
           (eapp (eapp (eapp Sr u0') f') (ihR f'))
           (stepP w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext').
    Proof.
      intros HW HR Hih.
      (* the labels, read in the domain family, and the codomain equality
         their relation gives *)
      assert (Hlab : kEqAt FA u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)
                       FA u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z')).
      { apply (famTo_eq FA A0 (wAccA A0 B0 (ew A0 B0) wfC wpf) (evalAg_refl A0)
                 u0 z A0 (wAccA A0 B0 (ew A0 B0) wfC wpf) (evalAg_refl A0) u0' z').
        exact (proj1 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC
                        w0 u0 z f ev gd0 sub w0' u0' z' f' ev' gd0' sub' HW)). }
      assert (Q : kceq (kAt (FB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)))
                       (kAt (FB u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z'))))
        by exact (cohB u0 (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0 z)
                    u0' (wxc k A0 B0 FA (ew A0 B0) wfC wpf u0' z') Hlab).
      unfold stepP.
      eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
      eapply kRel_trans; [| apply moveTo_rel ].
      apply stepSrel.
      - exact Hlab.
      - intros v0 y v0' y' Hy.
        exact (wBr_ext2 w0 u0 z f sub _ ev gd w0' u0' z' f' sub' _ ev' gd'
                 (proj2 (kWRel_sup_inv k nodeC (ew A0 B0) aaC bbC
                           w0 u0 z f ev gd0 sub w0' u0' z' f' ev' gd0' sub' HW))
                 HR Q v0 y v0' y' Hy).
      - exact (Rel_red (ew A0 B0) w0 w0' (esup u0 f) (esup u0' f')
                 (proj1 ev) (proj1 ev') HR).
      - intros v0 y v0' y' Hy.
        apply Hih; exact (wIdxBack_eq2 u0 z u0' z' Q v0 y v0' y' Hy).
    Qed.

    Definition wRecS : forall w (x : kElAt WF w), kElAt (FC w x) (ewrec Sr w) :=
      wRecG m Sr SC FC cohC stepP stepP_rel.

    Lemma wRecS_rel w x w' x' :
      kEqAt WF w x WF w' x' ->
      kRel (FC w x) (ewrec Sr w) (wRecS w x) (FC w' x') (ewrec Sr w') (wRecS w' x').
    Proof. exact (wRecG_rel m Sr SC FC cohC stepP stepP_rel w x w' x'). Qed.

    (* the induction hypothesis the computation rule supplies, and its
       extensionality: both are the recursor's own *)
    Lemma wIh_ext u0 (z : kElAt FA u0) f
      (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
      (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
          kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
      v0 y v0' y' :
      kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
      kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0)
           (famExp (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0)
              (ewrec Sr (eapp f v0)) (reds_wih_beta Sr f v0)
              (wRecS (eapp f v0) (sub v0 y)))
           (FC (eapp f v0') (sub v0' y')) (eapp (ihR f) v0')
           (famExp (FC (eapp f v0') (sub v0' y')) (eapp (ihR f) v0')
              (ewrec Sr (eapp f v0')) (reds_wih_beta Sr f v0')
              (wRecS (eapp f v0') (sub v0' y'))).
    Proof.
      intros H.
      eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
      eapply kRel_trans;
        [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel ].
      apply wRecS_rel; exact (subext v0 y v0' y' H).
    Qed.

    (* ---- THE COMPUTATION RULE ----

       `wrec Sr (sup u0 f)` reduces to the step applied to the label, the
       branching function and the induction hypothesis; this is that reduction
       at the semantic level.  Five steps: out of the recursor's top coercion
       (`moveTo_rel`), across the round trip `wDn (wUp _)` (`wRecOnG_rel` with
       `famFrom_famTo`), the node-level rule (`wRecN_step`), out of the step's
       own coercion (`moveTo_rel`), and across the step's congruence, which
       reconciles the rebuilt label (`famTo_famFrom`) and branches
       (`wSup_br`, `wSup_brC`) with the original ones. *)
    Lemma wRecS_sup u0 (z : kElAt FA u0) f sub subext gd :
      kRel (FC (esup u0 f) (wSup u0 f z sub subext gd)) (ewrec Sr (esup u0 f))
           (wRecS (esup u0 f) (wSup u0 f z sub subext gd))
           (FC (esup u0 f) (wSup u0 f z sub subext gd))
           (eapp (eapp (eapp Sr u0) f) (ihR f))
           (stepS u0 z f sub subext gd
              (fun v0 y => famExp (FC (eapp f v0) (sub v0 y)) (eapp (ihR f) v0)
                             (ewrec Sr (eapp f v0)) (reds_wih_beta Sr f v0)
                             (wRecS (eapp f v0) (sub v0 y)))
              (wIh_ext u0 z f sub subext)).
    Proof.
      unfold wRecS, wRecG.
      eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
      eapply kRel_trans;
        [ apply (wRecOnG_rel m Sr SC FC stepP stepP_rel);
          exact (famFrom_famTo WF (ew A0 B0) (Acc_intro (ew A0 B0) wfC) wpf
                   (esup u0 f) _) |].
      cbn [wRecOnG].
      eapply kRel_trans; [apply (wRecN_step m Sr SC FC stepP stepP_rel) |].
      eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
      apply stepSrel.
      - exact (famTo_famFrom FA A0 (wAccA A0 B0 (ew A0 B0) wfC wpf)
                 (evalAg_refl A0) u0 z).
      - intros v0 y v0' y' Hy.
        apply (wSup_br u0 z f sub subext v0 y v0' y' Hy).
      - exact gd.
      - intros v0 y v0' y' Hy.
        unfold ihN.
        eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
        eapply kRel_trans;
          [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel ].
        unfold wRecS, wRecG.
        eapply kRel_trans; [| apply moveTo_rel ].
        apply (wRecOnG_rel m Sr SC FC stepP stepP_rel).
        exact (wSup_brC u0 z f sub subext v0 y v0' y' Hy _ _).
    Qed.
  End RecS.


End WEl.

(* ------------------------------------------------------------------ *)
(* THE RECURSOR ACROSS TWO READINGS.                                   *)
(*                                                                    *)
(* Functionality at `wrec` compares the recursors of two DIFFERENT      *)
(* readings of one syntactic W type: their label and branching families *)
(* are only EQUAL, so the two tree types, the two codes and the two     *)
(* motives all differ.  `semrec_rel` does the same job for natrec and    *)
(* fits inside one section, because a natrec's scrutinee always lives in *)
(* the canonical `natFam j`; a tree's lives in the reading's own W       *)
(* family, so this needs two copies of everything.                      *)
(*                                                                    *)
(* The graph pays off again: the statement is about the two GRAPHS, so   *)
(* the induction is `wGr_rel`'s, with primes.                           *)
(* ------------------------------------------------------------------ *)

Section RecGX.
  Context (k : nat).
  Context (A0 B0 : etm) (FA : kUFam k A0)
          (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x))
          (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x')))
          (gW : eqty k (ew A0 B0) (ew A0 B0)).
  Context (A0' B0' : etm) (FA' : kUFam k A0')
          (SB' : forall u, kElAt FA' u -> etm)
          (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
          (redB' : forall u x, reds (eapp B0' u) (SB' u x))
          (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
             kceq (kAt (FB' u x)) (kAt (FB' u' x')))
          (gW' : eqty k (ew A0' B0') (ew A0' B0')).
  Local Notation WF := (wFam k A0 B0 FA SB FB redB cohB gW).
  Local Notation hC := (wfC k A0 B0 FA SB FB redB cohB gW).
  Local Notation pfC := (wpf A0 B0).
  Local Notation nC := (rk (ew A0 B0) (hT (ew A0 B0) hC)).
  Local Notation aC := (placeWDom k (ew A0 B0) A0 B0 hC
                          (wEv A0 B0 (ew A0 B0) hC pfC)
                          (wcA k A0 B0 FA (ew A0 B0) hC pfC)).
  Local Notation bC := (wbb k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
                           (wcA k A0 B0 FA (ew A0 B0) hC pfC)
                           (weA k A0 B0 FA (ew A0 B0) hC pfC)
                           (wcB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)).
  Local Notation mkW1 w t tr gd :=
    (mkWel k nC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) hC pfC) aC
       (wea_holds k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
          (wcA k A0 B0 FA (ew A0 B0) hC pfC) (weA k A0 B0 FA (ew A0 B0) hC pfC)) bC
       (web_holds k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
          (wcA k A0 B0 FA (ew A0 B0) hC pfC) (weA k A0 B0 FA (ew A0 B0) hC pfC)
          (wcB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)
          (weB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)) w t tr gd).
  Local Notation up1 w x := (wUp k A0 B0 FA SB FB redB cohB gW w x).
  Local Notation el1 w t tr gd := (up1 w (mkW1 w t tr gd)).
  Local Notation WF' := (wFam k A0' B0' FA' SB' FB' redB' cohB' gW').
  Local Notation hC' := (wfC k A0' B0' FA' SB' FB' redB' cohB' gW').
  Local Notation pfC' := (wpf A0' B0').
  Local Notation nC' := (rk (ew A0' B0') (hT (ew A0' B0') hC')).
  Local Notation aC' := (placeWDom k (ew A0' B0') A0' B0' hC'
                          (wEv A0' B0' (ew A0' B0') hC' pfC')
                          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC')).
  Local Notation bC' := (wbb k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
                           (wcA k A0' B0' FA' (ew A0' B0') hC' pfC')
                           (weA k A0' B0' FA' (ew A0' B0') hC' pfC')
                           (wcB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')).
  Local Notation mkW2 w t tr gd :=
    (mkWel k nC' (ew A0' B0') A0' B0' (wEv A0' B0' (ew A0' B0') hC' pfC') aC'
       (wea_holds k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC') (weA k A0' B0' FA' (ew A0' B0') hC' pfC')) bC'
       (web_holds k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC') (weA k A0' B0' FA' (ew A0' B0') hC' pfC')
          (wcB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')
          (weB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')) w t tr gd).
  Local Notation up2 w x := (wUp k A0' B0' FA' SB' FB' redB' cohB' gW' w x).
  Local Notation el2 w t tr gd := (up2 w (mkW2 w t tr gd)).

  (* the cross-instance tree relation: `WRel` was generic in the two stages
     from the start (Codes/Def.v), which is what makes this statable at all *)
  Local Notation trRel t t' :=
    (WRel (ew A0 B0) (ew A0' B0') aC aC' bC bC'
       (fun u1 x1 u1' x1' => kcEl aC u1 x1 aC' u1' x1')
       (fun u1 x1 u1' x1' v y v' y' => kcEl (bC u1 x1) v y (bC' u1' x1') v' y')
       t t').

  Context (m : nat) (Sr Sr' : etm).
  Context (SC : forall w, kElAt WF w -> etm)
          (FC : forall w (x : kElAt WF w), kUFam m (SC w x)).
  Context (SC' : forall w, kElAt WF' w -> etm)
          (FC' : forall w (x : kElAt WF' w), kUFam m (SC' w x)).
  Local Notation ihR1 f :=
    (elam (ewrec (ren_etm rshift Sr) (eapp (ren_etm rshift f) (var_etm 0)))).
  Local Notation subC1 w0 u0 z f ev gd0 sub tr v0 y :=
    (FC (eapp f v0)
       (el1 (eapp f v0) (sub v0 y)
          (subTr k A0 B0 FA SB FB redB cohB gW w0 u0 z f ev gd0 sub tr v0 y)
          (subGd k A0 B0 FA SB FB redB cohB gW w0 u0 z f sub v0 y))).
  Local Notation IH1 w0 u0 z f ev gd0 sub tr :=
    (forall v0 (y : kElS (bC u0 z) v0),
       kElAt (subC1 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR1 f) v0)).
  Local Notation IHext1 w0 u0 z f ev gd0 sub tr ih :=
    (forall v0 y v0' y', kcEl (bC u0 z) v0 y (bC u0 z) v0' y' ->
       kRel (subC1 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR1 f) v0) (ih v0 y)
            (subC1 w0 u0 z f ev gd0 sub tr v0' y') (eapp (ihR1 f) v0') (ih v0' y')).
  Local Notation ihR2 f :=
    (elam (ewrec (ren_etm rshift Sr') (eapp (ren_etm rshift f) (var_etm 0)))).
  Local Notation subC2 w0 u0 z f ev gd0 sub tr v0 y :=
    (FC' (eapp f v0)
       (el2 (eapp f v0) (sub v0 y)
          (subTr k A0' B0' FA' SB' FB' redB' cohB' gW' w0 u0 z f ev gd0 sub tr v0 y)
          (subGd k A0' B0' FA' SB' FB' redB' cohB' gW' w0 u0 z f sub v0 y))).
  Local Notation IH2 w0 u0 z f ev gd0 sub tr :=
    (forall v0 (y : kElS (bC' u0 z) v0),
       kElAt (subC2 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR2 f) v0)).
  Local Notation IHext2 w0 u0 z f ev gd0 sub tr ih :=
    (forall v0 y v0' y', kcEl (bC' u0 z) v0 y (bC' u0 z) v0' y' ->
       kRel (subC2 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR2 f) v0) (ih v0 y)
            (subC2 w0 u0 z f ev gd0 sub tr v0' y') (eapp (ihR2 f) v0') (ih v0' y')).
  Context (step : forall w0 u0 z f ev gd0 sub tr gd
             (ih : IH1 w0 u0 z f ev gd0 sub tr)
             (ihext : IHext1 w0 u0 z f ev gd0 sub tr ih),
             kElAt (FC w0 (el1 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                   (eapp (eapp (eapp Sr u0) f) (ihR1 f))).
  Context (step' : forall w0 u0 z f ev gd0 sub tr gd
             (ih : IH2 w0 u0 z f ev gd0 sub tr)
             (ihext : IHext2 w0 u0 z f ev gd0 sub tr ih),
             kElAt (FC' w0 (el2 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                   (eapp (eapp (eapp Sr' u0) f) (ihR2 f))).

  (* and what relates the two steps: this is the functionality of the step
     term, which Interp/Fun.v's `FTm` gives at the reading of `s` *)
  Context (stepRelX : forall w0 u0 z f ev gd0 sub tr gd ih ihext
                             w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext',
     trRel (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
     Rel (ew A0 B0) w0 w0' ->
     (forall v0 y v0' y', kcEl (bC u0 z) v0 y (bC' u0' z') v0' y' ->
        kRel (subC1 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR1 f) v0) (ih v0 y)
             (subC2 w0' u0' z' f' ev' gd0' sub' tr' v0' y') (eapp (ihR2 f') v0')
             (ih' v0' y')) ->
     kRel (FC w0 (el1 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
          (eapp (eapp (eapp Sr u0) f) (ihR1 f))
          (step w0 u0 z f ev gd0 sub tr gd ih ihext)
          (FC' w0' (el2 w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
          (eapp (eapp (eapp Sr' u0') f') (ihR2 f'))
          (step' w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext')).

  Context (cohC : forall w x w' x', kEqAt WF w x WF w' x' ->
             kceq (kAt (FC w x)) (kAt (FC w' x')))
          (stepRel : forall w0 u0 z f ev gd0 sub tr gd ih ihext
                            w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext',
             kWRel k nC (ew A0 B0) aC bC
               (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
             Rel (ew A0 B0) w0 w0' ->
             (forall v0 y v0' y', kcEl (bC u0 z) v0 y (bC u0' z') v0' y' ->
                kRel (subC1 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR1 f) v0) (ih v0 y)
                     (subC1 w0' u0' z' f' ev' gd0' sub' tr' v0' y')
                     (eapp (ihR1 f') v0') (ih' v0' y')) ->
             kRel (FC w0 (el1 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                  (eapp (eapp (eapp Sr u0) f) (ihR1 f))
                  (step w0 u0 z f ev gd0 sub tr gd ih ihext)
                  (FC w0' (el1 w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
                  (eapp (eapp (eapp Sr u0') f') (ihR1 f'))
                  (step w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext')).
  Local Notation WCc1 := (wcode k A0 B0 FA SB FB redB (ew A0 B0) hC pfC).
  Context (cohC' : forall w x w' x', kEqAt WF' w x WF' w' x' ->
             kceq (kAt (FC' w x)) (kAt (FC' w' x')))
          (stepRel' : forall w0 u0 z f ev gd0 sub tr gd ih ihext
                            w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext',
             kWRel k nC' (ew A0' B0') aC' bC'
               (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
             Rel (ew A0' B0') w0 w0' ->
             (forall v0 y v0' y', kcEl (bC' u0 z) v0 y (bC' u0' z') v0' y' ->
                kRel (subC2 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR2 f) v0) (ih v0 y)
                     (subC2 w0' u0' z' f' ev' gd0' sub' tr' v0' y')
                     (eapp (ihR2 f') v0') (ih' v0' y')) ->
             kRel (FC' w0 (el2 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
                  (eapp (eapp (eapp Sr' u0) f) (ihR2 f))
                  (step' w0 u0 z f ev gd0 sub tr gd ih ihext)
                  (FC' w0' (el2 w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
                  (eapp (eapp (eapp Sr' u0') f') (ihR2 f'))
                  (step' w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext')).
  Local Notation WCc2 := (wcode k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC').

  Lemma wGr_relX :
    forall w (t : kWEl k nC (ew A0 B0) aC bC w) tr gd x,
      wGr k A0 B0 FA SB FB redB cohB gW m Sr SC FC step t tr gd x ->
    forall w' (t' : kWEl k nC' (ew A0' B0') aC' bC' w') tr' gd' x',
      wGr k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' step' t' tr' gd' x' ->
      trRel t t' -> Rel (ew A0 B0) w w' ->
      kRel (FC w (el1 w t tr gd)) (ewrec Sr w) x
           (FC' w' (el2 w' t' tr' gd')) (ewrec Sr' w') x'.
  Proof.
    intros w t; induction t as [w0 u0 z f ev gd0 sub IHt].
    intros tr gd x [ih [ihext [Hsub Hx]]] w' t'.
    destruct t' as [w0' u0' z' f' ev' gd0' sub'].
    intros tr' gd' x' [ih' [ihext' [Hsub' Hx']]] HW HR.
    eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); exact Hx |].
    eapply kRel_trans;
      [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); exact Hx'].
    eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel |].
    eapply kRel_trans;
      [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famExp_rel].
    apply (stepRelX w0 u0 z f ev gd0 sub tr gd ih ihext
             w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext' HW HR).
    (* the two hypotheses are related, by the induction hypothesis *)
    intros v0 y v0' y' Hy.
    eapply kRel_trans; [apply (proj1 (kRel_same _ _ _ _ _)); apply famRed_rel |].
    eapply kRel_trans;
      [| apply kRel_sym; apply (proj1 (kRel_same _ _ _ _ _)); apply famRed_rel].
    apply (IHt v0 y _ _ _ (Hsub v0 y) (eapp f' v0') (sub' v0' y') _ _ _
             (Hsub' v0' y')).
    - exact (proj2 HW v0 y v0' y' Hy).
    - apply (Rel_w_br2 (ew A0 B0) A0 B0 (kFam_good_ty WF)
               (eval_whnf _ (whnf_w A0 B0)) w0 w0' HR u0 f u0' f' ev ev').
      eapply Rel_exp_ty;
        [ exact (redB u0 (wxc k A0 B0 FA (ew A0 B0) hC pfC u0 z)) |].
      eapply Rel_tyeq;
        [ exact (ex_intro (fun n => eqty n (kSh (bC u0 z))
                                      (SB u0 (wxc k A0 B0 FA (ew A0 B0) hC pfC u0 z)))
                   k (uf_sh (FB u0 (wxc k A0 B0 FA (ew A0 B0) hC pfC u0 z))
                        (eapp B0 u0) _ _))
        | exact (krelX (bC u0 z) v0 y (bC' u0' z') v0' y' Hy) ].
  Qed.

  (* and then the recursors themselves, at a node and at an arbitrary element
     of the two families *)
  Lemma wRecN_relX w t tr gd w' t' tr' gd' :
    trRel t t' -> Rel (ew A0 B0) w w' ->
    kRel (FC w (el1 w t tr gd)) (ewrec Sr w)
         (wRecN k A0 B0 FA SB FB redB cohB gW m Sr SC FC step stepRel w t tr gd)
         (FC' w' (el2 w' t' tr' gd')) (ewrec Sr' w')
         (wRecN k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' step' stepRel'
            w' t' tr' gd').
  Proof.
    intros H HR.
    exact (wGr_relX w t tr gd _
             (proj2_sig (wGr_tot k A0 B0 FA SB FB redB cohB gW m Sr SC FC step
                           stepRel w t tr gd))
             w' t' tr' gd' _
             (proj2_sig (wGr_tot k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC'
                           step' stepRel' w' t' tr' gd')) H HR).
  Qed.

  Lemma wRecOnG_relX w (y : kElC WCc1 w) w' (y' : kElC WCc2 w') :
    kcel WCc1 w y WCc2 w' y' ->
    kRel (FC w (up1 w y)) (ewrec Sr w)
         (wRecOnG k A0 B0 FA SB FB redB cohB gW m Sr SC FC step stepRel w y)
         (FC' w' (up2 w' y')) (ewrec Sr' w')
         (wRecOnG k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' step' stepRel'
            w' y').
  Proof.
    destruct y as [[t tr] gd]; destruct y' as [[t' tr'] gd']; intros H.
    exact (wRecN_relX w t tr gd w' t' tr' gd' (proj1 H) (proj2 (proj2 H))).
  Qed.

  Lemma wRecG_relX (HQ : kceq (kAt WF) (kAt WF')) w x w' x' :
    kEqAt WF w x WF' w' x' ->
    kRel (FC w x) (ewrec Sr w)
         (wRecG k A0 B0 FA SB FB redB cohB gW m Sr SC FC cohC step stepRel w x)
         (FC' w' x') (ewrec Sr' w')
         (wRecG k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' cohC' step'
            stepRel' w' x').
  Proof.
    intros H; unfold wRecG.
    eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
    eapply kRel_trans; [| apply moveTo_rel].
    apply wRecOnG_relX.
    exact (famFrom_eqX WF (ew A0 B0) (Acc_intro (ew A0 B0) hC) pfC w x
             WF' (ew A0' B0') (Acc_intro (ew A0' B0') hC') pfC' w' x' HQ H).
  Qed.
End RecGX.


(* ------------------------------------------------------------------ *)
(* And the same at the SEMANTIC step, which is the form the             *)
(* interpretation supplies: the node-level congruence `stepP_relX` is   *)
(* derived from it exactly as `stepP_rel` is in the one-reading case,   *)
(* through the cross-reading versions of the two reconciliation         *)
(* lemmas.                                                             *)
(* ------------------------------------------------------------------ *)

Section RecSX.
  Context (k : nat).
  Context (A0 B0 : etm) (FA : kUFam k A0)
          (SB : forall u, kElAt FA u -> etm)
          (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
          (redB : forall u x, reds (eapp B0 u) (SB u x))
          (cohB : forall u x u' x', kEqAt FA u x FA u' x' ->
             kceq (kAt (FB u x)) (kAt (FB u' x')))
          (gW : eqty k (ew A0 B0) (ew A0 B0)).
  Context (A0' B0' : etm) (FA' : kUFam k A0')
          (SB' : forall u, kElAt FA' u -> etm)
          (FB' : forall u (x : kElAt FA' u), kUFam k (SB' u x))
          (redB' : forall u x, reds (eapp B0' u) (SB' u x))
          (cohB' : forall u x u' x', kEqAt FA' u x FA' u' x' ->
             kceq (kAt (FB' u x)) (kAt (FB' u' x')))
          (gW' : eqty k (ew A0' B0') (ew A0' B0')).
  Local Notation WF := (wFam k A0 B0 FA SB FB redB cohB gW).
  Local Notation hC := (wfC k A0 B0 FA SB FB redB cohB gW).
  Local Notation pfC := (wpf A0 B0).
  Local Notation nC := (rk (ew A0 B0) (hT (ew A0 B0) hC)).
  Local Notation aC := (placeWDom k (ew A0 B0) A0 B0 hC
                          (wEv A0 B0 (ew A0 B0) hC pfC)
                          (wcA k A0 B0 FA (ew A0 B0) hC pfC)).
  Local Notation bC := (wbb k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
                           (wcA k A0 B0 FA (ew A0 B0) hC pfC)
                           (weA k A0 B0 FA (ew A0 B0) hC pfC)
                           (wcB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)).
  Local Notation wxc1 u0 z := (wxc k A0 B0 FA (ew A0 B0) hC pfC u0 z).
  Local Notation up1 w x := (wUp k A0 B0 FA SB FB redB cohB gW w x).
  Local Notation el1 w t tr gd :=
    (up1 w (mkWel k nC (ew A0 B0) A0 B0 (wEv A0 B0 (ew A0 B0) hC pfC) aC
       (wea_holds k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
          (wcA k A0 B0 FA (ew A0 B0) hC pfC) (weA k A0 B0 FA (ew A0 B0) hC pfC)) bC
       (web_holds k (ew A0 B0) A0 B0 hC (wEv A0 B0 (ew A0 B0) hC pfC)
          (wcA k A0 B0 FA (ew A0 B0) hC pfC) (weA k A0 B0 FA (ew A0 B0) hC pfC)
          (wcB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)
          (weB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC)) w t tr gd)).
  Local Notation WF' := (wFam k A0' B0' FA' SB' FB' redB' cohB' gW').
  Local Notation hC' := (wfC k A0' B0' FA' SB' FB' redB' cohB' gW').
  Local Notation pfC' := (wpf A0' B0').
  Local Notation nC' := (rk (ew A0' B0') (hT (ew A0' B0') hC')).
  Local Notation aC' := (placeWDom k (ew A0' B0') A0' B0' hC'
                          (wEv A0' B0' (ew A0' B0') hC' pfC')
                          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC')).
  Local Notation bC' := (wbb k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
                           (wcA k A0' B0' FA' (ew A0' B0') hC' pfC')
                           (weA k A0' B0' FA' (ew A0' B0') hC' pfC')
                           (wcB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')).
  Local Notation wxc2 u0 z := (wxc k A0' B0' FA' (ew A0' B0') hC' pfC' u0 z).
  Local Notation up2 w x := (wUp k A0' B0' FA' SB' FB' redB' cohB' gW' w x).
  Local Notation el2 w t tr gd :=
    (up2 w (mkWel k nC' (ew A0' B0') A0' B0' (wEv A0' B0' (ew A0' B0') hC' pfC') aC'
       (wea_holds k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC') (weA k A0' B0' FA' (ew A0' B0') hC' pfC')) bC'
       (web_holds k (ew A0' B0') A0' B0' hC' (wEv A0' B0' (ew A0' B0') hC' pfC')
          (wcA k A0' B0' FA' (ew A0' B0') hC' pfC') (weA k A0' B0' FA' (ew A0' B0') hC' pfC')
          (wcB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')
          (weB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC')) w t tr gd)).

  (* what relates the two readings *)
  Context (HQW : kceq (kAt WF) (kAt WF'))
          (HA : kceq (kAt FA) (kAt FA'))
          (HBx : forall u x u' x', kEqAt FA u x FA' u' x' ->
             kceq (kAt (FB u x)) (kAt (FB' u' x'))).

  Local Notation trRel t t' :=
    (WRel (ew A0 B0) (ew A0' B0') aC aC' bC bC'
       (fun u1 x1 u1' x1' => kcEl aC u1 x1 aC' u1' x1')
       (fun u1 x1 u1' x1' v y v' y' => kcEl (bC u1 x1) v y (bC' u1' x1') v' y')
       t t').

  (* the label of a node, read in the two domain families *)
  Lemma wLabX u0 (z : kElS aC u0) u0' (z' : kElS aC' u0') :
    kcEl aC u0 z aC' u0' z' -> kEqAt FA u0 (wxc1 u0 z) FA' u0' (wxc2 u0' z').
  Proof.
    intros H.
    apply (famTo_eqX FA A0 (wAccA A0 B0 (ew A0 B0) hC pfC) (evalAg_refl A0) u0 z
             FA' A0' (wAccA A0' B0' (ew A0' B0') hC' pfC') (evalAg_refl A0') u0' z');
      [ exact (famCeq_all FA FA' HA _ _ _ _ _ _) | exact H ].
  Qed.

  (* a branch index, across the two readings *)
  Lemma wIdxBack_eqX u0 (z : kElS aC u0) u0' (z' : kElS aC' u0')
    (Q : kceq (kAt (FB u0 (wxc1 u0 z))) (kAt (FB' u0' (wxc2 u0' z'))))
    v0 y v0' y' :
    kEqAt (FB u0 (wxc1 u0 z)) v0 y (FB' u0' (wxc2 u0' z')) v0' y' ->
    kcEl (bC u0 z) v0 (wIdxBack k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z v0 y)
         (bC' u0' z') v0' (wIdxBack k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z' v0' y').
  Proof.
    intros H.
    eapply ktrE;
      [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z)
      | exact (famAtWf (FB u0 (wxc1 u0 z)))
      | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z')
      | exact (wcB_at k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z)
      | apply knsym; exact (wIdxBack_rel k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z v0 y) |].
    eapply ktrE;
      [ exact (famAtWf (FB u0 (wxc1 u0 z)))
      | exact (famAtWf (FB' u0' (wxc2 u0' z')))
      | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z')
      | exact Q | exact H
      | exact (wIdxBack_rel k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z' v0' y') ].
  Qed.

  (* and a branch itself *)
  Lemma wBr_extX w0 u0 (z : kElS aC u0) f
    (sub : forall v0, kElS (bC u0 z) v0 -> kWEl k nC (ew A0 B0) aC bC (eapp f v0))
    trs (ev : eval w0 (esup u0 f)) (gd : Good (ew A0 B0) w0)
    w0' u0' (z' : kElS aC' u0') f'
    (sub' : forall v0, kElS (bC' u0' z') v0 ->
              kWEl k nC' (ew A0' B0') aC' bC' (eapp f' v0))
    trs' (ev' : eval w0' (esup u0' f')) (gd' : Good (ew A0' B0') w0')
    (Hbr : forall v0 y v0' y', kcEl (bC u0 z) v0 y (bC' u0' z') v0' y' ->
       trRel (sub v0 y) (sub' v0' y'))
    (HR : Rel (ew A0 B0) w0 w0')
    (Q : kceq (kAt (FB u0 (wxc1 u0 z))) (kAt (FB' u0' (wxc2 u0' z'))))
    v0 y v0' y' :
    kEqAt (FB u0 (wxc1 u0 z)) v0 y (FB' u0' (wxc2 u0' z')) v0' y' ->
    kEqAt WF (eapp f v0) (up1 (eapp f v0) (wBr k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z f sub trs v0 y))
          WF' (eapp f' v0')
             (up2 (eapp f' v0') (wBr k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z' f' sub' trs' v0' y')).
  Proof.
    intros H.
    apply (famTo_eqX WF (ew A0 B0) (Acc_intro (ew A0 B0) hC) pfC _ _
             WF' (ew A0' B0') (Acc_intro (ew A0' B0') hC') pfC' _ _);
      [ exact (famCeq_all WF WF' HQW _ _ _ _ _ _) |].
    split;
      [ apply Hbr; exact (wIdxBack_eqX u0 z u0' z' Q v0 y v0' y' H)
      | split; [ exact (ceq_ty WF WF' HQW) |] ].
    (* the two branch realisers are layer-1 related *)
    apply (Rel_w_br2 (ew A0 B0) A0 B0 (kFam_good_ty WF)
             (eval_whnf _ (whnf_w A0 B0)) w0 w0' HR u0 f u0' f' ev ev').
    eapply Rel_exp_ty; [ exact (redB u0 (wxc1 u0 z)) |].
    eapply Rel_tyeq;
      [ exact (ex_intro (fun n => eqty n (kSh (bC u0 z)) (SB u0 (wxc1 u0 z))) k
                 (uf_sh (FB u0 (wxc1 u0 z)) (eapp B0 u0) _ _))
      | exact (krelX (bC u0 z) v0 (wIdxBack k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 z v0 y)
                 (bC' u0' z') v0' (wIdxBack k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0' z' v0' y')
                 (wIdxBack_eqX u0 z u0' z' Q v0 y v0' y' H)) ].
  Qed.

  (* ---- SUP, ACROSS THE TWO READINGS.                              ----

     This is `wSup_cong` with the two instances separated: the two
     placements, the two branching instances and the two tree types all
     differ, and `WRel`'s genericity in the two stages is again what makes
     the statement expressible.  It does not use the recursor's step, so it
     sits before that context; functionality at `sup` is its only client. *)

  Local Notation lab1 u0 z := (wLab k A0 B0 FA (ew A0 B0) hC pfC u0 z).
  Local Notation lab2 u0 z := (wLab k A0' B0' FA' (ew A0' B0') hC' pfC' u0 z).
  Local Notation idx1 u0 z v0 y :=
    (wIdx k A0 B0 FA SB FB redB cohB (ew A0 B0) hC pfC u0 z v0 y).
  Local Notation idx2 u0 z v0 y :=
    (wIdx k A0' B0' FA' SB' FB' redB' cohB' (ew A0' B0') hC' pfC' u0 z v0 y).

  (* a branch index, forward: out of the two placed branching instances and
     into the two branching families.  `wIdxBack_eqX` is the other direction,
     which the recursor needs; this one is what a sup's branches need. *)
  Lemma wIdxX u0 (z : kElAt FA u0) u0' (z' : kElAt FA' u0')
    (Q : kceq (kAt (FB u0 z)) (kAt (FB' u0' z'))) v0 y v0' y' :
    kcEl (bC u0 (lab1 u0 z)) v0 y (bC' u0' (lab2 u0' z')) v0' y' ->
    kEqAt (FB u0 z) v0 (idx1 u0 z v0 y) (FB' u0' z') v0' (idx2 u0' z' v0' y').
  Proof.
    intros H.
    eapply ktrE;
      [ exact (famAtWf (FB u0 z))
      | exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 (lab1 u0 z))
      | exact (famAtWf (FB' u0' z'))
      | apply knsymU;
        exact (wcB_ceq k A0 B0 FA SB FB redB cohB (ew A0 B0) hC pfC u0 z)
      | apply knsym;
        exact (wIdx_rel k A0 B0 FA SB FB redB cohB (ew A0 B0) hC pfC u0 z v0 y) |].
    eapply ktrE;
      [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 (lab1 u0 z))
      | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0'
                 (lab2 u0' z'))
      | exact (famAtWf (FB' u0' z'))
      | eapply ktrU;
          [ exact (wwfB k A0 B0 FA SB FB redB (ew A0 B0) hC pfC u0 (lab1 u0 z))
          | exact (famAtWf (FB u0 z))
          | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0'
                     (lab2 u0' z'))
          | exact (wcB_ceq k A0 B0 FA SB FB redB cohB (ew A0 B0) hC pfC u0 z)
          | eapply ktrU;
              [ exact (famAtWf (FB u0 z))
              | exact (famAtWf (FB' u0' z'))
              | exact (wwfB k A0' B0' FA' SB' FB' redB' (ew A0' B0') hC' pfC' u0'
                         (lab2 u0' z'))
              | exact Q
              | apply knsymU;
                exact (wcB_ceq k A0' B0' FA' SB' FB' redB' cohB' (ew A0' B0') hC'
                         pfC' u0' z') ] ]
      | exact H
      | exact (wIdx_rel k A0' B0' FA' SB' FB' redB' cohB' (ew A0' B0') hC' pfC'
                 u0' z' v0' y') ].
  Qed.

  Lemma wSup_congX u0 (z : kElAt FA u0) f sub subext gd
    u0' (z' : kElAt FA' u0') f' sub' subext' gd' :
    kEqAt FA u0 z FA' u0' z' ->
    (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB' u0' z') v0' y' ->
       kEqAt WF (eapp f v0) (sub v0 y) WF' (eapp f' v0') (sub' v0' y')) ->
    Rel (ew A0 B0) (esup u0 f) (esup u0' f') ->
    kEqAt WF (esup u0 f)
            (wSup k A0 B0 FA SB FB redB cohB gW u0 f z sub subext gd)
          WF' (esup u0' f')
            (wSup k A0' B0' FA' SB' FB' redB' cohB' gW' u0' f' z' sub' subext'
               gd').
  Proof.
    intros Hz Hsub HR.
    unfold wSup.
    apply (famTo_eqX WF (ew A0 B0) (Acc_intro (ew A0 B0) hC) pfC _ _
             WF' (ew A0' B0') (Acc_intro (ew A0' B0') hC') pfC' _ _);
      [ exact (famCeq_all WF WF' HQW _ _ _ _ _ _) |].
    split; [| split; [ exact (ceq_ty WF WF' HQW) | exact HR ]].
    split.
    - (* labels: the two placements of related elements are related *)
      apply (famFrom_eqX FA A0 (wAccA A0 B0 (ew A0 B0) hC pfC) (evalAg_refl A0)
               u0 z FA' A0' (wAccA A0' B0' (ew A0' B0') hC' pfC')
               (evalAg_refl A0') u0' z');
        [ exact HA | exact Hz ].
    - (* branches: read the two placed indices in the two branching families,
         then the hypothesis, then back down *)
      intros v0 y v0' y' Hy.
      exact (proj1 (famFrom_eqX WF (ew A0 B0) (Acc_intro (ew A0 B0) hC) pfC _ _
                      WF' (ew A0' B0') (Acc_intro (ew A0' B0') hC') pfC' _ _
                      HQW
                      (Hsub _ _ _ _
                         (wIdxX u0 z u0' z' (HBx u0 z u0' z' Hz) v0 y v0' y' Hy)))).
  Qed.

  Context (m : nat) (Sr Sr' : etm).
  Context (SC : forall w, kElAt WF w -> etm)
          (FC : forall w (x : kElAt WF w), kUFam m (SC w x))
          (cohC : forall w x w' x', kEqAt WF w x WF w' x' ->
             kceq (kAt (FC w x)) (kAt (FC w' x'))).
  Context (SC' : forall w, kElAt WF' w -> etm)
          (FC' : forall w (x : kElAt WF' w), kUFam m (SC' w x))
          (cohC' : forall w x w' x', kEqAt WF' w x WF' w' x' ->
             kceq (kAt (FC' w x)) (kAt (FC' w' x'))).
  Local Notation ihR1 f :=
    (elam (ewrec (ren_etm rshift Sr) (eapp (ren_etm rshift f) (var_etm 0)))).
  Local Notation subC1 w0 u0 z f ev gd0 sub tr v0 y :=
    (FC (eapp f v0)
       (el1 (eapp f v0) (sub v0 y)
          (subTr k A0 B0 FA SB FB redB cohB gW w0 u0 z f ev gd0 sub tr v0 y)
          (subGd k A0 B0 FA SB FB redB cohB gW w0 u0 z f sub v0 y))).
  Local Notation ihR2 f :=
    (elam (ewrec (ren_etm rshift Sr') (eapp (ren_etm rshift f) (var_etm 0)))).
  Local Notation subC2 w0 u0 z f ev gd0 sub tr v0 y :=
    (FC' (eapp f v0)
       (el2 (eapp f v0) (sub v0 y)
          (subTr k A0' B0' FA' SB' FB' redB' cohB' gW' w0 u0 z f ev gd0 sub tr v0 y)
          (subGd k A0' B0' FA' SB' FB' redB' cohB' gW' w0 u0 z f sub v0 y))).
  Context (stepS : forall u0 (z : kElAt FA u0) f
             (sub : forall v0 (y : kElAt (FB u0 z) v0), kElAt WF (eapp f v0))
             (subext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
                kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f v0') (sub v0' y'))
             (gd : Good (ew A0 B0) (esup u0 f))
             (ih : forall v0 y, kElAt (FC (eapp f v0) (sub v0 y)) (eapp (ihR1 f) v0))
             (ihext : forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0 z) v0' y' ->
                kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR1 f) v0) (ih v0 y)
                     (FC (eapp f v0') (sub v0' y')) (eapp (ihR1 f) v0') (ih v0' y')),
             kElAt (FC (esup u0 f)
                      (wSup k A0 B0 FA SB FB redB cohB gW u0 f z sub subext gd))
                   (eapp (eapp (eapp Sr u0) f) (ihR1 f)))
          (stepSrel : forall u0 z f sub subext gd ih ihext
                             u0' z' f' sub' subext' gd' ih' ihext',
             kEqAt FA u0 z FA u0' z' ->
             (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0' z') v0' y' ->
                kEqAt WF (eapp f v0) (sub v0 y) WF (eapp f' v0') (sub' v0' y')) ->
             Rel (ew A0 B0) (esup u0 f) (esup u0' f') ->
             (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB u0' z') v0' y' ->
                kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR1 f) v0) (ih v0 y)
                     (FC (eapp f' v0') (sub' v0' y')) (eapp (ihR1 f') v0')
                     (ih' v0' y')) ->
             kRel (FC (esup u0 f)
                     (wSup k A0 B0 FA SB FB redB cohB gW u0 f z sub subext gd))
                  (eapp (eapp (eapp Sr u0) f) (ihR1 f))
                  (stepS u0 z f sub subext gd ih ihext)
                  (FC (esup u0' f')
                     (wSup k A0 B0 FA SB FB redB cohB gW u0' f' z' sub' subext' gd'))
                  (eapp (eapp (eapp Sr u0') f') (ihR1 f'))
                  (stepS u0' z' f' sub' subext' gd' ih' ihext')).
  Context (stepS' : forall u0 (z : kElAt FA' u0) f
             (sub : forall v0 (y : kElAt (FB' u0 z) v0), kElAt WF' (eapp f v0))
             (subext : forall v0 y v0' y', kEqAt (FB' u0 z) v0 y (FB' u0 z) v0' y' ->
                kEqAt WF' (eapp f v0) (sub v0 y) WF' (eapp f v0') (sub v0' y'))
             (gd : Good (ew A0' B0') (esup u0 f))
             (ih : forall v0 y, kElAt (FC' (eapp f v0) (sub v0 y)) (eapp (ihR2 f) v0))
             (ihext : forall v0 y v0' y', kEqAt (FB' u0 z) v0 y (FB' u0 z) v0' y' ->
                kRel (FC' (eapp f v0) (sub v0 y)) (eapp (ihR2 f) v0) (ih v0 y)
                     (FC' (eapp f v0') (sub v0' y')) (eapp (ihR2 f) v0') (ih v0' y')),
             kElAt (FC' (esup u0 f)
                      (wSup k A0' B0' FA' SB' FB' redB' cohB' gW' u0 f z sub subext gd))
                   (eapp (eapp (eapp Sr' u0) f) (ihR2 f)))
          (stepSrel' : forall u0 z f sub subext gd ih ihext
                             u0' z' f' sub' subext' gd' ih' ihext',
             kEqAt FA' u0 z FA' u0' z' ->
             (forall v0 y v0' y', kEqAt (FB' u0 z) v0 y (FB' u0' z') v0' y' ->
                kEqAt WF' (eapp f v0) (sub v0 y) WF' (eapp f' v0') (sub' v0' y')) ->
             Rel (ew A0' B0') (esup u0 f) (esup u0' f') ->
             (forall v0 y v0' y', kEqAt (FB' u0 z) v0 y (FB' u0' z') v0' y' ->
                kRel (FC' (eapp f v0) (sub v0 y)) (eapp (ihR2 f) v0) (ih v0 y)
                     (FC' (eapp f' v0') (sub' v0' y')) (eapp (ihR2 f') v0')
                     (ih' v0' y')) ->
             kRel (FC' (esup u0 f)
                     (wSup k A0' B0' FA' SB' FB' redB' cohB' gW' u0 f z sub subext gd))
                  (eapp (eapp (eapp Sr' u0) f) (ihR2 f))
                  (stepS' u0 z f sub subext gd ih ihext)
                  (FC' (esup u0' f')
                     (wSup k A0' B0' FA' SB' FB' redB' cohB' gW' u0' f' z' sub' subext' gd'))
                  (eapp (eapp (eapp Sr' u0') f') (ihR2 f'))
                  (stepS' u0' z' f' sub' subext' gd' ih' ihext')).

  (* the cross-reading step relation: this is the functionality of the step
     term, which the fundamental lemma gets from its own induction *)
  Context (stepSrelX : forall u0 z f sub subext gd ih ihext
                              u0' z' f' sub' subext' gd' ih' ihext',
     kEqAt FA u0 z FA' u0' z' ->
     (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB' u0' z') v0' y' ->
        kEqAt WF (eapp f v0) (sub v0 y) WF' (eapp f' v0') (sub' v0' y')) ->
     Rel (ew A0 B0) (esup u0 f) (esup u0' f') ->
     (forall v0 y v0' y', kEqAt (FB u0 z) v0 y (FB' u0' z') v0' y' ->
        kRel (FC (eapp f v0) (sub v0 y)) (eapp (ihR1 f) v0) (ih v0 y)
             (FC' (eapp f' v0') (sub' v0' y')) (eapp (ihR2 f') v0') (ih' v0' y')) ->
     kRel (FC (esup u0 f)
             (wSup k A0 B0 FA SB FB redB cohB gW u0 f z sub subext gd))
          (eapp (eapp (eapp Sr u0) f) (ihR1 f))
          (stepS u0 z f sub subext gd ih ihext)
          (FC' (esup u0' f')
             (wSup k A0' B0' FA' SB' FB' redB' cohB' gW' u0' f' z' sub' subext' gd'))
          (eapp (eapp (eapp Sr' u0') f') (ihR2 f'))
          (stepS' u0' z' f' sub' subext' gd' ih' ihext')).

  Lemma stepP_relX w0 u0 z f ev gd0 sub tr gd ih ihext
                   w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext' :
    trRel (wel_sup w0 u0 z f ev gd0 sub) (wel_sup w0' u0' z' f' ev' gd0' sub') ->
    Rel (ew A0 B0) w0 w0' ->
    (forall v0 y v0' y', kcEl (bC u0 z) v0 y (bC' u0' z') v0' y' ->
       kRel (subC1 w0 u0 z f ev gd0 sub tr v0 y) (eapp (ihR1 f) v0) (ih v0 y)
            (subC2 w0' u0' z' f' ev' gd0' sub' tr' v0' y') (eapp (ihR2 f') v0')
            (ih' v0' y')) ->
    kRel (FC w0 (el1 w0 (wel_sup w0 u0 z f ev gd0 sub) tr gd))
         (eapp (eapp (eapp Sr u0) f) (ihR1 f))
         (stepP k A0 B0 FA SB FB redB cohB gW m Sr SC FC cohC stepS
            w0 u0 z f ev gd0 sub tr gd ih ihext)
         (FC' w0' (el2 w0' (wel_sup w0' u0' z' f' ev' gd0' sub') tr' gd'))
         (eapp (eapp (eapp Sr' u0') f') (ihR2 f'))
         (stepP k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' cohC' stepS'
            w0' u0' z' f' ev' gd0' sub' tr' gd' ih' ihext').
  Proof.
    intros HW HR Hih.
    assert (Hlab : kEqAt FA u0 (wxc1 u0 z) FA' u0' (wxc2 u0' z'))
      by exact (wLabX u0 z u0' z' (proj1 HW)).
    assert (Q : kceq (kAt (FB u0 (wxc1 u0 z))) (kAt (FB' u0' (wxc2 u0' z'))))
      by exact (HBx u0 (wxc1 u0 z) u0' (wxc2 u0' z') Hlab).
    unfold stepP.
    eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
    eapply kRel_trans; [| apply moveTo_rel ].
    apply stepSrelX.
    - exact Hlab.
    - intros v0 y v0' y' Hy.
      exact (wBr_extX w0 u0 z f sub _ ev gd w0' u0' z' f' sub' _ ev' gd'
               (proj2 HW) HR Q v0 y v0' y' Hy).
    - exact (Rel_red (ew A0 B0) w0 w0' (esup u0 f) (esup u0' f')
               (proj1 ev) (proj1 ev') HR).
    - intros v0 y v0' y' Hy.
      apply Hih; exact (wIdxBack_eqX u0 z u0' z' Q v0 y v0' y' Hy).
  Qed.

  (* and the recursor itself, across the two readings *)
  Lemma wRecS_relX w x w' x' :
    kEqAt WF w x WF' w' x' ->
    kRel (FC w x) (ewrec Sr w)
         (wRecS k A0 B0 FA SB FB redB cohB gW m Sr SC FC cohC stepS stepSrel w x)
         (FC' w' x') (ewrec Sr' w')
         (wRecS k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' cohC' stepS'
            stepSrel' w' x').
  Proof.
    intros H.
    exact (wRecG_relX k A0 B0 FA SB FB redB cohB gW A0' B0' FA' SB' FB' redB' cohB'
             gW' m Sr Sr' SC FC SC' FC'
             (stepP k A0 B0 FA SB FB redB cohB gW m Sr SC FC cohC stepS)
             (stepP k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' cohC' stepS')
             stepP_relX cohC
             (stepP_rel k A0 B0 FA SB FB redB cohB gW m Sr SC FC cohC stepS stepSrel)
             cohC'
             (stepP_rel k A0' B0' FA' SB' FB' redB' cohB' gW' m Sr' SC' FC' cohC'
                stepS' stepSrel')
             HQW w x w' x' H).
  Qed.
End RecSX.
