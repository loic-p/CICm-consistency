From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules Typing.Subst Typing.WSubst.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.PiFam Interp.SigFam Interp.WFam Interp.Univ Interp.Env Interp.Elem
  Interp.PiEl Interp.SigEl Interp.WEl Interp.Rec Interp.Lift Interp.LiftN
  Interp.LiftFam Interp.Def Interp.Inv Interp.Ctx Interp.Subst Interp.Fun.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* Theorem 9.2, the layer-2 fundamental lemma.  Three things about the shape
   of the statement are forced, and each is worth spelling out, because none
   of them is what one would write down first.

   1.  THE TYPE'S INTERPRETATION IS AN INPUT, NOT AN OUTPUT.  Every rule of
   the redundant style carries the formation judgement of every type it
   mentions, so a term's type always comes with its own derivation, and its
   family is available from that sibling premise.  Taking it as an input is
   what makes the conversion case work: there the conclusion's type is a
   DIFFERENT type from the premise's, and a statement that produced the type's
   family would have to produce two unrelated ones and then reconcile them.

   2.  THE TYPE PART IS CONDITIONED ON AN EQUALITY TO THE UNIVERSE FAMILY,
   not on the type index being syntactically `univ m`.  A term whose type is
   merely CONVERTIBLE to a universe is still a type, and the equality travels
   along the conversion while the syntax does not.  Note the order of the
   binders: m is bound before the level S m appears, so no cast is needed --
   `kceq` relates codes at one level, and writing the level as `S m` is what
   keeps that constraint solvable.

   3.  THE CONVERSION CLAUSE OF THE INTERPRETATION IS WHAT MAKES 1 POSSIBLE.
   With the type's family an input, the conversion case has to move a value
   from the family of the premise's type to the family of the conclusion's,
   and `i_conv` (Interp/Def.v) is exactly that move. *)

(* ------------------------------------------------------------------ *)
(* Related environments.                                              *)
(* ------------------------------------------------------------------ *)

(* Two environments fitting G and related, TOGETHER with the layer-1
   relatedness of the substitutions they induce.  In v1 that last part was
   not derivable from the other three -- v1's `EnvOf_SubstRel` needed an
   induction on `wfc G`, which 9.2 does not have at hand -- so it travelled
   with them.  In v2 `EnvOf_SubstRel` needs no derivations (Interp/Ctx.v), so
   the bundle is kept only because every consumer wants all four at once. *)
Definition EnvRelOf (G : ctx) (rho rho' : Env) : Prop :=
  EnvOf G rho /\ EnvOf G rho' /\ EnvRel rho rho' /\ SubstRel G (rsub rho) (rsub rho').

Lemma EnvRelOf_nil : EnvRelOf nil nil nil.
Proof. repeat split; exact I. Qed.

Lemma EnvRelOf_ext G rho rho' (A : tm) k
  (FA : kUFam k (ers rho A)) (FA' : kUFam k (ers rho' A)) u x u' x' :
  EnvRelOf G rho rho' -> kRel FA u x FA' u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros [HO [HO' [HR HS]]] Hrel; split; [| split; [| split]].
  - apply EnvOf_ext; exact HO.
  - apply EnvOf_ext; exact HO'.
  - apply EnvRel_ext; [exact HR | exact Hrel].
  - apply SubstRel_cons; [exact HS |].
    exact (kRel_rel FA u x FA' u' x' Hrel).
Qed.

(* and the same when the entry's realiser is only layer-1 equal to the context
   type's, which a congruence at a binder forces *)
Lemma EnvRelOf_ext_ty G rho rho' (A : tm) k S S'
  (FA : kUFam k S) (FA' : kUFam k S') u x u' x' :
  EnvRelOf G rho rho' -> tyeq S (ers rho A) -> tyeq S' (ers rho' A) ->
  kRel FA u x FA' u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros [HO [HO' [HR HS]]] Hty Hty' Hrel; split; [| split; [| split]].
  - apply EnvOf_ext_ty; [exact HO | exact Hty].
  - apply EnvOf_ext_ty; [exact HO' | exact Hty'].
  - apply EnvRel_ext; [exact HR | exact Hrel].
  - apply SubstRel_cons; [exact HS |].
    destruct Hty as [n Hn].
    eapply Rel_cast; [exact Hn | exact (kRel_rel FA u x FA' u' x' Hrel)].
Qed.

Lemma lvls_of_EnvRelOf G rho rho' : EnvRelOf G rho rho' -> lvls rho = lvls rho'.
Proof. intros [_ [_ [HR _]]]; exact (lvls_of_EnvRel rho rho' HR). Qed.

(* ------------------------------------------------------------------ *)
(* FUNCTIONALITY, PROVED INSIDE 9.2.                                  *)
(*                                                                    *)
(* Not as a standalone theorem about raw derivations, because one side  *)
(* condition is missing there: FTy needs `tyeq w w'` -- that the two    *)
(* erasures of one type are equal TYPES -- and only layer 1 proves it.  *)
(* It threads downward through the type formers (eqty_pi_dom and        *)
(* friends), which is why the clause lemmas in Interp/Fun.v are         *)
(* provable untyped, but it does NOT thread through a term elimination:  *)
(* at `app A B f a` the conclusion's realiser is wB wa xa, and the       *)
(* domain's tyeq cannot be recovered from it.  Under the typing          *)
(* derivation it comes from fundamental_U applied to the formation        *)
(* premises that the redundant style already carries.                     *)
(* ------------------------------------------------------------------ *)

Definition FunTm (G : ctx) (t : tm) : Prop :=
  forall rho rho' (HE : EnvRelOf G rho rho')
    k Sy (F : kUFam k Sy) w (x : kElAt F w) (D : ITm rho t k Sy F w x)
    Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w') (D' : ITm rho' t k Sy' F' w' x'),
    kceq (kAt F) (kAt F') -> Rel Sy' w w' -> kRel F w x F' w' x'.

(* Functionality on TYPES is the same statement one level up: a type is a term
   of the universe, and the universe's own equality IS the equality of the
   families it decodes to. *)
Lemma FunTy_of_FunTm (G : ctx) (A : tm) (H : FunTm G A) :
  forall rho rho' (HE : EnvRelOf G rho rho')
    k w (F : kUFam k w) w' (F' : kUFam k w'),
    ITy rho A k w F -> ITy rho' A k w' F' -> eqty k w w' ->
    kceq (kAt F) (kAt F').
Proof.
  intros rho rho' HE k w F w' F' DA DA' Hty.
  assert (Hrel : Rel (euniv k) w w').
  { apply (Rel_univ_intro (euniv k) k w w');
      [ exact (univ_good_ty (S k) k (euniv k) (Nat.lt_succ_diag_r k)
                 (eval_whnf _ (whnf_univ k)))
      | apply eval_whnf, whnf_univ
      | exact Hty ]. }
  pose proof (H rho rho' HE (S k) (euniv k) (univFam k) w (famEl F)
                (i_ty rho A k w F DA)
                (euniv k) (univFam k) w' (famEl F')
                (i_ty rho' A k w' F' DA')
                (famAtSelf (univFam k)) Hrel) as Hr.
  pose proof (uEq_at (famEl F) (famEl F') (kRel_at Hr)) as Hi.
  rewrite !elFam_famEl in Hi.
  exact Hi.
Qed.

(* ---- t_var.  Both derivations read the same entry of their own
     environment, and EnvRel relates those two entries: composing the three is
     EntryRel_trans, which the package formulation of EntryRel supports.  The
     induction is on the INDEX, which the induction on the typing derivation
     does not supply. ---- *)
Lemma funtm_var : forall i (G : ctx), FunTm G (var_tm i).
Proof.
  intros i G rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  destruct HE as [_ [_ [HR _]]].
  revert rho rho' HR x x' D D'; induction i as [| i IH];
    intros rho rho' HR x x' D D';
    pose proof (itm_inv _ _ _ _ _ _ _ D) as E;
    pose proof (itm_inv _ _ _ _ _ _ _ D') as E';
    cbn [TmInv] in E, E';
    destruct E' as [[HT' _] | E'];
      try (solve [exact (kRel_of_total F F' Pc HT' w x w' x' Hrel)]);
    destruct E as [[HT _] | E];
      try (solve [exact (kRel_of_total F F' Pc
                           (TotalFam_ceq F F' Pc HT) w x w' x' Hrel)]);
    cbn [TmShape VarShape] in E, E';
    destruct rho as [| en rho0]; try (solve [destruct E]);
    destruct rho' as [| en' rho0']; try (solve [destruct E']);
    cbn [EnvRel] in HR.
  - destruct HR as [_ Hen].
    eapply EntryRel_at.
    eapply EntryRel_trans; [exact E |].
    eapply EntryRel_trans; [exact Hen | apply EntryRel_sym; exact E'].
  - destruct HR as [HR0 _].
    destruct E as [x0 [D0 HE]]; destruct E' as [x0' [D0' HE']].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same F w x w x0)); exact HE |].
    eapply kRel_trans;
      [ exact (IH rho0 rho0' HR0 x0 x0' D0 D0')
      | apply (proj1 (kRel_same F' w' x0' w' x')); apply kEqAt_sym; exact HE' ].
Qed.

(* Both derivations are arbitrary here, so both get decoded and both IsVals
   have to be absorbed -- one on each side of the relation between the two
   clauses' canonical values.  That is all any case's plumbing amounts to. *)
Lemma kRel_of_IsVal_l {k Sy Syc} (F : kUFam k Sy) (Fc : kUFam k Syc)
  w (x : kElAt F w) wc (xc : kElAt Fc wc) :
  IsVal F w x Fc wc xc -> kRel F w x Fc wc xc.
Proof.
  intros [P HP].
  eapply kRel_trans;
    [ split; [exact P | apply kto_coh]
    | apply (proj1 (kRel_same Fc w _ wc xc)); exact HP ].
Qed.

Lemma kRel_of_IsVal2 {k Sy Sy' Syc Syc'} (F : kUFam k Sy) (F' : kUFam k Sy')
  (Fc : kUFam k Syc) (Fc' : kUFam k Syc')
  w (x : kElAt F w) w' (x' : kElAt F' w')
  wc (xc : kElAt Fc wc) wc' (xc' : kElAt Fc' wc') :
  IsVal F w x Fc wc xc -> IsVal F' w' x' Fc' wc' xc' ->
  kRel Fc wc xc Fc' wc' xc' -> kRel F w x F' w' x'.
Proof.
  intros H1 H2 Hm.
  eapply kRel_trans; [exact (kRel_of_IsVal_l F Fc w x wc xc H1) |].
  eapply kRel_trans; [exact Hm |].
  apply kRel_sym; exact (kRel_of_IsVal_l F' Fc' w' x' wc' xc' H2).
Qed.

(* The shape common to every case: kill the two proof readings, then compare
   the two clauses' own values. *)
Ltac funtm_start D D' :=
  pose proof (itm_inv _ _ _ _ _ _ _ D) as E;
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E'.

Ltac funtm_proofs Ea Eb F F' Pc w x w' x' Hrel :=
  destruct Eb as [[HT' _] | Eb];
  [ exact (kRel_of_total F F' Pc HT' w x w' x' Hrel) |];
  destruct Ea as [[HT _] | Ea];
  [ exact (kRel_of_total F F' Pc (TotalFam_ceq F F' Pc HT) w x w' x' Hrel) |].

Lemma funtm_zero (G : ctx) (kk : nat) : FunTm G (zero kk).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv TmShape ZeroVal Shaped] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  destruct E as [Ek Hv]; destruct E' as [Ek' Hv'].
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x]; apply kRel_refl.
Qed.

Lemma funtm_false (G : ctx) (kk : nat) : FunTm G (false_ kk).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv TmShape FalseVal Shaped] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x].
  apply (proj1 (kRel_same (propFam k) _ _ _ _)).
  apply propEq_iff; split; [split; exact (fun h => h) | exact (fl_g d)].
Qed.

(* ---- the type formers, once.  At such a subject the decoder's branch IS
     TyVal, so both readings hand over an ITy derivation and the universe's own
     equality turns their equality into the relation asked for.  Each former
     then only has to say why its two readings agree, which is what its
     inversion lemma in Interp/Inv.v is for. ---- *)
Lemma funtm_former (G : ctx) (t : tm)
  (Hsh : forall rho k Sy (F : kUFam k Sy) w (x : kElAt F w),
           TmShape rho t k Sy F w x -> TyVal rho t k Sy F w x)
  (H : forall rho rho' k w (F : kUFam k w) w' (F' : kUFam k w'),
         EnvRelOf G rho rho' -> ITy rho t k w F -> ITy rho' t k w' F' ->
         eqty k w w' /\ kceq (kAt F) (kAt F')) :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  apply Hsh in E; apply Hsh in E'.
  destruct k as [| k0]; [cbn [TyVal] in E; destruct E |].
  cbn [TyVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct (H rho rho' k0 w (ty_F0 d) w' (ty_F0 d') HE (ty_D d) (ty_D d'))
    as [Hty Hi].
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x].
  apply (proj1 (kRel_same (univFam k0) _ _ _ _)).
  apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
  exact (famCeq_all (ty_F0 d) (ty_F0 d') Hi v h pf v' h' pf').
Qed.

Lemma funtm_nat (G : ctx) (kk : nat) : FunTm G (nat_ kk).
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  split; [exact (uf_ty F) |].
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf (natFam k)) | exact (famAtWf F')
    | exact (ity_nat_inv rho (nat_ kk) k (ers rho (nat_ kk)) F D)
    | apply knsymU;
      exact (ity_nat_inv rho' (nat_ kk) k (ers rho' (nat_ kk)) F' D') ].
Qed.

Lemma funtm_prop (G : ctx) (kk : nat) : FunTm G (prop kk).
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  split; [exact (uf_ty F) |].
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf (propFam k)) | exact (famAtWf F')
    | exact (ity_prop_inv rho (prop kk) k (ers rho (prop kk)) F D)
    | apply knsymU;
      exact (ity_prop_inv rho' (prop kk) k (ers rho' (prop kk)) F' D') ].
Qed.

Lemma funtm_univ (G : ctx) (kk m : nat) : FunTm G (univ kk m).
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  pose proof (ity_lvl_dec rho _ k _ F D) as El; cbn [LvlDec] in El; subst k.
  split; [exact (uf_ty F) |].
  destruct (ity_univ_ceq rho (univ kk m) kk _ F D) as [d1 [E1 Q]].
  destruct (ity_univ_ceq rho' (univ kk m) kk _ F' D') as [d2 [E2 Q']].
  assert (Ed : d2 = d1) by lia; subst d2.
  rewrite (upF_pirr d1 kk E2 E1 (univFam m)) in Q'.
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf (upF d1 kk E1 (univFam m)))
    | exact (famAtWf F') | exact Q | apply knsymU; exact Q' ].
Qed.

Lemma funtm_succ (G : ctx) (n : tm) (IHn : FunTm G n) : FunTm G (succ n).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv TmShape SuccVal Shaped] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  assert (Hs : Rel enat (esucc (sc_wn d)) (esucc (sc_wn d'))).
  { destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
    eapply Rel_trans;
      [ apply Rel_sym; exact (proj2 (proj1 (natEq_iff _ _) HQ)) |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy' enat w w' (ceq_ty F' (natFam k) Q') Hrel)
      | exact (proj2 (proj1 (natEq_iff _ _) HQ')) ]. }
  assert (Hn : Rel enat (sc_wn d) (sc_wn d'))
    by (apply Rel_nat_intro;
        [ apply gt_nat | apply ev_nat
        | apply (NatPer_succ_inv (esucc (sc_wn d)) (esucc (sc_wn d'))
                   (sc_wn d) (sc_wn d') eq_refl eq_refl);
          exact (Rel_nat_elim enat (esucc (sc_wn d)) (esucc (sc_wn d')) ev_nat Hs) ]).
  pose proof (IHn rho rho' HE k enat (natFam k) (sc_wn d) (sc_xn d) (sc_D d)
                enat (natFam k) (sc_wn d') (sc_xn d') (sc_D d')
                (famAtSelf (natFam k)) Hn) as Hx.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x].
  apply (proj1 (kRel_same (natFam k) _ _ _ _)).
  apply natEq_iff; split;
    [ unfold natSucc; rewrite !natIdx_natE;
      exact (f_equal S (proj1 (proj1 (natEq_iff _ _) (kRel_at Hx))))
    | exact Hs ].
Qed.

(* ------------------------------------------------------------------ *)
(* The layer-1 side condition.  A type former's functionality needs the *)
(* two realisers to be layer-1 equal AT THE LEVEL OF THE FAMILIES in    *)
(* hand, which is not the level the layer-1 fundamental theorem happens  *)
(* to produce.  eqty_restrict bridges the two: both realisers are        *)
(* reflexively equal at the family's level (uf_ty), and that is enough   *)
(* to restrict an equality obtained at any other level.                  *)
(* ------------------------------------------------------------------ *)

Definition LTy (G : ctx) (t : tm) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> tyeq (ers rho t) (ers rho' t).

Lemma eqty_at_lvl k w w' : eqty k w w -> eqty k w' w' -> tyeq w w' -> eqty k w w'.
Proof. intros Hw Hw' [n Hn]; exact (eqty_restrict k n w w' Hn Hw Hw'). Qed.

Lemma funtm_former_l (G : ctx) (t : tm)
  (Hsh : forall rho k Sy (F : kUFam k Sy) w (x : kElAt F w),
           TmShape rho t k Sy F w x -> TyVal rho t k Sy F w x)
  (Lt : LTy G t)
  (H : forall rho rho' k w (F : kUFam k w) w' (F' : kUFam k w'),
         EnvRelOf G rho rho' -> ITy rho t k w F -> ITy rho' t k w' F' ->
         kceq (kAt F) (kAt F')) :
  FunTm G t.
Proof.
  apply funtm_former; [exact Hsh |].
  intros rho rho' k w F w' F' HE D D'.
  split; [| exact (H rho rho' k w F w' F' HE D D')].
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  exact (eqty_at_lvl k _ _ (uf_ty F) (uf_ty F') (Lt rho rho' HE)).
Qed.

Lemma funtm_prf (G : ctx) (kk : nat) (p : tm)
  (Lp : LTy G (prf kk p)) (IHp : FunTm G p) :
  FunTm G (prf kk p).
Proof.
  apply (funtm_former_l G (prf kk p));
    [intros rho k Sy F w x H; exact H | exact Lp |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ity_lvl_dec rho (prf kk p) k w F D) as El; cbn [LvlDec] in El; subst k.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  pose proof (Lp rho rho' HE) as Hty.
  destruct (ity_prf_inv rho (prf kk p) kk (ers rho (prf kk p)) F D)
    as [j [wp [xp [Dp Hc]]]].
  destruct (ity_prf_inv rho' (prf kk p) kk (ers rho' (prf kk p)) F' D')
    as [j' [wp' [xp' [Dp' Hc']]]].
  pose proof (itm_lvl p rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                NotPrfR_prop Dp _ _ _ _ _ NotPrfR_prop Dp') as Ej; subst j'.
  assert (Ep : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ep' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  subst wp wp'.
  assert (Hpr : PR (ers rho p) (ers rho' p)).
  { destruct Hty as [n Hn].
    exact (eqty_prf_inv n _ _ _ _ Hn (ev_prf_self _) (ev_prf_self _)). }
  assert (Hrp : Rel eprop (ers rho p) (ers rho' p))
    by (apply Rel_prop_intro;
        [ exact good_ty_prop | apply eval_whnf, whnf_prop | exact Hpr ]).
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf (prfF kk xp)) | exact (famAtWf F')
    | exact Hc |].
  eapply ktrU;
    [ exact (famAtWf (prfF kk xp)) | exact (famAtWf (prfF kk xp'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  apply prfFam_ceq; [exact Hty |].
  exact (proj1 (proj1 (propEq_iff xp xp')
                  (kRel_at (IHp rho rho' HE j eprop (propFam j) _ xp Dp
                              eprop (propFam j) _ xp' Dp'
                              (famAtSelf (propFam j)) Hrp)))).
Qed.

(* The universe lift.  The realiser is untouched, so nothing moves on the
   layer-1 side; the families move by famLiftK_ceq. *)
Lemma funtm_up (G : ctx) (A : tm) (j : nat)
  (LA : LTy G A) (IHA : FunTm G A) : FunTm G (up j A).
Proof.
  apply (funtm_former_l G (up j A));
    [intros rho k Sy F w x H; exact H
    | intros rho rho' HE; exact (LA rho rho' HE) |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ity_lvl_dec rho (up j A) k w F D) as El;
    cbn [LvlDec] in El; subst k.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_up_inv rho (up j A) (S j) _ F D) as [F1 [[Ej DA] Hi]].
  destruct (ity_up_inv rho' (up j A) (S j) _ F' D') as [F1' [[Ej' DA'] Hi']].
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf (famLiftK F1)) | exact (famAtWf F')
    | exact Hi |].
  eapply ktrU;
    [ exact (famAtWf (famLiftK F1)) | exact (famAtWf (famLiftK F1'))
    | exact (famAtWf F') | | apply knsymU; exact Hi' ].
  apply famLiftK_ceq.
  exact (FunTy_of_FunTm G A IHA rho rho' HE j _ F1 _ F1' DA DA'
           (eqty_at_lvl j _ _ (uf_ty F1) (uf_ty F1') (LA rho rho' HE))).
Qed.

(* ------------------------------------------------------------------ *)
(* Pi, Sigma and W.  The codomain is interpreted in an environment      *)
(* EXTENDED by the domain's family, and the two derivations decompose    *)
(* the type with different domain families, so the codomain's induction  *)
(* hypothesis is used at (A :: G) with the two extended environments     *)
(* related by EnvRelOf_ext.  Each of the two GAPS is determined once its  *)
(* component's level is, and the equations that witness them are then     *)
(* equal by UIP -- the second gap only inside the codomain step, where    *)
(* the arguments the two readings are compared at are to hand.           *)
(* ------------------------------------------------------------------ *)

Lemma funtm_pi (G : ctx) (kk : nat) (A B : tm)
  (Lpi : LTy G (pi kk A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) : FunTm G (pi kk A B).
Proof.
  apply (funtm_former_l G (pi kk A B));
    [intros rho k Sy F w x H; exact H | exact Lpi |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_pi_inv rho (pi kk A B) k _ F D) as
    [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB [gPi
      [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  destruct (ity_pi_inv rho' (pi kk A B) k _ F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gPi'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA0' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  eapply ktrU;
    [ exact (famAtWf F)
    | exact (famAtWf (piFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gPi))
    | exact (famAtWf F') | exact Hc |].
  eapply ktrU;
    [ exact (famAtWf (piFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gPi))
    | exact (famAtWf (piFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gPi'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  apply piFam_ceq.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact (Lpi rho rho' HE) | exact Hw'].
  - apply upF_ceq; exact HA.
  - intros u x u' y Hrel.
    (* the arguments, brought down to the domain's own level *)
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    pose proof (EnvRelOf_ext G rho rho' A i FA FA' u (dnEl dA k EA FA u x)
                  u' (dnEl dA k EA FA' u' y) HE (conj HA Hd)) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' y) as DBx'.
    (* the codomain's level, hence the second gap *)
    pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                  j _ (FB u x) j' _ (FB' u' y) DBx DBx') as Ej; subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    assert (EB0 : wB u x = ers (ext rho FA u (dnEl dA k EA FA u x)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u' y = ers (ext rho' FA' u' (dnEl dA k EA FA' u' y)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    assert (Htyb : tyeq (wB u x) (wB' u' y))
      by (rewrite EB0, EB0'; exact (LB _ _ HEx)).
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ (FB u x) _ (FB' u' y)
             DBx DBx'
             (eqty_at_lvl j _ _ (uf_ty (FB u x)) (uf_ty (FB' u' y)) Htyb)).
Qed.

Lemma funtm_sig (G : ctx) (kk : nat) (A B : tm)
  (Lsig : LTy G (sig_ kk A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) : FunTm G (sig_ kk A B).
Proof.
  apply (funtm_former_l G (sig_ kk A B));
    [intros rho k Sy F w x H; exact H | exact Lsig |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_sig_inv rho (sig_ kk A B) k _ F D) as
    [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB [gSig
      [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  destruct (ity_sig_inv rho' (sig_ kk A B) k _ F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gSig'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA0' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  eapply ktrU;
    [ exact (famAtWf F)
    | exact (famAtWf (sigFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gSig))
    | exact (famAtWf F') | exact Hc |].
  eapply ktrU;
    [ exact (famAtWf (sigFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gSig))
    | exact (famAtWf (sigFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gSig'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  apply sigFam_ceq.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact (Lsig rho rho' HE) | exact Hw'].
  - apply upF_ceq; exact HA.
  - intros u x u' y Hrel.
    (* the arguments, brought down to the domain's own level *)
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    pose proof (EnvRelOf_ext G rho rho' A i FA FA' u (dnEl dA k EA FA u x)
                  u' (dnEl dA k EA FA' u' y) HE (conj HA Hd)) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' y) as DBx'.
    (* the codomain's level, hence the second gap *)
    pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                  j _ (FB u x) j' _ (FB' u' y) DBx DBx') as Ej; subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    assert (EB0 : wB u x = ers (ext rho FA u (dnEl dA k EA FA u x)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u' y = ers (ext rho' FA' u' (dnEl dA k EA FA' u' y)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    assert (Htyb : tyeq (wB u x) (wB' u' y))
      by (rewrite EB0, EB0'; exact (LB _ _ HEx)).
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ (FB u x) _ (FB' u' y)
             DBx DBx'
             (eqty_at_lvl j _ _ (uf_ty (FB u x)) (uf_ty (FB' u' y)) Htyb)).
Qed.

Lemma funtm_w (G : ctx) (kk : nat) (A B : tm)
  (Lw : LTy G (wt kk A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) : FunTm G (wt kk A B).
Proof.
  apply (funtm_former_l G (wt kk A B));
    [intros rho k Sy F w x H; exact H | exact Lw |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_w_inv rho (wt kk A B) k _ F D) as
    [i [j [dA [dB [EA [EB [wA [FA [B0 [wB [FB [redB [cohB [gW
      [[[DA DB] Hw] Hc]]]]]]]]]]]]]]].
  destruct (ity_w_inv rho' (wt kk A B) k _ F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gW'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA0' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  eapply ktrU;
    [ exact (famAtWf F)
    | exact (famAtWf (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gW))
    | exact (famAtWf F') | exact Hc |].
  eapply ktrU;
    [ exact (famAtWf (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gW))
    | exact (famAtWf (wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gW'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  apply wFam_ceq.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact (Lw rho rho' HE) | exact Hw'].
  - apply upF_ceq; exact HA.
  - intros u x u' y Hrel.
    (* the arguments, brought down to the domain's own level *)
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    pose proof (EnvRelOf_ext G rho rho' A i FA FA' u (dnEl dA k EA FA u x)
                  u' (dnEl dA k EA FA' u' y) HE (conj HA Hd)) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' y) as DBx'.
    (* the codomain's level, hence the second gap *)
    pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                  j _ (FB u x) j' _ (FB' u' y) DBx DBx') as Ej; subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    assert (EB0 : wB u x = ers (ext rho FA u (dnEl dA k EA FA u x)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u' y = ers (ext rho' FA' u' (dnEl dA k EA FA' u' y)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    assert (Htyb : tyeq (wB u x) (wB' u' y))
      by (rewrite EB0, EB0'; exact (LB _ _ HEx)).
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ (FB u x) _ (FB' u' y)
             DBx DBx'
             (eqty_at_lvl j _ _ (uf_ty (FB u x)) (uf_ty (FB' u' y)) Htyb)).
Qed.

Definition LTm (G : ctx) (t A : tm) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> Rel (ers rho A) (ers rho t) (ers rho' t).

Lemma LTm_of_ty G t A (d : ty G t A) : LTm G t A.
Proof. intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_ty G t A d _ _ HS). Qed.

Lemma LTy_of_ty G A k (d : ty G A (UU k)) : LTy G A.
Proof.
  intros rho rho' [_ [_ [_ HS]]]; exists k; exact (fundamental_U G A k d _ _ HS).
Qed.

(* Impredicative forall: a TERM of prop, so the value is a proposition and
   functionality is an iff.  The domain's level is existential in the
   decoder, and the two readings agree on it by ity_lvl. *)
Lemma funtm_all (G : ctx) (jj : nat) (A p : tm)
  (LA : LTy G A) (Lp : LTm (A :: G) p (prop jj))
  (IHA : FunTm G A) (IHp : FunTm (A :: G) p) : FunTm G (all jj A p).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv TmShape AllVal Shaped] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  (* both records are taken apart at once, so that the two domain levels are
     plain variables and the equality between them can be substituted *)
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as [kA wA FA wp xp wv g lvl DA Dp].
  destruct d' as [kA' wA' FA' wp' xp' wv' g' lvl' DA' Dp'].
  cbn [al_kA al_wA al_FA al_wp al_xp al_wv al_g al_DA al_Dp
       cn_Sy cn_F cn_w cn_x] in Hv, Hv' |- *.
  pose proof (lvls_of_EnvRelOf G rho rho' HE) as HL.
  pose proof (ity_lvl rho rho' HL A kA wA FA kA' wA' FA' DA DA') as Ek; subst kA'.
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (PA : kceq (kAt FA) (kAt FA')).
  { apply (FunTy_of_FunTm G A IHA rho rho' HE kA _ FA _ FA' DA DA').
    apply (eqty_at_lvl kA _ _ (uf_ty FA) (uf_ty FA')).
    rewrite EA, EA'; exact (LA rho rho' HE). }
  assert (Key : forall u (y : kElAt FA u) u2 (y2 : kElAt FA' u2),
             kRel FA u y FA' u2 y2 -> (propVal (xp u y) <-> propVal (xp' u2 y2))).
  { intros u y u2 y2 Hy.
    assert (HEx : EnvRelOf (A :: G) (ext rho FA u y) (ext rho' FA' u2 y2)).
    { apply (EnvRelOf_ext_ty G rho rho' A kA _ _ FA FA');
        [ exact HE
        | exists kA; rewrite <- EA; exact (uf_ty FA)
        | exists kA; rewrite <- EA'; exact (uf_ty FA')
        | exact Hy ]. }
    assert (Ew : wp u y = ers (ext rho FA u y) p)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp u y)).
    assert (Ew' : wp' u2 y2 = ers (ext rho' FA' u2 y2) p)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp' u2 y2)).
    assert (Hr : Rel eprop (wp u y) (wp' u2 y2))
      by (rewrite Ew, Ew'; exact (Lp _ _ HEx)).
    exact (proj1 (proj1 (propEq_iff (xp u y) (xp' u2 y2))
                    (kRel_at
                       (IHp _ _ HEx k eprop (propFam k) _ (xp u y) (Dp u y)
                          eprop (propFam k) _ (xp' u2 y2) (Dp' u2 y2)
                          (famAtSelf (propFam k)) Hr)))). }
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hw : Rel eprop w wv) by exact (proj2 (proj1 (propEq_iff _ _) HQ)).
  assert (Hw' : Rel eprop w' wv') by exact (proj2 (proj1 (propEq_iff _ _) HQ')).
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  apply (proj1 (kRel_same (propFam k) _ _ _ _)).
  apply propEq_iff; split.
  - cbn [propVal propElem Datatypes.fst]; split.
    + intros H u2 y2.
      exact (proj1 (Key u2 (moveTo FA' FA (knsymU _ _ PA) u2 y2 u2 (reds_refl u2))
                      u2 y2
                      (kRel_sym _ _ _ _ _ _
                         (moveTo_rel FA' FA (knsymU _ _ PA) u2 y2 u2
                            (reds_refl u2))))
               (H u2 _)).
    + intros H u y.
      exact (proj2 (Key u y u (moveTo FA FA' PA u y u (reds_refl u))
                      (moveTo_rel FA FA' PA u y u (reds_refl u)))
               (H u _)).
  - eapply Rel_trans; [apply Rel_sym; exact Hw |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy' eprop w w' (ceq_ty F' (propFam k) Q') Hrel)
      | exact Hw' ].
Qed.

(* ------------------------------------------------------------------ *)
(* Proof terms.  The interpretation has ONE clause for them (i_proof),  *)
(* so their decoder branch is empty and every reading is the universal   *)
(* one, which is functional by proof irrelevance.  This covers plam,     *)
(* papp and absurd at once.                                             *)
(* ------------------------------------------------------------------ *)

Lemma funtm_noval (G : ctx) (t : tm)
  (Hsh : forall rho k Sy (F : kUFam k Sy) w (x : kElAt F w),
           TmShape rho t k Sy F w x -> False) :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  destruct (Hsh _ _ _ _ _ _ E).
Qed.

Lemma funtm_plam (G : ctx) (A p : tm) : FunTm G (plam A p).
Proof.
  apply funtm_noval; intros rho k Sy F w x H;
    cbn [TmShape NoVal] in H; destruct H.
Qed.

Lemma funtm_papp (G : ctx) (f a : tm) : FunTm G (papp f a).
Proof.
  apply funtm_noval; intros rho k Sy F w x H;
    cbn [TmShape NoVal] in H; destruct H.
Qed.

Lemma funtm_absurd (G : ctx) (T e : tm) : FunTm G (absurd T e).
Proof.
  apply funtm_noval; intros rho k Sy F w x H;
    cbn [TmShape NoVal] in H; destruct H.
Qed.

(* ------------------------------------------------------------------ *)
(* THE LIFT, ON THE RELATION.                                          *)
(*                                                                    *)
(* In v1 these four were the longest plumbing in the file: `kRel` was   *)
(* an existential over an iso together with a transport equation, so     *)
(* pushing it through the lift meant chasing the lift's naturality        *)
(* square against the transport, and pulling it back meant three          *)
(* `hetC` steps plus both round trips.  Here `kRel` is a PAIR of the      *)
(* codes' equality and the elements', each of which the lift already       *)
(* preserves (Interp/Lift.v), so both directions are one `split`.          *)
(*                                                                    *)
(* Reflection still asks for the unlifted families' equality as an input:  *)
(* the hypothesis only gives it about the lifts, and nothing recovers it   *)
(* from there.  At every use site the components' functionality supplies   *)
(* it, exactly as in v1.                                                  *)
(* ------------------------------------------------------------------ *)

Lemma kRel_lift {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kRel F w x F' w' x' ->
  kRel (famLiftK F) w (elLift F w x) (famLiftK F') w' (elLift F' w' x').
Proof.
  intros [H1 H2]; split;
    [ exact (famLiftK_ceq F F' H1) | exact (elLift_eq F w x F' w' x' H1 H2) ].
Qed.

Lemma kRel_unlift {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (Q : kceq (kAt F) (kAt F')) w y w' y' :
  kRel (famLiftK F) w y (famLiftK F') w' y' ->
  kRel F w (elUnlift F w y) F' w' (elUnlift F' w' y').
Proof.
  intros [_ H2]; split; [exact Q | exact (elUnlift_eq F w y F' w' y' Q H2)].
Qed.

Lemma kRel_liftN d {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kRel F w x F' w' x' ->
  kRel (famLiftN d F) w (elLiftN d F w x) (famLiftN d F') w' (elLiftN d F' w' x').
Proof.
  intros [H1 H2]; split;
    [ exact (famLiftN_ceq d F F' H1) | exact (elLiftN_eq d F w x F' w' x' H1 H2) ].
Qed.

Lemma kRel_unliftN d {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (Q : kceq (kAt F) (kAt F')) w y w' y' :
  kRel (famLiftN d F) w y (famLiftN d F') w' y' ->
  kRel F w (elUnliftN d F w y) F' w' (elUnliftN d F' w' y').
Proof.
  intros [_ H2]; split; [exact Q | exact (elUnliftN_eq d F w y F' w' y' Q H2)].
Qed.

(* The same two, at an annotated gap: this is the form the eliminators meet,
   because a component at level j inside a former at level k is read through
   `upF d k E` (Interp/LiftN.v). *)
Lemma kRel_up {i u u'} (d k : nat) (E : d + i = k) (F : kUFam i u) w x
  (F' : kUFam i u') w' x' :
  kRel F w x F' w' x' ->
  kRel (upF d k E F) w (upEl d k E F w x) (upF d k E F') w' (upEl d k E F' w' x').
Proof.
  intros [H1 H2]; split;
    [ exact (upF_ceq d k E F F' H1) | exact (upEl_eq d k E F w x F' w' x' H1 H2) ].
Qed.

Lemma kRel_dn {i u u'} (d k : nat) (E : d + i = k) (F : kUFam i u)
  (F' : kUFam i u') (Q : kceq (kAt F) (kAt F')) w x w' x' :
  kRel (upF d k E F) w x (upF d k E F') w' x' ->
  kRel F w (dnEl d k E F w x) F' w' (dnEl d k E F' w' x').
Proof.
  intros [_ H2]; split; [exact Q | exact (dnEl_eq d k E F w x F' w' x' Q H2)].
Qed.

(* The term lift.  Its realiser is the subject's, so the layer-1 side does not
   move; the families and the elements move by kRel_lift. *)
Lemma funtm_uptm (G : ctx) (A t : tm) (LA : LTy G A)
  (IHA : FunTm G A) (IHt : FunTm G t) : FunTm G (uptm A t).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv TmShape] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  destruct k as [| k0]; [cbn [UpTmVal] in E; destruct E |].
  cbn [UpTmVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as [Sy1 F1 x1 DA D1]; destruct d' as [Sy1' F1' x1' DA' D1'].
  cbn [ut_Sy ut_F ut_x] in Hv, Hv'.
  assert (E1 : Sy1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (E1' : Sy1' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst Sy1 Sy1'.
  assert (PA : kceq (kAt F1) (kAt F1'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE k0 _ F1 _ F1' DA DA'
                (eqty_at_lvl k0 _ _ (uf_ty F1) (uf_ty F1') (LA rho rho' HE))).
  assert (Hr : Rel (ers rho' A) w w').
  { apply (Rel_tyeq Sy' (ers rho' A) w w'); [| exact Hrel].
    exists (S k0); exact (ceq_eqty F' (famLiftK F1') (projT1 Hv')). }
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x].
  apply kRel_lift.
  exact (IHt rho rho' HE k0 _ F1 w x1 D1 _ F1' w' x1' D1' PA Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* THE ELIMINATORS.                                                    *)
(*                                                                    *)
(* None of these subjects pins its level, so the i_proof reading has to  *)
(* be discharged at level 0 and the same argument then run at every       *)
(* level.  funtm_shape does that once and for all: its hypothesis is the  *)
(* decoder's branch against the decoder's branch, which is what every     *)
(* case below actually proves.                                           *)
(* ------------------------------------------------------------------ *)

Lemma funtm_shape (G : ctx) (t : tm)
  (H : forall rho rho' k Sy (F : kUFam k Sy) w (x : kElAt F w)
              Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w'),
         EnvRelOf G rho rho' ->
         TmShape rho t k Sy F w x -> TmShape rho' t k Sy' F' w' x' ->
         kceq (kAt F) (kAt F') -> Rel Sy' w w' -> kRel F w x F' w' x') :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Pc Hrel.
  funtm_start D D'.
  cbn [TmInv] in E, E'.
  funtm_proofs E E' F F' Pc w x w' x' Hrel.
  exact (H rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel).
Qed.

(* ---- a binder's components, read twice ----

   Every elimination decomposes its subject's type with the formation lemma
   for its former (that is the pin on the realiser, Interp/Def.v), so the two
   readings arrive with two sets of components at two sets of levels, and what
   the elimination needs is what piFam_ceq / sigFam_ceq / wFam_ceq ask about
   them.  Nothing here is specific to the former, so one lemma serves all
   three.  The levels and the gaps agree: the domain's by ity_lvl at A, the
   codomain's by ity_lvl at B -- the latter only once a pair of related
   arguments is to hand, which is exactly where the second output is asked
   for.  Both gaps are then equal by UIP.

   In v1 the corresponding lemma produced the two families' isomorphism and
   nothing else, because v1's sigFst_to/sigSnd_to only needed that.  Here the
   heterogeneous laws (sigFst_eqX, sigSnd_eqX, piApp_eqX) want the components'
   equalities themselves, so they are what travels. *)
Lemma comp_ceq (G : ctx) (A B : tm)
  (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B)
  rho rho' (HE : EnvRelOf G rho rho') (ks : nat)
  (i j dA dB : nat) (EA : dA + i = ks) (EB : dB + j = ks)
  (wA : etm) (FA : kUFam i wA)
  (wB : forall u, kElAt (upF dA ks EA FA) u -> etm)
  (FB : forall u (x : kElAt (upF dA ks EA FA) u), kUFam j (wB u x))
  (i' j' dA' dB' : nat) (EA' : dA' + i' = ks) (EB' : dB' + j' = ks)
  (wA' : etm) (FA' : kUFam i' wA')
  (wB' : forall u, kElAt (upF dA' ks EA' FA') u -> etm)
  (FB' : forall u (x : kElAt (upF dA' ks EA' FA') u), kUFam j' (wB' u x))
  (DA : ITy rho A i wA FA) (DA' : ITy rho' A i' wA' FA')
  (DB : forall u x,
     ITy (ext rho FA u (dnEl dA ks EA FA u x)) B j (wB u x) (FB u x))
  (DB' : forall u x,
     ITy (ext rho' FA' u (dnEl dA' ks EA' FA' u x)) B j' (wB' u x) (FB' u x)) :
  kceq (kAt (upF dA ks EA FA)) (kAt (upF dA' ks EA' FA')) /\
  (forall u x u' y,
     kEqAt (upF dA ks EA FA) u x (upF dA' ks EA' FA') u' y ->
     kceq (kAt (upF dB ks EB (FB u x))) (kAt (upF dB' ks EB' (FB' u' y)))).
Proof.
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  split.
  - apply upF_ceq; exact HA.
  - intros u x u' y Hrel.
    (* the arguments, brought down to the domain's own level *)
    assert (Hd : kEqAt FA u (dnEl dA ks EA FA u x) FA' u' (dnEl dA ks EA FA' u' y))
      by exact (dnEl_eq dA ks EA FA u x FA' u' y HA Hrel).
    pose proof (EnvRelOf_ext G rho rho' A i FA FA' u (dnEl dA ks EA FA u x)
                  u' (dnEl dA ks EA FA' u' y) HE (conj HA Hd)) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' y) as DBx'.
    (* the codomain's level, hence the second gap *)
    pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                  j _ (FB u x) j' _ (FB' u' y) DBx DBx') as Ej; subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    assert (EB0 : wB u x = ers (ext rho FA u (dnEl dA ks EA FA u x)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u' y = ers (ext rho' FA' u' (dnEl dA ks EA FA' u' y)) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ (FB u x) _ (FB' u' y)
             DBx DBx'
             (eqty_at_lvl j _ _ (uf_ty (FB u x)) (uf_ty (FB' u' y))
                (eq_ind_r (fun T => tyeq T _) (eq_ind_r (fun T' => tyeq _ T')
                   (LB _ _ HEx) EB0') EB0))).
Qed.

(* The codomain's own equality, at ONE pair of related arguments and at the
   codomain's own level.  comp_ceq's second component is this one lifted
   into the former's level, and a lift does not come back by itself, so the
   eliminations that land IN the codomain (snd, app) ask for it here. *)
Lemma cod_ceq (G : ctx) (A B : tm)
  (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  rho rho' (HE : EnvRelOf G rho rho') (ks i j dA : nat) (EA : dA + i = ks)
  (wA : etm) (FA : kUFam i wA)
  (wB : forall u, kElAt (upF dA ks EA FA) u -> etm)
  (FB : forall u (x : kElAt (upF dA ks EA FA) u), kUFam j (wB u x))
  (wA' : etm) (FA' : kUFam i wA')
  (wB' : forall u, kElAt (upF dA ks EA FA') u -> etm)
  (FB' : forall u (x : kElAt (upF dA ks EA FA') u), kUFam j (wB' u x))
  (DA : ITy rho A i wA FA) (DA' : ITy rho' A i wA' FA')
  (HA : kceq (kAt FA) (kAt FA'))
  (DB : forall u x,
     ITy (ext rho FA u (dnEl dA ks EA FA u x)) B j (wB u x) (FB u x))
  (DB' : forall u x,
     ITy (ext rho' FA' u (dnEl dA ks EA FA' u x)) B j (wB' u x) (FB' u x))
  u x u' y (Hrel : kEqAt (upF dA ks EA FA) u x (upF dA ks EA FA') u' y) :
  kceq (kAt (FB u x)) (kAt (FB' u' y)).
Proof.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (Hd : kEqAt FA u (dnEl dA ks EA FA u x) FA' u' (dnEl dA ks EA FA' u' y))
    by exact (dnEl_eq dA ks EA FA u x FA' u' y HA Hrel).
  pose proof (EnvRelOf_ext G rho rho' A i FA FA' u (dnEl dA ks EA FA u x)
                u' (dnEl dA ks EA FA' u' y) HE (conj HA Hd)) as HEx.
  pose proof (DB u x) as DBx; pose proof (DB' u' y) as DBx'.
  assert (EB0 : wB u x = ers (ext rho FA u (dnEl dA ks EA FA u x)) B)
    by exact (ers_of_ITy _ _ _ _ _ DBx).
  assert (EB0' : wB' u' y = ers (ext rho' FA' u' (dnEl dA ks EA FA' u' y)) B)
    by exact (ers_of_ITy _ _ _ _ _ DBx').
  apply (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ (FB u x) _ (FB' u' y)
           DBx DBx').
  apply (eqty_at_lvl j _ _ (uf_ty (FB u x)) (uf_ty (FB' u' y))).
  rewrite EB0, EB0'; exact (LB _ _ HEx).
Qed.

(* ---- the two projections ----

   The pin on the subject's Sigma-realiser (Interp/Def.v) is what makes these
   work: the clause rebuilds the subject's type with ity_sig, so the two
   readings' Sigma-families are equal by sigFam_ceq and the projections then
   travel across by sigFst_eqX / sigSnd_eqX.  What the heterogeneous levels
   add is the gap: a component sits in the Sigma at the Sigma's level and is
   eliminated at its own, so the two canonical values are `dnEl`s and the
   relation has to come back down -- which is kRel_dn, and it needs the
   component's own equality, below the lift. *)
Lemma funtm_fst (G : ctx) (kk : nat) (A B p : tm)
  (Lsig : LTy G (sig_ kk A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B)
  (Lp : LTm G p (sig_ kk A B)) (IHp : FunTm G p) : FunTm G (fst A B p).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape FstVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [ks j dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp Ep DA DB Dp].
  destruct d' as
    [ks' j' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gSig' wp' xp'
     Ep' DA' DB' Dp'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold fd_val in Hv, Hv'.
  cbn [fd_ks fd_j fd_dA fd_dB fd_EA fd_EB fd_wA fd_FA fd_B0 fd_wB fd_FB
       fd_redB fd_cohB fd_gSig fd_wp fd_xp] in Hv, Hv'.
  (* the Sigma's level, hence the domain's gap, is the same on both sides *)
  pose proof (itm_lvl p rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                (NotPrfR_sig wA B0) Dp _ _ _ _ _ (NotPrfR_sig wA' B0') Dp')
    as Eks.
  (* `subst ks'` would take the clause's own gap equation for the substitution
     and destroy it, so the level is eliminated by hand *)
  destruct Eks.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (Hty : tyeq (esig wA B0) (esig wA' B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE ks
              k j dA dB EA EB wA FA wB FB
              k j' dA dB' EA EB' wA' FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  assert (HA : kceq (kAt FA) (kAt FA')).
  { assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
    assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
    apply (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA').
    apply (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA')).
    rewrite EwA, EwA'; exact (LA rho rho' HE). }
  assert (Hrp : Rel (esig wA' B0') wp wp').
  { assert (Ewp : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
    assert (Ewp' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
    rewrite Ewp, Ewp'.
    apply (Rel_tyeq (ers rho (sig_ ks A B)) (esig wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  pose proof (IHp rho rho' HE ks (esig wA B0) _ wp xp Dp
                (esig wA' B0') _ wp' xp' Dp'
                (sigFam_ceq ks wA B0 (upF dA ks EA FA) wB
                   (fun u y => upF dB ks EB (FB u y)) redB cohB gSig
                   wA' B0' (upF dA ks EA FA') wB'
                   (fun u y => upF dB' ks EB' (FB' u y)) redB' cohB' gSig'
                   Hty HAu HBu) Hrp) as Hx.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dA ks EA FA FA' HA).
  split; [exact HAu |].
  eapply sigFst_eqX; [exact HAu | exact (kRel_at Hx)].
Qed.

Lemma funtm_snd (G : ctx) (kk : nat) (A B p : tm)
  (Lsig : LTy G (sig_ kk A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B)
  (Lp : LTm G p (sig_ kk A B)) (IHp : FunTm G p) : FunTm G (snd A B p).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape SndVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [ks i dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp Ep DA DB Dp].
  destruct d' as
    [ks' i' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gSig' wp' xp'
     Ep' DA' DB' Dp'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold sd_val, sd_fst in Hv, Hv'.
  cbn [sd_ks sd_i sd_dA sd_dB sd_EA sd_EB sd_wA sd_FA sd_B0 sd_wB sd_FB
       sd_redB sd_cohB sd_gSig sd_wp sd_xp] in Hv, Hv'.
  (* the Sigma's level, the domain's level, and both gaps agree *)
  pose proof (itm_lvl p rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                (NotPrfR_sig wA B0) Dp _ _ _ _ _ (NotPrfR_sig wA' B0') Dp')
    as Eks.
  destruct Eks.
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EdB : dB' = dB) by lia; subst dB'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
  assert (Hty : tyeq (esig wA B0) (esig wA' B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE ks
              i k dA dB EA EB wA FA wB FB
              i k dA dB EA EB wA' FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  assert (HA : kceq (kAt FA) (kAt FA')).
  { assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
    assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
    apply (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA').
    apply (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA')).
    rewrite EwA, EwA'; exact (LA rho rho' HE). }
  assert (Hrp : Rel (esig wA' B0') wp wp').
  { assert (Ewp : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
    assert (Ewp' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
    rewrite Ewp, Ewp'.
    apply (Rel_tyeq (ers rho (sig_ ks A B)) (esig wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  pose proof (IHp rho rho' HE ks (esig wA B0) _ wp xp Dp
                (esig wA' B0') _ wp' xp' Dp'
                (sigFam_ceq ks wA B0 (upF dA ks EA FA) wB
                   (fun u y => upF dB ks EB (FB u y)) redB cohB gSig
                   wA' B0' (upF dA ks EA FA') wB'
                   (fun u y => upF dB ks EB (FB' u y)) redB' cohB' gSig'
                   Hty HAu HBu) Hrp) as Hx.
  (* the two first projections, which the codomains are read at *)
  pose proof (sigFst_eqX ks wA B0 (upF dA ks EA FA) wB
                (fun u y => upF dB ks EB (FB u y)) redB cohB gSig
                wA' B0' (upF dA ks EA FA') wB'
                (fun u y => upF dB ks EB (FB' u y)) redB' cohB' gSig'
                HAu wp xp wp' xp' (kRel_at Hx)) as Hf.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dB ks EB _ _
           (cod_ceq G A B LB IHB rho rho' HE ks i k dA EA wA FA wB FB
              wA' FA' wB' FB' DA DA' HA DB DB' _ _ _ _ Hf)).
  eapply sigSnd_eqX; [exact HAu | exact HBu | exact (kRel_at Hx)].
Qed.

(* Application.  Its level is the codomain's and the function's is the Pi's
   annotation, which the subject does not record, so the Pi's level -- hence
   the domain's gap -- is existential on both sides and agrees by level
   functionality at the function.  The value is the codomain's own, below the
   gap, so again kRel_dn, with the codomain's equality AT THE ARGUMENT from
   cod_ceq. *)
Lemma funtm_app (G : ctx) (kk : nat) (A B f a : tm)
  (LA : LTy G A) (LB : LTy (A :: G) B) (IHA : FunTm G A) (IHB : FunTm (A :: G) B)
  (Lpi : LTy G (pi kk A B))
  (Lf : LTm G f (pi kk A B)) (IHf : FunTm G f)
  (La : LTm G a A) (IHa : FunTm G a) : FunTm G (app A B f a).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape AppVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [kp i dA dB EA EB wA FA B0 wB FB redB cohB gPi wf xf wa xa Ep DA DB Df Da].
  destruct d' as
    [kp' i' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gPi' wf' xf' wa' xa'
     Ep' DA' DB' Df' Da'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold ap_val, ap_arg in Hv, Hv'.
  cbn [ap_kp ap_i ap_dA ap_dB ap_EA ap_EB ap_wA ap_FA ap_B0 ap_wB ap_FB
       ap_redB ap_cohB ap_gPi ap_wf ap_xf ap_wa ap_xa] in Hv, Hv'.
  (* the Pi's level, the domain's level, and both gaps *)
  pose proof (itm_lvl f rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                (NotPrfR_pi wA B0) Df _ _ _ _ _ (NotPrfR_pi wA' B0') Df')
    as Ekp.
  destruct Ekp.
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EdB : dB' = dB) by lia; subst dB'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
  assert (Hty : tyeq (epi wA B0) (epi wA' B0'))
    by (rewrite Ep, Ep'; exact (Lpi rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE kp
              i k dA dB EA EB wA FA wB FB
              i k dA dB EA EB wA' FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (HA : kceq (kAt FA) (kAt FA')).
  { apply (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA').
    apply (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA')).
    rewrite EwA, EwA'; exact (LA rho rho' HE). }
  (* the function and the argument, each related in its own family *)
  assert (Hrf : Rel (epi wA' B0') wf wf').
  { assert (Ewf : wf = ers rho f) by exact (ers_of_ITm _ _ _ _ _ _ _ Df).
    assert (Ewf' : wf' = ers rho' f) by exact (ers_of_ITm _ _ _ _ _ _ _ Df').
    rewrite Ewf, Ewf'.
    apply (Rel_tyeq (ers rho (pi kp A B)) (epi wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lf rho rho' HE) ]. }
  assert (Hra : Rel wA' wa wa').
  { assert (Ewa : wa = ers rho a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
    assert (Ewa' : wa' = ers rho' a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
    rewrite Ewa, Ewa', EwA'.
    apply (Rel_tyeq (ers rho A) (ers rho' A));
      [ exact (LA rho rho' HE) | exact (La rho rho' HE) ]. }
  pose proof (IHf rho rho' HE kp (epi wA B0) _ wf xf Df
                (epi wA' B0') _ wf' xf' Df'
                (piFam_ceq kp wA B0 (upF dA kp EA FA) wB
                   (fun u y => upF dB kp EB (FB u y)) redB cohB gPi
                   wA' B0' (upF dA kp EA FA') wB'
                   (fun u y => upF dB kp EB (FB' u y)) redB' cohB' gPi'
                   Hty HAu HBu) Hrf) as Hxf.
  pose proof (IHa rho rho' HE i wA FA wa xa Da wA' FA' wa' xa' Da' HA Hra) as Hxa.
  (* the argument, lifted into the Pi's level, where the application happens *)
  pose proof (upEl_eq dA kp EA FA wa xa FA' wa' xa' HA (kRel_at Hxa)) as Hau.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dB kp EB _ _
           (cod_ceq G A B LB IHB rho rho' HE kp i k dA EA wA FA wB FB
              wA' FA' wB' FB' DA DA' HA DB DB' _ _ _ _ Hau)).
  (* the application itself; the codomain is a lambda in the Pi's level, so
     piApp_eqX gets its components explicitly rather than by unification *)
  exact (piApp_eqX kp wA B0 (upF dA kp EA FA) wB
           (fun u y => upF dB kp EB (FB u y)) redB cohB gPi
           wA' B0' (upF dA kp EA FA') wB'
           (fun u y => upF dB kp EB (FB' u y)) redB' cohB' gPi' HAu HBu
           wf xf wf' xf' wa (upEl dA kp EA FA wa xa)
           wa' (upEl dA kp EA FA' wa' xa') (kRel_at Hxf) Hau).
Qed.

(* ------------------------------------------------------------------ *)
(* THE PAIR.                                                           *)
(*                                                                    *)
(* There is no heterogeneous law for sigPair: the Sigma code's element    *)
(* relation is stated on the PROJECTIONS, so nothing says what a pair     *)
(* built in one family has to do with a pair built in another.  The two    *)
(* readings are therefore compared through SURJECTIVE PAIRING, exactly as  *)
(* in v1: inside the second reading's family the coerced pair IS the pair  *)
(* of its own projections, and those projections are handled by            *)
(* sigFst_to / sigSnd_to and sigFst_pair / sigSnd_pair.  sigPair_surj      *)
(* asks for two layer-1 facts about the reconstructed pair, and            *)
(* sig_eta_rel supplies them.                                              *)
(* ------------------------------------------------------------------ *)

Lemma sig_eta_rel T A0 B0 u v : Good_ty T -> eval T (esig A0 B0) -> Rel T u v ->
  Rel T (epair (efst u) (esnd u)) v.
Proof.
  intros gT ev H.
  destruct (Rel_sig_elim T A0 B0 u v ev H) as [H1 H2].
  assert (Hu : Rel A0 (efst u) (efst u))
    by (eapply Rel_trans; [exact H1 | apply Rel_sym; exact H1]).
  assert (Hfst : Rel A0 (efst (epair (efst u) (esnd u))) (efst u))
    by (eapply Rel_exp; [apply reds_fst_pair | apply reds_refl | exact Hu]).
  apply (Rel_sig_intro T A0 B0); [exact gT | exact ev | |].
  - eapply Rel_exp; [apply reds_fst_pair | apply reds_refl | exact H1].
  - destruct (Rel_sig_cod T A0 B0 _ _ gT ev Hfst) as [n Hn].
    apply (proj2 (Rel_resp n _ _ Hn _ _)).
    eapply Rel_exp; [apply reds_snd_pair | apply reds_refl | exact H2].
Qed.

Lemma funtm_pair (G : ctx) (kk : nat) (A B t a : tm)
  (LA : LTy G A) (IHA : FunTm G A)
  (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  (Lsig : LTy G (sig_ kk A B))
  (Lp : LTm G (pair kk A B t a) (sig_ kk A B))
  (Lt : LTm G t A) (IHt : FunTm G t)
  (La : LTm G a (B [t..])) (IHa : FunTm G a) : FunTm G (pair kk A B t a).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape PairVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [i j dA dB EA EB wA FA B0 wB FB redB cohB gSig wt xt wa xa g
     Ekk Ep DA DB Dt Da].
  destruct d' as
    [i' j' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gSig' wt' xt' wa' xa' g'
     Ekk' Ep' DA' DB' Dt' Da'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold pd_SF, pd_val in Hv, Hv'.
  cbn [pd_i pd_j pd_dA pd_dB pd_EA pd_EB pd_wA pd_FA pd_B0 pd_wB pd_FB pd_redB
       pd_cohB pd_gSig pd_wt pd_xt pd_wa pd_xa pd_g] in Hv, Hv'.
  (* every realiser is the erasure it should be *)
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (Ewt : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt).
  assert (Ewt' : wt' = ers rho' t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt').
  assert (Ewa : wa = ers rho a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho' a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  subst wA wA' wt wt' wa wa'.
  (* the domain's level and gap *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE k
              i j dA dB EA EB _ FA wB FB
              i j' dA dB' EA EB' _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  (* the first component *)
  assert (Hrt : Rel (ers rho' A) (ers rho t) (ers rho' t))
    by (apply (Rel_tyeq (ers rho A) (ers rho' A));
        [ exact (LA rho rho' HE) | exact (Lt rho rho' HE) ]).
  assert (A3 : kRel FA (ers rho t) xt FA' (ers rho' t) xt')
    by exact (IHt rho rho' HE i _ FA _ xt Dt _ FA' _ xt' Dt' HA Hrt).
  pose proof (upEl_eq dA k EA FA _ xt FA' _ xt' HA (kRel_at A3)) as A3u.
  (* the codomain's level and gap, at that pair of arguments *)
  (* the codomain is read at the argument's ROUND TRIP through the Sigma's
     level, so the extended environments carry that element, not xt itself *)
  pose proof (kRel_dn dA k EA FA FA' HA _ _ _ _ (conj HAu A3u)) as A3rt.
  pose proof (EnvRelOf_ext G rho rho' A i FA FA' _ _ _ _ HE A3rt) as HEx.
  pose proof (DB _ (upEl dA k EA FA _ xt)) as DBx.
  pose proof (DB' _ (upEl dA k EA FA' _ xt')) as DBx'.
  pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                j _ _ j' _ _ DBx DBx') as Ej; subst j'.
  assert (EdB : dB' = dB) by lia; subst dB'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
  assert (Htb : tyeq (wB _ (upEl dA k EA FA _ xt))
                  (wB' _ (upEl dA k EA FA' _ xt'))).
  { assert (EB0 : wB _ (upEl dA k EA FA _ xt)
                  = ers (ext rho FA (ers rho t) xt) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' _ (upEl dA k EA FA' _ xt')
                   = ers (ext rho' FA' (ers rho' t) xt') B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    rewrite EB0, EB0'; exact (LB _ _ HEx). }
  assert (QB : kceq (kAt (FB _ (upEl dA k EA FA _ xt)))
                    (kAt (FB' _ (upEl dA k EA FA' _ xt'))))
    by exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx j _ _ _ _ DBx DBx'
                (eqty_at_lvl j _ _ (uf_ty (FB _ (upEl dA k EA FA _ xt)))
                   (uf_ty (FB' _ (upEl dA k EA FA' _ xt'))) Htb)).
  assert (Hra : Rel (wB' _ (upEl dA k EA FA' _ xt')) (ers rho a) (ers rho' a)).
  { apply (Rel_tyeq (wB _ (upEl dA k EA FA _ xt))
             (wB' _ (upEl dA k EA FA' _ xt'))); [exact Htb |].
    assert (EB0 : wB _ (upEl dA k EA FA _ xt) = ers _ B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    rewrite EB0, <- (ers_sub1 rho B t FA _); exact (La rho rho' HE). }
  assert (B3 : kRel (FB _ (upEl dA k EA FA _ xt)) (ers rho a) xa
                 (FB' _ (upEl dA k EA FA' _ xt')) (ers rho' a) xa')
    by exact (IHa rho rho' HE j _ _ _ xa Da _ _ _ xa' Da' QB Hra).
  pose proof (kRel_up dB k EB _ _ _ _ _ _ B3) as B3u.
  (* the two families, and the layer-1 facts about the pairs *)
  assert (Hty : tyeq (esig (ers rho A) B0) (esig (ers rho' A) B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  pose proof (sigFam_ceq k (ers rho A) B0 (upF dA k EA FA) wB
                (fun u y => upF dB k EB (FB u y)) redB cohB gSig
                (ers rho' A) B0' (upF dA k EA FA') wB'
                (fun u y => upF dB k EB (FB' u y)) redB' cohB' gSig'
                Hty HAu HBu) as Psig.
  assert (Hrp : Rel (esig (ers rho' A) B0')
                  (epair (ers rho t) (ers rho a))
                  (epair (ers rho' t) (ers rho' a))).
  { apply (Rel_tyeq (ers rho (sig_ k A B)) (esig (ers rho' A) B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  assert (gT' : Good_ty (esig (ers rho' A) B0')) by (exists k; exact gSig').
  assert (Hsame : Rel (esig (ers rho' A) B0')
                    (epair (ers rho t) (ers rho a))
                    (epair (ers rho t) (ers rho a)))
    by (eapply Rel_trans; [exact Hrp | apply Rel_sym; exact Hrp]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hsame) as gr.
  assert (g2 : Good (esig (ers rho' A) B0')
                 (epair (efst (epair (ers rho t) (ers rho a)))
                        (esnd (epair (ers rho t) (ers rho a)))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hrp) as Hc.
  (* and the comparison itself *)
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  split; [exact Psig |].
  eapply kEqAt_trans; [exact Psig | apply kto_coh |].
  eapply kEqAt_trans;
    [ exact (famAtSelf _)
    | apply kEqAt_sym;
      exact (sigPair_surj k (ers rho' A) B0' (upF dA k EA FA') wB'
               (fun u y => upF dB k EB (FB' u y)) redB' cohB' gSig' _ _ g2 gr) |].
  apply (sigPair_eq k (ers rho' A) B0' (upF dA k EA FA') wB'
           (fun u y => upF dB k EB (FB' u y)) redB' cohB' gSig');
    [ exact Hc | |].
  - (* the first components *)
    eapply kEqAt_trans;
      [ apply knsymU; exact HAu
      | apply kEqAt_sym;
        exact (sigFst_to k (ers rho A) B0 (upF dA k EA FA) wB
                 (fun u y => upF dB k EB (FB u y)) redB cohB gSig
                 (ers rho' A) B0' (upF dA k EA FA') wB'
                 (fun u y => upF dB k EB (FB' u y)) redB' cohB' gSig'
                 HAu Psig _ _) |].
    eapply kEqAt_trans;
      [ exact (famAtSelf _)
      | exact (sigFst_pair k (ers rho A) B0 (upF dA k EA FA) wB
                 (fun u y => upF dB k EB (FB u y)) redB cohB gSig _ _ _ _ g)
      | exact A3u ].
  - (* the second components *)
    eapply kRel_trans;
      [ apply kRel_sym;
        exact (sigSnd_to k (ers rho A) B0 (upF dA k EA FA) wB
                 (fun u y => upF dB k EB (FB u y)) redB cohB gSig
                 (ers rho' A) B0' (upF dA k EA FA') wB'
                 (fun u y => upF dB k EB (FB' u y)) redB' cohB' gSig'
                 HAu HBu Psig _ _) |].
    eapply kRel_trans;
      [ exact (sigSnd_pair k (ers rho A) B0 (upF dA k EA FA) wB
                 (fun u y => upF dB k EB (FB u y)) redB cohB gSig _ _ _ _ g)
      | exact B3u ].
Qed.

(* ------------------------------------------------------------------ *)
(* THE LAMBDA.                                                         *)
(*                                                                    *)
(* i_lam pins its value only by its BEHAVIOUR, so nothing but pointwise  *)
(* agreement is available to compare two readings: that is piLam_eq       *)
(* (Interp/PiEl.v), v2's extensionality at Pi, and all this case does is   *)
(* feed it the body's functionality at each pair of related arguments.     *)
(* The codomain's level is existential and is NOT determined globally --    *)
(* an empty domain leaves the two readings free to differ -- so it is       *)
(* settled inside the pointwise obligation, where the arguments are.       *)
(* ------------------------------------------------------------------ *)

Lemma funtm_lam (G : ctx) (kk : nat) (A B t : tm)
  (LA : LTy G A) (IHA : FunTm G A)
  (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  (Lpi : LTy G (pi kk A B))
  (Lt : LTm (A :: G) t B) (IHt : FunTm (A :: G) t) : FunTm G (lam kk A B t).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape LamVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [i j dA dB EA EB wA FA B0 wB FB redB cohB gPi wt xt redt xtext gd
     Ekk Ew Ep DA DB Dt].
  destruct d' as
    [i' j' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gPi' wt' xt' redt'
     xtext' gd' Ekk' Ew' Ep' DA' DB' Dt'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold ld_PF, ld_val in Hv, Hv'.
  cbn [ld_i ld_j ld_dA ld_dB ld_EA ld_EB ld_wA ld_FA ld_B0 ld_wB ld_FB ld_redB
       ld_cohB ld_gPi ld_wt ld_xt ld_redt ld_xtext ld_gd] in Hv, Hv'.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  (* the domain's level and gap *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  assert (Hty : tyeq (epi (ers rho A) B0) (epi (ers rho' A) B0'))
    by (rewrite Ep, Ep'; exact (Lpi rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE k
              i j dA dB EA EB _ FA wB FB
              i j' dA dB' EA EB' _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  (* the two realisers are related at the Pi, which is the subject's own
     relatedness read through the second family's shadow *)
  assert (HR : Rel (epi (ers rho A) B0) w w').
  { apply (Rel_tyeq Sy' (epi (ers rho A) B0) w w'); [| exact Hrel].
    eapply tyeq_trans; [| apply tyeq_sym; exact Hty].
    exists k.
    exact (ceq_eqty F' (piFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                          (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gPi')
             (projT1 Hv')). }
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  split;
    [ exact (piFam_ceq k (ers rho A) B0 (upF dA k EA FA) wB
               (fun u y => upF dB k EB (FB u y)) redB cohB gPi
               (ers rho' A) B0' (upF dA k EA FA') wB'
               (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gPi'
               Hty HAu HBu) |].
  apply (piLam_eq k (ers rho A) B0 (upF dA k EA FA) wB
           (fun u y => upF dB k EB (FB u y)) redB cohB gPi
           (ers rho' A) B0' (upF dA k EA FA') wB'
           (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gPi'
           Hty HAu HBu); [exact HR |].
  (* the body, pointwise *)
  intros u y u' y' Hy.
  pose proof (kRel_dn dA k EA FA FA' HA _ _ _ _ (conj HAu Hy)) as Hyd.
  pose proof (EnvRelOf_ext G rho rho' A i FA FA' _ _ _ _ HE Hyd) as HEx.
  pose proof (DB u y) as DBx; pose proof (DB' u' y') as DBx'.
  pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                j _ (FB u y) j' _ (FB' u' y') DBx DBx') as Ej; subst j'.
  assert (EdB : dB' = dB) by lia; subst dB'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
  assert (Htb : tyeq (wB u y) (wB' u' y')).
  { assert (EB0 : wB u y = ers _ B) by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u' y' = ers _ B) by exact (ers_of_ITy _ _ _ _ _ DBx').
    rewrite EB0, EB0'; exact (LB _ _ HEx). }
  assert (QB : kceq (kAt (FB u y)) (kAt (FB' u' y')))
    by exact (cod_ceq G A B LB IHB rho rho' HE k i j dA EA _ FA wB FB
                _ FA' wB' FB' DA DA' HA DB DB' u y u' y' Hy).
  assert (Hrb : Rel (wB' u' y') (wt u y) (wt' u' y')).
  { apply (Rel_tyeq (wB u y) (wB' u' y')); [exact Htb |].
    assert (Et : wt u y = ers _ t) by exact (ers_of_ITm _ _ _ _ _ _ _ (Dt u y)).
    assert (Et' : wt' u' y' = ers _ t)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dt' u' y')).
    assert (EB0 : wB u y = ers _ B) by exact (ers_of_ITy _ _ _ _ _ DBx).
    rewrite Et, Et', EB0; exact (Lt _ _ HEx). }
  pose proof (IHt _ _ HEx j _ (FB u y) _ (xt u y) (Dt u y)
                _ (FB' u' y') _ (xt' u' y') (Dt' u' y') QB Hrb) as Hb.
  exact (upEl_eq dB k EB (FB u y) _ (xt u y) (FB' u' y') _ (xt' u' y')
           QB (kRel_at Hb)).
Qed.

(* ------------------------------------------------------------------ *)
(* THE RECURSOR ON NAT.                                                *)
(*                                                                    *)
(* semrec_rel (Interp/Rec.v) does the recursion; what has to be supplied  *)
(* is the two base values' relatedness, the step's -- which is the body's  *)
(* induction hypothesis in the DOUBLY extended environment, the step term  *)
(* carrying its own two binders -- and the fact that the two scrutinees     *)
(* have the same index.  The motive's families are related at every         *)
(* related pair of naturals, which is IHC in the singly extended            *)
(* environment.                                                             *)
(* ------------------------------------------------------------------ *)

Lemma EnvRelOf_ext' G rho rho' (A : tm) k S S'
  (FA : kUFam k S) (FA' : kUFam k S') u x u' x' :
  EnvRelOf G rho rho' -> S = ers rho A -> S' = ers rho' A ->
  kRel FA u x FA' u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros HE E E' Hr; subst S S'; apply EnvRelOf_ext; [exact HE | exact Hr].
Qed.

Lemma natSucc_eq {k m m'} (x : kElAt (natFam k) m) (x' : kElAt (natFam k) m') :
  kEqAt (natFam k) m x (natFam k) m' x' ->
  kEqAt (natFam k) (esucc m) (natSucc x) (natFam k) (esucc m') (natSucc x').
Proof.
  intros H; destruct (proj1 (natEq_iff x x') H) as [Ej _].
  apply natEq_iff; split; [exact (f_equal S Ej) |].
  assert (e2 : NatAt (S (natIdx x')) (esucc m))
    by (rewrite <- Ej; exact (NatAt_succ _ _ (natSpec x))).
  apply Rel_nat_intro; [apply gt_nat | apply ev_nat |].
  exact (NatAt_NatPer _ _ _ e2 (NatAt_succ _ _ (natSpec x'))).
Qed.

(* semrec_rel at an arbitrary pair of scrutinees: their indices agree because
   they are related, which is what lets one induction serve both. *)
Lemma semrec_rel_el (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (cohC : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
            kceq (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  (SC' : etm -> etm) (FC' : forall m (x : kElAt (natFam k0) m), kUFam k (SC' m))
  (cohC' : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             kceq (kAt (FC' m x)) (kAt (FC' m' x')))
  (zr' sr' : etm) (xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) zr')
  (step' : forall m x w (y : kElAt (FC' m x) w),
             kElAt (FC' (esucc m) (natSucc x)) (eapp (eapp sr' m) w))
  (Hz : kRel (FC ezero (natE 0 NatAt_zero)) zr xz
             (FC' ezero (natE 0 NatAt_zero)) zr' xz')
  (Hstep : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             forall w y w' y', kRel (FC m x) w y (FC' m' x') w' y' ->
             kRel (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w) (step m x w y)
                  (FC' (esucc m') (natSucc x')) (eapp (eapp sr' m') w')
                  (step' m' x' w' y'))
  m (x : kElAt (natFam k0) m) m' (x' : kElAt (natFam k0) m')
  (Hx : kEqAt (natFam k0) m x (natFam k0) m' x') :
  kRel (FC m (natE (natIdx x) (natSpec x))) (enatrec zr sr m)
         (semrec k k0 SC FC cohC zr sr xz step (natIdx x) m (natSpec x))
       (FC' m' (natE (natIdx x') (natSpec x'))) (enatrec zr' sr' m')
         (semrec k k0 SC' FC' cohC' zr' sr' xz' step' (natIdx x') m' (natSpec x')).
Proof.
  destruct (proj1 (natEq_iff x x') Hx) as [Ej _]; clear Hx.
  revert Ej; destruct x as [[j e] gd]; destruct x' as [[j' e'] gd'];
    cbn [natIdx natSpec Datatypes.fst projT1 projT2];
    intros Ej; subst j'.
  exact (semrec_rel k k0 SC FC cohC zr sr xz step SC' FC' cohC' zr' sr' xz' step'
           Hz Hstep j m e m' e').
Qed.

Lemma funtm_natrec (G : ctx) (j : nat) (C z s n : tm)
  (LC : LTy (nat_ j :: G) C) (IHC : FunTm (nat_ j :: G) C)
  (Lz : LTm G z (C [(zero j)..])) (IHz : FunTm G z)
  (Ls : LTm (C :: nat_ j :: G) s (nrec_succ C)) (IHs : FunTm (C :: nat_ j :: G) s)
  (Ln : LTm G n (nat_ j)) (IHn : FunTm G n) : FunTm G (natrec C z s n).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape RecVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [jb SC FC cohC S0 wz xz ws xs redS wn xn ES DC Dz Ds Dn].
  destruct d' as
    [jb' SC' FC' cohC' S0' wz' xz' ws' xs' redS' wn' xn' ES' DC' Dz' Ds' Dn'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold rd_val in Hv, Hv'.
  cbn [rd_j rd_SC rd_FC rd_cohC rd_S0 rd_wz rd_xz rd_ws rd_xs rd_redS rd_wn
       rd_xn] in Hv, Hv'.
  (* the scrutinee's level agrees on both sides *)
  pose proof (itm_lvl n rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                NotPrfR_nat Dn _ _ _ _ _ NotPrfR_nat Dn') as Ejb; subst jb'.
  (* the motive: related environments, and related families at related naturals *)
  assert (HEm : forall m (xm : kElAt (natFam jb) m) m' (xm' : kElAt (natFam jb) m'),
             kEqAt (natFam jb) m xm (natFam jb) m' xm' ->
             EnvRelOf (nat_ j :: G) (ext rho (natFam jb) m xm)
                                    (ext rho' (natFam jb) m' xm')).
  { intros m xm m' xm' Hm.
    apply (EnvRelOf_ext' G rho rho' (nat_ j) jb enat enat);
      [ exact HE | reflexivity | reflexivity
      | apply (proj1 (kRel_same (natFam jb) _ _ _ _)); exact Hm ]. }
  assert (HCm : forall m (xm : kElAt (natFam jb) m) m' (xm' : kElAt (natFam jb) m'),
             kEqAt (natFam jb) m xm (natFam jb) m' xm' ->
             kceq (kAt (FC m xm)) (kAt (FC' m' xm'))).
  { intros m xm m' xm' Hm.
    assert (ECm : SC m = ers (ext rho (natFam jb) m xm) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC m xm)).
    assert (ECm' : SC' m' = ers (ext rho' (natFam jb) m' xm') C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' m' xm')).
    assert (Htc : tyeq (SC m) (SC' m'))
      by (rewrite ECm, ECm'; exact (LC _ _ (HEm m xm m' xm' Hm))).
    exact (FunTy_of_FunTm (nat_ j :: G) C IHC _ _ (HEm m xm m' xm' Hm) k
             _ (FC m xm) _ (FC' m' xm') (DC m xm) (DC' m' xm')
             (eqty_at_lvl k _ _ (uf_ty (FC m xm)) (uf_ty (FC' m' xm')) Htc)). }
  (* the scrutinee *)
  assert (Ewn : wn = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn).
  assert (Ewn' : wn' = ers rho' n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn').
  assert (Hrn : Rel enat wn wn') by (rewrite Ewn, Ewn'; exact (Ln rho rho' HE)).
  assert (Hxn : kEqAt (natFam jb) wn xn (natFam jb) wn' xn')
    by exact (kRel_at (IHn rho rho' HE jb enat (natFam jb) wn xn Dn
                         enat (natFam jb) wn' xn' Dn'
                         (famAtSelf (natFam jb)) Hrn)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (semrec_rel_el k jb SC FC cohC wz S0 xz _ SC' FC' cohC' wz' S0' xz' _);
    [ | | exact Hxn ].
  - (* the base value *)
    assert (Hz0 : kEqAt (natFam jb) ezero (natE 0 NatAt_zero)
                    (natFam jb) ezero (natE 0 NatAt_zero))
      by apply (natE_eq 0 NatAt_zero NatAt_zero).
    assert (EC0 : SC ezero = ers (ext rho (natFam jb) ezero (natE 0 NatAt_zero)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC ezero (natE 0 NatAt_zero))).
    assert (EC0' : SC' ezero
                   = ers (ext rho' (natFam jb) ezero (natE 0 NatAt_zero)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' ezero (natE 0 NatAt_zero))).
    assert (Htc0 : tyeq (SC ezero) (SC' ezero))
      by (rewrite EC0, EC0'; exact (LC _ _ (HEm _ _ _ _ Hz0))).
    assert (Ewz : wz = ers rho z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz).
    assert (Ewz' : wz' = ers rho' z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz').
    assert (Esub : ers rho (C [(zero j)..]) = SC ezero).
    { rewrite EC0; exact (ers_sub1 rho C (zero j) (natFam jb) (natE 0 NatAt_zero)). }
    assert (Hrz : Rel (SC' ezero) wz wz').
    { rewrite Ewz, Ewz'.
      apply (Rel_tyeq (SC ezero) (SC' ezero)); [exact Htc0 |].
      rewrite <- Esub; exact (Lz rho rho' HE). }
    exact (IHz rho rho' HE k _ (FC ezero (natE 0 NatAt_zero)) _ xz Dz
             _ (FC' ezero (natE 0 NatAt_zero)) _ xz' Dz'
             (HCm _ _ _ _ Hz0) Hrz).
  - (* the step *)
    intros m xm m' xm' Hm w0 y0 w0' y0' Hy.
    eapply kRel_trans; [ apply kRel_sym; apply moveTo_rel |].
    eapply kRel_trans; [| apply moveTo_rel ].
    assert (ECm : SC m = ers (ext rho (natFam jb) m xm) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC m xm)).
    assert (ECm' : SC' m' = ers (ext rho' (natFam jb) m' xm') C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' m' xm')).
    pose proof (EnvRelOf_ext' (nat_ j :: G) (ext rho (natFam jb) m xm)
                  (ext rho' (natFam jb) m' xm') C k _ _ (FC m xm) (FC' m' xm')
                  w0 y0 w0' y0' (HEm m xm m' xm' Hm) ECm ECm' Hy) as HEs.
    assert (Hsucc : kEqAt (natFam jb) (esucc m) (natSucc xm)
                      (natFam jb) (esucc m') (natSucc xm'))
      by (apply natSucc_eq; exact Hm).
    assert (ECs : SC (esucc m)
                  = ers (ext rho (natFam jb) (esucc m) (natSucc xm)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC (esucc m) (natSucc xm))).
    assert (ECs' : SC' (esucc m')
                   = ers (ext rho' (natFam jb) (esucc m') (natSucc xm')) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' (esucc m') (natSucc xm'))).
    assert (Htcs : tyeq (SC (esucc m)) (SC' (esucc m')))
      by (rewrite ECs, ECs'; exact (LC _ _ (HEm _ _ _ _ Hsucc))).
    assert (Ews : ws m xm w0 y0
                  = ers (ext (ext rho (natFam jb) m xm) (FC m xm) w0 y0) s)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds m xm w0 y0)).
    assert (Ews' : ws' m' xm' w0' y0'
                   = ers (ext (ext rho' (natFam jb) m' xm') (FC' m' xm') w0' y0') s)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds' m' xm' w0' y0')).
    assert (Esub2 : ers (ext (ext rho (natFam jb) m xm) (FC m xm) w0 y0)
                      (nrec_succ C) = SC (esucc m)).
    { rewrite ECs; exact (er_nrec_succ C (rsub rho) m w0). }
    assert (Hrs : Rel (SC' (esucc m')) (ws m xm w0 y0) (ws' m' xm' w0' y0')).
    { rewrite Ews, Ews'.
      apply (Rel_tyeq (SC (esucc m)) (SC' (esucc m'))); [exact Htcs |].
      rewrite <- Esub2; exact (Ls _ _ HEs). }
    exact (IHs _ _ HEs k _ (FC (esucc m) (natSucc xm)) _ (xs m xm w0 y0)
             (Ds m xm w0 y0) _ (FC' (esucc m') (natSucc xm')) _
             (xs' m' xm' w0' y0') (Ds' m' xm' w0' y0')
             (HCm _ _ _ _ Hsucc) Hrs).
Qed.

(* ------------------------------------------------------------------ *)
(* SUP.                                                                *)
(*                                                                    *)
(* `wSup_congX` (Interp/WEl.v) does the work: related labels and         *)
(* pointwise related branches give related sups across the two readings.  *)
(* What this case supplies is the branching function's functionality --    *)
(* `brApp` is a `piApp`, so that is `piApp_eqX` at the branching Pi --     *)
(* and the one layer-1 fact the clause does NOT pin: `i_sup` pins only     *)
(* the W type's realiser, never the Pi the branching function lives at     *)
(* (just as `i_pair` leaves its second component's type unpinned), so the  *)
(* two functions' relatedness is recovered from the two SUPS' instead,     *)
(* by Rel_w_br2 branchwise and Rel_pi_intro.                               *)
(* ------------------------------------------------------------------ *)

Lemma funtm_sup (G : ctx) (kk : nat) (A B a f : tm)
  (LA : LTy G A) (IHA : FunTm G A) (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  (Lw : LTy G (wt kk A B))
  (La : LTm G a A) (IHa : FunTm G a) (IHf : FunTm G f) : FunTm G (sup kk A B a f).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape SupVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [i j dA dB EA EB wA FA B0 wB FB redB cohB gW Bbr redBbr gBr
     wa xa wf xf gd Ekk Ew DA DB Da Df].
  destruct d' as
    [i' j' dA' dB' EA' EB' wA' FA' B0' wB' FB' redB' cohB' gW' Bbr' redBbr' gBr'
     wa' xa' wf' xf' gd' Ekk' Ew' DA' DB' Da' Df'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold sp_WF, sp_val in Hv, Hv'.
  cbn [sp_i sp_j sp_dA sp_dB sp_EA sp_EB sp_wA sp_FA sp_B0 sp_wB sp_FB sp_redB
       sp_cohB sp_gW sp_Bbr sp_redBbr sp_gBr sp_wa sp_xa sp_wf sp_xf sp_gd]
    in Hv, Hv'.
  (* the label's level and gap *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA'
                (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  assert (Hty : tyeq (ew (ers rho A) B0) (ew (ers rho' A) B0'))
    by (rewrite Ew, Ew'; exact (Lw rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE k
              i j dA dB EA EB (ers rho A) FA wB FB
              i j' dA dB' EA EB' (ers rho' A) FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  pose proof (wFam_ceq k (ers rho A) B0 (upF dA k EA FA) wB
                (fun u y => upF dB k EB (FB u y)) redB cohB gW
                (ers rho' A) B0' (upF dA k EA FA') wB'
                (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gW'
                Hty HAu HBu) as HQW.
  (* the label *)
  assert (Ewa : wa = ers rho a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho' a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  assert (Hra : Rel (ers rho' A) wa wa').
  { rewrite Ewa, Ewa'.
    apply (Rel_tyeq (ers rho A) (ers rho' A));
      [ exact (LA rho rho' HE) | exact (La rho rho' HE) ]. }
  pose proof (IHa rho rho' HE i _ FA wa xa Da _ FA' wa' xa' Da' HA Hra) as Hxa.
  pose proof (upEl_eq dA k EA FA wa xa FA' wa' xa' HA (kRel_at Hxa)) as Hz.
  (* the two sups' realisers are related: the subject's own relatedness, moved
     onto the two canonical values by the decoder's two IsVals *)
  assert (HRw : Rel (ew (ers rho A) B0) w w').
  { apply (Rel_tyeq Sy' (ew (ers rho A) B0) w w'); [| exact Hrel].
    eapply tyeq_trans; [| apply tyeq_sym; exact Hty].
    exists k.
    exact (ceq_eqty F' (wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                          (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gW')
             (projT1 Hv')). }
  assert (HR : Rel (ew (ers rho A) B0) (esup wa wf) (esup wa' wf')).
  { eapply Rel_trans;
      [ apply Rel_sym;
        exact (famEl_rel (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                            (fun u y => upF dB k EB (FB u y)) redB cohB gW)
                 w _ _ (esup wa wf) _ (projT2 Hv)) |].
    eapply Rel_trans; [exact HRw |].
    apply (Rel_tyeq (ew (ers rho' A) B0') (ew (ers rho A) B0));
      [ apply tyeq_sym; exact Hty |].
    exact (famEl_rel (wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                        (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gW')
             w' _ _ (esup wa' wf') _ (projT2 Hv')). }
  (* the branching type, read twice: its realiser IS pinned, through the
     codomain's derivation at the label's round trip *)
  pose proof (kRel_dn dA k EA FA FA' HA _ _ _ _ (conj HAu Hz)) as Hzd.
  pose proof (EnvRelOf_ext G rho rho' A i FA FA' _ _ _ _ HE Hzd) as HEx.
  pose proof (DB _ (upEl dA k EA FA wa xa)) as DBx.
  pose proof (DB' _ (upEl dA k EA FA' wa' xa')) as DBx'.
  assert (Htb : tyeq (wB _ (upEl dA k EA FA wa xa))
                  (wB' _ (upEl dA k EA FA' wa' xa'))).
  { assert (EB0 : wB _ (upEl dA k EA FA wa xa) = ers _ B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' _ (upEl dA k EA FA' wa' xa') = ers _ B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    rewrite EB0, EB0'; exact (LB _ _ HEx). }
  (* the two branching Pi types are layer-1 equal: equal domains, and
     codomains that both reduce to the W type *)
  assert (Htp : tyeq (epi (wB _ (upEl dA k EA FA wa xa)) Bbr)
                  (epi (wB' _ (upEl dA k EA FA' wa' xa')) Bbr')).
  { exists k; apply eqty_pi.
    - exact (eqty_at_lvl k _ _ (uf_ty (upF dB k EB (FB _ (upEl dA k EA FA wa xa))))
               (uf_ty (upF dB' k EB' (FB' _ (upEl dA k EA FA' wa' xa')))) Htb).
    - intros u u' _.
      eapply eqty_exp; [ exact (redBbr u) | exact (redBbr' u') |].
      exact (eqty_at_lvl k _ _ (uf_ty (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                                         (fun u0 y => upF dB k EB (FB u0 y))
                                         redB cohB gW))
               (uf_ty (wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                         (fun u0 y => upF dB' k EB' (FB' u0 y)) redB' cohB' gW'))
               Hty). }
  (* and the branching functions are related, which the sups' relatedness
     gives branchwise *)
  assert (Hrf : Rel (epi (wB' _ (upEl dA k EA FA' wa' xa')) Bbr') wf wf').
  { apply (Rel_pi_intro _ (wB' _ (upEl dA k EA FA' wa' xa')) Bbr');
      [ exists k; exact (gBr' _ (upEl dA k EA FA' wa' xa'))
      | apply ev_pi
      | intros u u' Hu ].
    eapply Rel_exp_ty; [ exact (redBbr' u) |].
    apply (Rel_tyeq (ew (ers rho A) B0) (ew (ers rho' A) B0')); [exact Hty |].
    apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0 (kFam_good_ty
             (wFam k (ers rho A) B0 (upF dA k EA FA) wB (fun u0 y => upF dB k EB (FB u0 y))
                redB cohB gW)) (ev_w _ _) _ _ HR wa wf wa' wf'
             (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB wa (upEl dA k EA FA wa xa)) |].
    apply (Rel_tyeq (wB' _ (upEl dA k EA FA' wa' xa'))
             (wB _ (upEl dA k EA FA wa xa)));
      [ apply tyeq_sym; exact Htb | exact Hu ]. }
  pose proof (IHf rho rho' HE k _ _ wf xf Df _ _ wf' xf' Df'
                (piFam_ceq k (wB _ (upEl dA k EA FA wa xa)) Bbr
                   (upF dB k EB (FB _ (upEl dA k EA FA wa xa)))
                   (fun _ _ => ew (ers rho A) B0)
                   (fun _ _ => wFam k (ers rho A) B0 (upF dA k EA FA) wB
                                 (fun u0 y => upF dB k EB (FB u0 y)) redB cohB gW)
                   (fun v _ => redBbr v)
                   (fun v y v' y' _ => famAtSelf (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                                          (fun u0 y0 => upF dB k EB (FB u0 y0))
                                          redB cohB gW))
                   (gBr _ (upEl dA k EA FA wa xa))
                   (wB' _ (upEl dA k EA FA' wa' xa')) Bbr'
                   (upF dB' k EB' (FB' _ (upEl dA k EA FA' wa' xa')))
                   (fun _ _ => ew (ers rho' A) B0')
                   (fun _ _ => wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                                 (fun u0 y => upF dB' k EB' (FB' u0 y)) redB' cohB'
                                 gW')
                   (fun v _ => redBbr' v)
                   (fun v y v' y' _ => famAtSelf (wFam k (ers rho' A) B0' (upF dA k EA FA')
                                          wB' (fun u0 y0 => upF dB' k EB' (FB' u0 y0))
                                          redB' cohB' gW'))
                   (gBr' _ (upEl dA k EA FA' wa' xa'))
                   Htp (HBu _ _ _ _ Hz) (fun v y v' y' _ => HQW))
                Hrf) as Hxf.
  (* and now the two sups *)
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  split; [exact HQW |].
  apply (wSup_congX k (ers rho A) B0 (upF dA k EA FA) wB
           (fun u y => upF dB k EB (FB u y)) redB cohB gW
           (ers rho' A) B0' (upF dA k EA FA') wB'
           (fun u y => upF dB' k EB' (FB' u y)) redB' cohB' gW'
           HQW HAu HBu);
    [ exact Hz | | exact HR ].
  (* the branches: brApp is a piApp, so this is piApp_eqX *)
  intros v0 y v0' y' Hy.
  exact (kRel_at
           (piApp_eqX k (wB _ (upEl dA k EA FA wa xa)) Bbr
              (upF dB k EB (FB _ (upEl dA k EA FA wa xa)))
              (fun _ _ => ew (ers rho A) B0)
              (fun _ _ => wFam k (ers rho A) B0 (upF dA k EA FA) wB
                            (fun u0 y0 => upF dB k EB (FB u0 y0)) redB cohB gW)
              (fun v _ => redBbr v)
              (fun v yy v' yy' _ => famAtSelf (wFam k (ers rho A) B0 (upF dA k EA FA) wB
                                     (fun u0 y0 => upF dB k EB (FB u0 y0))
                                     redB cohB gW))
              (gBr _ (upEl dA k EA FA wa xa))
              (wB' _ (upEl dA k EA FA' wa' xa')) Bbr'
              (upF dB' k EB' (FB' _ (upEl dA k EA FA' wa' xa')))
              (fun _ _ => ew (ers rho' A) B0')
              (fun _ _ => wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                            (fun u0 y0 => upF dB' k EB' (FB' u0 y0)) redB' cohB' gW')
              (fun v _ => redBbr' v)
              (fun v yy v' yy' _ => famAtSelf (wFam k (ers rho' A) B0' (upF dA k EA FA') wB'
                                     (fun u0 y0 => upF dB' k EB' (FB' u0 y0))
                                     redB' cohB' gW'))
              (gBr' _ (upEl dA k EA FA' wa' xa'))
              (HBu _ _ _ _ Hz) (fun v yy v' yy' _ => HQW)
              wf xf wf' xf' v0 y v0' y' (kRel_at Hxf) Hy)).
Qed.

(* ------------------------------------------------------------------ *)
(* THE W-RECURSION.                                                    *)
(*                                                                    *)
(* `wRecS_relX` (Interp/WEl.v) does the recursion; its one open premise  *)
(* is the step's congruence across the two readings, and discharging      *)
(* that is what this case is about.  The step is typed in the three-entry  *)
(* context `wih n k A B C :: wbr k A B :: A :: G`, so the two readings'     *)
(* environments have to be related THERE -- and the two Pi entries are      *)
(* the only families in the whole interpretation whose shadow the clause     *)
(* does not pin (`i_wrec` pins the W type's realiser and the step's, not     *)
(* the branching function's type nor the induction hypothesis's).  Their     *)
(* shadows are recognised instead: both are Pi types whose codomain          *)
(* REDUCES to something known, which is exactly the shape layer 1's          *)
(* eqty_cfun / eqty_dfun are stated at, and `er_wbr_sub` / `er_wih_sub`      *)
(* (Layer1/Fundamental.v) say that the context types erase to the same       *)
(* shape.                                                                    *)
(* ------------------------------------------------------------------ *)

(* a Pi whose codomain reduces to a CONSTANT is layer-1 equal to the explicit
   constant-codomain Pi: this recognises `wbr`'s erasure *)
Lemma cfun_tyeq (kw : nat) (S0 Bf W : etm)
  (hB : eqty kw S0 S0) (hW : eqty kw W W)
  (red : forall v, reds (eapp Bf v) W) :
  tyeq (epi S0 Bf) (epi S0 (elam (ren_etm ↑ W))).
Proof.
  exists kw; apply eqty_pi; [exact hB |].
  intros u u' _; eapply eqty_exp;
    [ apply red | apply reds_const_cod | exact hW ].
Qed.

(* and the dependent version, where both codomains reduce to the same family
   of types: this recognises `wih`'s erasure *)
Lemma dfun_tyeq (nn : nat) (S0 Bf Y : etm) (Cy : etm -> etm)
  (hB : eqty nn S0 S0)
  (red : forall v, reds (eapp Bf v) (Cy v))
  (redY : forall v, reds (eapp (elam Y) v) (Cy v))
  (hC : forall u u', Rel S0 u u' -> eqty nn (Cy u) (Cy u')) :
  tyeq (epi S0 Bf) (epi S0 (elam Y)).
Proof.
  exists nn; apply eqty_pi; [exact hB |].
  intros u u' Hu; eapply eqty_exp;
    [ apply red | apply redY | apply hC; exact Hu ].
Qed.

(* The recursion itself.  Its one open premise in `wRecS_relX` is the step's
   congruence across the two readings, and discharging it means relating the
   two THREE-ENTRY environments the step is read in: the label, the branching
   function and the induction hypothesis.  The last two are the only families
   in the interpretation whose shadow the clause does not pin, so they are
   RECOGNISED instead -- `wbr`'s codomain reduces to the tree type at every
   realiser (cfun_tyeq), `wih`'s to the motive at the subtree (dfun_tyeq, and
   this is what the clause's `ESC` is for).  Their layer-1 relatedness comes
   from the two sups': `Rel_w_br2` for the branching functions, and for the
   two induction hypotheses layer 1's own recursor lemma `sem_wrec`, which is
   where the hypotheses of this case are in SubstRel form -- they are what
   `fundamental_U` and `fundamental_ty` hand over, and the step's context has
   no semantic elements to build an `EnvRelOf` out of. *)
Lemma funtm_wrec (G : ctx) (kk ii jj mm nn : nat) (A B C s w0 : tm)
  (Hik : ii <= kk) (Hjk : jj <= kk) (Hjn : jj <= nn) (Hmn : mm <= nn)
  (LAm : forall g g', SubstRel G g g' ->
     eqty ii (subst_etm g (er A)) (subst_etm g' (er A)))
  (LBm : forall g g', SubstRel (A :: G) g g' ->
     eqty jj (subst_etm g (er B)) (subst_etm g' (er B)))
  (LCm : forall g g', SubstRel (wt kk A B :: G) g g' ->
     eqty mm (subst_etm g (er C)) (subst_etm g' (er C)))
  (Lsm : forall sigma sigma',
     SubstRel (wih nn kk A B C :: wbr kk A B :: A :: G) sigma sigma' ->
     Rel (subst_etm sigma (er (wsup_ty kk A B C)))
         (subst_etm sigma (er s)) (subst_etm sigma' (er s)))
  (Lwm : forall g g', SubstRel G g g' ->
     Rel (subst_etm g (er (wt kk A B))) (subst_etm g (er w0)) (subst_etm g' (er w0)))
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) (IHC : FunTm (wt kk A B :: G) C)
  (IHs : FunTm (wih nn kk A B C :: wbr kk A B :: A :: G) s) (IHw : FunTm G w0) :
  FunTm G (wrec A B C s w0).
Proof.
  (* the layer-1 hypotheses, in the forms the other cases use *)
  assert (LA : LTy G A)
    by (intros r r' [_ [_ [_ HS]]]; exists ii; exact (LAm _ _ HS)).
  assert (LB : LTy (A :: G) B)
    by (intros r r' [_ [_ [_ HS]]]; exists jj; exact (LBm _ _ HS)).
  assert (LC : LTy (wt kk A B :: G) C)
    by (intros r r' [_ [_ [_ HS]]]; exists mm; exact (LCm _ _ HS)).
  assert (Lw : LTy G (wt kk A B)).
  { intros r r' [_ [_ [_ HS]]]; exists kk.
    apply sem_w_eq;
      [ exact (eqty_cumul ii kk _ _ Hik (LAm _ _ HS))
      | intros u u' Hu; apply (eqty_cumul jj kk _ _ Hjk);
        exact (LBm _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu)) ]. }
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Pc Hrel.
  cbn [TmShape WRecVal Shaped] in E, E'.
  destruct E as [d Hv]; destruct E' as [d' Hv'].
  destruct d as
    [kw i j n dA dB dBn dC EA EB EBn EC En wA FA B0 wB FB redB cohB gW
     SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr gf gih ws xs redS stepSrel
     ww xw ESr Ew ESC DA DB DC Dstep Dw].
  destruct d' as
    [kw' i' j' n' dA' dB' dBn' dC' EA' EB' EBn' EC' En' wA' FA' B0' wB' FB'
     redB' cohB' gW' SC' FC' cohC' Bbr' redBbr' gBr' Bih' gIh' Bih_red' Sr' gf'
     gih' ws' xs' redS' stepSrel' ww' xw' ESr' Ew' ESC' DA' DB' DC' Dstep' Dw'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold wr_val in Hv, Hv'.
  cbn [wr_kw wr_i wr_j wr_n wr_dA wr_dB wr_dBn wr_dC wr_EA wr_EB wr_EBn wr_EC
       wr_wA wr_FA wr_B0 wr_wB wr_FB wr_redB wr_cohB wr_gW wr_SC wr_FC wr_cohC
       wr_Bbr wr_redBbr wr_gBr wr_Bih wr_gIh wr_Bih_red wr_Sr wr_gf wr_gih
       wr_ws wr_xs wr_redS wr_stepSrel wr_ww wr_xw] in Hv, Hv'.
  pose proof (proj2 (proj2 (proj2 HE))) as HS.
  (* the tree type's level, hence the label's gap *)
  pose proof (itm_lvl w0 rho rho' (lvls_of_EnvRelOf G rho rho' HE) _ _ _ _ _
                (NotPrfR_w wA B0) Dw _ _ _ _ _ (NotPrfR_w wA' B0') Dw') as Ekw.
  destruct Ekw.
  pose proof (ity_lvl rho rho' (lvls_of_EnvRelOf G rho rho' HE) A i _ FA i' _ FA'
                DA DA') as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (HA : kceq (kAt FA) (kAt FA')).
  { apply (FunTy_of_FunTm G A IHA rho rho' HE i _ FA _ FA' DA DA').
    apply (eqty_at_lvl i _ _ (uf_ty FA) (uf_ty FA')).
    rewrite EwA, EwA'; exact (LA rho rho' HE). }
  assert (Hty : tyeq (ew wA B0) (ew wA' B0'))
    by (rewrite Ew, Ew'; exact (Lw rho rho' HE)).
  destruct (comp_ceq G A B LA LB IHA IHB rho rho' HE kw
              i j dA dB EA EB wA FA wB FB
              i j' dA dB' EA EB' wA' FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  pose proof (wFam_ceq kw wA B0 (upF dA kw EA FA) wB
                (fun u y => upF dB kw EB (FB u y)) redB cohB gW
                wA' B0' (upF dA kw EA FA') wB'
                (fun u y => upF dB' kw EB' (FB' u y)) redB' cohB' gW'
                Hty HAu HBu) as HQW.
  (* the motive, at every related pair of trees *)
  assert (HCm : forall w1 x1 w1' x1',
             kEqAt (wFam kw wA B0 (upF dA kw EA FA) wB
                      (fun u y => upF dB kw EB (FB u y)) redB cohB gW) w1 x1
                   (wFam kw wA' B0' (upF dA kw EA FA') wB'
                      (fun u y => upF dB' kw EB' (FB' u y)) redB' cohB' gW') w1' x1' ->
             kceq (kAt (FC w1 x1)) (kAt (FC' w1' x1'))).
  { intros w1 x1 w1' x1' H1.
    pose proof (EnvRelOf_ext' G rho rho' (wt kk A B) kw _ _ _ _ w1 x1 w1' x1'
                  HE Ew Ew' (conj HQW H1)) as HEw.
    apply (FunTy_of_FunTm (wt kk A B :: G) C IHC _ _ HEw k _ (FC w1 x1) _
             (FC' w1' x1') (DC w1 x1) (DC' w1' x1')).
    apply (eqty_at_lvl k _ _ (uf_ty (FC w1 x1)) (uf_ty (FC' w1' x1'))).
    rewrite ESC, ESC'; exact (LC _ _ HEw). }
  (* the subject *)
  assert (Hrw : Rel (ew wA' B0') ww ww').
  { assert (Eww : ww = ers rho w0) by exact (ers_of_ITm _ _ _ _ _ _ _ Dw).
    assert (Eww' : ww' = ers rho' w0) by exact (ers_of_ITm _ _ _ _ _ _ _ Dw').
    rewrite Eww, Eww'.
    apply (Rel_tyeq (ew wA B0) (ew wA' B0')); [exact Hty |].
    rewrite Ew; exact (Lwm _ _ HS). }
  pose proof (IHw rho rho' HE kw _ _ ww xw Dw _ _ ww' xw' Dw' HQW Hrw) as Hxw.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  refine (wRecS_relX kw wA B0 (upF dA kw EA FA) wB
            (fun u y => upF dB kw EB (FB u y)) redB cohB gW
            wA' B0' (upF dA kw EA FA') wB'
            (fun u y => upF dB' kw EB' (FB' u y)) redB' cohB' gW'
            HQW HAu HBu k Sr Sr'
            (fun w1 _ => SC w1) FC cohC (fun w1 _ => SC' w1) FC' cohC'
            (stepOf kw i j dA dB EA EB wA FA B0 wB FB redB cohB gW k SC FC Sr
               ws xs redS) stepSrel
            (stepOf kw i j' dA dB' EA EB' wA' FA' B0' wB' FB' redB' cohB' gW' k
               SC' FC' Sr' ws' xs' redS') stepSrel'
            _ ww xw ww' xw' (kRel_at Hxw)).
  (* ---- the step's congruence across the two readings ---- *)
  intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
         Hz Hsub HRsup Hih.
  (* the codomain's level and gap, and then the induction hypothesis's *)
  pose proof (kRel_dn dA kw EA FA FA' HA _ _ _ _ (conj HAu Hz)) as Hzd.
  pose proof (EnvRelOf_ext' G rho rho' A i wA wA' FA FA' _ _ _ _ HE EwA EwA' Hzd)
    as HE1.
  pose proof (DB u0 z) as DBx; pose proof (DB' u0' z') as DBx'.
  pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HE1) B
                j _ (FB u0 z) j' _ (FB' u0' z') DBx DBx') as Ej; subst j'.
  assert (EdB : dB' = dB) by lia; subst dB'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
  assert (Enn : n = n') by (rewrite En, En'; reflexivity).
  destruct Enn.
  assert (EdBn : dBn' = dBn) by lia; subst dBn'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EBn' EBn) as EEBn; subst EBn'.
  assert (EdC : dC' = dC) by lia; subst dC'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EC' EC) as EEC; subst EC'.
  (* the branching type, at the two labels *)
  assert (QB : kceq (kAt (FB u0 z)) (kAt (FB' u0' z')))
    by exact (cod_ceq G A B LB IHB rho rho' HE kw i j dA EA wA FA wB FB
                wA' FA' wB' FB' DA DA' HA DB DB' u0 z u0' z' Hz).
  assert (Htb : tyeq (wB u0 z) (wB' u0' z')).
  { assert (EB0 : wB u0 z = ers _ B) by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB0' : wB' u0' z' = ers _ B) by exact (ers_of_ITy _ _ _ _ _ DBx').
    rewrite EB0, EB0'; exact (LB _ _ HE1). }
  (* the branching function's Pi, and the function's own relatedness, which
     comes out of the two sups' *)
  assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB' u0' z') Bbr')).
  { exists kw; apply eqty_pi.
    - exact (eqty_at_lvl kw _ _ (uf_ty (upF dB kw EB (FB u0 z)))
               (uf_ty (upF dB kw EB (FB' u0' z'))) Htb).
    - intros u u' _.
      eapply eqty_exp; [ exact (redBbr u) | exact (redBbr' u') |].
      exact (eqty_at_lvl kw _ _
               (uf_ty (wFam kw wA B0 (upF dA kw EA FA) wB
                         (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW))
               (uf_ty (wFam kw wA' B0' (upF dA kw EA FA') wB'
                         (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW'))
               Hty). }
  assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
  { apply (Rel_pi_intro _ (wB u0 z) Bbr);
      [ exists kw; exact (gBr u0 z) | apply ev_pi | intros u u' Hu ].
    eapply Rel_exp_ty; [ exact (redBbr u) |].
    apply (Rel_w_br2 (ew wA B0) wA B0
             (kFam_good_ty (wFam kw wA B0 (upF dA kw EA FA) wB
                              (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW))
             (ev_w _ _) _ _ HRsup u0 f u0' f' (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hu ]. }
  (* the two branch entries *)
  assert (EB0 : wB u0 z = subst_etm (scons u0 (rsub rho)) (er B))
    by exact (ers_of_ITy _ _ _ _ _ DBx).
  assert (EB0' : wB' u0' z' = subst_etm (scons u0' (rsub rho')) (er B))
    by exact (ers_of_ITy _ _ _ _ _ DBx').
  assert (EwW : ew wA B0 = subst_etm (rsub rho) (er (wt kk A B))) by exact Ew.
  assert (EwW' : ew wA' B0' = subst_etm (rsub rho') (er (wt kk A B))) by exact Ew'.
  assert (Tbr : tyeq (epi (wB u0 z) Bbr)
                  (subst_etm (scons u0 (rsub rho)) (er (wbr kk A B)))).
  { rewrite (er_wbr_sub kk A B (rsub rho) u0), <- EB0, <- EwW.
    exact (cfun_tyeq kw (wB u0 z) Bbr (ew wA B0)
             (uf_ty (upF dB kw EB (FB u0 z)))
             (uf_ty (wFam kw wA B0 (upF dA kw EA FA) wB
                       (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW))
             redBbr). }
  assert (Tbr' : tyeq (epi (wB' u0' z') Bbr')
                   (subst_etm (scons u0' (rsub rho')) (er (wbr kk A B)))).
  { rewrite (er_wbr_sub kk A B (rsub rho') u0'), <- EB0', <- EwW'.
    exact (cfun_tyeq kw (wB' u0' z') Bbr' (ew wA' B0')
             (uf_ty (upF dB kw EB (FB' u0' z')))
             (uf_ty (wFam kw wA' B0' (upF dA kw EA FA') wB'
                       (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW'))
             redBbr'). }
  pose proof (piFam_ceq kw (wB u0 z) Bbr (upF dB kw EB (FB u0 z))
                (fun v _ => ew wA B0)
                (fun v _ => wFam kw wA B0 (upF dA kw EA FA) wB
                              (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW)
                (fun v _ => redBbr v)
                (fun v y v' y' _ =>
                   famAtSelf (wFam kw wA B0 (upF dA kw EA FA) wB
                                (fun u1 y1 => upF dB kw EB (FB u1 y1)) redB cohB gW))
                (gBr u0 z)
                (wB' u0' z') Bbr' (upF dB kw EB (FB' u0' z'))
                (fun v _ => ew wA' B0')
                (fun v _ => wFam kw wA' B0' (upF dA kw EA FA') wB'
                              (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW')
                (fun v _ => redBbr' v)
                (fun v y v' y' _ =>
                   famAtSelf (wFam kw wA' B0' (upF dA kw EA FA') wB'
                                (fun u1 y1 => upF dB kw EB (FB' u1 y1)) redB' cohB'
                                gW'))
                (gBr' u0' z')
                Htp (HBu u0 z u0' z' Hz) (fun v y v' y' _ => HQW)) as Hbrceq.
  pose proof (piLam_eq kw (wB u0 z) Bbr (upF dB kw EB (FB u0 z))
                (fun v _ => ew wA B0)
                (fun v _ => wFam kw wA B0 (upF dA kw EA FA) wB
                              (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW)
                (fun v _ => redBbr v)
                (fun v y v' y' _ =>
                   famAtSelf (wFam kw wA B0 (upF dA kw EA FA) wB
                                (fun u1 y1 => upF dB kw EB (FB u1 y1)) redB cohB gW))
                (gBr u0 z)
                (wB' u0' z') Bbr' (upF dB kw EB (FB' u0' z'))
                (fun v _ => ew wA' B0')
                (fun v _ => wFam kw wA' B0' (upF dA kw EA FA') wB'
                              (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW')
                (fun v _ => redBbr' v)
                (fun v y v' y' _ =>
                   famAtSelf (wFam kw wA' B0' (upF dA kw EA FA') wB'
                                (fun u1 y1 => upF dB kw EB (FB' u1 y1)) redB' cohB'
                                gW'))
                (gBr' u0' z')
                Htp (HBu u0 z u0' z' Hz) (fun v y v' y' _ => HQW)
                f (fun v _ => eapp f v) sub (fun v y => reds_refl (eapp f v))
                subext (gf u0 z f gd)
                f' (fun v _ => eapp f' v) sub' (fun v y => reds_refl (eapp f' v))
                subext' (gf' u0' z' f' gd') HRf Hsub) as Hbrel.
  pose proof (EnvRelOf_ext_ty (A :: G) _ _ (wbr kk A B) kw _ _ _ _
                f _ f' _ HE1 Tbr Tbr' (conj Hbrceq Hbrel)) as HE2.
  (* ---- the layer-1 side of the induction hypothesis's entry ---- *)
  pose proof (SubstRel_refl G _ _ HS) as HSr.
  assert (HBg : forall u u', Rel (subst_etm (rsub rho) (er A)) u u' ->
                  eqty jj (subst_etm (scons u (rsub rho)) (er B))
                          (subst_etm (scons u' (rsub rho)) (er B)))
    by (intros u u' Hu; exact (LBm _ _ (SubstRel_cons _ _ _ _ _ _ HSr Hu))).
  assert (HWk : eqty kk (subst_etm (rsub rho) (er (wt kk A B)))
                  (subst_etm (rsub rho) (er (wt kk A B)))).
  { apply sem_w_eq;
      [ exact (eqty_cumul ii kk _ _ Hik (LAm _ _ HSr))
      | intros u u' Hu; exact (eqty_cumul jj kk _ _ Hjk (HBg u u' Hu)) ]. }
  assert (HCg : forall x1 y1, Rel (subst_etm (rsub rho) (er (wt kk A B))) x1 y1 ->
                  eqty mm (subst_etm (scons x1 (rsub rho)) (er C))
                          (subst_etm (scons y1 (rsub rho)) (er C)))
    by (intros x1 y1 Hxy; exact (LCm _ _ (SubstRel_cons _ _ _ _ _ _ HSr Hxy))).
  pose proof (sem_wrec kk mm A B C (rsub rho) _ _ (gt_of kk _ HWk) HCg
                (sem_wrec_step G kk jj mm nn A B C s s (rsub rho) (rsub rho')
                   Hjk Hjn Hmn HS HBg HWk HCg Lsm)) as Hrec0.
  (* the two branchings, read at layer 1: out of the two sups' relatedness *)
  assert (Hbr : forall u u', Rel (wB u0 z) u u' ->
             Rel (subst_etm (rsub rho) (er (wt kk A B))) (eapp f u) (eapp f' u')).
  { intros u u' Hu; rewrite <- EwW.
    apply (Rel_w_br2 (ew wA B0) wA B0
             (kFam_good_ty (wFam kw wA B0 (upF dA kw EA FA) wB
                              (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW))
             (ev_w _ _) _ _ HRsup u0 f u0' f' (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hu ]. }
  assert (Hbrd : forall u u', Rel (wB u0 z) u u' ->
             Rel (subst_etm (rsub rho) (er (wt kk A B))) (eapp f u) (eapp f u')).
  { intros u u' Hu; rewrite <- EwW.
    apply (Rel_w_br2 (ew wA B0) wA B0
             (kFam_good_ty (wFam kw wA B0 (upF dA kw EA FA) wB
                              (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW))
             (ev_w _ _) _ _
             (Rel_trans _ _ _ _ HRsup (Rel_sym _ _ _ HRsup))
             u0 f u0 f (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hu ]. }
  (* the induction hypothesis's own realiser-level relatedness *)
  assert (HRih : Rel (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f) (ihR Sr' f')).
  { apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
      [ exists n; exact (gIh u0 z f gd) | apply ev_pi | intros u u' Hu ].
    eapply Rel_exp_ty; [ exact (Bih_red u0 z f u) |].
    eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
    rewrite ESC, ESr, ESr'.
    exact (Hrec0 _ _ (Hbr u u' Hu)). }
  (* the induction hypothesis's entry: its shadow is a Pi whose codomain
     reduces to the motive at the subtree, which is how `wih` erases *)
  destruct (er_wih_sub nn kk A B C (rsub rho) u0 f) as [Y [EY HY]].
  destruct (er_wih_sub nn kk A B C (rsub rho') u0' f') as [Y' [EY' HY']].
  assert (Tih : tyeq (epi (wB u0 z) (Bih u0 z f))
                  (subst_etm (scons f (scons u0 (rsub rho))) (er (wih nn kk A B C)))).
  { rewrite EY, <- EB0.
    apply (dfun_tyeq (Nat.max mm n) (wB u0 z) (Bih u0 z f) Y
             (fun v => SC (eapp f v)));
      [ exact (eqty_cumul n (Nat.max mm n) _ _ (Nat.le_max_r mm n)
                 (uf_ty (upF dBn n EBn (FB u0 z))))
      | exact (Bih_red u0 z f)
      | intros v; rewrite ESC; exact (HY v)
      | intros u u' Hu; rewrite (ESC (eapp f u)), (ESC (eapp f u'));
        exact (eqty_cumul mm (Nat.max mm n) _ _ (Nat.le_max_l mm n)
                 (HCg _ _ (Hbrd u u' Hu))) ]. }
  assert (Hd' : Rel (ew wA' B0') (esup u0' f') (esup u0' f')).
  { apply (Rel_tyeq (ew wA B0) (ew wA' B0')); [exact Hty |].
    eapply Rel_trans; [apply Rel_sym; exact HRsup | exact HRsup]. }
  assert (Hbrd' : forall u u', Rel (wB' u0' z') u u' ->
             Rel (subst_etm (rsub rho') (er (wt kk A B))) (eapp f' u) (eapp f' u')).
  { intros u u' Hu; rewrite <- EwW'.
    apply (Rel_w_br2 (ew wA' B0') wA' B0'
             (kFam_good_ty (wFam kw wA' B0' (upF dA kw EA FA') wB'
                              (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW'))
             (ev_w _ _) _ _ Hd' u0' f' u0' f' (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB' u0' z') | exact Hu ]. }
  assert (HSr' : SubstRel G (rsub rho') (rsub rho'))
    by exact (EnvOf_SubstRel G rho' rho' (proj1 (proj2 HE)) (proj1 (proj2 HE))
                (EnvRel_refl rho')).
  assert (Tih' : tyeq (epi (wB' u0' z') (Bih' u0' z' f'))
                   (subst_etm (scons f' (scons u0' (rsub rho')))
                      (er (wih nn kk A B C)))).
  { rewrite EY', <- EB0'.
    apply (dfun_tyeq (Nat.max mm n) (wB' u0' z') (Bih' u0' z' f') Y'
             (fun v => SC' (eapp f' v)));
      [ exact (eqty_cumul n (Nat.max mm n) _ _ (Nat.le_max_r mm n)
                 (uf_ty (upF dBn n EBn (FB' u0' z'))))
      | exact (Bih_red' u0' z' f')
      | intros v; rewrite ESC'; exact (HY' v)
      | intros u u' Hu; rewrite (ESC' (eapp f' u)), (ESC' (eapp f' u'));
        exact (eqty_cumul mm (Nat.max mm n) _ _ (Nat.le_max_l mm n)
                 (LCm _ _ (SubstRel_cons _ _ _ _ _ _ HSr' (Hbrd' u u' Hu)))) ]. }
  assert (Htih : tyeq (epi (wB u0 z) (Bih u0 z f))
                   (epi (wB' u0' z') (Bih' u0' z' f'))).
  { exists (Nat.max mm n); apply eqty_pi.
    - exact (eqty_cumul n (Nat.max mm n) _ _ (Nat.le_max_r mm n)
               (eqty_at_lvl n _ _ (uf_ty (upF dBn n EBn (FB u0 z)))
                  (uf_ty (upF dBn n EBn (FB' u0' z'))) Htb)).
    - intros u u' Hu.
      eapply eqty_exp; [ exact (Bih_red u0 z f u) | exact (Bih_red' u0' z' f' u') |].
      rewrite (ESC (eapp f u)), (ESC' (eapp f' u')).
      exact (eqty_cumul mm (Nat.max mm n) _ _ (Nat.le_max_l mm n)
               (LCm _ _ (SubstRel_cons _ _ _ _ _ _ HS (Hbr u u' Hu)))). }
  assert (Hihceq :
    kceq (kAt (ihFam kw i j dA dB EA EB wA FA B0 wB FB redB cohB gW k SC FC cohC
                 n dBn dC EBn EC Bih gIh Bih_red u0 z f gd sub subext))
         (kAt (ihFam kw i j dA dB EA EB wA' FA' B0' wB' FB' redB' cohB' gW' k
                 SC' FC' cohC' n dBn dC EBn EC Bih' gIh' Bih_red' u0' z' f' gd'
                 sub' subext'))).
  { unfold ihFam; apply piFam_ceq;
      [ exact Htih
      | exact (upF_ceq dBn n EBn (FB u0 z) (FB' u0' z') QB)
      | intros v y v' y' Hy; apply upF_ceq; apply HCm;
        exact (Hsub v (ihIdx kw i j dA dB EA EB wA FA wB FB n dBn EBn u0 z v y)
                 v' (ihIdx kw i j dA dB EA EB wA' FA' wB' FB' n dBn EBn u0' z' v' y')
                 (reLvl_eq (FB u0 z) (FB' u0' z') dB kw EB dBn n EBn v y v' y'
                    QB Hy)) ]. }
  assert (Hihel :
    kEqAt (ihFam kw i j dA dB EA EB wA FA B0 wB FB redB cohB gW k SC FC cohC
             n dBn dC EBn EC Bih gIh Bih_red u0 z f gd sub subext) (ihR Sr f)
          (ihEl kw i j dA dB EA EB wA FA B0 wB FB redB cohB gW k SC FC cohC
             n dBn dC EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
             (gih u0 z f gd))
          (ihFam kw i j dA dB EA EB wA' FA' B0' wB' FB' redB' cohB' gW' k
             SC' FC' cohC' n dBn dC EBn EC Bih' gIh' Bih_red' u0' z' f' gd'
             sub' subext') (ihR Sr' f')
          (ihEl kw i j dA dB EA EB wA' FA' B0' wB' FB' redB' cohB' gW' k
             SC' FC' cohC' n dBn dC EBn EC Bih' gIh' Bih_red' Sr' u0' z' f' gd'
             sub' subext' ih' ihext' (gih' u0' z' f' gd'))).
  { unfold ihEl, ihFam; apply piLam_eq;
      [ exact Htih
      | exact (upF_ceq dBn n EBn (FB u0 z) (FB' u0' z') QB)
      | intros v y v' y' Hy; apply upF_ceq; apply HCm;
        exact (Hsub v (ihIdx kw i j dA dB EA EB wA FA wB FB n dBn EBn u0 z v y)
                 v' (ihIdx kw i j dA dB EA EB wA' FA' wB' FB' n dBn EBn u0' z' v' y')
                 (reLvl_eq (FB u0 z) (FB' u0' z') dB kw EB dBn n EBn v y v' y'
                    QB Hy))
      | exact HRih
      | intros v y v' y' Hy;
        exact (upEl_eq dC n EC _ _ _ _ _ _
                 (kRel_ceq (Hih v (ihIdx kw i j dA dB EA EB wA FA wB FB n dBn EBn
                                     u0 z v y)
                             v' (ihIdx kw i j dA dB EA EB wA' FA' wB' FB' n dBn EBn
                                   u0' z' v' y')
                             (reLvl_eq (FB u0 z) (FB' u0' z') dB kw EB dBn n EBn
                                v y v' y' QB Hy)))
                 (kRel_at (Hih v (ihIdx kw i j dA dB EA EB wA FA wB FB n dBn EBn
                                    u0 z v y)
                            v' (ihIdx kw i j dA dB EA EB wA' FA' wB' FB' n dBn EBn
                                  u0' z' v' y')
                            (reLvl_eq (FB u0 z) (FB' u0' z') dB kw EB dBn n EBn
                               v y v' y' QB Hy)))) ]. }
  pose proof (EnvRelOf_ext_ty (wbr kk A B :: A :: G) _ _ (wih nn kk A B C) n
                _ _ _ _ (ihR Sr f) _ (ihR Sr' f') _ HE2 Tih Tih'
                (conj Hihceq Hihel)) as HE3.
  (* the two sups' motives, and the step's own reading *)
  pose proof (HCm _ _ _ _
                (wSup_congX kw wA B0 (upF dA kw EA FA) wB
                   (fun u1 y => upF dB kw EB (FB u1 y)) redB cohB gW
                   wA' B0' (upF dA kw EA FA') wB'
                   (fun u1 y => upF dB kw EB (FB' u1 y)) redB' cohB' gW'
                   HQW HAu HBu u0 z f sub subext gd u0' z' f' sub' subext' gd'
                   Hz Hsub HRsup)) as Hstepceq.
  assert (Hstepr : Rel (SC' (esup u0' f'))
                     (ws u0 z f sub subext gd ih ihext)
                     (ws' u0' z' f' sub' subext' gd' ih' ihext')).
  { assert (Ews : ws u0 z f sub subext gd ih ihext
                  = subst_etm (scons (ihR Sr f) (scons f (scons u0 (rsub rho))))
                      (er s))
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dstep u0 z f sub subext gd ih ihext)).
    assert (Ews' : ws' u0' z' f' sub' subext' gd' ih' ihext'
                   = subst_etm (scons (ihR Sr' f')
                                  (scons f' (scons u0' (rsub rho')))) (er s))
      by exact (ers_of_ITm _ _ _ _ _ _ _
                  (Dstep' u0' z' f' sub' subext' gd' ih' ihext')).
    rewrite Ews, Ews'.
    apply (Rel_tyeq (SC (esup u0 f)) (SC' (esup u0' f')));
      [ exists k; exact (ceq_eqty (FC (esup u0 f) _) (FC' (esup u0' f') _) Hstepceq)
      |].
    rewrite ESC, <- (er_wsup_ty kk A B C (rsub rho) u0 f (ihR Sr f)).
    exact (Lsm _ _ (proj2 (proj2 (proj2 HE3)))). }
  pose proof (IHs _ _ HE3 k _ _ _ (xs u0 z f sub subext gd ih ihext)
                (Dstep u0 z f sub subext gd ih ihext)
                _ _ _ (xs' u0' z' f' sub' subext' gd' ih' ihext')
                (Dstep' u0' z' f' sub' subext' gd' ih' ihext')
                Hstepceq Hstepr) as Hxs.
  (* and the step itself: the two expansions come off *)
  unfold stepOf.
  eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
  eapply kRel_trans; [ exact Hxs |].
  split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ].
Qed.

(* ------------------------------------------------------------------ *)
(* FUNCTIONALITY OF THE INTERPRETATION OF TERMS.                      *)
(*                                                                    *)
(* The cases above are stated per term former, with the layer-1 side   *)
(* conditions as hypotheses; here they are assembled by induction on   *)
(* the typing derivation, which is what discharges those hypotheses -- *)
(* LTy_of_ty / LTm_of_ty, and at `wrec` the SubstRel forms             *)
(* `fundamental_U` / `fundamental_ty` themselves, are layer 1's         *)
(* fundamental theorem, and every rule carries derivations for exactly  *)
(* the types the corresponding case needs.  That is what the full       *)
(* Church annotations bought.                                          *)
(*                                                                    *)
(* t_conv needs nothing: FunTm quantifies over ALL readings of the      *)
(* subject, and i_conv produces one of them.                           *)
(* ------------------------------------------------------------------ *)

Theorem funtm (G : ctx) (t A : tm) (d : ty G t A) : FunTm G t.
Proof.
  revert G t A d.
  apply (ty_mind (fun _ => True) (fun G t A => FunTm G t) (fun _ _ _ _ => True));
    try (intros; exact I).
  - (* t_var *) intros G i A W IHW Hl; apply funtm_var.
  - (* t_conv *) intros G t A B k dt IHt dA IHA dB IHB c IHc; exact IHt.
  - (* t_univ *) intros G k j Hjk W IHW; apply funtm_univ.
  - (* t_up *) intros G j A dA IHA.
    apply funtm_up; [exact (LTy_of_ty G A j dA) | exact IHA].
  - (* t_up_tm *) intros G j A t dA IHA dt IHt.
    apply funtm_uptm; [exact (LTy_of_ty G A j dA) | exact IHA | exact IHt].
  - (* t_pi *) intros G k i j A B Hik Hjk dA IHA dB IHB.
    apply (funtm_pi G k A B);
      [ exact (LTy_of_ty G (pi k A B) k (t_pi G k i j A B Hik Hjk dA dB))
      | exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB ].
  - (* t_lam *) intros G k i j A B t Hik Hjk dA IHA dB IHB dt IHt.
    apply (funtm_lam G k A B t);
      [ exact (LTy_of_ty G A i dA) | exact IHA
      | exact (LTy_of_ty (A :: G) B j dB) | exact IHB
      | exact (LTy_of_ty G (pi k A B) k (t_pi G k i j A B Hik Hjk dA dB))
      | exact (LTm_of_ty (A :: G) t B dt) | exact IHt ].
  - (* t_app *) intros G k i j A B f u Hik Hjk dA IHA dB IHB df IHf du IHu.
    apply (funtm_app G k A B f u);
      [ exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB
      | exact (LTy_of_ty G (pi k A B) k (t_pi G k i j A B Hik Hjk dA dB))
      | exact (LTm_of_ty G f (pi k A B) df) | exact IHf
      | exact (LTm_of_ty G u A du) | exact IHu ].
  - (* t_sig *) intros G k i j A B Hik Hjk dA IHA dB IHB.
    apply (funtm_sig G k A B);
      [ exact (LTy_of_ty G (sig_ k A B) k (t_sig G k i j A B Hik Hjk dA dB))
      | exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB ].
  - (* t_pair *) intros G k i j A B t u Hik Hjk dA IHA dB IHB dt IHt du IHu.
    apply (funtm_pair G k A B t u);
      [ exact (LTy_of_ty G A i dA) | exact IHA
      | exact (LTy_of_ty (A :: G) B j dB) | exact IHB
      | exact (LTy_of_ty G (sig_ k A B) k (t_sig G k i j A B Hik Hjk dA dB))
      | exact (LTm_of_ty G (pair k A B t u) (sig_ k A B)
                 (t_pair G k i j A B t u Hik Hjk dA dB dt du))
      | exact (LTm_of_ty G t A dt) | exact IHt
      | exact (LTm_of_ty G u (B [t..]) du) | exact IHu ].
  - (* t_fst *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp.
    apply (funtm_fst G k A B p);
      [ exact (LTy_of_ty G (sig_ k A B) k (t_sig G k i j A B Hik Hjk dA dB))
      | exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB
      | exact (LTm_of_ty G p (sig_ k A B) dp) | exact IHp ].
  - (* t_snd *) intros G k i j A B p Hik Hjk dA IHA dB IHB dp IHp.
    apply (funtm_snd G k A B p);
      [ exact (LTy_of_ty G (sig_ k A B) k (t_sig G k i j A B Hik Hjk dA dB))
      | exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB
      | exact (LTm_of_ty G p (sig_ k A B) dp) | exact IHp ].
  - (* t_w *) intros G k i j A B Hik Hjk dA IHA dB IHB.
    apply (funtm_w G k A B);
      [ exact (LTy_of_ty G (wt k A B) k (t_w G k i j A B Hik Hjk dA dB))
      | exact (LTy_of_ty G A i dA) | exact (LTy_of_ty (A :: G) B j dB)
      | exact IHA | exact IHB ].
  - (* t_sup *) intros G k i j A B a f Hik Hjk dA IHA dB IHB da IHa df IHf.
    apply (funtm_sup G k A B a f);
      [ exact (LTy_of_ty G A i dA) | exact IHA
      | exact (LTy_of_ty (A :: G) B j dB) | exact IHB
      | exact (LTy_of_ty G (wt k A B) k (t_w G k i j A B Hik Hjk dA dB))
      | exact (LTm_of_ty G a A da) | exact IHa | exact IHf ].
  - (* t_wrec *) intros G k i j m n A B C s w Hik Hjk Hjn Hmn En dA IHA dB IHB
      dC IHC dbr IHbr dih IHih ds IHs dw IHw.
    apply (funtm_wrec G k i j m n A B C s w);
      [ exact Hik | exact Hjk | exact Hjn | exact Hmn
      | exact (fundamental_U G A i dA)
      | exact (fundamental_U (A :: G) B j dB)
      | exact (fundamental_U (wt k A B :: G) C m dC)
      | exact (fundamental_ty _ s (wsup_ty k A B C) ds)
      | exact (fundamental_ty G w (wt k A B) dw)
      | exact IHA | exact IHB | exact IHC | exact IHs | exact IHw ].
  - (* t_nat *) intros G k W IHW; apply funtm_nat.
  - (* t_zero *) intros G k W IHW; apply funtm_zero.
  - (* t_succ *) intros G k n dn IHn; apply funtm_succ; exact IHn.
  - (* t_natrec *) intros G C z s n k j dC IHC dz IHz ds IHs dn IHn.
    apply (funtm_natrec G j C z s n);
      [ exact (LTy_of_ty (nat_ j :: G) C k dC) | exact IHC
      | exact (LTm_of_ty G z (C [(zero j)..]) dz) | exact IHz
      | exact (LTm_of_ty (C :: nat_ j :: G) s (nrec_succ C) ds) | exact IHs
      | exact (LTm_of_ty G n (nat_ j) dn) | exact IHn ].
  - (* t_prop *) intros G k W IHW; apply funtm_prop.
  - (* t_prf *) intros G k j p Hjk dp IHp.
    apply funtm_prf;
      [ exact (LTy_of_ty G (prf k p) k (t_prf G k j p Hjk dp)) | exact IHp ].
  - (* t_all *) intros G A p j k dA IHA dp IHp.
    apply (funtm_all G j A p);
      [ exact (LTy_of_ty G A k dA) | exact (LTm_of_ty (A :: G) p (prop j) dp)
      | exact IHA | exact IHp ].
  - (* t_all_intro *) intros; apply funtm_plam.
  - (* t_all_elim *) intros; apply funtm_papp.
  - (* t_false *) intros G k W IHW; apply funtm_false.
  - (* t_absurd *) intros; apply funtm_absurd.
Qed.

(* ================================================================== *)
(* THEOREM 9.2, THE LAYER-2 FUNDAMENTAL LEMMA.                         *)
(*                                                                    *)
(* The statement is proved in ONE environment and lifted to two by      *)
(* `funtm`.  That factoring is what keeps it tractable: functionality    *)
(* -- two readings in two related environments -- is already a theorem,  *)
(* so what is left is TOTALITY (a well-typed term has a value at every   *)
(* interpretation of its type) together with the semantic content of      *)
(* CONVERSION (convertible terms get equal values), and both of those     *)
(* speak of a single environment.  One statement covers both judgements:   *)
(* the typing motive is `IRel G t t A` and the conversion motive            *)
(* `IRel G t u A`.                                                        *)
(*                                                                    *)
(* Everything below is Type-valued: the Pi, Sigma and W cases have to      *)
(* produce a FUNCTION assigning a codomain family to every argument, so    *)
(* a Prop-valued (`inhabited`) formulation would need choice.             *)
(* ================================================================== *)

(* An environment that carries the interpretation of every context type.
   `EnvOf` records only the realisers; the variable case needs the families
   to be interpretations of the context types, because that is what makes the
   entry's family equal to the one the statement is handed. *)
Fixpoint EnvITy (G : ctx) (rho : Env) : Type :=
  match G, rho with
  | nil, nil => unit
  | A :: G0, en :: rho0 =>
      (EnvITy G0 rho0 *
       { F0 : kUFam (en_k en) (ers rho0 A) &
         (ITy rho0 A (en_k en) (ers rho0 A) F0 *
          kceq (kAt (en_F en)) (kAt F0))%type })%type
  | _, _ => Empty_set
  end.

Lemma EnvOf_of_EnvITy : forall G rho, EnvITy G rho -> EnvOf G rho.
Proof.
  induction G as [| A G0 IH]; intros [| en rho0] H; cbn in H |- *;
    try (exact I); try (solve [destruct H]).
  destruct H as [H0 [F0 [D0 P0]]]; split;
    [exact (IH rho0 H0) | exact (ceq_ty (en_F en) F0 P0)].
Qed.

Definition EnvITy_ext G rho (A : tm) k (FA : kUFam k (ers rho A))
  (DA : ITy rho A k (ers rho A) FA) u x (H : EnvITy G rho)
  : EnvITy (A :: G) (ext rho FA u x) :=
  (H, existT _ FA (DA, famAtSelf FA)).

(* the same, for a family that only happens to be EQUAL to an interpretation
   of the context type: what a conversion of that type gives *)
Definition EnvITy_ext_ceq G rho (A : tm) k S (FS : kUFam k S)
  (F0 : kUFam k (ers rho A)) (D0 : ITy rho A k (ers rho A) F0)
  (P : kceq (kAt FS) (kAt F0)) u x (H : EnvITy G rho)
  : EnvITy (A :: G) (ext rho FS u x) :=
  (H, existT _ F0 (D0, P)).

Lemma EnvRelOf_selfE G rho (H : EnvITy G rho) : EnvRelOf G rho rho.
Proof.
  pose proof (EnvOf_of_EnvITy G rho H) as HO.
  split; [exact HO | split; [exact HO | split; [apply EnvRel_refl |]]].
  exact (EnvOf_SubstRel G rho rho HO HO (EnvRel_refl rho)).
Qed.

(* The layer-1 side condition AT A FIXED LEVEL.  `LTy` loses the level to an
   existential, which is enough for a tyeq but not for the `eqty k` a Pi-,
   Sigma- or W-family carries as its own goodness field. *)
Definition LTyK (G : ctx) (A : tm) (k : nat) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> eqty k (ers rho A) (ers rho' A).

Lemma LTyK_of_ty G A k (d : ty G A (UU k)) : LTyK G A k.
Proof. intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_U G A k d _ _ HS). Qed.

(* Two interpretations of one well-typed type in one environment are EQUAL.
   This is functionality on the diagonal, where the layer-1 side condition is
   free (`uf_ty`), and it is what lets a case build its value at the family it
   constructs and then move it to the family it was handed. *)
Lemma ity_same_ceq G A (HA : FunTm G A) rho (H : EnvITy G rho)
  k (F F0 : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D0 : ITy rho A k (ers rho A) F0) :
  kceq (kAt F) (kAt F0).
Proof.
  exact (FunTy_of_FunTm G A HA rho rho
           (EnvRelOf_selfE G rho H) k _ F _ F0 D D0 (uf_ty F)).
Qed.

(* The typing derivation of a type is only ever used to call `funtm`, whose
   conclusion is a Prop -- so it may be supplied wrapped, which is what the
   variable case needs: `lookup` is Prop-valued and cannot be eliminated into
   Type. *)
Lemma FunTm_of_inh G A : inhabited { k : nat & ty G A (UU k) } -> FunTm G A.
Proof. intros [[k d]]; exact (funtm G A (UU k) d). Qed.

Lemma FunTm_of_ty G A k (d : ty G A (UU k)) : FunTm G A.
Proof. exact (funtm G A (UU k) d). Qed.

(* The statement, split into TOTALITY and RELATEDNESS.  The split is what
   makes c_trans work -- composing two conversions needs a value for the
   middle term, which only a totality statement provides -- and it makes the
   typing half cheap: `IRel G t t A` is functionality at one family in one
   environment, which is `funtm`. *)
Definition ITot (G : ctx) (t A : tm) : Type :=
  forall rho (H : EnvITy G rho) k (F : kUFam k (ers rho A))
    (DA : ITy rho A k (ers rho A) F),
    { x : kElAt F (ers rho t) & ITm rho t k (ers rho A) F (ers rho t) x }.

Definition IRel (G : ctx) (t u A : tm) : Prop :=
  forall rho (H : EnvITy G rho) k (F : kUFam k (ers rho A))
    (DA : ITy rho A k (ers rho A) F) x y,
    ITm rho t k (ers rho A) F (ers rho t) x ->
    ITm rho u k (ers rho A) F (ers rho u) y ->
    kEqAt F (ers rho t) x F (ers rho u) y.

Definition ISem (G : ctx) (t u A : tm) : Type :=
  (ITot G t A * ITot G u A * IRel G t u A)%type.

(* Relatedness on the diagonal is functionality. *)
Lemma IRel_self G t A (d : ty G t A) : IRel G t t A.
Proof.
  intros rho Hrho k F DA x y Dx Dy.
  refine (kRel_at (funtm G t A d rho rho (EnvRelOf_selfE G rho Hrho) k _ F _ x Dx
                     _ F _ y Dy (famAtSelf F) _)).
  exact (LTm_of_ty G t A d rho rho (EnvRelOf_selfE G rho Hrho)).
Qed.

(* Moving a value to another interpretation of the same type. *)
Lemma itot_move G (t A : tm) (HA : FunTm G A)
  rho (Hrho : EnvITy G rho) k (F F0 : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D0 : ITy rho A k (ers rho A) F0)
  x (Dx : ITm rho t k (ers rho A) F0 (ers rho t) x) :
  { y : kElAt F (ers rho t) & ITm rho t k (ers rho A) F (ers rho t) y }.
Proof.
  pose proof (ity_same_ceq G A HA rho Hrho k F0 F D0 D) as P.
  exists (kto (kAt F0) (kAt F) (famAtWf F0) (famAtWf F) P (ers rho t) x).
  exact (i_conv rho t k (ers rho A) F0 (ers rho A) F (ers rho t) x P Dx).
Qed.

(* ---- the constants.  Each is its canonical family's code, read as an
     element of the universe, moved to whatever interpretation of that
     universe the statement was handed. ---- *)

(* A universe.  `univ k j` is legal exactly when j < k, i.e. k = d + S j, and
   its value is the d-fold lift of the universe that level S j adds.  The
   universe it INHABITS is the next one up, `UU k`, whose own value is
   univFam k -- that is the d = 0 instance of the same clause. *)
Lemma itot_univ G (W : Rules.wfc G) k j (H : j < k) : ITot G (univ k j) (UU k).
Proof.
  intros rho Hrho k0 F DA.
  pose proof (ity_lvl_dec rho (UU k) k0 (ers rho (UU k)) F DA) as El;
    cbn [LvlDec] in El; subst k0.
  assert (E : (k - S j) + S j = k) by lia.
  refine (itot_move G (univ k j) (UU k)
            (FunTm_of_ty G (UU k) (S k)
               (t_univ G (S k) k (Nat.lt_succ_diag_r k) W))
            rho Hrho (S k) F (univFam k) DA
            (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl) _ _).
  exact (i_ty rho (univ k j) k (euniv j) (upF (k - S j) k E (univFam j))
           (ity_univ rho k (k - S j) j E (ers rho (univ k j)) eq_refl)).
Qed.

Lemma itot_nat G (W : Rules.wfc G) j : ITot G (nat_ j) (UU j).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (UU j) k (ers rho (UU j)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G (nat_ j) (UU j)
            (FunTm_of_ty G (UU j) (S j)
               (t_univ G (S j) j (Nat.lt_succ_diag_r j) W))
            rho Hrho (S j) F (univFam j) DA
            (ity_univ rho (S j) 0 j eq_refl (ers rho (UU j)) eq_refl) _ _).
  exact (i_ty rho (nat_ j) j enat (natFam j)
           (ity_nat rho j (ers rho (nat_ j)) eq_refl)).
Qed.

Lemma itot_prop G (W : Rules.wfc G) j : ITot G (prop j) (UU j).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (UU j) k (ers rho (UU j)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G (prop j) (UU j)
            (FunTm_of_ty G (UU j) (S j)
               (t_univ G (S j) j (Nat.lt_succ_diag_r j) W))
            rho Hrho (S j) F (univFam j) DA
            (ity_univ rho (S j) 0 j eq_refl (ers rho (UU j)) eq_refl) _ _).
  exact (i_ty rho (prop j) j eprop (propFam j)
           (ity_prop rho j (ers rho (prop j)) eq_refl)).
Qed.

Lemma itot_zero G (W : Rules.wfc G) j : ITot G (zero j) (nat_ j).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (nat_ j) k (ers rho (nat_ j)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G (zero j) (nat_ j) (FunTm_of_ty G (nat_ j) j (t_nat G j W))
            rho Hrho j F (natFam j) DA
            (ity_nat rho j (ers rho (nat_ j)) eq_refl) _ (i_zero rho j)).
Qed.

Lemma itot_succ G (W : Rules.wfc G) j (n : tm) (IHn : ITot G n (nat_ j)) :
  ITot G (succ n) (nat_ j).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (nat_ j) k (ers rho (nat_ j)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  destruct (IHn rho Hrho j (natFam j) (ity_nat rho j (ers rho (nat_ j)) eq_refl))
    as [xn Dn].
  refine (itot_move G (succ n) (nat_ j) (FunTm_of_ty G (nat_ j) j (t_nat G j W))
            rho Hrho j F (natFam j) DA
            (ity_nat rho j (ers rho (nat_ j)) eq_refl) _
            (i_succ rho j n (ers rho n) xn Dn)).
Qed.

Lemma itot_false G (W : Rules.wfc G) j : ITot G (false_ j) (prop j).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (prop j) k (ers rho (prop j)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G (false_ j) (prop j)
            (FunTm_of_ty G (prop j) j (t_prop G j W))
            rho Hrho j F (propFam j) DA
            (ity_prop rho j (ers rho (prop j)) eq_refl) _ _).
  refine (i_false rho j (ers rho (false_ j)) _ eq_refl).
  apply Rel_prop_intro;
    [ exact good_ty_prop | apply eval_whnf, whnf_prop
    | apply PR_false; apply ev_false ].
Qed.

(* ---- variables.  The value is the environment entry's own, and the entry's
     family is an interpretation of the context type (which is what EnvITy
     records), so it is equal to whichever interpretation the statement was
     handed.  The recursion is on the INDEX: `lookup` is Prop-valued and
     cannot be eliminated into Type, so the context type comes out as an
     OUTPUT together with a lookup proof, and lookup_fun identifies it with
     the one the rule names. ---- *)

Lemma ers_shift_en (en : Entry) rho t : ers (en :: rho) (t ⟨↑⟩) = ers rho t.
Proof. destruct en; apply ers_shift. Qed.

Lemma env_var : forall i G rho, EnvITy G rho -> i < length G ->
  { A : tm & { k0 : nat & { F0 : kUFam k0 (ers rho A) &
    (lookup i G A * ITy rho A k0 (ers rho A) F0 *
     { x : kElAt F0 (ers rho (var_tm i)) &
       ITm rho (var_tm i) k0 (ers rho A) F0 (ers rho (var_tm i)) x })%type } } }.
Proof.
  induction i as [| i IH]; intros [| B G0] [| en rho0] H Hlt; cbn in H;
    try (solve [destruct H]);
    try (solve [destruct (Nat.nlt_0_r _ Hlt)]).
  - destruct H as [H0 D].
    destruct en as [k0 S0 F0 u0 x0]; cbn [en_k en_S en_F en_u en_x] in D |- *.
    destruct D as [FB0 [DB0 Pc]].
    exists (B ⟨↑⟩), k0.
    rewrite (ers_shift_en (Build_Entry k0 S0 F0 u0 x0) rho0 B).
    exists FB0; split; [split |].
    + apply lookup_O.
    + exact (weaken1_ITy rho0 B k0 (ers rho0 B) FB0
               (Build_Entry k0 S0 F0 u0 x0) DB0).
    + exists (kto (kAt F0) (kAt FB0) (famAtWf F0) (famAtWf FB0) Pc u0 x0).
      exact (i_conv (ext rho0 F0 u0 x0) (var_tm 0) k0 S0 F0 (ers rho0 B) FB0
               u0 x0 Pc (i_var0 rho0 k0 S0 F0 u0 x0)).
  - destruct H as [H0 D]; cbn in Hlt.
    destruct (IH G0 rho0 H0 ltac:(lia)) as [A [k0 [F0 [[Hl DA] [x Dx]]]]].
    exists (A ⟨↑⟩), k0.
    rewrite (ers_shift_en en rho0 A).
    exists F0; split; [split |].
    + apply lookup_S; exact Hl.
    + exact (weaken1_ITy rho0 A k0 (ers rho0 A) F0 en DA).
    + exists x;
        exact (i_varS rho0 en i k0 (ers rho0 A) F0 (ers rho0 (var_tm i)) x Dx).
Qed.

Lemma itot_var G i A (W : Rules.wfc G) (Hl : lookup i G A) :
  ITot G (var_tm i) A.
Proof.
  intros rho Hrho k F DA.
  destruct (env_var i G rho Hrho (lookup_len i G A Hl))
    as [A' [k0 [F0 [[Hl' DA'] [x Dx]]]]].
  pose proof (lookup_fun i G A A' Hl Hl') as E; subst A'.
  (* the two readings of A agree on the level *)
  pose proof (ity_lvl rho rho eq_refl A k0 (ers rho A) F0 k (ers rho A) F DA' DA)
    as Ek; subst k0.
  exact (itot_move G (var_tm i) A (FunTm_of_inh G A (lookup_ty i G A Hl W))
           rho Hrho k F F0 DA DA' x Dx).
Qed.

(* At a type, totality gives an interpretation of it: a term of a universe IS
   a family (itm_univ_ty). *)
Definition ITyT (G : ctx) (A : tm) (k : nat) : Type :=
  forall rho (H : EnvITy G rho),
    { F : kUFam k (ers rho A) & ITy rho A k (ers rho A) F }.

Lemma ityT_of_ITot G A k (H : ITot G A (UU k)) : ITyT G A k.
Proof.
  intros rho Hrho.
  destruct (H rho Hrho (S k) (univFam k)
              (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl)) as [x Dx].
  destruct (itm_univ_ty rho A k (euniv k) (univFam k) (ers rho A) x
              (famAtSelf (univFam k)) Dx) as [F0 [D0 _]].
  exists F0; exact D0.
Qed.

(* and a CONVERSION of types gives the equality of any two of their
   interpretations. *)
Lemma ceq_of_IRel G A B k
  (HA : ITot G A (UU k)) (HB : ITot G B (UU k)) (HR : IRel G A B (UU k))
  (fA : FunTm G A) (fB : FunTm G B)
  rho (Hrho : EnvITy G rho)
  (FA : kUFam k (ers rho A)) (DA : ITy rho A k (ers rho A) FA)
  (FB : kUFam k (ers rho B)) (DB : ITy rho B k (ers rho B) FB) :
  kceq (kAt FA) (kAt FB).
Proof.
  destruct (HA rho Hrho (S k) (univFam k)
              (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl)) as [x Dx].
  destruct (HB rho Hrho (S k) (univFam k)
              (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl)) as [y Dy].
  pose proof (HR rho Hrho (S k) (univFam k)
                (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl)
                x y Dx Dy) as Heq.
  destruct (itm_univ_ty rho A k (euniv k) (univFam k) (ers rho A) x
              (famAtSelf (univFam k)) Dx) as [F1 [D1 H1]].
  destruct (itm_univ_ty rho B k (euniv k) (univFam k) (ers rho B) y
              (famAtSelf (univFam k)) Dy) as [F2 [D2 H2]].
  assert (Hfe : kEqAt (univFam k) (ers rho A) (famEl F1)
                  (univFam k) (ers rho B) (famEl F2)).
  { eapply kEqAt_trans;
      [ exact (famAtSelf (univFam k)) | apply kEqAt_sym; exact H1 |].
    eapply kEqAt_trans;
      [ exact (famAtSelf (univFam k)) | apply kEqAt_sym; apply kto_coh |].
    eapply kEqAt_trans;
      [ exact (famAtSelf (univFam k)) | exact Heq |].
    eapply kEqAt_trans;
      [ exact (famAtSelf (univFam k)) | apply kto_coh | exact H2 ]. }
  pose proof (uEq_at (famEl F1) (famEl F2) Hfe) as Hi.
  rewrite !elFam_famEl in Hi.
  eapply ktrU;
    [ exact (famAtWf FA) | exact (famAtWf F1) | exact (famAtWf FB)
    | exact (ity_same_ceq G A fA rho Hrho k FA F1 DA D1) |].
  eapply ktrU;
    [ exact (famAtWf F1) | exact (famAtWf F2) | exact (famAtWf FB)
    | exact Hi | exact (ity_same_ceq G B fB rho Hrho k F2 FB D2 DB) ].
Qed.

(* ---- conversion of the type ---- *)
Lemma itot_conv G t A B k
  (dA : ty G A (UU k)) (dB : ty G B (UU k))
  (IHt : ITot G t A) (IHA : ITot G A (UU k)) (IHB : ITot G B (UU k))
  (IHc : IRel G A B (UU k)) : ITot G t B.
Proof.
  intros rho Hrho k' F DB'.
  destruct (ityT_of_ITot G B k IHB rho Hrho) as [FB DB].
  pose proof (ity_lvl rho rho eq_refl B k (ers rho B) FB k' (ers rho B) F DB DB')
    as Ek; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DA].
  destruct (IHt rho Hrho k FA DA) as [x Dx].
  pose proof (ceq_of_IRel G A B k IHA IHB IHc
                (FunTm_of_ty G A k dA) (FunTm_of_ty G B k dB) rho Hrho FA DA F DB')
    as P.
  exists (kto (kAt FA) (kAt F) (famAtWf FA) (famAtWf F) P (ers rho t) x).
  exact (i_conv rho t k (ers rho A) FA (ers rho B) F (ers rho t) x P Dx).
Qed.

(* ---- Prf ---- *)
Lemma itot_prf G kk j p (Hjk : j <= kk) (W : Rules.wfc G) (dp : ty G p (prop j))
  (IHp : ITot G p (prop j)) :
  ITot G (prf kk p) (UU kk).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (UU kk) k (ers rho (UU kk)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  destruct (IHp rho Hrho j (propFam j) (ity_prop rho _ _ eq_refl)) as [xp Dp].
  refine (itot_move G (prf kk p) (UU kk)
            (FunTm_of_ty G (UU kk) (S kk)
               (t_univ G (S kk) kk (Nat.lt_succ_diag_r kk) W))
            rho Hrho (S kk) F (univFam kk) DA
            (ity_univ rho (S kk) 0 kk eq_refl (ers rho (UU kk)) eq_refl) _ _).
  exact (i_ty rho (prf kk p) kk (eprf (ers rho p)) (prfF kk xp)
           (ity_prf rho kk j p (ers rho p) xp Dp)).
Qed.

(* ---- the type lift ---- *)
Lemma itot_up G A k (W : Rules.wfc G) (dA : ty G A (UU k))
  (IHA : ITot G A (UU k)) : ITot G (up k A) (UU (S k)).
Proof.
  intros rho Hrho k' F DA'.
  pose proof (ity_lvl_dec rho (UU (S k)) k' (ers rho (UU (S k))) F DA') as El;
    cbn [LvlDec] in El; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  refine (itot_move G (up k A) (UU (S k))
            (FunTm_of_ty G (UU (S k)) (S (S k))
               (t_univ G (S (S k)) (S k) (Nat.lt_succ_diag_r (S k)) W))
            rho Hrho (S (S k)) F (univFam (S k)) DA'
            (ity_univ rho (S (S k)) 0 (S k) eq_refl (ers rho (UU (S k))) eq_refl)
            _ _).
  exact (i_ty rho (up k A) (S k) (ers rho A) (famLiftK FA)
           (ity_up rho A k (ers rho A) FA DFA)).
Qed.

(* ---- the term lift ---- *)
Lemma itot_uptm G A t k (dA : ty G A (UU k)) (dt : ty G t A)
  (IHA : ITot G A (UU k)) (IHt : ITot G t A) :
  ITot G (uptm A t) (up k A).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (up k A) k' (ers rho (up k A)) F DU)
    as El; cbn [LvlDec] in El; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  destruct (IHt rho Hrho k FA DFA) as [x Dx].
  refine (itot_move G (uptm A t) (up k A)
            (FunTm_of_ty G (up k A) (S k) (t_up G k A dA)) rho Hrho
            (S k) F (famLiftK FA) DU (ity_up rho A k (ers rho A) FA DFA) _ _).
  exact (i_up_tm rho A t k (ers rho A) FA (ers rho t) x DFA Dx).
Qed.

(* ---- absurd: the proof of falsity's value carries the truth of False. ---- *)
Lemma good_false : Good eprop efalse.
Proof.
  apply Rel_prop_intro;
    [ exact good_ty_prop | apply eval_whnf, whnf_prop
    | apply PR_false; apply ev_false ].
Qed.

Lemma itot_absurd G T j e (IHe : ITot G e (prf j (false_ j))) :
  ITot G (absurd T e) T.
Proof.
  intros rho Hrho k' F DT.
  pose proof (i_false rho j (ers rho (false_ j)) good_false eq_refl) as Df.
  pose proof (ity_prf rho j j (false_ j) efalse
                (propElem efalse False good_false) Df) as DP.
  destruct (IHe rho Hrho j (prfF j (propElem efalse False good_false)) DP) as [x _].
  destruct (prfVal x).
Qed.

(* ---- the impredicative forall.  The value is the proposition
     "for every element of the domain, the body holds", which is exactly what
     i_all records; the builder is shared with the forall-introduction, whose
     truth-component has to be that very proposition, not one merely
     equivalent to it. ---- *)
Lemma build_all G A p j k (dA : ty G A (UU k)) (dp : ty (A :: G) p (prop j))
  (IHA : ITot G A (UU k)) (IHp : ITot (A :: G) p (prop j))
  rho (Hrho : EnvITy G rho) :
  { FA : kUFam k (ers rho A) &
  { xp : forall u (y : kElAt FA u), kElAt (propFam j) (ers (ext rho FA u y) p) &
    (ITy rho A k (ers rho A) FA *
     (forall u y, ITm (ext rho FA u y) p j eprop (propFam j)
                    (ers (ext rho FA u y) p) (xp u y)))%type } }.
Proof.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  exists FA.
  refine (existT _ (fun u y =>
            projT1 (IHp (ext rho FA u y) (EnvITy_ext G rho A k FA DFA u y Hrho)
                      j (propFam j)
                      (ity_prop (ext rho FA u y) j
                         (ers (ext rho FA u y) (prop j)) eq_refl)))
            _).
  split; [exact DFA |].
  intros u y.
  exact (projT2 (IHp (ext rho FA u y) (EnvITy_ext G rho A k FA DFA u y Hrho)
                   j (propFam j)
                   (ity_prop (ext rho FA u y) j
                      (ers (ext rho FA u y) (prop j)) eq_refl))).
Qed.

Lemma itot_all G A p j k (W : Rules.wfc G) (dA : ty G A (UU k))
  (dp : ty (A :: G) p (prop j))
  (IHA : ITot G A (UU k)) (IHp : ITot (A :: G) p (prop j)) :
  ITot G (all j A p) (prop j).
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho (prop j) k' (ers rho (prop j)) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p j k dA dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all j A p)))
    by exact (LTm_of_ty G (all j A p) (prop j) (t_all G A p j k dA dp) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  refine (itot_move G (all j A p) (prop j)
            (FunTm_of_ty G (prop j) j (t_prop G j W)) rho Hrho
            j F (propFam j) DP (ity_prop rho _ _ eq_refl) _ _).
  exact (i_all rho j A p k (ers rho A) FA (fun u y => ers (ext rho FA u y) p) xp
           (ers rho (all j A p)) g eq_refl DFA Dp).
Qed.

(* ---- forall-introduction.  plam has no clause of its own: i_proof gives a
     value to ANY subject at a Prf type, provided the proposition is TRUE, and
     the truth is the body's value at every argument. ---- *)
Lemma itot_plam G A p t j k (dA : ty G A (UU k))
  (dp : ty (A :: G) p (prop j)) (dt : ty (A :: G) t (prf j p))
  (IHA : ITot G A (UU k)) (IHp : ITot (A :: G) p (prop j))
  (IHt : ITot (A :: G) t (prf j p)) :
  ITot G (plam A t) (prf j (all j A p)).
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho (prf j (all j A p)) k'
                (ers rho (prf j (all j A p))) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p j k dA dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all j A p)))
    by exact (LTm_of_ty G (all j A p) (prop j) (t_all G A p j k dA dp) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (i_all rho j A p k (ers rho A) FA (fun u y => ers (ext rho FA u y) p)
                xp (ers rho (all j A p)) g eq_refl DFA Dp) as DAll.
  (* the proposition is true: the body has a value at every argument *)
  assert (h : forall u (y : kElAt FA u), propVal (xp u y)).
  { intros u y.
    refine (prfVal (projT1 (IHt (ext rho FA u y)
                              (EnvITy_ext G rho A k FA DFA u y Hrho)
                              j (prfF j (xp u y)) _))).
    exact (ity_prf (ext rho FA u y) j j p (ers (ext rho FA u y) p) (xp u y)
             (Dp u y)). }
  assert (gp : Good (eprf (ers rho (all j A p))) (ers rho (plam A t)))
    by exact (LTm_of_ty G (plam A t) (prf j (all j A p))
                (t_all_intro G A p t j k dA dp dt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  refine (itot_move G (plam A t) (prf j (all j A p))
            (FunTm_of_ty G (prf j (all j A p)) j
               (t_prf G j j (all j A p) (le_n j) (t_all G A p j k dA dp)))
            rho Hrho j F
            (prfF j (propElem (ers rho (all j A p))
                       (forall u (y : kElAt FA u), propVal (xp u y)) g))
            DP (ity_prf rho j j (all j A p) (ers rho (all j A p)) _ DAll) _ _).
  exact (i_proof rho (plam A t) (all j A p) j j (ers rho (all j A p))
           (propElem (ers rho (all j A p))
              (forall u (y : kElAt FA u), propVal (xp u y)) g)
           h (ers rho (plam A t)) gp eq_refl DAll).
Qed.

(* ---- Pi, Sigma and W.  The three share all their data -- domain family,
     codomain family at every LIFTED argument, and the codomain's coherence --
     so it is built once; only the realiser's head differs.  The two
     components are read at their own levels and the gaps are `k - i` and
     `k - j`, which is what the typing rule's `i <= k` and `j <= k` give. ---- *)

Lemma build_fam_data G A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  rho (Hrho : EnvITy G rho) :
  { FA : kUFam i (ers rho A) &
  { FB : forall u (x : kElAt (upF dA k EA FA) u),
           kUFam j (ers (ext rho FA u (dnEl dA k EA FA u x)) B) &
    (ITy rho A i (ers rho A) FA *
     (forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j
                    (ers (ext rho FA u (dnEl dA k EA FA u x)) B) (FB u x)) *
     (forall u x u' x',
        kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
        kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x')))))%type } }.
Proof.
  destruct (ityT_of_ITot G A i IHA rho Hrho) as [FA DFA].
  exists FA.
  pose (FB := fun u (x : kElAt (upF dA k EA FA) u) =>
                projT1 (ityT_of_ITot (A :: G) B j IHB
                          (ext rho FA u (dnEl dA k EA FA u x))
                          (EnvITy_ext G rho A i FA DFA u
                             (dnEl dA k EA FA u x) Hrho))).
  assert (DB : forall u x, ITy (ext rho FA u (dnEl dA k EA FA u x)) B j
                 (ers (ext rho FA u (dnEl dA k EA FA u x)) B) (FB u x))
    by (intros u x;
        exact (projT2 (ityT_of_ITot (A :: G) B j IHB
                         (ext rho FA u (dnEl dA k EA FA u x))
                         (EnvITy_ext G rho A i FA DFA u
                            (dnEl dA k EA FA u x) Hrho)))).
  exists FB; split; [split; [exact DFA | exact DB] |].
  intros u x u' x' Hxx.
  apply upF_ceq.
  assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA u' (dnEl dA k EA FA u' x'))
    by exact (dnEl_eq dA k EA FA u x FA u' x' (famAtSelf FA) Hxx).
  assert (HEx : EnvRelOf (A :: G) (ext rho FA u (dnEl dA k EA FA u x))
                  (ext rho FA u' (dnEl dA k EA FA u' x')))
    by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                (EnvRelOf_selfE G rho Hrho) (conj (famAtSelf FA) Hd)).
  exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j _
           (FB u x) _ (FB u' x') (DB u x) (DB u' x')
           (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
Qed.

Lemma build_pi G A B k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITyT G (pi k A B) k.
Proof.
  intros rho Hrho.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  refine (existT _
            (piFam k (ers rho A) (elam (subst_etm (up_etm (rsub rho)) (er B)))
               (upF (k - i) k EA FA)
               (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B)
               (fun u x => upF (k - j) k EB (FB u x))
               (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
               (LTyK_of_ty G (pi k A B) k
                  (t_pi G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho))) _).
  exact (ity_pi rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA
           (elam (subst_etm (up_etm (rsub rho)) (er B)))
           (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B) FB
           (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
           (LTyK_of_ty G (pi k A B) k (t_pi G k i j A B Hik Hjk dAt dBt) rho rho
              (EnvRelOf_selfE G rho Hrho))
           eq_refl DFA DB).
Qed.

Lemma build_sig G A B k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITyT G (sig_ k A B) k.
Proof.
  intros rho Hrho.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  refine (existT _
            (sigFam k (ers rho A) (elam (subst_etm (up_etm (rsub rho)) (er B)))
               (upF (k - i) k EA FA)
               (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B)
               (fun u x => upF (k - j) k EB (FB u x))
               (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
               (LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho))) _).
  exact (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA
           (elam (subst_etm (up_etm (rsub rho)) (er B)))
           (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B) FB
           (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
           (LTyK_of_ty G (sig_ k A B) k (t_sig G k i j A B Hik Hjk dAt dBt)
              rho rho (EnvRelOf_selfE G rho Hrho))
           eq_refl DFA DB).
Qed.

Lemma build_w G A B k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITyT G (wt k A B) k.
Proof.
  intros rho Hrho.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  refine (existT _
            (wFam k (ers rho A) (elam (subst_etm (up_etm (rsub rho)) (er B)))
               (upF (k - i) k EA FA)
               (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B)
               (fun u x => upF (k - j) k EB (FB u x))
               (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
               (LTyK_of_ty G (wt k A B) k
                  (t_w G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho))) _).
  exact (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA
           (elam (subst_etm (up_etm (rsub rho)) (er B)))
           (fun u x => ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B) FB
           (fun u x => reds_lam_app (er B) (rsub rho) u) cohB
           (LTyK_of_ty G (wt k A B) k (t_w G k i j A B Hik Hjk dAt dBt)
              rho rho (EnvRelOf_selfE G rho Hrho))
           eq_refl DFA DB).
Qed.

Lemma itot_pi G A B k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITot G (pi k A B) (UU k).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (UU k) k' (ers rho (UU k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_pi G A B k i j Hik Hjk dAt dBt IHA IHB rho Hrho) as [FP DP].
  refine (itot_move G (pi k A B) (UU k)
            (FunTm_of_ty G (UU k) (S k)
               (t_univ G (S k) k (Nat.lt_succ_diag_r k) W))
            rho Hrho (S k) F (univFam k) DU
            (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl) _ _).
  exact (i_ty rho (pi k A B) k (ers rho (pi k A B)) FP DP).
Qed.

Lemma itot_sig G A B k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITot G (sig_ k A B) (UU k).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (UU k) k' (ers rho (UU k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_sig G A B k i j Hik Hjk dAt dBt IHA IHB rho Hrho) as [FP DP].
  refine (itot_move G (sig_ k A B) (UU k)
            (FunTm_of_ty G (UU k) (S k)
               (t_univ G (S k) k (Nat.lt_succ_diag_r k) W))
            rho Hrho (S k) F (univFam k) DU
            (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl) _ _).
  exact (i_ty rho (sig_ k A B) k (ers rho (sig_ k A B)) FP DP).
Qed.

Lemma itot_wt G A B k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ITot G (wt k A B) (UU k).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (UU k) k' (ers rho (UU k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_w G A B k i j Hik Hjk dAt dBt IHA IHB rho Hrho) as [FP DP].
  refine (itot_move G (wt k A B) (UU k)
            (FunTm_of_ty G (UU k) (S k)
               (t_univ G (S k) k (Nat.lt_succ_diag_r k) W))
            rho Hrho (S k) F (univFam k) DU
            (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl) _ _).
  exact (i_ty rho (wt k A B) k (ers rho (wt k A B)) FP DP).
Qed.

(* ================================================================== *)
(* The substitution lemma's side condition, discharged.                *)
(*                                                                    *)
(* SubUniv asks that every image of the substitution which is a term of *)
(* a universe be a FAMILY -- at the family its value names, `elFam v`.   *)
(* For an image that is a variable this is ity_of; for the substituted    *)
(* term itself ity_of applies only when it is not a type former, and       *)
(* itm_univ_ty gives a family that is merely EQUAL to the one asked for.    *)
(* ity_conv (Interp/Def.v) closes that gap, and with it the condition       *)
(* holds for every term, so the substitution lemma is usable where the      *)
(* fundamental lemma needs it: at t_app, t_pair, t_snd, t_natrec, t_wrec    *)
(* and t_all_elim, whose conclusion types are substitution instances.      *)
(* ================================================================== *)

Lemma subUniv_all rho a : SubUniv rho a.
Proof.
  intros delta i k' w' v' D.
  destruct (itm_univ_ty (delta ++ rho) (upn (length delta) (a..) i) k' (euniv k')
              (univFam k') w' v' (famAtSelf (univFam k')) D) as [F0 [D0 HE]].
  assert (HE2 : kEqAt (univFam k') w' v' (univFam k') w' (famEl F0)).
  { eapply kEqAt_trans;
      [ exact (famAtSelf (univFam k'))
      | apply kEqAt_sym; apply kto_self | exact HE ]. }
  pose proof (uEq_at v' (famEl F0) HE2) as Hi.
  rewrite elFam_famEl in Hi.
  refine (ity_conv _ _ _ _ F0 (elFam v') _ D0).
  apply knsymU; exact Hi.
Qed.

(* The forms the fundamental lemma uses. *)
Corollary isubst_ITm (rho : Env) (b : tm) k' Sy' (FA : kUFam k' Sy') (ub : etm)
  (xb : kElAt FA ub) (Hub : ub = ers rho b)
  (Db : ITm rho b k' Sy' FA ub xb)
  t k Sy (F : kUFam k Sy) w (x : kElAt F w) :
  ITm (Build_Entry k' Sy' FA ub xb :: rho) t k Sy F w x ->
  ITm rho (t [b..]) k Sy F w x.
Proof.
  exact (subst1_ITm rho b k' Sy' FA ub xb Hub Db (subUniv_all rho b)
           t k Sy F w x).
Qed.

Corollary isubst_ITy (rho : Env) (b : tm) k' Sy' (FA : kUFam k' Sy') (ub : etm)
  (xb : kElAt FA ub) (Hub : ub = ers rho b)
  (Db : ITm rho b k' Sy' FA ub xb)
  A k w (F : kUFam k w) :
  ITy (Build_Entry k' Sy' FA ub xb :: rho) A k w F ->
  ITy rho (A [b..]) k w F.
Proof.
  exact (subst1_ITy rho b k' Sy' FA ub xb Hub Db (subUniv_all rho b) A k w F).
Qed.

(* Casting a family, its derivation and its values along an equality of
   realisers.  Erasure does not commute with substitution definitionally, so
   the codomain instance of a Pi-family and the interpretation of `B [u..]`
   have realisers that are equal (ers_sub1) but not convertible. *)
Lemma ITy_cast rho A k w w' (E : w = w') (F : kUFam k w) :
  ITy rho A k w F -> ITy rho A k w' (famCast E F).
Proof. destruct E; exact (fun D => D). Qed.

Lemma ITm_cast rho t k w w' (E : w = w') (F : kUFam k w) v (x : kElAt F v) :
  ITm rho t k w F v x -> ITm rho t k w' (famCast E F) v (elCast E F v x).
Proof. destruct E; exact (fun D => D). Qed.

(* ---- the first projection.  Its level is the domain's, and the value the
     clause builds is the projection brought back down through the gap. ---- *)
Lemma itot_fst G A B p k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j)) (dp : ty G p (sig_ k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ k A B)) : ITot G (fst A B p) A.
Proof.
  intros rho Hrho k' F DA'.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose proof (ity_lvl rho rho eq_refl A i (ers rho A) FA k' (ers rho A) F DFA DA')
    as Ek; subst k'.
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u (x : kElAt (upF (k - i) k EA FA) u) =>
                ers (ext rho FA u (dnEl (k - i) k EA FA u x)) B).
  pose (redB := fun u (x : kElAt (upF (k - i) k EA FA) u) =>
                  reds_lam_app (er B) (rsub rho) u).
  pose (gSig := LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u x => upF (k - j) k EB (FB u x)) redB cohB gSig) Dsig)
    as [xp Dp].
  refine (itot_move G (fst A B p) A (FunTm_of_ty G A i dAt) rho Hrho i F FA DA'
            DFA _ _).
  exact (i_fst rho A B p k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
           redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp).
Qed.

(* ---- application.  The conclusion type is a substitution instance, which is
     what ty_subst1 (Typing/Subst.v) and isubst_ITy are for: the first makes
     `B [u..]` a well typed type, so functionality applies to it, and the
     second turns the codomain's interpretation in the extended environment
     into one of `B [u..]` in rho.

     The heterogeneous levels add one step.  The clause indexes the codomain
     by the LIFTED argument and reads it in the environment carrying the
     argument's ROUND TRIP, while isubst_ITy wants the environment carrying
     the argument's own value -- so the codomain is read twice, and the two
     readings are equal because the two environments differ only in that
     element and `dnEl_upEl` says the two elements are equal. ---- *)
Lemma itot_app G A B f u k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (df : ty G f (pi k A B)) (du : ty G u A)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHf : ITot G f (pi k A B)) (IHu : ITot G u A) :
  ITot G (app A B f u) (B [u..]).
Proof.
  intros rho Hrho k' F DBu.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gPi := LTyK_of_ty G (pi k A B) k
                 (t_pi G k i j A B Hik Hjk dAt dBt) rho rho
                 (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_pi rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gPi eq_refl DFA DB) as Dpi.
  destruct (IHf rho Hrho k
              (piFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gPi) Dpi)
    as [xf Df].
  destruct (IHu rho Hrho i FA DFA) as [xu Du].
  (* the codomain, read in the environment that carries the argument itself *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  pose proof (isubst_ITy rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                B j (ers (ext rho FA (ers rho u) xu) B) FBu DBu0) as DBsub.
  pose proof (ITy_cast rho (B [u..]) j _ _ E FBu DBsub) as DBc.
  (* and the two readings of the codomain agree *)
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho u) xu)
                  (ext rho FA (ers rho u)
                     (dnEl (k - i) k EA FA (ers rho u)
                        (upEl (k - i) k EA FA (ers rho u) xu)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho u) xu (ers rho u) _
             (EnvRelOf_selfE G rho Hrho)).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho u) (upEl (k - i) k EA FA (ers rho u) xu))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho u) (upEl (k - i) k EA FA (ers rho u) xu))
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (UU j) u dBt du) as [dsub].
    exact (FunTm_of_ty G (B [u..]) j dsub). }
  pose proof (ity_lvl rho rho eq_refl (B [u..]) j (ers rho (B [u..]))
                (famCast E FBu) k' (ers rho (B [u..])) F DBc DBu) as Ek; subst k'.
  refine (itot_move G (app A B f u) (B [u..]) Hfun rho Hrho j F
            (famCast E FBu) DBu DBc _ _).
  refine (ITm_cast rho (app A B f u) j _ _ E FBu _ _ _).
  refine (i_conv rho (app A B f u) j _
            (FB (ers rho u) (upEl (k - i) k EA FA (ers rho u) xu)) _ FBu _ _
            (knsymU _ _ P) _).
  exact (i_app rho A B f u k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
           redB cohB gPi (ers rho f) xf (ers rho u) xu eq_refl DFA DB Df Du).
Qed.

(* The other direction of the cast: a value living in a cast family is a value
   in the original one. *)
Lemma ITm_uncast rho t k w w' (E : w = w') (F : kUFam k w) v
  (y : kElAt (famCast E F) v) :
  ITm rho t k w' (famCast E F) v y -> { x : kElAt F v & ITm rho t k w F v x }.
Proof. destruct E; intros D; exists y; exact D. Qed.

(* ---- the pair.  Its type is the annotation, so only the SECOND component's
     type is a substitution instance: its interpretation is the codomain
     instance at the first component's value -- and, as at the application,
     the clause indexes that instance by the LIFTED value, so the codomain is
     read twice and the two readings are equal. ---- *)
Lemma itot_pair G A B t u k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ITot G (pair k A B t u) (sig_ k A B).
Proof.
  intros rho Hrho k' F Dsg.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHt rho Hrho i FA DFA) as [xt Dt].
  (* the second component, at the codomain read in the environment that
     carries the first component's own value *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i FA DFA (ers rho t) xt Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  destruct (IHu rho Hrho j (famCast E FBu)
              (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)) as [xu' Du'].
  destruct (ITm_uncast rho u j _ _ E FBu _ _ Du') as [xu Du].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                  (ext rho FA (ers rho t)
                     (dnEl (k - i) k EA FA (ers rho t)
                        (upEl (k - i) k EA FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho t) xt (ers rho t) _
             (EnvRelOf_selfE G rho Hrho)).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho t) (upEl (k - i) k EA FA (ers rho t) xt))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho t) (upEl (k - i) k EA FA (ers rho t) xt))
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  pose proof (i_conv rho u j _ FBu _
                (FB (ers rho t) (upEl (k - i) k EA FA (ers rho t) xt))
                (ers rho u) xu P Du) as Du2.
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair k A B t u) (sig_ k A B)
                (t_pair G k i j A B t u Hik Hjk dAt dBt dt du) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_lvl rho rho eq_refl (sig_ k A B) k (ers rho (sig_ k A B))
                (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                   (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig)
                k' (ers rho (sig_ k A B)) F Dsig Dsg) as Ek; subst k'.
  refine (itot_move G (pair k A B t u) (sig_ k A B)
            (FunTm_of_ty G (sig_ k A B) k
               (t_sig G k i j A B Hik Hjk dAt dBt)) rho Hrho k F
            (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig)
            Dsg Dsig _ _).
  exact (i_pair rho A B t u k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gSig (ers rho t) xt (ers rho u) _ g eq_refl
           DFA DB Dt Du2).
Qed.

(* ---- the second projection.  Its type is a substitution instance whose
     substituted term is the FIRST projection, so the codomain instance is
     taken at that projection's own value -- and here the two agree without
     any further step, because i_fst's value IS the lifted projection brought
     back down, which is exactly the element the codomain's environment
     carries. ---- *)
Lemma itot_snd G A B p k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j)) (dp : ty G p (sig_ k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ k A B)) : ITot G (snd A B p) (B [(fst A B p)..]).
Proof.
  intros rho Hrho k' F DBs.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig) Dsig)
    as [xp Dp].
  pose proof (i_fst rho A B p k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  pose (xf := sigFst k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig
                (ers rho p) xp).
  assert (E : ers (ext rho FA (efst (ers rho p))
                     (dnEl (k - i) k EA FA (efst (ers rho p)) xf)) B
              = ers rho (B [(fst A B p)..]))
    by exact (eq_sym (ers_sub1 rho B (fst A B p) FA _)).
  pose proof (isubst_ITy rho (fst A B p) i (ers rho A) FA (efst (ers rho p)) _
                eq_refl Dfst B j _ _ (DB (efst (ers rho p)) xf)) as DBsub.
  pose proof (ITy_cast rho (B [(fst A B p)..]) j _ _ E _ DBsub) as DBc.
  assert (Hfun : FunTm G (B [(fst A B p)..])).
  { destruct (ty_subst1 G A B (UU j) (fst A B p) dBt
                (t_fst G k i j A B p Hik Hjk dAt dBt dp)) as [dsub].
    exact (FunTm_of_ty G (B [(fst A B p)..]) j dsub). }
  pose proof (ity_lvl rho rho eq_refl (B [(fst A B p)..]) j
                (ers rho (B [(fst A B p)..])) (famCast E _)
                k' (ers rho (B [(fst A B p)..])) F DBc DBs) as Ek; subst k'.
  refine (itot_move G (snd A B p) (B [(fst A B p)..]) Hfun rho Hrho j F
            (famCast E _) DBs DBc _ _).
  refine (ITm_cast rho (snd A B p) j _ _ E _ _ _ _).
  exact (i_snd rho A B p k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp).
Qed.

(* ---- forall-elimination.  papp has no clause of its own either: the value
     is i_proof's, and the truth it carries is the function's truth
     instantiated at the argument's value.  The proposition itself travels by
     isubst_ITm. ---- *)
Lemma itot_papp G A p f u j k (dAt : ty G A (UU k))
  (dp : ty (A :: G) p (prop j)) (df : ty G f (prf j (all j A p))) (du : ty G u A)
  (IHA : ITot G A (UU k)) (IHp : ITot (A :: G) p (prop j))
  (IHf : ITot G f (prf j (all j A p))) (IHu : ITot G u A) :
  ITot G (papp f u) (prf j (p [u..])).
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho (prf j (p [u..])) k'
                (ers rho (prf j (p [u..]))) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p j k dAt dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all j A p)))
    by exact (LTm_of_ty G (all j A p) (prop j) (t_all G A p j k dAt dp) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (i_all rho j A p k (ers rho A) FA
                (fun u0 y => ers (ext rho FA u0 y) p) xp
                (ers rho (all j A p)) g eq_refl DFA Dp) as DAll.
  (* the function's value carries the truth of the universally quantified
     body *)
  destruct (IHf rho Hrho j
              (prfF j (propElem (ers rho (all j A p))
                         (forall u0 (y : kElAt FA u0), propVal (xp u0 y)) g))
              (ity_prf rho j j (all j A p) (ers rho (all j A p)) _ DAll))
    as [xf _].
  pose proof (prfVal xf) as htruth.
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  (* the substituted proposition, and its value *)
  pose proof (isubst_ITm rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                p j eprop (propFam j) (ers (ext rho FA (ers rho u) xu) p)
                (xp (ers rho u) xu) (Dp (ers rho u) xu)) as Dpu.
  assert (E : eprf (ers (ext rho FA (ers rho u) xu) p) = eprf (ers rho (p [u..])))
    by exact (f_equal eprf (eq_sym (ers_sub1 rho p u FA xu))).
  assert (gp : Good (eprf (ers (ext rho FA (ers rho u) xu) p))
                 (ers rho (papp f u))).
  { rewrite E.
    exact (LTm_of_ty G (papp f u) (prf j (p [u..]))
             (t_all_elim G A p f u j k dAt dp df du) rho rho
             (EnvRelOf_selfE G rho Hrho)). }
  pose proof (i_proof rho (papp f u) (p [u..]) j j
                (ers (ext rho FA (ers rho u) xu) p) (xp (ers rho u) xu)
                (htruth (ers rho u) xu) (ers rho (papp f u)) gp eq_refl Dpu)
    as Dpapp.
  pose proof (ITy_cast rho (prf j (p [u..])) j _ _ E _
                (ity_prf rho j j (p [u..]) (ers (ext rho FA (ers rho u) xu) p)
                   (xp (ers rho u) xu) Dpu)) as DPc.
  assert (Hfun : FunTm G (prf j (p [u..]))).
  { destruct (ty_subst1 G A p (prop j) u dp du) as [dsub].
    exact (FunTm_of_ty G (prf j (p [u..])) j
             (t_prf G j j (p [u..]) (le_n j) dsub)). }
  refine (itot_move G (papp f u) (prf j (p [u..])) Hfun rho Hrho j F
            (famCast E _) DP DPc _ _).
  exact (ITm_cast rho (papp f u) j _ _ E _ _ _ Dpapp).
Qed.

(* ---- natrec.  The one case whose step term lives two entries deep, and
     whose TYPE `nrec_succ C` is therefore not a single substitution instance
     of the motive.  It is a composite of the three operations Interp/Subst.v
     does provide: weaken C in the tail, replace its nat variable by its own
     successor, weaken at the front (Typing/Subst.v's nrec_succ_as). ---- *)

Lemma ity_nrec_succ rho (C : tm) k j m (x : kElAt (natFam j) m)
  (FCs : kUFam k (ers (ext rho (natFam j) (esucc m) (natSucc x)) C))
  (DCs : ITy (ext rho (natFam j) (esucc m) (natSucc x)) C k
           (ers (ext rho (natFam j) (esucc m) (natSucc x)) C) FCs)
  kc Sc (FCm : kUFam kc Sc) w (y : kElAt FCm w) :
  ITy (ext (ext rho (natFam j) m x) FCm w y) (nrec_succ C) k
      (ers (ext rho (natFam j) (esucc m) (natSucc x)) C) FCs.
Proof.
  rewrite nrec_succ_as.
  apply (weaken1_ITy (ext rho (natFam j) m x)
           ((C ⟨up_ren ↑⟩) [(succ (var_tm 0))..]) k _ FCs
           (Build_Entry kc Sc FCm w y)).
  refine (subst_ITy (ext rho (natFam j) m x) (succ (var_tm 0))
            (Build_Entry j enat (natFam j) (esucc m) (natSucc x)) eq_refl
            (i_succ (ext rho (natFam j) m x) j (var_tm 0) m x
               (i_var0 rho j enat (natFam j) m x))
            (subUniv_all (ext rho (natFam j) m x) (succ (var_tm 0)))
            _ (C ⟨up_ren ↑⟩) k _ FCs _ nil eq_refl).
  exact (weaken_ITy (ext rho (natFam j) (esucc m) (natSucc x)) C k _ FCs DCs
           (Build_Entry j enat (natFam j) (esucc m) (natSucc x) :: nil) rho
           (Build_Entry j enat (natFam j) m x) eq_refl).
Qed.

Lemma itot_natrec G C z s n k j
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C)) (dn : ty G n (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHz : ITot G z (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C)) (IHn : ITot G n (nat_ j)) :
  ITot G (natrec C z s n) (C [n..]).
Proof.
  intros rho Hrho k' F DCn.
  pose (SC := fun m : etm => subst_etm (scons m (rsub rho)) (er C)).
  assert (HEm : forall m (x : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x)).
  { intros m x.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam j) m) =>
                projT1 (ityT_of_ITot (nat_ j :: G) C k IHC
                          (ext rho (natFam j) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam j) m x) C k (SC m) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ j :: G) C k IHC
                         (ext rho (natFam j) m x) (HEm m x)))).
  assert (cohC : forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
             kceq (kAt (FC m x)) (kAt (FC m' x'))).
  { intros m x m' x' Hm.
    assert (HEx : EnvRelOf (nat_ j :: G) (ext rho (natFam j) m x)
                    (ext rho (natFam j) m' x')).
    { apply (EnvRelOf_ext G rho rho (nat_ j) j (natFam j) (natFam j) m x m' x'
               (EnvRelOf_selfE G rho Hrho)).
      split; [exact (famAtSelf (natFam j)) | exact Hm]. }
    exact (FunTy_of_FunTm (nat_ j :: G) C (funtm (nat_ j :: G) C (UU k) dC)
             _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
             (LTyK_of_ty (nat_ j :: G) C k dC _ _ HEx)). }
  (* the base value *)
  assert (E0 : SC ezero = ers rho (C [(zero j)..]))
    by exact (eq_sym (ers_sub1 rho C (zero j) (natFam j) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho (zero j) j enat (natFam j) ezero
                (natE 0 NatAt_zero) eq_refl (i_zero rho j) C k (SC ezero)
                (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [(zero j)..]) k _ _ E0 _ DCz)) as [xz' Dz'].
  destruct (ITm_uncast rho z k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dz')
    as [xz Dz].
  (* the step value, at every predecessor and recursive result *)
  assert (Hstep : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w),
             { xs : kElAt (FC (esucc m) (natSucc x))
                      (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) &
               ITm (ext (ext rho (natFam j) m x) (FC m x) w y) s k
                   (SC (esucc m)) (FC (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) xs }).
  { intros m x w y.
    pose proof (ity_nrec_succ rho C k j m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k (SC m) (FC m x) w y) as DS.
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam j) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs (ext (ext rho (natFam j) m x) (FC m x) w y)
                (EnvITy_ext (nat_ j :: G) (ext rho (natFam j) m x) C k (FC m x)
                   (DC m x) w y (HEm m x))
                k (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [xs' Ds'].
    destruct (ITm_uncast _ s k _ _ Es (FC (esucc m) (natSucc x)) _ _ Ds')
      as [xs Ds].
    exists xs; exact Ds. }
  pose (ws := fun m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w) =>
                ers (ext (ext rho (natFam j) m x) (FC m x) w y) s).
  pose (xs := fun m x w y => projT1 (Hstep m x w y)).
  assert (Ds : forall m x w y,
             ITm (ext (ext rho (natFam j) m x) (FC m x) w y) s k
                 (SC (esucc m)) (FC (esucc m) (natSucc x)) (ws m x w y)
                 (xs m x w y))
    by (intros m x w y; exact (projT2 (Hstep m x w y))).
  pose (redS := fun m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w) =>
                  reds_lam2_app (er s) (rsub rho) m w).
  (* the scrutinee *)
  destruct (IHn rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)) as [xn Dn].
  pose proof (i_natrec rho C z s n k j SC FC cohC (ers rho (stepWrap s))
                (ers rho z) xz ws xs redS (ers rho n) xn
                eq_refl DC Dz Ds Dn) as Dnr.
  (* the conclusion type *)
  assert (En : SC (ers rho n) = ers rho (C [n..]))
    by exact (eq_sym (ers_sub1 rho C n (natFam j) xn)).
  pose proof (isubst_ITy rho n j enat (natFam j) (ers rho n) xn eq_refl Dn
                C k (SC (ers rho n)) (FC (ers rho n) xn)
                (DC (ers rho n) xn)) as DCsub.
  pose proof (ITy_cast rho (C [n..]) k _ _ En _ DCsub) as DCc.
  assert (Hfun : FunTm G (C [n..])).
  { destruct (ty_subst1 G (nat_ j) C (UU k) n dC dn) as [dsub].
    exact (FunTm_of_ty G (C [n..]) k dsub). }
  pose proof (ity_lvl rho rho eq_refl (C [n..]) k (ers rho (C [n..]))
                (famCast En (FC (ers rho n) xn)) k' (ers rho (C [n..])) F
                DCc DCn) as Ek; subst k'.
  refine (itot_move G (natrec C z s n) (C [n..]) Hfun rho Hrho k F
            (famCast En (FC (ers rho n) xn)) DCn DCc _ _).
  refine (ITm_cast rho (natrec C z s n) k _ _ En (FC (ers rho n) xn) _ _ _).
  (* the recursor's value, moved to the motive instance at the scrutinee's
     own value: the two nat-values agree (natEq_self) *)
  exact (i_conv rho (natrec C z s n) k (SC (ers rho n))
           (FC (ers rho n) (natE (natIdx xn) (natSpec xn)))
           (SC (ers rho n)) (FC (ers rho n) xn)
           (enatrec (ers rho z) (ers rho (stepWrap s)) (ers rho n)) _
           (cohC (ers rho n) (natE (natIdx xn) (natSpec xn)) (ers rho n) xn
              (natEq_self _ _)) Dnr).
Qed.

(* ---- the lambda.  v1 needed a Pi-INTRODUCTION built here, because its
     clause carried the value as an index together with an equation saying
     what it did; v2's clause builds it with `piLam` (Interp/PiEl.v), so this
     case only has to supply the body's values, the beta step of the
     lambda's realiser, and the body's functionality -- which is `funtm` at
     the two extended environments. ---- *)
Lemma itot_lam G A B t k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j)) (dt : ty (A :: G) t B)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot (A :: G) t B) :
  ITot G (lam k A B t) (pi k A B).
Proof.
  intros rho Hrho k' F Dpi'.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gPi := LTyK_of_ty G (pi k A B) k
                 (t_pi G k i j A B Hik Hjk dAt dBt) rho rho
                 (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_pi rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gPi eq_refl DFA DB) as Dpi.
  (* the body's value at every argument *)
  pose (wt := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) t).
  pose (xt := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                projT1 (IHt (ext rho FA u0 (dnEl (k - i) k EA FA u0 x))
                          (EnvITy_ext G rho A i FA DFA u0
                             (dnEl (k - i) k EA FA u0 x) Hrho)
                          j (FB u0 x) (DB u0 x))).
  assert (Dt : forall u0 x,
             ITm (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) t j (wB u0 x)
                 (FB u0 x) (wt u0 x) (xt u0 x)).
  { intros u0 x.
    exact (projT2 (IHt (ext rho FA u0 (dnEl (k - i) k EA FA u0 x))
                     (EnvITy_ext G rho A i FA DFA u0
                        (dnEl (k - i) k EA FA u0 x) Hrho)
                     j (FB u0 x) (DB u0 x))). }
  (* ... and the body is functional across the two extended environments *)
  assert (Hext : forall u0 x u0' x',
             kEqAt (upF (k - i) k EA FA) u0 x (upF (k - i) k EA FA) u0' x' ->
             kEqAt (upF (k - j) k EB (FB u0 x))
                     (ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) t)
                     (upEl (k - j) k EB (FB u0 x) _ (xt u0 x))
                   (upF (k - j) k EB (FB u0' x'))
                     (ers (ext rho FA u0' (dnEl (k - i) k EA FA u0' x')) t)
                     (upEl (k - j) k EB (FB u0' x') _ (xt u0' x'))).
  { intros u0 x u0' x' Hxx.
    assert (Hd : kEqAt FA u0 (dnEl (k - i) k EA FA u0 x)
                   FA u0' (dnEl (k - i) k EA FA u0' x'))
      by exact (dnEl_eq (k - i) k EA FA u0 x FA u0' x' (famAtSelf FA) Hxx).
    assert (HEx : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 x))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' x')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho) (conj (famAtSelf FA) Hd)).
    assert (QB : kceq (kAt (FB u0 x)) (kAt (FB u0' x')))
      by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx
                  j _ (FB u0 x) _ (FB u0' x') (DB u0 x) (DB u0' x')
                  (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
    assert (Hb : kRel (FB u0 x) (wt u0 x) (xt u0 x)
                   (FB u0' x') (wt u0' x') (xt u0' x')).
    { refine (funtm (A :: G) t B dt _ _ HEx j _ (FB u0 x) _ (xt u0 x) (Dt u0 x)
                _ (FB u0' x') _ (xt u0' x') (Dt u0' x') QB _).
      apply (Rel_tyeq (wB u0 x) (wB u0' x'));
        [ exact (LTy_of_ty (A :: G) B j dBt _ _ HEx)
        | exact (LTm_of_ty (A :: G) t B dt _ _ HEx) ]. }
    exact (upEl_eq (k - j) k EB (FB u0 x) _ (xt u0 x) (FB u0' x') _ (xt u0' x')
             QB (kRel_at Hb)). }
  assert (gw : Good (epi (ers rho A) B0) (ers rho (lam k A B t)))
    by exact (LTm_of_ty G (lam k A B t) (pi k A B)
                (t_lam G k i j A B t Hik Hjk dAt dBt dt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_lvl rho rho eq_refl (pi k A B) k (ers rho (pi k A B))
                (piFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                   (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gPi)
                k' (ers rho (pi k A B)) F Dpi Dpi') as Ek; subst k'.
  refine (itot_move G (lam k A B t) (pi k A B)
            (FunTm_of_ty G (pi k A B) k (t_pi G k i j A B Hik Hjk dAt dBt))
            rho Hrho k F
            (piFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gPi)
            Dpi' Dpi _ _).
  exact (i_lam rho A B t k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gPi (ers rho (lam k A B t)) wt xt
           (fun u0 x => reds_lam_app (er t) (rsub rho) u0) Hext gw
           eq_refl eq_refl DFA DB Dt).
Qed.

(* ---- sup.  New in v2.  Besides the W type's own components, the clause
     asks for the BRANCHING FUNCTION's semantic value -- an element of the Pi
     whose domain is the branching type at the label and whose codomain is
     constantly the tree type.  That Pi is an interpretation of the type
     t_sup gives f, which is what `er_wsup_fun_sub` says on the erased side,
     so the value comes from the induction hypothesis for f at that very
     family.  The codomain's gap is 0 and its equation `eq_refl`, which is
     what makes `upF 0 k eq_refl` disappear and the family built here BE the
     clause's `brFam`. ---- *)
Lemma itot_sup G A B a f k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (da : ty G a A) (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHa : ITot G a A) (IHf : ITot G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  ITot G (sup k A B a f) (wt k A B).
Proof.
  intros rho Hrho k' F DW'.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* the label *)
  destruct (IHa rho Hrho i FA DFA) as [xa Da].
  pose (Xa := upEl (k - i) k EA FA (ers rho a) xa).
  (* the branching type at the label: read in the environment carrying the
     label's own value, then moved to the clause's instance *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho a) xa)
              (EnvITy_ext G rho A i FA DFA (ers rho a) xa Hrho)) as [FBu DBu0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho a) xa)
                  (ext rho FA (ers rho a)
                     (dnEl (k - i) k EA FA (ers rho a) Xa))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho a) xa (ers rho a) _
             (EnvRelOf_selfE G rho Hrho)).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu) (kAt (FB (ers rho a) Xa)))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0 (DB (ers rho a) Xa)
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  pose proof (ity_conv rho (B [a..]) j _ FBu (FB (ers rho a) Xa) P
                (isubst_ITy rho a i (ers rho A) FA (ers rho a) xa eq_refl Da
                   B j (ers (ext rho FA (ers rho a) xa) B) FBu DBu0)) as DBa.
  (* the branching function's type, as a Pi whose codomain is the tree type *)
  pose proof (ity_pi rho (B [a..]) ((wt k A B) ⟨↑⟩) k j k (k - j) 0 EB eq_refl
                (wB (ers rho a) Xa) (FB (ers rho a) Xa) Bbr
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho a) Xa)
                (eq_sym (er_wsup_fun_sub k A B a (rsub rho)))
                DBa
                (fun u0 x =>
                   weaken1_ITy rho (wt k A B) k (ew (ers rho A) B0) WF
                     (Build_Entry j (wB (ers rho a) Xa) (FB (ers rho a) Xa) u0
                        (dnEl (k - j) k EB (FB (ers rho a) Xa) u0 x)) DW))
    as Dfpi.
  assert (Ef : epi (wB (ers rho a) Xa) Bbr
               = ers rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
    by exact (eq_sym (er_wsup_fun_sub k A B a (rsub rho))).
  destruct (IHf rho Hrho k (famCast Ef _)
              (ITy_cast rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) k _ _ Ef _ Dfpi))
    as [xf' Df'].
  destruct (ITm_uncast rho f k _ _ Ef _ _ _ Df') as [xf Df].
  assert (gd : Good (ew (ers rho A) B0) (esup (ers rho a) (ers rho f)))
    by exact (LTm_of_ty G (sup k A B a f) (wt k A B)
                (t_sup G k i j A B a f Hik Hjk dAt dBt da df) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_lvl rho rho eq_refl (wt k A B) k (ers rho (wt k A B)) WF
                k' (ers rho (wt k A B)) F DW DW') as Ek; subst k'.
  refine (itot_move G (sup k A B a f) (wt k A B)
            (FunTm_of_ty G (wt k A B) k (t_w G k i j A B Hik Hjk dAt dBt))
            rho Hrho k F WF DW' DW _ _).
  exact (i_sup rho A B a f k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gW Bbr redBbr gBr (ers rho a) xa (ers rho f) xf gd
           eq_refl DFA DB Da Df).
Qed.

(* ---- the W-recursion.  The last and largest case of totality.  Besides
     the W type's own components and the motive, the clause asks for the
     three guarded goodness premises (discharged from the node's own `gd`
     through Rel_w_br2/Rel_pi_intro and layer 1's sem_wrec), the induction
     hypothesis's type `Bih` -- which is just the erasure of `wih`'s
     codomain, so `Bih_red` is reds_lam_app + er_wih_cod -- and the step:
     its value comes from the induction hypothesis for `s` in the three-entry
     environment, which is why the two Pi-typed context types have to be
     RECOGNISED as the clause's own `brFam` and `ihFam` (Dbr, Dih), the
     latter through the motive at a subtree (Dsub), where the subtree is the
     branching function applied to the branch and `i_app`'s index is
     literally `ihIdx`.  `stepSrel` is then the same argument as
     funtm_wrec's step obligation with both sides in one reading. ---- *)
(* The branching function's type, as the step's context sees it: three
   entries above rho, and with the Pi's own binder that is where the four
   shifts on the tree type go. *)
Lemma ers_wbr_app_ty (rho : Env) (A B : tm) (k : nat) (e1 e2 e3 : Entry) :
  ers (e1 :: e2 :: e3 :: rho) (pi k (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩))
  = epi (ers (e3 :: rho) B) (elam (ren_etm ↑ (ers rho (wt k A B)))).
Proof.
  unfold ers; cbn [rsub].
  rewrite er_pi_sub, !er_ren, sub_shift_up, !subst_cons_shift_etm.
  reflexivity.
Qed.

(* The tree type as the step's context sees it: three entries above rho, and
   `sh3` peels exactly those three. *)
Lemma ers_wt_sh3 (rho : Env) (A B : tm) (k : nat) (e1 e2 e3 : Entry) :
  ers (e3 :: e2 :: e1 :: rho) (wt k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩))
  = ew (ers rho A) (elam (subst_etm (up_etm (rsub rho)) (er B))).
Proof.
  unfold ers; cbn [rsub].
  rewrite (er_w_sub k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)).
  rewrite !er_ren, !subst_ren_etm.
  apply (f_equal2 ew).
  - apply ext_etm; intros i; reflexivity.
  - apply (f_equal elam); apply ext_etm; intros [| i]; reflexivity.
Qed.

Lemma itot_wrec G A B C s w0 k i j m nn
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= nn) (Hmn : m <= nn)
  (En : nn = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih nn k A B C) (UU nn))
  (ds : ty (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (dw : ty G w0 (wt k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHC : ITot (wt k A B :: G) C (UU m))
  (IHs : ITot (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (IHw : ITot G w0 (wt k A B)) :
  ITot G (wrec A B C s w0) (C [w0..]).
Proof.
  intros rho Hrho k' F DCw.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* ---- the motive ---- *)
  pose (SC := fun w1 : etm => subst_etm (scons w1 (rsub rho)) (er C)).
  assert (HEw : forall w1 (x : kElAt WF w1),
             EnvITy (wt k A B :: G) (ext rho WF w1 x)).
  { intros w1 x.
    exact (EnvITy_ext_ceq G rho (wt k A B) k (ers rho (wt k A B)) WF WF DW
             (famAtSelf WF) w1 x Hrho). }
  pose (FC := fun w1 (x : kElAt WF w1) =>
                projT1 (ityT_of_ITot (wt k A B :: G) C m IHC
                          (ext rho WF w1 x) (HEw w1 x))).
  assert (DC : forall w1 x, ITy (ext rho WF w1 x) C m (SC w1) (FC w1 x))
    by (intros w1 x;
        exact (projT2 (ityT_of_ITot (wt k A B :: G) C m IHC
                         (ext rho WF w1 x) (HEw w1 x)))).
  assert (cohC : forall w1 x w1' x', kEqAt WF w1 x WF w1' x' ->
             kceq (kAt (FC w1 x)) (kAt (FC w1' x'))).
  { intros w1 x w1' x' Hx.
    assert (HExx : EnvRelOf (wt k A B :: G) (ext rho WF w1 x) (ext rho WF w1' x'))
      by exact (EnvRelOf_ext' G rho rho (wt k A B) k _ _ WF WF w1 x w1' x'
                  (EnvRelOf_selfE G rho Hrho) eq_refl eq_refl
                  (conj (famAtSelf WF) Hx)).
    exact (FunTy_of_FunTm (wt k A B :: G) C
             (funtm (wt k A B :: G) C (UU m) dCt) _ _ HExx m _ (FC w1 x) _
             (FC w1' x') (DC w1 x) (DC w1' x')
             (LTyK_of_ty (wt k A B :: G) C m dCt _ _ HExx)). }
  (* ---- the layer-1 side, for the guarded goodness premises ---- *)
  pose proof (proj2 (proj2 (proj2 (EnvRelOf_selfE G rho Hrho)))) as HS.
  assert (HBg : forall u u', Rel (subst_etm (rsub rho) (er A)) u u' ->
                  eqty j (subst_etm (scons u (rsub rho)) (er B))
                          (subst_etm (scons u' (rsub rho)) (er B)))
    by (intros u u' Hu;
        exact (fundamental_U (A :: G) B j dBt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hu))).
  assert (HCg : forall x1 y1, Rel (ers rho (wt k A B)) x1 y1 ->
                  eqty m (SC x1) (SC y1))
    by (intros x1 y1 Hxy;
        exact (fundamental_U (wt k A B :: G) C m dCt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hxy))).
  pose proof (sem_wrec k m A B C (rsub rho) _ _ (gt_of k _ gW) HCg
                (sem_wrec_step G k j m nn A B C s s (rsub rho) (rsub rho)
                   Hjk Hjn Hmn HS HBg gW HCg
                   (fundamental_ty _ s (wsup_ty k A B C) ds))) as Hrec0.
  (* the branches of a node are trees, which is what the two guarded
     premises are about *)
  assert (Hbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f v')).
  { intros u0 z f gd v v' Hv.
    apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
             (kFam_good_ty WF) (ev_w _ _) _ _ gd u0 f u0 f
             (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
  (* ---- the induction hypothesis's type ---- *)
  assert (EBn : (nn - j) + j = nn) by lia.
  assert (EC : (nn - m) + m = nn) by lia.
  pose (Cih := C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                     (var_tm 1) (var_tm 0) .:s sh3 ]).
  pose (Bih := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) (f : etm) =>
                 subst_etm (scons f (scons u0 (rsub rho))) (elam (er Cih))).
  assert (Bih_red : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f v,
             reds (eapp (Bih u0 z f) v) (SC (eapp f v))).
  { intros u0 z f v; unfold SC.
    rewrite <- (er_wih_cod k A B C (rsub rho) u0 f v).
    exact (reds_lam_app (er Cih) (scons f (scons u0 (rsub rho))) v). }
  assert (gIh : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             eqty nn (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0 z) (Bih u0 z f))).
  { intros u0 z f gd.
    apply (eqty_dfun nn (wB u0 z) _ (fun v => SC (eapp f v)));
      [ exact (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
      | exact (Bih_red u0 z f)
      | intros v v' Hv;
        exact (eqty_cumul m nn _ _ Hmn
                 (HCg _ _ (Hbr u0 z f gd v v' Hv))) ]. }
  assert (gf : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) Bbr) f).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) Bbr);
      [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (redBbr v) |].
    exact (Hbr u0 z f gd v v' Hv). }
  assert (gih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) (Bih u0 z f))
                  (ihR (ers rho (stepWrap3 s)) f)).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
      [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
    eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
    exact (Hrec0 _ _ (Hbr u0 z f gd v v' Hv)). }
  (* ---- the step's first context type, interpreted: it IS the clause's
       own branching-function family ---- *)
  assert (Dbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             ITy (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B) k
                 (epi (wB u0 z) Bbr)
                 (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW Bbr redBbr gBr u0 z)).
  { intros u0 z; unfold brFam.
    apply (ity_pi (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) B
             ((wt k A B) ⟨↑⟩ ⟨↑⟩) k j k (k - j) 0 EB eq_refl
             (wB u0 z) (FB u0 z) Bbr (fun v _ => ew (ers rho A) B0)
             (fun v _ => WF) (fun v _ => redBbr v)
             (fun v y v' y' _ => famAtSelf WF) (gBr u0 z));
      [ exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))
      | exact (DB u0 z)
      | intros v y;
        exact (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                 (weaken1_ITy rho (wt k A B) k _ WF _ DW)) ]. }
  (* abbreviations for the two Pi-typed entries *)
  pose (BRF := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z).
  pose (BRE := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext =>
                 brEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z f sub subext
                   (gf u0 z f gd)).
  (* ---- the motive at a SUBTREE, which is the codomain of the induction
       hypothesis's type: the subtree is the branching function applied to the
       branch, read by i_app in the four-entry environment ---- *)
  assert (Dsub : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext v
                   (y : kElAt (upF (nn - j) nn EBn (FB u0 z)) v),
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                 (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                        (var_tm 1) (var_tm 0) .:s sh3 ])
                 m (SC (eapp f v))
                 (FC (eapp f v)
                    (sub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                              wB FB nn (nn - j) EBn u0 z v y)))).
  { intros u0 z f gd sub subext v y.
    pose (Xa := ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                  nn (nn - j) EBn u0 z v y).
    (* the application *)
    pose proof (i_app
                  (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                     (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                  (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                  (var_tm 1) (var_tm 0) k j k (k - j) 0 EB eq_refl
                  (wB u0 z) (FB u0 z) Bbr (fun v' _ => ew (ers rho A) B0)
                  (fun v' _ => WF) (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext)
                  v (dnEl (nn - j) nn EBn (FB u0 z) v y)
                  (eq_sym (ers_wbr_app_ty rho A B k _ _ _))
                  (weaken1_ITy _ (B ⟨↑⟩) j _ (FB u0 z) _
                     (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z)))
                  (fun u x =>
                     weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) k _ WF _
                       (weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩) k _ WF _
                          (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                             (weaken1_ITy rho (wt k A B) k _ WF _ DW))))
                  (i_varS _ _ 0 k _ (BRF u0 z) f (BRE u0 z f gd sub subext)
                     (i_var0 _ k _ (BRF u0 z) f (BRE u0 z f gd sub subext)))
                  (i_var0 _ j _ (FB u0 z) v
                     (dnEl (nn - j) nn EBn (FB u0 z) v y))) as Dapp.
    (* the value the application names, and the motive's index at it *)
    pose (Xv := piApp k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext) v Xa).
    assert (Hidx : kEqAt WF (eapp f v) Xv WF (eapp f v) (sub v Xa))
      by exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (fun v' _ => eapp f v') sub
                  (fun v' y' => reds_refl (eapp f v')) subext (gf u0 z f gd)
                  v Xa).
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry j (wB u0 z) (FB u0 z) v
                  (dnEl (nn - j) nn EBn (FB u0 z) v y)).
    pose (em := Build_Entry k (ew (ers rho A) B0) WF (eapp f v) Xv).
    rewrite wsub3_as, <- ren3_as.
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                 (var_tm 1) (var_tm 0))
              k (ew (ers rho A) B0) WF (eapp f v) Xv eq_refl Dapp
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (eapp f v)) _ _).
    refine (ity_conv _ _ _ _ (FC (eapp f v) Xv) (FC (eapp f v) (sub v Xa))
              (cohC (eapp f v) Xv (eapp f v) (sub v Xa) Hidx) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e1 :: rho) e2 eq_refl).
    exact (weaken_ITy _ C m _ _ (DC (eapp f v) Xv)
             (em :: nil) rho e1 eq_refl). }
  assert (Epi2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             epi (wB u0 z) (Bih u0 z f)
             = ers (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                      (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C)).
  { intros u0 z f gd sub subext.
    unfold wB, Bih, ers, wih; cbn [rsub ext].
    rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity. }
  (* ---- the step's second context type, interpreted: it IS the clause's
       own induction-hypothesis family ---- *)
  assert (Dih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             ITy (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C) nn
                 (epi (wB u0 z) (Bih u0 z f))
                 (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                    Bih gIh Bih_red u0 z f gd sub subext)).
  { intros u0 z f gd sub subext.
    unfold ihFam, wih.
    apply (ity_pi _ (B ⟨↑⟩)
             (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                    (var_tm 1) (var_tm 0) .:s sh3 ])
             nn j m (nn - j) (nn - m) EBn EC
             (wB u0 z) (FB u0 z) (Bih u0 z f) _ _ _ _ _);
      [ exact (Epi2 u0 z f gd sub subext)
      | exact (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z))
      | exact (Dsub u0 z f gd sub subext) ]. }
  (* ---- and hence the step's environment carries an interpretation of every
       one of its context types ---- *)
  assert (Ebr2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             epi (wB u0 z) Bbr
             = ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B))
    by (intros u0 z; exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))).
  assert (HE3 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                  ih ihext,
             EnvITy (wih nn k A B C :: wbr k A B :: A :: G)
               (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd)))).
  { intros u0 z f gd sub subext ih ihext.
    refine (EnvITy_ext_ceq (wbr k A B :: A :: G) _ (wih nn k A B C) nn _ _
              (famCast (Epi2 u0 z f gd sub subext) _) _ _ _ _ _).
    - exact (ITy_cast _ (wih nn k A B C) nn _ _
               (Epi2 u0 z f gd sub subext) _ (Dih u0 z f gd sub subext)).
    - apply famCast_ceq.
    - refine (EnvITy_ext_ceq (A :: G) _ (wbr k A B) k _ _
                (famCast (Ebr2 u0 z) _) _ _ _ _ _).
      + exact (ITy_cast _ (wbr k A B) k _ _ (Ebr2 u0 z) _ (Dbr u0 z)).
      + apply famCast_ceq.
      + exact (EnvITy_ext G rho A i FA DFA u0
                 (dnEl (k - i) k EA FA u0 z) Hrho). }
  (* ---- the motive at the TREE the step builds ---- *)
  assert (Dwsup : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                    ih ihext,
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR (ers rho (stepWrap3 s)) f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                       subext ih ihext (gih u0 z f gd)))
                 (wsup_ty k A B C) m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))).
  { intros u0 z f gd sub subext ih ihext.
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry nn (epi (wB u0 z) (Bih u0 z f))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd))).
    (* the tree, read in the step's own environment *)
    pose (Z' := upEl (k - i) k EA FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (HzZ : kEqAt (upF (k - i) k EA FA) u0 z (upF (k - i) k EA FA) u0 Z')
      by (apply kEqAt_sym; apply upEl_dnEl).
    assert (Hbrceq : kceq (kAt (BRF u0 z)) (kAt (BRF u0 Z'))).
    { unfold BRF, brFam; apply piFam_ceq.
      - exists k; apply eqty_pi.
        + exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                   (uf_ty (upF (k - j) k EB (FB u0 Z')))
                   (ceq_ty (upF (k - j) k EB (FB u0 z))
                      (upF (k - j) k EB (FB u0 Z')) (cohB u0 z u0 Z' HzZ))).
        + intros v v' _.
          eapply eqty_exp; [ apply redBbr | apply redBbr |].
          exact gW.
      - exact (cohB u0 z u0 Z' HzZ).
      - intros v y v' y' _; exact (famAtSelf WF). }
    pose (ea := Build_Entry i (ers rho A) FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (DA3 : ITy (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) i (ers rho A) FA).
    { rewrite <- sh3_as.
      exact (weaken1_ITy _ ((A ⟨↑⟩) ⟨↑⟩) i _ FA _
               (weaken1_ITy _ (A ⟨↑⟩) i _ FA _
                  (weaken1_ITy rho A i _ FA _ DFA))). }
    assert (DB3 : forall u x,
               ITy (ext (e3 :: e2 :: e1 :: rho) FA u
                      (dnEl (k - i) k EA FA u x))
                   (B ⟨up_ren sh3⟩) j (wB u x) (FB u x)).
    { intros u x; rewrite <- ren3_as.
      refine (weaken_ITy _ ((B ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e2 :: e1 :: rho) e3 eq_refl).
      refine (weaken_ITy _ (B ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e1 :: rho) e2 eq_refl).
      exact (weaken_ITy _ B j _ _ (DB u x)
               (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
               rho e1 eq_refl). }
    pose proof (i_sup (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)
                  (var_tm 2) (var_tm 1) k i j (k - i) (k - j) EA EB
                  (ers rho A) FA B0 wB FB redB cohB gW Bbr redBbr gBr
                  u0 (dnEl (k - i) k EA FA u0 z) f
                  (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z')) (famAtWf (BRF u0 z))
                     (famAtWf (BRF u0 Z')) Hbrceq f
                     (BRE u0 z f gd sub subext))
                  gd (eq_sym (ers_wt_sh3 rho A B k e1 e2 e3))
                  DA3 DB3
                  (i_varS _ e3 1 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                     (i_varS _ e2 0 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                        (i_var0 rho i _ FA u0 (dnEl (k - i) k EA FA u0 z))))
                  (i_conv _ (var_tm 1) k (epi (wB u0 z) Bbr) (BRF u0 z) _
                     (BRF u0 Z') f (BRE u0 z f gd sub subext) Hbrceq
                     (i_varS _ e3 0 k _ (BRF u0 z) f
                        (BRE u0 z f gd sub subext)
                        (i_var0 (e1 :: rho) k _ (BRF u0 z) f
                           (BRE u0 z f gd sub subext))))) as Dsup3.
    (* i_sup's value is the clause's own tree: its label is the round trip of
       the entry's, and its branches are the branching function's semantic
       value applied -- which is what it was built from *)
    assert (Hsups : kEqAt WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f Z'
                         (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         gd)
                      WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd)).
    { apply (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW);
        [ apply upEl_dnEl | intros v0 y v0' y' Hy | exact gd ].
      eapply kEqAt_trans; [ exact (famAtSelf WF) |
        exact (kRel_at
                 (piApp_eqX k (wB u0 Z') Bbr (upF (k - j) k EB (FB u0 Z'))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 Z')
                    (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 z)
                    (cohB u0 Z' u0 z (upEl_dnEl (k - i) k EA FA u0 z))
                    (fun v y1 v' y1' _ => famAtSelf WF)
                    f (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                         (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                         (BRE u0 z f gd sub subext))
                    f (BRE u0 z f gd sub subext) v0 y v0' y'
                    (kEqAt_sym (BRF u0 z) f (BRE u0 z f gd sub subext) _ _ _
                       (kto_coh (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                          (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                          (BRE u0 z f gd sub subext)))
                    Hy)) |].
      exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
               (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
               (fun v _ => redBbr v) (fun v y1 v' y1' _ => famAtSelf WF)
               (gBr u0 z) f (fun v _ => eapp f v) sub
               (fun v y1 => reds_refl (eapp f v)) subext (gf u0 z f gd)
               v0' y'). }
    (* and then the motive, substituted and weakened as at the subtree *)
    unfold wsup_ty; rewrite wsub3_as, <- (ren3_as C).
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1))
              k (ew (ers rho A) B0) WF (esup u0 f) _ eq_refl Dsup3
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (esup u0 f)) _ _).
    refine (ity_conv _ _ _ _ _ _
              (cohC (esup u0 f) _ (esup u0 f) _ Hsups) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e1 :: rho) e2 eq_refl).
    refine (weaken_ITy _ C m _ _ _ (_ :: nil) rho e1 eq_refl).
    exact (DC (esup u0 f) _). }
  (* ---- the step's realiser and value ---- *)
  assert (Hstep : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                    ih ihext,
             { xs : kElAt (FC (esup u0 f)
                             (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                (fun u x => upF (k - j) k EB (FB u x)) redB
                                cohB gW u0 f z sub subext gd))
                      (ers (ext (ext (ext rho FA u0
                                        (dnEl (k - i) k EA FA u0 z))
                                   (BRF u0 z) f (BRE u0 z f gd sub subext))
                              (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red u0 z f gd sub
                                 subext)
                              (ihR (ers rho (stepWrap3 s)) f)
                              (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red
                                 (ers rho (stepWrap3 s)) u0 z f gd sub subext
                                 ih ihext (gih u0 z f gd))) s) &
               ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                      (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red u0 z f gd sub subext)
                      (ihR (ers rho (stepWrap3 s)) f)
                      (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                         subext ih ihext (gih u0 z f gd)))
                   s m (SC (esup u0 f))
                   (FC (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd))
                   (ers _ s) xs }).
  { intros u0 z f sub subext gd ih ihext.
    assert (Es : SC (esup u0 f)
                 = ers (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                              (BRF u0 z) f (BRE u0 z f gd sub subext))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                         (ihR (ers rho (stepWrap3 s)) f)
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red (ers rho (stepWrap3 s))
                            u0 z f gd sub subext ih ihext (gih u0 z f gd)))
                     (wsup_ty k A B C))
      by exact (eq_sym (er_wsup_ty k A B C (rsub rho) u0 f
                          (ihR (ers rho (stepWrap3 s)) f))).
    destruct (IHs _ (HE3 u0 z f gd sub subext ih ihext) m (famCast Es _)
                (ITy_cast _ (wsup_ty k A B C) m _ _ Es _
                   (Dwsup u0 z f gd sub subext ih ihext))) as [xs' Ds'].
    destruct (ITm_uncast _ s m _ _ Es _ _ _ Ds') as [xs Ds].
    exists xs; exact Ds. }
  pose (Sr := ers rho (stepWrap3 s)).
  pose (ws := (fun u0 z f sub subext gd ih ihext =>
                 subst_etm (scons (ihR Sr f) (scons f (scons u0 (rsub rho))))
                   (er s))
              : WsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr).
  pose (xs := (fun u0 z f sub subext gd ih ihext =>
                 projT1 (Hstep u0 z f sub subext gd ih ihext))
              : XsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr ws).
  pose (redS := (fun u0 z f sub subext gd ih ihext =>
                   reds_lam3_app (er s) (rsub rho) u0 f (ihR Sr f))
                : RedSTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC Sr ws).
  assert (Ds : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                 ih ihext,
             ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR Sr f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                       (gih u0 z f gd)))
                 s m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))
                 (ws u0 z f sub subext gd ih ihext)
                 (xs u0 z f sub subext gd ih ihext))
    by (intros u0 z f sub subext gd ih ihext;
        exact (projT2 (Hstep u0 z f sub subext gd ih ihext))).
  (* ---- the step's congruence, within this one reading ---- *)
  assert (stepSrel : StepRelTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                       wB FB redB cohB gW m SC FC Sr ws xs redS).
  { intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
           Hz Hsub HRsup Hih.
    (* the branching type at the two labels, at its own level *)
    assert (QB : kceq (kAt (FB u0 z)) (kAt (FB u0' z')))
      by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                  (funtm (A :: G) B (UU j) dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA (ers rho A) FA
                  wB FB (ers rho A) FA wB FB DFA DFA (famAtSelf FA) DB DB
                  u0 z u0' z' Hz).
    assert (Htb : tyeq (wB u0 z) (wB u0' z'))
      by exact (ceq_ty (FB u0 z) (FB u0' z') QB).
    (* the two branching Pi types, and the two branching functions *)
    assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB u0' z') Bbr)).
    { exists k; apply eqty_pi.
      - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                 (uf_ty (upF (k - j) k EB (FB u0' z'))) Htb).
      - intros v v' _.
        eapply eqty_exp; [ apply redBbr | apply redBbr |]; exact gW. }
    assert (Hbr2 : forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f' v')).
    { intros v v' Hv.
      apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
               (kFam_good_ty WF) (ev_w _ _) _ _ HRsup u0 f u0' f'
               (ev_sup _ _) (ev_sup _ _)).
      eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
    assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
    { apply (Rel_pi_intro _ (wB u0 z) Bbr);
        [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (redBbr v) |].
      exact (Hbr2 v v' Hv). }
    assert (HRih : Rel (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f) (ihR Sr f')).
    { apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
        [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
      eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
      exact (Hrec0 _ _ (Hbr2 v v' Hv)). }
    (* the two IH types *)
    assert (Htih : tyeq (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0' z') (Bih u0' z' f'))).
    { exists nn; apply eqty_pi.
      - exact (eqty_at_lvl nn _ _ (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
                 (uf_ty (upF (nn - j) nn EBn (FB u0' z'))) Htb).
      - intros v v' Hv.
        eapply eqty_exp;
          [ exact (Bih_red u0 z f v) | exact (Bih_red u0' z' f' v') |].
        exact (eqty_cumul m nn _ _ Hmn (HCg _ _ (Hbr2 v v' Hv))). }
    (* the three entries of the step's context, related *)
    assert (HE1 : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' z')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (kRel_dn (k - i) k EA FA FA (famAtSelf FA) _ _ _ _
                     (conj (famAtSelf (upF (k - i) k EA FA)) Hz))).
    assert (T2 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1),
               tyeq (epi (wB u1 z1) Bbr)
                 (ers (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1)) (wbr k A B)))
      by (intros u1 z1; rewrite <- (Ebr2 u1 z1); exists k; exact (gBr u1 z1)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G)
                    (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                       (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 (T2 u0 z) (T2 u0' z')).
      split.
      - unfold BRF, brFam; apply piFam_ceq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF) ].
      - unfold BRE, brEl, BRF, brFam; apply piLam_eq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF)
          | exact HRf | exact Hsub ]. }
    assert (T3 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1) f1 gd1 sub1
                   subext1,
               tyeq (epi (wB u1 z1) (Bih u1 z1 f1))
                 (ers (ext (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1))
                         (BRF u1 z1) f1 (BRE u1 z1 f1 gd1 sub1 subext1))
                    (wih nn k A B C)))
      by (intros u1 z1 f1 gd1 sub1 subext1;
          rewrite <- (Epi2 u1 z1 f1 gd1 sub1 subext1);
          exists nn; exact (gIh u1 z1 f1 gd1)).
    assert (HE3r : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                     (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                             (BRF u0 z) f (BRE u0 z f gd sub subext))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                        (ihR Sr f)
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih
                           ihext (gih u0 z f gd)))
                     (ext (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                             (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0' z' f' gd' sub' subext')
                        (ihR Sr f')
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0' z' f' gd' sub' subext'
                           ih' ihext' (gih u0' z' f' gd')))).
    { apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
               _ _ _ _ _ _ _ _ HE2 (T3 u0 z f gd sub subext)
               (T3 u0' z' f' gd' sub' subext')).
      split.
      - unfold ihFam; apply piFam_ceq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy)) ].
      - unfold ihEl, ihFam; apply piLam_eq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy))
          | exact HRih
          | intros v y v' y' Hy;
            exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                     (kRel_ceq (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)
                                  v' (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0' z' v' y')
                                  (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                     (nn - j) nn EBn v y v' y' QB Hy)))
                     (kRel_at (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0 z v y)
                                 v' (ihIdx k i j (k - i) (k - j) EA EB
                                       (ers rho A) FA wB FB nn (nn - j) EBn
                                       u0' z' v' y')
                                 (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                    (nn - j) nn EBn v y v' y' QB Hy)))) ]. }
    (* the two motives at the two trees, and the step's own realisers *)
    assert (Hmot : kceq (kAt (FC (esup u0 f)
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0 f z sub subext gd)))
                        (kAt (FC (esup u0' f')
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0' f' z' sub' subext' gd'))))
      by exact (cohC _ _ _ _
                  (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
                     (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                     u0 z f sub subext gd u0' z' f' sub' subext' gd'
                     Hz Hsub HRsup)).
    assert (Hrs : Rel (SC (esup u0' f')) (ws u0 z f sub subext gd ih ihext)
                    (ws u0' z' f' sub' subext' gd' ih' ihext')).
    { apply (Rel_tyeq (SC (esup u0 f)) (SC (esup u0' f')));
        [ exists m;
          exact (ceq_eqty (FC (esup u0 f) _) (FC (esup u0' f') _) Hmot) |].
      unfold ws, SC.
      rewrite <- (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr f)).
      exact (fundamental_ty _ s (wsup_ty k A B C) ds _ _
               (proj2 (proj2 (proj2 HE3r)))). }
    pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s
                  (wsup_ty k A B C) ds _ _ HE3r m _ _ _
                  (xs u0 z f sub subext gd ih ihext)
                  (Ds u0 z f sub subext gd ih ihext) _ _ _
                  (xs u0' z' f' sub' subext' gd' ih' ihext')
                  (Ds u0' z' f' sub' subext' gd' ih' ihext')
                  Hmot Hrs) as Hxs.
    (* and the two expansions come off *)
    unfold stepOf.
    eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
    eapply kRel_trans; [ exact Hxs |].
    split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ]. }
  (* ---- the subject, and the recursor's own value ---- *)
  destruct (IHw rho Hrho k WF DW) as [xw Dw'].
  pose proof (i_wrec rho A B C s w0 k i j m nn (k - i) (k - j) (nn - j) (nn - m)
                EA EB EBn EC En (ers rho A) FA B0 wB FB redB cohB gW
                SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr gf gih
                ws xs redS stepSrel (ers rho w0) xw
                eq_refl eq_refl (fun _ => eq_refl) DFA DB DC Ds Dw') as Dwrec.
  (* the conclusion type *)
  assert (Ew0 : SC (ers rho w0) = ers rho (C [w0..]))
    by exact (eq_sym (ers_sub1 rho C w0 WF xw)).
  pose proof (isubst_ITy rho w0 k (ers rho (wt k A B)) WF (ers rho w0) xw
                eq_refl Dw' C m (SC (ers rho w0)) (FC (ers rho w0) xw)
                (DC (ers rho w0) xw)) as DCsub.
  pose proof (ITy_cast rho (C [w0..]) m _ _ Ew0 _ DCsub) as DCc.
  assert (Hfun : FunTm G (C [w0..])).
  { destruct (ty_subst1 G (wt k A B) C (UU m) w0 dCt dw) as [dsub].
    exact (FunTm_of_ty G (C [w0..]) m dsub). }
  pose proof (ity_lvl rho rho eq_refl (C [w0..]) m (ers rho (C [w0..]))
                (famCast Ew0 (FC (ers rho w0) xw)) k' (ers rho (C [w0..])) F
                DCc DCw) as Ek; subst k'.
  refine (itot_move G (wrec A B C s w0) (C [w0..]) Hfun rho Hrho m F
            (famCast Ew0 (FC (ers rho w0) xw)) DCw DCc _ _).
  exact (ITm_cast rho (wrec A B C s w0) m _ _ Ew0 (FC (ers rho w0) xw) _ _
           Dwrec).
Qed.

(* ================================================================== *)
(* THE CONVERSION CASES.                                               *)
(*                                                                    *)
(* For `cv G t u A` the statement is ISem: totality for both sides and   *)
(* their relatedness.  The congruences follow the corresponding typing    *)
(* case with two terms in place of one; the computation rules are the      *)
(* element laws of Interp/PiEl.v, Interp/SigEl.v, Interp/WEl.v and         *)
(* Interp/Rec.v.                                                          *)
(* ================================================================== *)

(* The coercion is injective on the equality, which is what a conversion of
   the TYPE needs: the values live at the new type's family and have to be
   compared at the old one's.  In v1 this was `cpullK_eq`, the transport's
   left inverse; here it is `kto_coh` twice. *)
Lemma kEqAt_of_kto {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) w x w' x' :
  kEqAt F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x)
        F' w' (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w' x') ->
  kEqAt F w x F w' x'.
Proof.
  intros H.
  eapply kEqAt_trans; [ exact P | apply kto_coh |].
  eapply kEqAt_trans; [ exact (famAtSelf F') | exact H |].
  apply kEqAt_sym; apply kto_coh.
Qed.

Lemma IRel_self' G t A (d : ty G t A) : IRel G t t A.
Proof. exact (IRel_self G t A d). Qed.

(* ---- the equivalence, and the conversion of the type ---- *)

Lemma isem_refl G t A (d : ty G t A) (IHd : ITot G t A) : ISem G t t A.
Proof. exact (IHd, IHd, IRel_self' G t A d). Qed.

Lemma isem_sym G t u A (H : ISem G t u A) : ISem G u t A.
Proof.
  destruct H as [[Ht Hu] HR]; split; [split; [exact Hu | exact Ht] |].
  intros rho Hrho k F DA x y Dx Dy.
  apply kEqAt_sym; exact (HR rho Hrho k F DA y x Dy Dx).
Qed.

Lemma isem_trans G t u v A (H1 : ISem G t u A) (H2 : ISem G u v A) :
  ISem G t v A.
Proof.
  destruct H1 as [[Ht Hu] HR1]; destruct H2 as [[Hu' Hv] HR2].
  split; [split; [exact Ht | exact Hv] |].
  intros rho Hrho k F DA x y Dx Dy.
  destruct (Hu rho Hrho k F DA) as [z Dz].
  eapply kEqAt_trans;
    [ exact (famAtSelf F)
    | exact (HR1 rho Hrho k F DA x z Dx Dz)
    | exact (HR2 rho Hrho k F DA z y Dz Dy) ].
Qed.

Lemma isem_conv G t u A B k
  (dA : ty G A (UU k)) (dB : ty G B (UU k))
  (H : ISem G t u A) (IHA : ITot G A (UU k)) (IHB : ITot G B (UU k))
  (IHc : IRel G A B (UU k)) : ISem G t u B.
Proof.
  destruct H as [[Ht Hu] HR].
  split; [split |].
  - exact (itot_conv G t A B k dA dB Ht IHA IHB IHc).
  - exact (itot_conv G u A B k dA dB Hu IHA IHB IHc).
  - intros rho Hrho k' F DB' x y Dx Dy.
    destruct (ityT_of_ITot G B k IHB rho Hrho) as [FB0 DB0].
    pose proof (ity_lvl rho rho eq_refl B k (ers rho B) FB0 k' (ers rho B) F
                  DB0 DB') as Ek; subst k'.
    destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA0 DA0].
    pose proof (ceq_of_IRel G A B k IHA IHB IHc
                  (FunTm_of_ty G A k dA) (FunTm_of_ty G B k dB)
                  rho Hrho FA0 DA0 F DB') as P.
    apply (kEqAt_of_kto F FA0 (knsymU _ _ P)).
    apply (HR rho Hrho k FA0 DA0);
      [ exact (i_conv rho t k (ers rho B) F (ers rho A) FA0 (ers rho t) x
                 (knsymU _ _ P) Dx)
      | exact (i_conv rho u k (ers rho B) F (ers rho A) FA0 (ers rho u) y
                 (knsymU _ _ P) Dy) ].
Qed.

(* ---- proof irrelevance: a Prf-family relates all of its elements, and at
     layer 1 all realisers of a Prf type are related. ---- *)
Lemma isem_prf_irr G kk p e e'
  (IHe : ITot G e (prf kk p)) (IHe' : ITot G e' (prf kk p)) :
  ISem G e e' (prf kk p).
Proof.
  split; [split; [exact IHe | exact IHe'] |].
  intros rho Hrho k F DP x y Dx Dy.
  pose proof (ity_lvl_dec rho (prf kk p) k (ers rho (prf kk p)) F DP) as El;
    cbn [LvlDec] in El; subst k.
  destruct (ity_prf_inv rho (prf kk p) kk (ers rho (prf kk p)) F DP)
    as [jp [wp [xp [Dp Hc]]]].
  pose proof (TotalFam_ceq (prfF kk xp) F (knsymU _ _ Hc)
                (prf_total kk jp wp xp)) as HT.
  apply HT.
  apply (Rel_prf_intro (ers rho (prf kk p)) (ers rho p));
    [ exists kk; exact (uf_ty F) | apply eval_whnf, whnf_prf ].
Qed.

(* The layer-1 side condition for a conversion, as fundamental_cv gives it. *)
Definition LCv (G : ctx) (t u A : tm) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> Rel (ers rho A) (ers rho t) (ers rho' u).

Lemma LCv_of_cv G t u A (c : cv G t u A) : LCv G t u A.
Proof.
  intros rho rho' [_ [_ [_ HS]]].
  exact (proj1 (fundamental_cv G t u A c _ _ HS)).
Qed.

(* ---- a congruence at a UNIVERSE: the two values are codes, so what has to
     be shown is that the two families are equal and their realisers layer-1
     equal -- which is the universe's own equality (uEq_of). ---- *)
Lemma isem_former_cv G (t u : tm) (k : nat)
  (Htot : ITot G t (UU k)) (Hutot : ITot G u (UU k))
  (Hsht : forall rho k' Sy (F : kUFam k' Sy) w (x : kElAt F w),
            TmShape rho t k' Sy F w x -> TyVal rho t k' Sy F w x)
  (Hshu : forall rho k' Sy (F : kUFam k' Sy) w (x : kElAt F w),
            TmShape rho u k' Sy F w x -> TyVal rho u k' Sy F w x)
  (Hfam : forall rho (Hrho : EnvITy G rho) F1 F2,
            ITy rho t k (ers rho t) F1 -> ITy rho u k (ers rho u) F2 ->
            (eqty k (ers rho t) (ers rho u) * kceq (kAt F1) (kAt F2))%type) :
  ISem G t u (UU k).
Proof.
  split; [split; [exact Htot | exact Hutot] |].
  intros rho Hrho k' F DU x y Dx Dy.
  pose proof (ity_lvl_dec rho (UU k) k' (ers rho (UU k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (itm_inv rho t (S k) (ers rho (UU k)) F (ers rho t) x Dx) as E.
  pose proof (itm_inv rho u (S k) (ers rho (UU k)) F (ers rho u) y Dy) as E'.
  cbn [TmInv] in E, E'.
  (* a universe is not a Prf, so the proof alternative is out on both sides *)
  destruct E as [[_ [q0 Hq0]] | E];
    [ solve [exfalso; refine (NotPrfR_univ k q0 _);
             eapply tyeq_trans; [| exact Hq0]; exists (S k); exact (uf_ty F)] |].
  destruct E' as [[_ [q0 Hq0]] | E'];
    [ solve [exfalso; refine (NotPrfR_univ k q0 _);
             eapply tyeq_trans; [| exact Hq0]; exists (S k); exact (uf_ty F)] |].
  apply Hsht in E; apply Hshu in E'; cbn [TyVal Shaped] in E, E'.
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct (Hfam rho Hrho (ty_F0 d1) (ty_F0 d2) (ty_D d1) (ty_D d2))
    as [Hty Hi].
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x].
  apply (proj1 (kRel_same (univFam k) _ _ _ _)).
  apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
  exact (famCeq_all (ty_F0 d1) (ty_F0 d2) Hi v h pf v' h' pf').
Qed.

(* The equality a conversion of types gives, at interpretations SUPPLIED by
   the caller: simpler than ceq_of_IRel, which has to build them. *)
Lemma ceq_of_IRel_at G t u k (HR : IRel G t u (UU k))
  rho (Hrho : EnvITy G rho)
  (F1 : kUFam k (ers rho t)) (D1 : ITy rho t k (ers rho t) F1)
  (F2 : kUFam k (ers rho u)) (D2 : ITy rho u k (ers rho u) F2) :
  kceq (kAt F1) (kAt F2).
Proof.
  pose proof (HR rho Hrho (S k) (univFam k)
                (ity_univ rho (S k) 0 k eq_refl (ers rho (UU k)) eq_refl)
                (famEl F1) (famEl F2)
                (i_ty rho t k (ers rho t) F1 D1)
                (i_ty rho u k (ers rho u) F2 D2)) as Heq.
  pose proof (uEq_at (famEl F1) (famEl F2) Heq) as Hi.
  rewrite !elFam_famEl in Hi.
  exact Hi.
Qed.

(* the same with the realisers left general: an inversion hands back a family
   at a realiser that is only PROVABLY the erasure. *)
Lemma ceq_of_IRel_at' G t u k (HR : IRel G t u (UU k))
  rho (Hrho : EnvITy G rho)
  w1 (F1 : kUFam k w1) (D1 : ITy rho t k w1 F1)
  w2 (F2 : kUFam k w2) (D2 : ITy rho u k w2 F2) :
  kceq (kAt F1) (kAt F2).
Proof.
  assert (E1 : w1 = ers rho t) by exact (ers_of_ITy _ _ _ _ _ D1).
  assert (E2 : w2 = ers rho u) by exact (ers_of_ITy _ _ _ _ _ D2).
  subst w1 w2.
  exact (ceq_of_IRel_at G t u k HR rho Hrho F1 D1 F2 D2).
Qed.

(* the layer-1 equality of two convertible TYPES, at their level *)
Definition LCvK (G : ctx) (A A' : tm) (k : nat) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> eqty k (ers rho A) (ers rho' A').

Lemma LCvK_of_cv G A A' k (c : cv G A A' (UU k)) : LCvK G A A' k.
Proof.
  intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_cv_U G A A' k c _ _ HS).
Qed.


(* ---- the congruences at Pi, Sigma and W.  The three differ only in the
     inversion and the family, so the WORK is done once here: given the two
     readings' decoded data, the domains are equal and the codomains are equal
     at related arguments -- exactly the two premises piFam_ceq, sigFam_ceq and
     wFam_ceq ask for.

     The codomains are compared in TWO steps: first B against B' in the SAME
     environment (the conversion's own induction hypothesis), then B' against
     itself across the two environments extended by the EQUAL domains
     (functionality).  The second step is what needed EnvOf to be closed under
     conversion -- the first environment's entry carries A's family while the
     context says A'.

     The component LEVELS are existentials of the inversion, and they are
     pinned against the syntactic ones by ity_lvl: the domain's outside, the
     codomain's INSIDE the per-argument obligation, because pinning it needs a
     reading of B in an extended environment and hence an argument to extend
     with. ---- *)

Lemma isem_binder_ceq G A A' B B' k i j
  (dB' : ty (A' :: G) B' (UU j))
  (IHB : ITot (A :: G) B (UU j)) (IHB' : ITot (A' :: G) B' (UU j))
  (IHcA : IRel G A A' (UU i)) (IHcB : IRel (A :: G) B B' (UU j))
  rho (Hrho : EnvITy G rho)
  dA1 (EA1 : dA1 + i = k) (FA1 : kUFam i (ers rho A))
  j1 dB1 (EB1 : dB1 + j1 = k)
  (wB1 : forall u, kElAt (upF dA1 k EA1 FA1) u -> etm)
  (FB1 : forall u x, kUFam j1 (wB1 u x))
  (DA1 : ITy rho A i (ers rho A) FA1)
  (DB1 : forall u x,
     ITy (ext rho FA1 u (dnEl dA1 k EA1 FA1 u x)) B j1 (wB1 u x) (FB1 u x))
  dA2 (EA2 : dA2 + i = k) (FA2 : kUFam i (ers rho A'))
  j2 dB2 (EB2 : dB2 + j2 = k)
  (wB2 : forall u, kElAt (upF dA2 k EA2 FA2) u -> etm)
  (FB2 : forall u x, kUFam j2 (wB2 u x))
  (DA2 : ITy rho A' i (ers rho A') FA2)
  (DB2 : forall u x,
     ITy (ext rho FA2 u (dnEl dA2 k EA2 FA2 u x)) B' j2 (wB2 u x) (FB2 u x)) :
  (kceq (kAt (upF dA1 k EA1 FA1)) (kAt (upF dA2 k EA2 FA2)) *
   (forall u x u' x',
      kEqAt (upF dA1 k EA1 FA1) u x (upF dA2 k EA2 FA2) u' x' ->
      kceq (kAt (upF dB1 k EB1 (FB1 u x))) (kAt (upF dB2 k EB2 (FB2 u' x')))))%type.
Proof.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EdA : dA2 = dA1) by lia; subst dA2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
  assert (QA : kceq (kAt FA1) (kAt FA2))
    by exact (ceq_of_IRel_at G A A' i IHcA rho Hrho FA1 DA1 FA2 DA2).
  assert (HtyA : tyeq (ers rho A) (ers rho A')) by exact (ceq_ty FA1 FA2 QA).
  split; [exact (upF_ceq dA1 k EA1 FA1 FA2 QA) |].
  intros u x u' x' Hxx.
  (* the arguments, brought down to the domain's own level *)
  assert (Hd : kEqAt FA1 u (dnEl dA1 k EA1 FA1 u x)
                 FA2 u' (dnEl dA1 k EA1 FA2 u' x'))
    by exact (dnEl_eq dA1 k EA1 FA1 u x FA2 u' x' QA Hxx).
  pose proof (EnvITy_ext G rho A i FA1 DA1 u (dnEl dA1 k EA1 FA1 u x) Hrho)
    as HExA.
  pose proof (EnvITy_ext_ceq G rho A' i (ers rho A) FA1 FA2 DA2 QA u
                (dnEl dA1 k EA1 FA1 u x) Hrho) as HExA'.
  pose proof (EnvITy_ext G rho A' i FA2 DA2 u' (dnEl dA1 k EA1 FA2 u' x') Hrho)
    as HExA2.
  (* the codomains' reading levels are the syntactic one *)
  destruct (ityT_of_ITot (A :: G) B j IHB _ HExA) as [FBj DBj].
  pose proof (ity_lvl _ _ eq_refl B j1 _ (FB1 u x) j _ FBj (DB1 u x) DBj) as Ej1.
  destruct (ityT_of_ITot (A' :: G) B' j IHB' _ HExA2) as [FBj' DBj'].
  pose proof (ity_lvl _ _ eq_refl B' j2 _ (FB2 u' x') j _ FBj' (DB2 u' x') DBj')
    as Ej2.
  subst j1; subst j2.
  assert (EdB : dB2 = dB1) by lia; subst dB2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB2 EB1) as EEB; subst EB2.
  apply upF_ceq.
  destruct (ityT_of_ITot (A' :: G) B' j IHB' _ HExA') as [FBm DBm].
  eapply ktrU;
    [ exact (famAtWf (FB1 u x)) | exact (famAtWf FBm)
    | exact (famAtWf (FB2 u' x'))
    | exact (ceq_of_IRel_at' (A :: G) B B' j IHcB _ HExA
               _ (FB1 u x) (DB1 u x) _ FBm DBm) |].
  assert (HEr : EnvRelOf (A' :: G)
                  (ext rho FA1 u (dnEl dA1 k EA1 FA1 u x))
                  (ext rho FA2 u' (dnEl dA1 k EA1 FA2 u' x'))).
  { apply (EnvRelOf_ext_ty G rho rho A' i (ers rho A) (ers rho A')
             FA1 FA2 u _ u' _ HEself HtyA);
      [ exists i; exact (uf_ty FA2) | split; [exact QA | exact Hd] ]. }
  refine (FunTy_of_FunTm (A' :: G) B' (funtm (A' :: G) B' (UU j) dB')
            _ _ HEr j _ FBm _ (FB2 u' x') DBm (DB2 u' x') _).
  assert (Eb2 : wB2 u' x' = ers (ext rho FA2 u' (dnEl dA1 k EA1 FA2 u' x')) B')
    by exact (ers_of_ITy _ _ _ _ _ (DB2 u' x')).
  rewrite Eb2; exact (LTyK_of_ty (A' :: G) B' j dB' _ _ HEr).
Qed.

(* composing family equalities.  Every family's code is well formed, so the
   transitivity's side conditions are free -- which is why this wrapper is
   worth having: `ktrU` leaves the middle code to unification. *)
Lemma famCeq_tr {k w1 w2 w3} (F1 : kUFam k w1) (F2 : kUFam k w2) (F3 : kUFam k w3) :
  kceq (kAt F1) (kAt F2) -> kceq (kAt F2) (kAt F3) -> kceq (kAt F1) (kAt F3).
Proof.
  intros H1 H2.
  exact (ktrU (kAt F1) (kAt F2) (kAt F3)
           (famAtWf F1) (famAtWf F2) (famAtWf F3) H1 H2).
Qed.

Lemma famCeq_sym {k w1 w2} (F1 : kUFam k w1) (F2 : kUFam k w2) :
  kceq (kAt F1) (kAt F2) -> kceq (kAt F2) (kAt F1).
Proof. apply knsymU. Qed.

Lemma isem_pi G A A' B B' k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dA' : ty G A' (UU i)) (dB' : ty (A' :: G) B' (UU j))
  (cA : cv G A A' (UU i)) (cB : cv (A :: G) B B' (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHA' : ITot G A' (UU i)) (IHB' : ITot (A' :: G) B' (UU j))
  (IHcA : IRel G A A' (UU i)) (IHcB : IRel (A :: G) B B' (UU j)) :
  ISem G (pi k A B) (pi k A' B') (UU k).
Proof.
  apply (isem_former_cv G (pi k A B) (pi k A' B') k
           (itot_pi G A B k i j W Hik Hjk dA dB IHA IHB)
           (itot_pi G A' B' k i j W Hik Hjk dA' dB' IHA' IHB')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  assert (Hcv : eqty k (ers rho (pi k A B)) (ers rho (pi k A' B')))
    by exact (LCvK_of_cv G (pi k A B) (pi k A' B') k
                (c_pi G k i j A A' B B' Hik Hjk dA dB dA' dB' cA cB)
                rho rho (EnvRelOf_selfE G rho Hrho)).
  split; [exact Hcv |].
  destruct (ity_pi_inv rho (pi k A B) k _ F1 D1) as
    [i1 [j1 [dA1 [dB1 [EA1 [EB1 [wA1 [FA1 [B01 [wB1 [FB1 [redB1 [cohB1 [gPi1
      [[[DA1 DB1] Hw1] Hc1]]]]]]]]]]]]]]].
  destruct (ity_pi_inv rho (pi k A' B') k _ F2 D2) as
    [i2 [j2 [dA2 [dB2 [EA2 [EB2 [wA2 [FA2 [B02 [wB2 [FB2 [redB2 [cohB2 [gPi2
      [[[DA2 DB2] Hw2] Hc2]]]]]]]]]]]]]]].
  assert (E1 : wA1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA1); subst wA1.
  assert (E2 : wA2 = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA2); subst wA2.
  destruct (ityT_of_ITot G A i IHA rho Hrho) as [FAm DAm].
  destruct (ityT_of_ITot G A' i IHA' rho Hrho) as [FAm' DAm'].
  pose proof (ity_lvl _ _ eq_refl A i1 _ FA1 i _ FAm DA1 DAm) as Ei1; subst i1.
  pose proof (ity_lvl _ _ eq_refl A' i2 _ FA2 i _ FAm' DA2 DAm') as Ei2; subst i2.
  assert (Hty : tyeq (epi (ers rho A) B01) (epi (ers rho A') B02)).
  { eapply tyeq_trans; [apply tyeq_sym; exact Hw1 |].
    eapply tyeq_trans; [| exact Hw2]; exists k; exact Hcv. }
  destruct (isem_binder_ceq G A A' B B' k i j dB' IHB IHB' IHcA IHcB rho Hrho
              dA1 EA1 FA1 j1 dB1 EB1 wB1 FB1 DA1 DB1
              dA2 EA2 FA2 j2 dB2 EB2 wB2 FB2 DA2 DB2) as [HQA HQB].
  refine (famCeq_tr _ _ _ Hc1 (famCeq_tr _ _ _ _ (famCeq_sym _ _ Hc2))).
  apply piFam_ceq; [exact Hty | exact HQA | exact HQB].
Qed.

Lemma isem_sig G A A' B B' k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dA' : ty G A' (UU i)) (dB' : ty (A' :: G) B' (UU j))
  (cA : cv G A A' (UU i)) (cB : cv (A :: G) B B' (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHA' : ITot G A' (UU i)) (IHB' : ITot (A' :: G) B' (UU j))
  (IHcA : IRel G A A' (UU i)) (IHcB : IRel (A :: G) B B' (UU j)) :
  ISem G (sig_ k A B) (sig_ k A' B') (UU k).
Proof.
  apply (isem_former_cv G (sig_ k A B) (sig_ k A' B') k
           (itot_sig G A B k i j W Hik Hjk dA dB IHA IHB)
           (itot_sig G A' B' k i j W Hik Hjk dA' dB' IHA' IHB')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  assert (Hcv : eqty k (ers rho (sig_ k A B)) (ers rho (sig_ k A' B')))
    by exact (LCvK_of_cv G (sig_ k A B) (sig_ k A' B') k
                (c_sig G k i j A A' B B' Hik Hjk dA dB dA' dB' cA cB)
                rho rho (EnvRelOf_selfE G rho Hrho)).
  split; [exact Hcv |].
  destruct (ity_sig_inv rho (sig_ k A B) k _ F1 D1) as
    [i1 [j1 [dA1 [dB1 [EA1 [EB1 [wA1 [FA1 [B01 [wB1 [FB1 [redB1 [cohB1 [gSig1
      [[[DA1 DB1] Hw1] Hc1]]]]]]]]]]]]]]].
  destruct (ity_sig_inv rho (sig_ k A' B') k _ F2 D2) as
    [i2 [j2 [dA2 [dB2 [EA2 [EB2 [wA2 [FA2 [B02 [wB2 [FB2 [redB2 [cohB2 [gSig2
      [[[DA2 DB2] Hw2] Hc2]]]]]]]]]]]]]]].
  assert (E1 : wA1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA1); subst wA1.
  assert (E2 : wA2 = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA2); subst wA2.
  destruct (ityT_of_ITot G A i IHA rho Hrho) as [FAm DAm].
  destruct (ityT_of_ITot G A' i IHA' rho Hrho) as [FAm' DAm'].
  pose proof (ity_lvl _ _ eq_refl A i1 _ FA1 i _ FAm DA1 DAm) as Ei1; subst i1.
  pose proof (ity_lvl _ _ eq_refl A' i2 _ FA2 i _ FAm' DA2 DAm') as Ei2; subst i2.
  assert (Hty : tyeq (esig (ers rho A) B01) (esig (ers rho A') B02)).
  { eapply tyeq_trans; [apply tyeq_sym; exact Hw1 |].
    eapply tyeq_trans; [| exact Hw2]; exists k; exact Hcv. }
  destruct (isem_binder_ceq G A A' B B' k i j dB' IHB IHB' IHcA IHcB rho Hrho
              dA1 EA1 FA1 j1 dB1 EB1 wB1 FB1 DA1 DB1
              dA2 EA2 FA2 j2 dB2 EB2 wB2 FB2 DA2 DB2) as [HQA HQB].
  refine (famCeq_tr _ _ _ Hc1 (famCeq_tr _ _ _ _ (famCeq_sym _ _ Hc2))).
  apply sigFam_ceq; [exact Hty | exact HQA | exact HQB].
Qed.

Lemma isem_w G A A' B B' k i j (W : Rules.wfc G) (Hik : i <= k) (Hjk : j <= k)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dA' : ty G A' (UU i)) (dB' : ty (A' :: G) B' (UU j))
  (cA : cv G A A' (UU i)) (cB : cv (A :: G) B B' (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHA' : ITot G A' (UU i)) (IHB' : ITot (A' :: G) B' (UU j))
  (IHcA : IRel G A A' (UU i)) (IHcB : IRel (A :: G) B B' (UU j)) :
  ISem G (wt k A B) (wt k A' B') (UU k).
Proof.
  apply (isem_former_cv G (wt k A B) (wt k A' B') k
           (itot_wt G A B k i j W Hik Hjk dA dB IHA IHB)
           (itot_wt G A' B' k i j W Hik Hjk dA' dB' IHA' IHB')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  assert (Hcv : eqty k (ers rho (wt k A B)) (ers rho (wt k A' B')))
    by exact (LCvK_of_cv G (wt k A B) (wt k A' B') k
                (c_w G k i j A A' B B' Hik Hjk dA dB dA' dB' cA cB)
                rho rho (EnvRelOf_selfE G rho Hrho)).
  split; [exact Hcv |].
  destruct (ity_w_inv rho (wt k A B) k _ F1 D1) as
    [i1 [j1 [dA1 [dB1 [EA1 [EB1 [wA1 [FA1 [B01 [wB1 [FB1 [redB1 [cohB1 [gW1
      [[[DA1 DB1] Hw1] Hc1]]]]]]]]]]]]]]].
  destruct (ity_w_inv rho (wt k A' B') k _ F2 D2) as
    [i2 [j2 [dA2 [dB2 [EA2 [EB2 [wA2 [FA2 [B02 [wB2 [FB2 [redB2 [cohB2 [gW2
      [[[DA2 DB2] Hw2] Hc2]]]]]]]]]]]]]]].
  assert (E1 : wA1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA1); subst wA1.
  assert (E2 : wA2 = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA2); subst wA2.
  destruct (ityT_of_ITot G A i IHA rho Hrho) as [FAm DAm].
  destruct (ityT_of_ITot G A' i IHA' rho Hrho) as [FAm' DAm'].
  pose proof (ity_lvl _ _ eq_refl A i1 _ FA1 i _ FAm DA1 DAm) as Ei1; subst i1.
  pose proof (ity_lvl _ _ eq_refl A' i2 _ FA2 i _ FAm' DA2 DAm') as Ei2; subst i2.
  assert (Hty : tyeq (ew (ers rho A) B01) (ew (ers rho A') B02)).
  { eapply tyeq_trans; [apply tyeq_sym; exact Hw1 |].
    eapply tyeq_trans; [| exact Hw2]; exists k; exact Hcv. }
  destruct (isem_binder_ceq G A A' B B' k i j dB' IHB IHB' IHcA IHcB rho Hrho
              dA1 EA1 FA1 j1 dB1 EB1 wB1 FB1 DA1 DB1
              dA2 EA2 FA2 j2 dB2 EB2 wB2 FB2 DA2 DB2) as [HQA HQB].
  refine (famCeq_tr _ _ _ Hc1 (famCeq_tr _ _ _ _ (famCeq_sym _ _ Hc2))).
  apply wFam_ceq; [exact Hty | exact HQA | exact HQB].
Qed.

(* ---- the lift, Prf and the successor ---- *)

Lemma isem_up G A A' k (W : Rules.wfc G)
  (dA : ty G A (UU k)) (dA' : ty G A' (UU k)) (cA : cv G A A' (UU k))
  (IHA : ITot G A (UU k)) (IHA' : ITot G A' (UU k))
  (IHcA : IRel G A A' (UU k)) :
  ISem G (up k A) (up k A') (UU (S k)).
Proof.
  apply (isem_former_cv G (up k A) (up k A') (S k)
           (itot_up G A k W dA IHA) (itot_up G A' k W dA' IHA')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  split.
  - apply (eqty_cumul k (S k)); [apply Nat.le_succ_diag_r |].
    exact (LCvK_of_cv G A A' k cA rho rho (EnvRelOf_selfE G rho Hrho)).
  - destruct (ity_up_inv rho (up k A) (S k) _ F1 D1) as [F1a [[Ej DA1] Hc1]].
    destruct (ity_up_inv rho (up k A') (S k) _ F2 D2) as [F2a [[Ej' DA2] Hc2]].
    refine (famCeq_tr _ _ _ Hc1 (famCeq_tr _ _ _ _ (famCeq_sym _ _ Hc2))).
    apply famLiftK_ceq.
    exact (ceq_of_IRel_at' G A A' k IHcA rho Hrho _ F1a DA1 _ F2a DA2).
Qed.

Lemma isem_prf G kk j p p' (Hjk : j <= kk) (W : Rules.wfc G)
  (dp : ty G p (prop j)) (dp' : ty G p' (prop j))
  (cp : cv G p p' (prop j)) (IHp : ITot G p (prop j)) (IHp' : ITot G p' (prop j))
  (IHc : IRel G p p' (prop j)) : ISem G (prf kk p) (prf kk p') (UU kk).
Proof.
  apply (isem_former_cv G (prf kk p) (prf kk p') kk
           (itot_prf G kk j p Hjk W dp IHp) (itot_prf G kk j p' Hjk W dp' IHp')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  destruct (ity_prf_inv rho (prf kk p) kk _ F1 D1) as [j1 [wp [xp [Dp Hc1]]]].
  destruct (ity_prf_inv rho (prf kk p') kk _ F2 D2) as [j2 [wp' [xp' [Dp' Hc2]]]].
  (* the propositions are read at the syntactic level: a Prop is not a Prf *)
  pose proof (itm_lvl p rho rho eq_refl _ _ _ _ _ NotPrfR_prop Dp
                _ _ _ _ _ NotPrfR_prop
                (projT2 (IHp rho Hrho j (propFam j)
                           (ity_prop rho j (ers rho (prop j)) eq_refl))))
    as Ej1; subst j1.
  pose proof (itm_lvl p' rho rho eq_refl _ _ _ _ _ NotPrfR_prop Dp'
                _ _ _ _ _ NotPrfR_prop
                (projT2 (IHp' rho Hrho j (propFam j)
                           (ity_prop rho j (ers rho (prop j)) eq_refl))))
    as Ej2; subst j2.
  assert (Ep : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ep' : wp' = ers rho p') by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  subst wp wp'.
  pose proof (IHc rho Hrho j (propFam j)
                (ity_prop rho j (ers rho (prop j)) eq_refl) xp xp' Dp Dp') as Hxx.
  destruct (proj1 (propEq_iff xp xp') Hxx) as [Hiff Hrelp].
  assert (Hpr : PR (ers rho p) (ers rho p'))
    by exact (Rel_prop_elim eprop _ _ (eval_whnf _ whnf_prop) Hrelp).
  split.
  - exact (eqty_prf kk (ers rho (prf kk p)) (ers rho (prf kk p'))
             (ers rho p) (ers rho p')
             (eval_whnf _ (whnf_prf _)) (eval_whnf _ (whnf_prf _)) Hpr).
  - refine (famCeq_tr _ _ _ Hc1 (famCeq_tr _ _ _ _ (famCeq_sym _ _ Hc2))).
    apply prfFam_ceq;
      [ exists kk;
        exact (eqty_prf kk (eprf (ers rho p)) (eprf (ers rho p'))
                 (ers rho p) (ers rho p')
                 (eval_whnf _ (whnf_prf _)) (eval_whnf _ (whnf_prf _)) Hpr)
      | exact Hiff ].
Qed.

(* ---- IRel, which compares two terms at ONE family, against kRel, which
     compares them at two.  The move is the coercion along the two families'
     equality -- available because the type is functional -- and the two
     coherences cancel it. ---- *)

Lemma kRel_of_IRel G (t u A : tm) (HR : IRel G t u A) (fA : FunTm G A)
  rho (Hrho : EnvITy G rho) k (F F' : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D' : ITy rho A k (ers rho A) F')
  x y (Dx : ITm rho t k (ers rho A) F (ers rho t) x)
      (Dy : ITm rho u k (ers rho A) F' (ers rho u) y) :
  kRel F (ers rho t) x F' (ers rho u) y.
Proof.
  pose proof (ity_same_ceq G A fA rho Hrho k F F' D D') as P.
  split; [exact P |].
  assert (Dy0 : ITm rho u k (ers rho A) F (ers rho u)
                  (kto (kAt F') (kAt F) (famAtWf F') (famAtWf F)
                     (knsymU _ _ P) (ers rho u) y))
    by exact (i_conv rho u k (ers rho A) F' (ers rho A) F (ers rho u) y
                (knsymU _ _ P) Dy).
  eapply kEqAt_trans;
    [ exact (famAtSelf F) | exact (HR rho Hrho k F D x _ Dx Dy0) |].
  apply kEqAt_sym.
  exact (kto_coh (kAt F') (kAt F) (famAtWf F') (famAtWf F)
           (knsymU _ _ P) (ers rho u) y).
Qed.

(* the realiser-general form: an inversion hands back families and values at
   realisers that are only PROVABLY the erasures *)
Lemma kRel_of_IRel' G (t u A : tm) (HR : IRel G t u A) (fA : FunTm G A)
  rho (Hrho : EnvITy G rho) k w (F : kUFam k w) w' (F' : kUFam k w')
  (D : ITy rho A k w F) (D' : ITy rho A k w' F')
  wt (x : kElAt F wt) wu (y : kElAt F' wu)
  (Dx : ITm rho t k w F wt x) (Dy : ITm rho u k w' F' wu y) :
  kRel F wt x F' wu y.
Proof.
  assert (E : w = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D).
  assert (E' : w' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D').
  subst w w'.
  assert (Et : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dx).
  assert (Eu : wu = ers rho u) by exact (ers_of_ITm _ _ _ _ _ _ _ Dy).
  subst wt wu.
  exact (kRel_of_IRel G t u A HR fA rho Hrho k F F' D D' x y Dx Dy).
Qed.

(* The level a reading of a term sits at is the one its TYPE's canonical
   reading sits at: level functionality, with the proof clause ruled out on
   both sides. *)
Lemma lvl_of_ITot G p T (IHp : ITot G p T) rho (Hrho : EnvITy G rho)
  kT (FT : kUFam kT (ers rho T)) (DT : ITy rho T kT (ers rho T) FT)
  (HnT : NotPrfR (ers rho T))
  k Sy (F : kUFam k Sy) w x (Hnp : NotPrfR Sy) (D : ITm rho p k Sy F w x) :
  k = kT.
Proof.
  destruct (IHp rho Hrho kT FT DT) as [x0 D0].
  exact (itm_lvl p rho rho eq_refl k Sy F w x Hnp D kT (ers rho T) FT _ x0 HnT D0).
Qed.

Lemma isem_succ G j n n' (W : Rules.wfc G) (dn : ty G n (nat_ j))
  (dn' : ty G n' (nat_ j)) (cn : cv G n n' (nat_ j))
  (IHn : ITot G n (nat_ j)) (IHn' : ITot G n' (nat_ j))
  (IHc : IRel G n n' (nat_ j)) : ISem G (succ n) (succ n') (nat_ j).
Proof.
  split;
    [split; [exact (itot_succ G W j n IHn) | exact (itot_succ G W j n' IHn')] |].
  intros rho Hrho k F DN x y Dx Dy.
  pose proof (ity_lvl_dec rho (nat_ j) k (ers rho (nat_ j)) F DN) as El;
    cbn [LvlDec] in El; subst k.
  pose proof (LCv_of_cv G (succ n) (succ n') (nat_ j)
                (c_succ G j n n' dn dn' cn) rho rho
                (EnvRelOf_selfE G rho Hrho)) as Hrel.
  pose proof (itm_inv rho (succ n) j (ers rho (nat_ j)) F
                (ers rho (succ n)) x Dx) as E.
  pose proof (itm_inv rho (succ n') j (ers rho (nat_ j)) F
                (ers rho (succ n')) y Dy) as E'.
  cbn [TmInv TmShape SuccVal Shaped] in E, E'.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [[wn xn Dn] Hv]; destruct E' as [[wn' xn' Dn'] Hv'].
  cbn [sc_wn sc_xn sc_D] in Hv, Hv', Dn, Dn' |- *.
  assert (Ewn : wn = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn).
  assert (Ewn' : wn' = ers rho n') by exact (ers_of_ITm _ _ _ _ _ _ _ Dn').
  subst wn wn'.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x sc_wn sc_xn].
  apply (proj1 (kRel_same (natFam j) _ _ _ _)).
  apply natSucc_eq.
  exact (IHc rho Hrho j (natFam j) (ity_nat rho j (ers rho (nat_ j)) eq_refl)
           xn xn' Dn Dn').
Qed.

Lemma isem_uptm G A t t' k (W : Rules.wfc G) (dA : ty G A (UU k))
  (dt : ty G t A) (dt' : ty G t' A) (ct : cv G t t' A)
  (IHA : ITot G A (UU k)) (IHt : ITot G t A) (IHt' : ITot G t' A)
  (IHc : IRel G t t' A) : ISem G (uptm A t) (uptm A t') (up k A).
Proof.
  split; [split; [exact (itot_uptm G A t k dA dt IHA IHt)
                 | exact (itot_uptm G A t' k dA dt' IHA IHt')] |].
  intros rho Hrho k' F DU x y Dx Dy.
  pose proof (ity_lvl_dec rho (up k A) k' (ers rho (up k A)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (itm_inv rho (uptm A t) (S k) (ers rho (up k A)) F
                (ers rho (uptm A t)) x Dx) as E.
  pose proof (itm_inv rho (uptm A t') (S k) (ers rho (up k A)) F
                (ers rho (uptm A t')) y Dy) as E'.
  cbn [TmInv TmShape UpTmVal Shaped] in E, E'.
  pose proof (LCv_of_cv G (uptm A t) (uptm A t') (up k A)
                (c_up_tm G k A t t' dA dt dt' ct) rho rho
                (EnvRelOf_selfE G rho Hrho)) as Hrelu.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrelu) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrelu) |].
  destruct E as [[Sy1 F1 x1 DA1 D1] Hv].
  destruct E' as [[Sy1' F1' x1' DA1' D1'] Hv'].
  cbn [ut_Sy ut_F ut_x ut_DA ut_D] in Hv, Hv', DA1, DA1', D1, D1' |- *.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  cbn [cn_Sy cn_F cn_w cn_x ut_Sy ut_F ut_x].
  apply kRel_lift.
  exact (kRel_of_IRel' G t t' A IHc (FunTm_of_ty G A k dA) rho Hrho k
           _ F1 _ F1' DA1 DA1' _ x1 _ x1' D1 D1').
Qed.

(* ---- the projections.  The shape of the proof is funtm_fst's, with one
     change: the two subjects are DIFFERENT terms read in ONE environment, so
     what relates their values is kRel_of_IRel' (the conversion's induction
     hypothesis) instead of functionality.  The two decoded Sigma-realisers
     are then literally equal -- both are `ers rho (sig_ kk A B)` -- which is
     what makes the two readings comparable at all. ---- *)

Lemma isem_fst G kk i j A B p p' (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dp : ty G p (sig_ kk A B)) (dp' : ty G p' (sig_ kk A B))
  (cp : cv G p p' (sig_ kk A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ kk A B)) (IHp' : ITot G p' (sig_ kk A B))
  (IHc : IRel G p p' (sig_ kk A B)) : ISem G (fst A B p) (fst A B p') A.
Proof.
  split;
    [split; [exact (itot_fst G A B p kk i j Hik Hjk dA dB dp IHA IHB IHp)
            | exact (itot_fst G A B p' kk i j Hik Hjk dA dB dp' IHA IHB IHp')] |].
  intros rho Hrho k F DFA x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (itm_inv rho (fst A B p) k (ers rho A) F
                (ers rho (fst A B p)) x Dx) as E.
  pose proof (itm_inv rho (fst A B p') k (ers rho A) F
                (ers rho (fst A B p')) y Dy) as E'.
  cbn [TmInv TmShape FstVal Shaped] in E, E'.
  pose proof (LCv_of_cv G (fst A B p) (fst A B p') A
                (c_fst G kk i j A B p p' Hik Hjk dA dB dp dp' cp)
                rho rho HEself) as Hrel.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct d1 as
    [ks j1 dA1 dB1 EA1 EB1 wA FA B0 wB FB redB cohB gSig wp xp Ep DA DB Dp].
  destruct d2 as
    [ks' j2 dA2 dB2 EA2 EB2 wA' FA' B0' wB' FB' redB' cohB' gSig' wp' xp'
     Ep' DA' DB' Dp'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold fd_val in Hv, Hv'.
  cbn [fd_ks fd_j fd_dA fd_dB fd_EA fd_EB fd_wA fd_FA fd_B0 fd_wB fd_FB
       fd_redB fd_cohB fd_gSig fd_wp fd_xp] in Hv, Hv'.
  (* both Sigma-readings sit at the type's annotation *)
  destruct (build_sig G A B kk i j Hik Hjk dA dB IHA IHB rho Hrho) as [FS DS].
  pose proof (lvl_of_ITot G p (sig_ kk A B) IHp rho Hrho kk FS DS
                (NotPrfR_sig _ _) ks _ _ _ xp (NotPrfR_sig _ _) Dp) as Eks.
  pose proof (lvl_of_ITot G p' (sig_ kk A B) IHp' rho Hrho kk FS DS
                (NotPrfR_sig _ _) ks' _ _ _ xp' (NotPrfR_sig _ _) Dp') as Eks'.
  destruct Eks; destruct Eks'.
  (* and their realisers are the same erasure, so the domains' are too *)
  assert (Esig : esig wA B0 = esig wA' B0') by (rewrite Ep, Ep'; reflexivity).
  injection Esig as EwA EB0; subst wA' B0'.
  assert (EdA : dA2 = dA1) by lia; subst dA2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
  assert (EwA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA); subst wA.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho k FA FA' DA DA').
  destruct (comp_ceq G A B (LTy_of_ty G A i dA) (LTy_of_ty (A :: G) B j dB)
              (funtm G A (UU i) dA) (funtm (A :: G) B (UU j) dB)
              rho rho HEself ks'
              k j1 dA1 dB1 EA1 EB1 _ FA wB FB
              k j2 dA1 dB2 EA1 EB2 _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  pose proof (kRel_of_IRel' G p p' (sig_ ks' A B) IHc
                (FunTm_of_ty G (sig_ ks' A B) ks'
                   (t_sig G ks' i j A B Hik Hjk dA dB))
                rho Hrho ks' _ _ _ _
                (ity_sig rho A B ks' k j1 dA1 dB1 EA1 EB1 _ FA B0 wB FB
                   redB cohB gSig Ep DA DB)
                (ity_sig rho A B ks' k j2 dA1 dB2 EA1 EB2 _ FA' B0 wB' FB'
                   redB' cohB' gSig' Ep' DA' DB')
                _ xp _ xp' Dp Dp') as Hx.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dA1 ks' EA1 FA FA' HA).
  split; [exact HAu |].
  eapply sigFst_eqX; [exact HAu | exact (kRel_at Hx)].
Qed.

(* The RIGHT-hand subject of a `snd` conversion, read at the LEFT-hand
   subject's type.  c_snd's conclusion type is `B [(fst A B p)..]`, taken at
   the left projection, so the right subject's own value -- which lives at the
   codomain instance taken at ITS projection -- has to travel along the
   codomain's coherence at the two (related) projections.  That is cod_ceq
   applied to sigFst_eq, and it is the only thing this proof adds to
   itot_snd. *)
Lemma itot_snd' G A B p p' k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dp : ty G p (sig_ k A B)) (dp' : ty G p' (sig_ k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ k A B)) (IHp' : ITot G p' (sig_ k A B))
  (IHc : IRel G p p' (sig_ k A B)) : ITot G (snd A B p') (B [(fst A B p)..]).
Proof.
  intros rho Hrho k' F DBs.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig) Dsig)
    as [xp Dp].
  destruct (IHp' rho Hrho k
              (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig) Dsig)
    as [xp' Dp'].
  pose proof (IHc rho Hrho k
                (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                   (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig)
                Dsig xp xp' Dp Dp') as Hpp.
  pose (xf := sigFst k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig
                (ers rho p) xp).
  pose (xf' := sigFst k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig
                 (ers rho p') xp').
  assert (Hfst : kEqAt (upF (k - i) k EA FA) (efst (ers rho p)) xf
                   (upF (k - i) k EA FA) (efst (ers rho p')) xf')
    by exact (sigFst_eq k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig
                (ers rho p) xp (ers rho p') xp' Hpp).
  pose proof (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) rho rho
                (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA
                (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
                (famAtSelf FA) DB DB _ xf _ xf' Hfst) as Pfam.
  pose proof (i_snd rho A B p' k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho p') xp' eq_refl DFA DB Dp')
    as Dsnd'.
  pose proof (i_conv rho (snd A B p') j _ _ _ _ _ _ (knsymU _ _ Pfam) Dsnd')
    as Dsnd.
  (* the conclusion's type, as in itot_snd *)
  assert (E : ers (ext rho FA (efst (ers rho p))
                     (dnEl (k - i) k EA FA (efst (ers rho p)) xf)) B
              = ers rho (B [(fst A B p)..]))
    by exact (eq_sym (ers_sub1 rho B (fst A B p) FA _)).
  pose proof (i_fst rho A B p k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  pose proof (isubst_ITy rho (fst A B p) i (ers rho A) FA (efst (ers rho p)) _
                eq_refl Dfst B j _ _ (DB (efst (ers rho p)) xf)) as DBsub.
  pose proof (ITy_cast rho (B [(fst A B p)..]) j _ _ E _ DBsub) as DBc.
  assert (Hfun : FunTm G (B [(fst A B p)..])).
  { destruct (ty_subst1 G A B (UU j) (fst A B p) dBt
                (t_fst G k i j A B p Hik Hjk dAt dBt dp)) as [dsub].
    exact (FunTm_of_ty G (B [(fst A B p)..]) j dsub). }
  pose proof (ity_lvl rho rho eq_refl (B [(fst A B p)..]) j
                (ers rho (B [(fst A B p)..])) (famCast E _)
                k' (ers rho (B [(fst A B p)..])) F DBc DBs) as Ek; subst k'.
  refine (itot_move G (snd A B p') (B [(fst A B p)..]) Hfun rho Hrho j F
            (famCast E _) DBs DBc _ _).
  refine (ITm_cast rho (snd A B p') j _ _ E _ _ _ _).
  exact Dsnd.
Qed.

(* `snd`'s conversion case.  As in isem_fst, the two decoded Sigma-realisers
   are the same erasure, so the readings are comparable; the value then comes
   down from the codomain's annotation by kRel_dn, along the codomain
   coherence at the two projections (cod_ceq of sigFst_eqX). *)
Lemma isem_snd G kk i j A B p p' (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dp : ty G p (sig_ kk A B)) (dp' : ty G p' (sig_ kk A B))
  (cp : cv G p p' (sig_ kk A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ kk A B)) (IHp' : ITot G p' (sig_ kk A B))
  (IHc : IRel G p p' (sig_ kk A B)) :
  ISem G (snd A B p) (snd A B p') (B [(fst A B p)..]).
Proof.
  split;
    [split; [exact (itot_snd G A B p kk i j Hik Hjk dA dB dp IHA IHB IHp)
            | exact (itot_snd' G A B p p' kk i j Hik Hjk dA dB dp dp'
                       IHA IHB IHp IHp' IHc)] |].
  intros rho Hrho k F DBs x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (itm_inv rho (snd A B p) k (ers rho (B [(fst A B p)..])) F
                (ers rho (snd A B p)) x Dx) as E.
  pose proof (itm_inv rho (snd A B p') k (ers rho (B [(fst A B p)..])) F
                (ers rho (snd A B p')) y Dy) as E'.
  cbn [TmInv TmShape SndVal Shaped] in E, E'.
  pose proof (LCv_of_cv G (snd A B p) (snd A B p') (B [(fst A B p)..])
                (c_snd G kk i j A B p p' Hik Hjk dA dB dp dp' cp)
                rho rho HEself) as Hrel.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct d1 as
    [ks i1 dA1 dB1 EA1 EB1 wA FA B0 wB FB redB cohB gSig wp xp Ep DA DB Dp].
  destruct d2 as
    [ks' i2 dA2 dB2 EA2 EB2 wA' FA' B0' wB' FB' redB' cohB' gSig' wp' xp'
     Ep' DA' DB' Dp'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold sd_val, sd_fst in Hv, Hv'.
  cbn [sd_ks sd_i sd_dA sd_dB sd_EA sd_EB sd_wA sd_FA sd_B0 sd_wB sd_FB
       sd_redB sd_cohB sd_gSig sd_wp sd_xp] in Hv, Hv'.
  destruct (build_sig G A B kk i j Hik Hjk dA dB IHA IHB rho Hrho) as [FS DS].
  pose proof (lvl_of_ITot G p (sig_ kk A B) IHp rho Hrho kk FS DS
                (NotPrfR_sig _ _) ks _ _ _ xp (NotPrfR_sig _ _) Dp) as Eks.
  pose proof (lvl_of_ITot G p' (sig_ kk A B) IHp' rho Hrho kk FS DS
                (NotPrfR_sig _ _) ks' _ _ _ xp' (NotPrfR_sig _ _) Dp') as Eks'.
  destruct Eks; destruct Eks'.
  assert (Esig : esig wA B0 = esig wA' B0') by (rewrite Ep, Ep'; reflexivity).
  injection Esig as EwA EB0; subst wA' B0'.
  pose proof (ity_lvl rho rho eq_refl A i1 _ FA i2 _ FA' DA DA') as Ei; subst i2.
  assert (EdA : dA2 = dA1) by lia; subst dA2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
  assert (EdB : dB2 = dB1) by lia; subst dB2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB2 EB1) as EEB; subst EB2.
  assert (EwA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA); subst wA.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i1 FA FA' DA DA').
  destruct (comp_ceq G A B (LTy_of_ty G A i dA) (LTy_of_ty (A :: G) B j dB)
              (funtm G A (UU i) dA) (funtm (A :: G) B (UU j) dB)
              rho rho HEself ks'
              i1 k dA1 dB1 EA1 EB1 _ FA wB FB
              i1 k dA1 dB1 EA1 EB1 _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  pose proof (kRel_of_IRel' G p p' (sig_ ks' A B) IHc
                (FunTm_of_ty G (sig_ ks' A B) ks'
                   (t_sig G ks' i j A B Hik Hjk dA dB))
                rho Hrho ks' _ _ _ _
                (ity_sig rho A B ks' i1 k dA1 dB1 EA1 EB1 _ FA B0 wB FB
                   redB cohB gSig Ep DA DB)
                (ity_sig rho A B ks' i1 k dA1 dB1 EA1 EB1 _ FA' B0 wB' FB'
                   redB' cohB' gSig' Ep' DA' DB')
                _ xp _ xp' Dp Dp') as Hx.
  pose proof (sigFst_eqX ks' (ers rho A) B0 (upF dA1 ks' EA1 FA) wB
                (fun u y0 => upF dB1 ks' EB1 (FB u y0)) redB cohB gSig
                (ers rho A) B0 (upF dA1 ks' EA1 FA') wB'
                (fun u y0 => upF dB1 ks' EB1 (FB' u y0)) redB' cohB' gSig'
                HAu wp xp wp' xp' (kRel_at Hx)) as Hf.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dB1 ks' EB1 _ _
           (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
              (funtm (A :: G) B (UU j) dB) rho rho HEself ks' i1 k dA1 EA1
              _ FA wB FB _ FA' wB' FB' DA DA' HA DB DB' _ _ _ _ Hf)).
  eapply sigSnd_eqX; [exact HAu | exact HBu | exact (kRel_at Hx)].
Qed.

(* ---- application ---- *)

(* The right-hand subject at the LEFT-hand type, as for the second projection:
   the codomain instances at the two (related) arguments are equal, by cod_ceq
   at the arguments lifted into the Pi's level. *)
Lemma itot_app' G A B f' u u' k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (df' : ty G f' (pi k A B)) (du : ty G u A) (du' : ty G u' A)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHf' : ITot G f' (pi k A B)) (IHu : ITot G u A) (IHu' : ITot G u' A)
  (IHcu : IRel G u u' A) : ITot G (app A B f' u') (B [u..]).
Proof.
  intros rho Hrho k' F DBu.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gPi := LTyK_of_ty G (pi k A B) k
                 (t_pi G k i j A B Hik Hjk dAt dBt) rho rho HEself).
  pose proof (ity_pi rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gPi eq_refl DFA DB) as Dpi.
  destruct (IHf' rho Hrho k
              (piFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                 (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gPi) Dpi)
    as [xf Df].
  destruct (IHu rho Hrho i FA DFA) as [xu Du].
  destruct (IHu' rho Hrho i FA DFA) as [xu' Du'].
  pose proof (IHcu rho Hrho i FA DFA xu xu' Du Du') as Huu.
  (* the codomain at the two arguments, lifted into the Pi's level *)
  pose proof (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) rho rho HEself k i j (k - i) EA
                (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
                (famAtSelf FA) DB DB
                _ (upEl (k - i) k EA FA (ers rho u) xu)
                _ (upEl (k - i) k EA FA (ers rho u') xu')
                (upEl_eq (k - i) k EA FA (ers rho u) xu FA (ers rho u') xu'
                   (famAtSelf FA) Huu)) as Pfam.
  (* and the reading of the codomain in the environment carrying the argument *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  pose proof (isubst_ITy rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                B j (ers (ext rho FA (ers rho u) xu) B) FBu DBu0) as DBsub.
  pose proof (ITy_cast rho (B [u..]) j _ _ E FBu DBsub) as DBc.
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho u) xu)
                  (ext rho FA (ers rho u)
                     (dnEl (k - i) k EA FA (ers rho u)
                        (upEl (k - i) k EA FA (ers rho u) xu)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho u) xu (ers rho u) _ HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho u) (upEl (k - i) k EA FA (ers rho u) xu))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho u) (upEl (k - i) k EA FA (ers rho u) xu))
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (UU j) u dBt du) as [dsub].
    exact (FunTm_of_ty G (B [u..]) j dsub). }
  pose proof (ity_lvl rho rho eq_refl (B [u..]) j (ers rho (B [u..]))
                (famCast E FBu) k' (ers rho (B [u..])) F DBc DBu) as Ek; subst k'.
  refine (itot_move G (app A B f' u') (B [u..]) Hfun rho Hrho j F
            (famCast E FBu) DBu DBc _ _).
  refine (ITm_cast rho (app A B f' u') j _ _ E FBu _ _ _).
  refine (i_conv rho (app A B f' u') j _
            (FB (ers rho u') (upEl (k - i) k EA FA (ers rho u') xu')) _ FBu _ _
            (famCeq_tr _ _ _ (knsymU _ _ Pfam) (knsymU _ _ P)) _).
  exact (i_app rho A B f' u' k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
           redB cohB gPi (ers rho f') xf (ers rho u') xu' eq_refl DFA DB Df Du').
Qed.

Lemma isem_app G kk i j A B f f' u u' (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (df : ty G f (pi kk A B)) (df' : ty G f' (pi kk A B))
  (du : ty G u A) (du' : ty G u' A)
  (cf : cv G f f' (pi kk A B)) (cu : cv G u u' A)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHf : ITot G f (pi kk A B)) (IHf' : ITot G f' (pi kk A B))
  (IHu : ITot G u A) (IHu' : ITot G u' A)
  (IHcf : IRel G f f' (pi kk A B)) (IHcu : IRel G u u' A) :
  ISem G (app A B f u) (app A B f' u') (B [u..]).
Proof.
  split;
    [split; [exact (itot_app G A B f u kk i j Hik Hjk dA dB df du IHA IHB IHf IHu)
            | exact (itot_app' G A B f' u u' kk i j Hik Hjk dA dB df' du du'
                       IHA IHB IHf' IHu IHu' IHcu)] |].
  intros rho Hrho k F DBu x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (itm_inv rho (app A B f u) k (ers rho (B [u..])) F
                (ers rho (app A B f u)) x Dx) as E.
  pose proof (itm_inv rho (app A B f' u') k (ers rho (B [u..])) F
                (ers rho (app A B f' u')) y Dy) as E'.
  cbn [TmInv TmShape AppVal Shaped] in E, E'.
  pose proof (LCv_of_cv G (app A B f u) (app A B f' u') (B [u..])
                (c_app G kk i j A B f f' u u' Hik Hjk dA dB df df' cf du du' cu)
                rho rho HEself) as Hrel.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct d1 as
    [kp i1 dA1 dB1 EA1 EB1 wA FA B0 wB FB redB cohB gPi wf xf wa xa
     Ep DA DB Df Da].
  destruct d2 as
    [kp' i2 dA2 dB2 EA2 EB2 wA' FA' B0' wB' FB' redB' cohB' gPi' wf' xf' wa' xa'
     Ep' DA' DB' Df' Da'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold ap_val, ap_arg in Hv, Hv'.
  cbn [ap_kp ap_i ap_dA ap_dB ap_EA ap_EB ap_wA ap_FA ap_B0 ap_wB ap_FB
       ap_redB ap_cohB ap_gPi ap_wf ap_xf ap_wa ap_xa] in Hv, Hv'.
  (* both functions are read at the Pi's annotation *)
  destruct (build_pi G A B kk i j Hik Hjk dA dB IHA IHB rho Hrho) as [FP DP].
  pose proof (lvl_of_ITot G f (pi kk A B) IHf rho Hrho kk FP DP
                (NotPrfR_pi _ _) kp _ _ _ xf (NotPrfR_pi _ _) Df) as Ekp.
  pose proof (lvl_of_ITot G f' (pi kk A B) IHf' rho Hrho kk FP DP
                (NotPrfR_pi _ _) kp' _ _ _ xf' (NotPrfR_pi _ _) Df') as Ekp'.
  destruct Ekp; destruct Ekp'.
  assert (Epi : epi wA B0 = epi wA' B0') by (rewrite Ep, Ep'; reflexivity).
  injection Epi as EwA EB0; subst wA' B0'.
  pose proof (ity_lvl rho rho eq_refl A i1 _ FA i2 _ FA' DA DA') as Ei; subst i2.
  assert (EdA : dA2 = dA1) by lia; subst dA2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
  assert (EdB : dB2 = dB1) by lia; subst dB2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB2 EB1) as EEB; subst EB2.
  assert (EwA0 : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA); subst wA.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i1 FA FA' DA DA').
  destruct (comp_ceq G A B (LTy_of_ty G A i dA) (LTy_of_ty (A :: G) B j dB)
              (funtm G A (UU i) dA) (funtm (A :: G) B (UU j) dB)
              rho rho HEself kp'
              i1 k dA1 dB1 EA1 EB1 _ FA wB FB
              i1 k dA1 dB1 EA1 EB1 _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  pose proof (kRel_of_IRel' G f f' (pi kp' A B) IHcf
                (FunTm_of_ty G (pi kp' A B) kp'
                   (t_pi G kp' i j A B Hik Hjk dA dB))
                rho Hrho kp' _ _ _ _
                (ity_pi rho A B kp' i1 k dA1 dB1 EA1 EB1 _ FA B0 wB FB
                   redB cohB gPi Ep DA DB)
                (ity_pi rho A B kp' i1 k dA1 dB1 EA1 EB1 _ FA' B0 wB' FB'
                   redB' cohB' gPi' Ep' DA' DB')
                _ xf _ xf' Df Df') as Hxf.
  pose proof (kRel_of_IRel' G u u' A IHcu (funtm G A (UU i) dA) rho Hrho i1
                _ FA _ FA' DA DA' _ xa _ xa' Da Da') as Hxa.
  pose proof (upEl_eq dA1 kp' EA1 FA wa xa FA' wa' xa' HA (kRel_at Hxa)) as Hau.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (kRel_dn dB1 kp' EB1 _ _
           (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
              (funtm (A :: G) B (UU j) dB) rho rho HEself kp' i1 k dA1 EA1
              _ FA wB FB _ FA' wB' FB' DA DA' HA DB DB' _ _ _ _ Hau)).
  exact (piApp_eqX kp' (ers rho A) B0 (upF dA1 kp' EA1 FA) wB
           (fun u0 y0 => upF dB1 kp' EB1 (FB u0 y0)) redB cohB gPi
           (ers rho A) B0 (upF dA1 kp' EA1 FA') wB'
           (fun u0 y0 => upF dB1 kp' EB1 (FB' u0 y0)) redB' cohB' gPi' HAu HBu
           wf xf wf' xf' wa (upEl dA1 kp' EA1 FA wa xa)
           wa' (upEl dA1 kp' EA1 FA' wa' xa') (kRel_at Hxf) Hau).
Qed.

(* IRel against kRel again, this time with the two values living at families
   that are only EQUAL to the type's own reading -- which is what a decoded
   eliminator hands over once the type is a substitution instance.  Both
   values travel to the canonical reading, are compared there, and come back
   by the coercion's coherence. *)
Lemma kRel_of_IRel_ceq G (t u A : tm) (HR : IRel G t u A)
  rho (Hrho : EnvITy G rho) k w0 (F0 : kUFam k w0) (D0 : ITy rho A k w0 F0)
  w (F : kUFam k w) w' (F' : kUFam k w')
  (Q : kceq (kAt F) (kAt F0)) (Q' : kceq (kAt F') (kAt F0))
  wt (x : kElAt F wt) wu (y : kElAt F' wu)
  (Dx : ITm rho t k w F wt x) (Dy : ITm rho u k w' F' wu y) :
  kRel F wt x F' wu y.
Proof.
  assert (E0 : w0 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D0); subst w0.
  assert (Et : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dx); subst wt.
  assert (Eu : wu = ers rho u) by exact (ers_of_ITm _ _ _ _ _ _ _ Dy); subst wu.
  split; [exact (famCeq_tr _ _ _ Q (famCeq_sym _ _ Q')) |].
  pose proof (HR rho Hrho k F0 D0 _ _
                (i_conv rho t k w F (ers rho A) F0 (ers rho t) x Q Dx)
                (i_conv rho u k w' F' (ers rho A) F0 (ers rho u) y Q' Dy)) as H0.
  eapply kEqAt_trans;
    [ exact Q
    | exact (kto_coh (kAt F) (kAt F0) (famAtWf F) (famAtWf F0) Q (ers rho t) x) |].
  eapply kEqAt_trans; [ exact (famAtSelf F0) | exact H0 |].
  apply kEqAt_sym.
  exact (kto_coh (kAt F') (kAt F0) (famAtWf F') (famAtWf F0) Q' (ers rho u) y).
Qed.

(* ---- the pair.  c_pair's two subjects are `pair k A B t u` and
     `pair k A B t' u'` with BOTH second components typed at `B [t..]`, so the
     primed pair is not an instance of t_pair and its totality has to be
     proved by hand: the second component is read at the codomain instance
     taken at t, and then moved to the one taken at t' along cod_ceq. ---- *)
Lemma itot_pair' G A B t t' u u' k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dt : ty G t A) (dt' : ty G t' A) (ct : cv G t t' A)
  (du : ty G u (B [t..])) (du' : ty G u' (B [t..])) (cu : cv G u u' (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHt' : ITot G t' A) (IHu' : ITot G u' (B [t..]))
  (IHct : IRel G t t' A) :
  ITot G (pair k A B t' u') (sig_ k A B).
Proof.
  intros rho Hrho k' F Dsg.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ k A B) k
                  (t_sig G k i j A B Hik Hjk dAt dBt) rho rho HEself).
  pose proof (ity_sig rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHt rho Hrho i FA DFA) as [xt Dt].
  destruct (IHt' rho Hrho i FA DFA) as [xt' Dt'].
  pose proof (IHct rho Hrho i FA DFA xt xt' Dt Dt') as A3.
  (* the codomain at t, where u' is read, and at t', where it has to land *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i FA DFA (ers rho t) xt Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  destruct (IHu' rho Hrho j (famCast E FBu)
              (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)) as [y0 Dy0].
  destruct (ITm_uncast rho u' j _ _ E FBu _ _ Dy0) as [ya Dya].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                  (ext rho FA (ers rho t)
                     (dnEl (k - i) k EA FA (ers rho t)
                        (upEl (k - i) k EA FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho t) xt (ers rho t) _ HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho t) (upEl (k - i) k EA FA (ers rho t) xt))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho t) (upEl (k - i) k EA FA (ers rho t) xt))
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  pose proof (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) rho rho HEself k i j (k - i) EA
                (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
                (famAtSelf FA) DB DB
                _ (upEl (k - i) k EA FA (ers rho t) xt)
                _ (upEl (k - i) k EA FA (ers rho t') xt')
                (upEl_eq (k - i) k EA FA (ers rho t) xt FA (ers rho t') xt'
                   (famAtSelf FA) A3)) as QB.
  pose proof (i_conv rho u' j _ FBu _
                (FB (ers rho t') (upEl (k - i) k EA FA (ers rho t') xt'))
                (ers rho u') ya (famCeq_tr _ _ _ P QB) Dya) as Dya2.
  (* the primed pair is layer-1 good: it is related to the unprimed one *)
  assert (gr : Rel (ers rho (sig_ k A B)) (ers rho (pair k A B t u))
                 (ers rho (pair k A B t' u')))
    by exact (LCv_of_cv G (pair k A B t u) (pair k A B t' u') (sig_ k A B)
                (c_pair G k i j A B t t' u u' Hik Hjk dAt dBt dt dt' ct du du' cu)
                rho rho HEself).
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t') (ers rho u')))
    by (eapply Rel_trans; [apply Rel_sym; exact gr | exact gr]).
  pose proof (ity_lvl rho rho eq_refl (sig_ k A B) k (ers rho (sig_ k A B))
                (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                   (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig)
                k' (ers rho (sig_ k A B)) F Dsig Dsg) as Ek; subst k'.
  refine (itot_move G (pair k A B t' u') (sig_ k A B)
            (FunTm_of_ty G (sig_ k A B) k
               (t_sig G k i j A B Hik Hjk dAt dBt)) rho Hrho k F
            (sigFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gSig)
            Dsg Dsig _ _).
  exact (i_pair rho A B t' u' k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gSig (ers rho t') xt' (ers rho u') _ g eq_refl
           DFA DB Dt' Dya2).
Qed.

(* The pair's conversion case.  The two pairs are compared through the
   Sigma-code's eta law, exactly as in funtm_pair: a pair is equal to the pair
   of its projections, and the projections of a pair are its components, so
   what is left is the two components' relations -- the first from the
   conversion at A, the second from the conversion at `B [t..]`, read at the
   canonical instance and moved to the two decoded ones. *)
Lemma isem_pair G kk i j A B t t' u u' (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dt : ty G t A) (dt' : ty G t' A) (ct : cv G t t' A)
  (du : ty G u (B [t..])) (du' : ty G u' (B [t..])) (cu : cv G u u' (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHt' : ITot G t' A) (IHct : IRel G t t' A)
  (IHu : ITot G u (B [t..])) (IHu' : ITot G u' (B [t..]))
  (IHcu : IRel G u u' (B [t..])) :
  ISem G (pair kk A B t u) (pair kk A B t' u') (sig_ kk A B).
Proof.
  split;
    [split; [exact (itot_pair G A B t u kk i j Hik Hjk dA dB dt du
                      IHA IHB IHt IHu)
            | exact (itot_pair' G A B t t' u u' kk i j Hik Hjk dA dB dt dt' ct
                       du du' cu IHA IHB IHt IHt' IHu' IHct)] |].
  intros rho Hrho k F Dsg x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (itm_inv rho (pair kk A B t u) k (ers rho (sig_ kk A B)) F
                (ers rho (pair kk A B t u)) x Dx) as E.
  pose proof (itm_inv rho (pair kk A B t' u') k (ers rho (sig_ kk A B)) F
                (ers rho (pair kk A B t' u')) y Dy) as E'.
  cbn [TmInv TmShape PairVal Shaped] in E, E'.
  pose proof (LCv_of_cv G (pair kk A B t u) (pair kk A B t' u') (sig_ kk A B)
                (c_pair G kk i j A B t t' u u' Hik Hjk dA dB dt dt' ct du du' cu)
                rho rho HEself) as Hrel.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct d1 as
    [i1 j1 dA1 dB1 EA1 EB1 wA FA B0 wB FB redB cohB gSig wt xt wa xa g
     Ekk Ep DA DB Dt Da].
  destruct d2 as
    [i2 j2 dA2 dB2 EA2 EB2 wA' FA' B0' wB' FB' redB' cohB' gSig' wt' xt' wa' xa'
     g' Ekk' Ep' DA' DB' Dt' Da'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  unfold pd_SF, pd_val in Hv, Hv'.
  cbn [pd_i pd_j pd_dA pd_dB pd_EA pd_EB pd_wA pd_FA pd_B0 pd_wB pd_FB pd_redB
       pd_cohB pd_gSig pd_wt pd_xt pd_wa pd_xa pd_g] in Hv, Hv'.
  assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EwA' : wA' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (Ewt : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt).
  assert (Ewt' : wt' = ers rho t') by exact (ers_of_ITm _ _ _ _ _ _ _ Dt').
  assert (Ewa : wa = ers rho u) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho u') by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  subst wA wA' wt wt' wa wa'.
  assert (Esig : esig (ers rho A) B0 = esig (ers rho A) B0')
    by (rewrite Ep, Ep'; reflexivity).
  injection Esig as EB0; subst B0'.
  pose proof (ity_lvl rho rho eq_refl A i1 _ FA i2 _ FA' DA DA') as Ei; subst i2.
  assert (EdA : dA2 = dA1) by lia; subst dA2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i1 FA FA' DA DA').
  pose proof (kRel_of_IRel' G t t' A IHct (funtm G A (UU i) dA) rho Hrho i1
                _ FA _ FA' DA DA' _ xt _ xt' Dt Dt') as A3.
  pose proof (upEl_eq dA1 k EA1 FA _ xt FA' _ xt' HA (kRel_at A3)) as A3u.
  destruct (comp_ceq G A B (LTy_of_ty G A i dA) (LTy_of_ty (A :: G) B j dB)
              (funtm G A (UU i) dA) (funtm (A :: G) B (UU j) dB)
              rho rho HEself k
              i1 j1 dA1 dB1 EA1 EB1 _ FA wB FB
              i1 j2 dA1 dB2 EA1 EB2 _ FA' wB' FB'
              DA DA' DB DB') as [HAu HBu].
  (* the codomain's level and gap, at the two first components *)
  pose proof (DB _ (upEl dA1 k EA1 FA _ xt)) as DBx.
  pose proof (DB' _ (upEl dA1 k EA1 FA' _ xt')) as DBx'.
  pose proof (kRel_dn dA1 k EA1 FA FA' HA _ _ _ _ (conj HAu A3u)) as A3rt.
  pose proof (EnvRelOf_ext G rho rho A i1 FA FA' _ _ _ _ HEself A3rt) as HEx.
  pose proof (ity_lvl _ _ (lvls_of_EnvRelOf (A :: G) _ _ HEx) B
                j1 _ _ j2 _ _ DBx DBx') as Ej; subst j2.
  assert (EdB : dB2 = dB1) by lia; subst dB2.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB2 EB1) as EEB; subst EB2.
  assert (QB : kceq (kAt (FB _ (upEl dA1 k EA1 FA _ xt)))
                    (kAt (FB' _ (upEl dA1 k EA1 FA' _ xt'))))
    by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
                (funtm (A :: G) B (UU j) dB) rho rho HEself k i1 j1 dA1 EA1
                _ FA wB FB _ FA' wB' FB' DA DA' HA DB DB' _ _ _ _ A3u).
  (* the second components, through the canonical reading of `B [t..]` *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i1 FA DA (ers rho t) xt Hrho)) as [FBu DBu0].
  (* the codomain's reading level is the syntactic one *)
  pose proof (ity_lvl
                (ext rho FA (ers rho t)
                   (dnEl dA1 k EA1 FA (ers rho t)
                      (upEl dA1 k EA1 FA (ers rho t) xt)))
                (ext rho FA (ers rho t) xt) eq_refl B
                j1 _ (FB _ (upEl dA1 k EA1 FA _ xt)) j _ FBu DBx DBu0)
    as Ej1; subst j1.
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i1 (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  assert (HEx2 : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                   (ext rho FA (ers rho t)
                      (dnEl dA1 k EA1 FA (ers rho t)
                         (upEl dA1 k EA1 FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i1 FA FA (ers rho t) xt (ers rho t) _
             HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu) (kAt (FB (ers rho t) (upEl dA1 k EA1 FA _ xt)))).
  { apply (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx2 j
             _ FBu _ _ DBu0 DBx).
    rewrite (ers_of_ITy _ _ _ _ _ DBx).
    exact (LTyK_of_ty (A :: G) B j dB _ _ HEx2). }
  pose proof (famCeq_tr _ _ _ (famCeq_sym _ _ P) (famCast_ceq E FBu)) as Q.
  pose proof (kRel_of_IRel_ceq G u u' (B [t..]) IHcu rho Hrho j
                _ (famCast E FBu) (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)
                _ (FB _ (upEl dA1 k EA1 FA _ xt))
                _ (FB' _ (upEl dA1 k EA1 FA' _ xt'))
                Q (famCeq_tr _ _ _ (famCeq_sym _ _ QB) Q)
                _ xa _ xa' Da Da') as B3.
  pose proof (kRel_up dB1 k EB1 _ _ _ _ _ _ B3) as B3u.
  (* the layer-1 facts about the two pairs, and the two families *)
  assert (Hty : tyeq (esig (ers rho A) B0) (esig (ers rho A) B0))
    by (exists k; exact gSig).
  pose proof (sigFam_ceq k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gSig
                (ers rho A) B0 (upF dA1 k EA1 FA') wB'
                (fun u0 y0 => upF dB1 k EB1 (FB' u0 y0)) redB' cohB' gSig'
                Hty HAu HBu) as Psig.
  assert (Hrp : Rel (esig (ers rho A) B0)
                  (epair (ers rho t) (ers rho u))
                  (epair (ers rho t') (ers rho u'))).
  { rewrite <- Ekk in Ep.
    apply (Rel_tyeq (ers rho (sig_ kk A B)) (esig (ers rho A) B0));
      [ rewrite <- Ep; exact Hty | exact Hrel ]. }
  assert (gT' : Good_ty (esig (ers rho A) B0)) by (exists k; exact gSig').
  assert (Hsame : Rel (esig (ers rho A) B0)
                    (epair (ers rho t) (ers rho u))
                    (epair (ers rho t) (ers rho u)))
    by (eapply Rel_trans; [exact Hrp | apply Rel_sym; exact Hrp]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hsame) as gr.
  assert (g2 : Good (esig (ers rho A) B0)
                 (epair (efst (epair (ers rho t) (ers rho u)))
                        (esnd (epair (ers rho t) (ers rho u)))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hrp) as Hc.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  split; [exact Psig |].
  eapply kEqAt_trans; [exact Psig | apply kto_coh |].
  eapply kEqAt_trans;
    [ exact (famAtSelf _)
    | apply kEqAt_sym;
      exact (sigPair_surj k (ers rho A) B0 (upF dA1 k EA1 FA') wB'
               (fun u0 y0 => upF dB1 k EB1 (FB' u0 y0)) redB' cohB' gSig' _ _
               g2 gr) |].
  apply (sigPair_eq k (ers rho A) B0 (upF dA1 k EA1 FA') wB'
           (fun u0 y0 => upF dB1 k EB1 (FB' u0 y0)) redB' cohB' gSig');
    [ exact Hc | |].
  - eapply kEqAt_trans;
      [ apply knsymU; exact HAu
      | apply kEqAt_sym;
        exact (sigFst_to k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                 (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gSig
                 (ers rho A) B0 (upF dA1 k EA1 FA') wB'
                 (fun u0 y0 => upF dB1 k EB1 (FB' u0 y0)) redB' cohB' gSig'
                 HAu Psig _ _) |].
    eapply kEqAt_trans;
      [ exact (famAtSelf _)
      | exact (sigFst_pair k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                 (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gSig _ _ _ _ g)
      | exact A3u ].
  - eapply kRel_trans;
      [ apply kRel_sym;
        exact (sigSnd_to k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                 (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gSig
                 (ers rho A) B0 (upF dA1 k EA1 FA') wB'
                 (fun u0 y0 => upF dB1 k EB1 (FB' u0 y0)) redB' cohB' gSig'
                 HAu HBu Psig _ _) |].
    eapply kRel_trans;
      [ exact (sigSnd_pair k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                 (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gSig _ _ _ _ g)
      | exact B3u ].
Qed.

(* ---- the universal quantifier.  Its type is `prop`, so the two values are
     propositions and what has to be shown is that they are logically
     equivalent.  The two directions are one statement about an arbitrary
     RELATED pair of arguments, read once each way, and each direction gets
     its pair by coercing the argument it is handed along the domains'
     equality. ---- *)
Lemma isem_all G A A' p p' jj k (W : Rules.wfc G) (dA : ty G A (UU k))
  (dp : ty (A :: G) p (prop jj)) (dA' : ty G A' (UU k))
  (dp' : ty (A' :: G) p' (prop jj))
  (cA : cv G A A' (UU k)) (cp : cv (A :: G) p p' (prop jj))
  (IHA : ITot G A (UU k)) (IHp : ITot (A :: G) p (prop jj))
  (IHA' : ITot G A' (UU k)) (IHp' : ITot (A' :: G) p' (prop jj))
  (IHcA : IRel G A A' (UU k)) (IHcp : IRel (A :: G) p p' (prop jj)) :
  ISem G (all jj A p) (all jj A' p') (prop jj).
Proof.
  pose proof (w_cons G A k W dA) as WA.
  split;
    [split; [exact (itot_all G A p jj k W dA dp IHA IHp)
            | exact (itot_all G A' p' jj k W dA' dp' IHA' IHp')] |].
  intros rho Hrho k' F DP x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (ity_lvl_dec rho (prop jj) k' (ers rho (prop jj)) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (LCv_of_cv G (all jj A p) (all jj A' p') (prop jj)
                (c_all G A A' p p' jj k dA dp dA' dp' cA cp) rho rho HEself)
    as Hrel.
  pose proof (itm_inv rho (all jj A p) jj (ers rho (prop jj)) F
                (ers rho (all jj A p)) x Dx) as E.
  pose proof (itm_inv rho (all jj A' p') jj (ers rho (prop jj)) F
                (ers rho (all jj A' p')) y Dy) as E'.
  cbn [TmInv] in E, E'.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  cbn [TmShape AllVal Shaped] in E, E'.
  destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
  destruct d1 as [kA wA FA wp xp wv g Ejj DA Dp].
  destruct d2 as [kA' wA' FA' wp' xp' wv' g' Ejj' DA' Dp'].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
  cbn [al_kA al_wA al_FA al_wp al_xp al_wv al_g] in Hv, Hv'.
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  (* both domains are read at the level their typing gives *)
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FAc DAc].
  pose proof (ity_lvl rho rho eq_refl A k (ers rho A) FAc kA (ers rho A) FA
                DAc DA) as EkA; subst kA.
  destruct (ityT_of_ITot G A' k IHA' rho Hrho) as [FAc' DAc'].
  pose proof (ity_lvl rho rho eq_refl A' k (ers rho A') FAc' kA' (ers rho A')
                FA' DAc' DA') as EkA'; subst kA'.
  assert (QA : kceq (kAt FA) (kAt FA'))
    by exact (ceq_of_IRel_at' G A A' k IHcA rho Hrho _ FA DA _ FA' DA').
  assert (HtyA : tyeq (ers rho A) (ers rho A'))
    by (exists k; exact (LCvK_of_cv G A A' k cA rho rho HEself)).
  (* the equivalence, at an arbitrary related pair of arguments *)
  assert (Key : forall u (z : kElAt FA u) u2 (z2 : kElAt FA' u2),
             kRel FA u z FA' u2 z2 -> (propVal (xp u z) <-> propVal (xp' u2 z2))).
  { intros u z u2 z2 Hz.
    pose proof (EnvITy_ext G rho A k FA DA u z Hrho) as HExA.
    pose proof (EnvITy_ext_ceq G rho A' k (ers rho A) FA FA' DA' QA u z Hrho)
      as HExA'.
    destruct (IHp' (ext rho FA u z) HExA' jj (propFam jj)
                (ity_prop (ext rho FA u z) jj
                   (ers (ext rho FA u z) (prop jj)) eq_refl)) as [w0 Dw0].
    pose proof (kRel_of_IRel' (A :: G) p p' (prop jj) IHcp
                  (FunTm_of_ty (A :: G) (prop jj) jj (t_prop (A :: G) jj WA))
                  (ext rho FA u z) HExA jj eprop (propFam jj) eprop (propFam jj)
                  (ity_prop _ _ _ eq_refl) (ity_prop _ _ _ eq_refl)
                  _ (xp u z) _ w0 (Dp u z) Dw0) as H1.
    assert (HEr : EnvRelOf (A' :: G) (ext rho FA u z) (ext rho FA' u2 z2)).
    { apply (EnvRelOf_ext_ty G rho rho A' k (ers rho A) (ers rho A')
               FA FA' u z u2 z2 HEself HtyA);
        [ exists k; exact (uf_ty FA') | exact Hz ]. }
    assert (Ew' : wp' u2 z2 = ers (ext rho FA' u2 z2) p')
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp' u2 z2)).
    assert (Hr2 : Rel eprop (ers (ext rho FA u z) p') (wp' u2 z2))
      by (rewrite Ew'; exact (LTm_of_ty (A' :: G) p' (prop jj) dp' _ _ HEr)).
    pose proof (funtm (A' :: G) p' (prop jj) dp' _ _ HEr jj eprop (propFam jj)
                  _ w0 Dw0 eprop (propFam jj) _ (xp' u2 z2) (Dp' u2 z2)
                  (famAtSelf (propFam jj)) Hr2) as H2.
    exact (proj1 (proj1 (propEq_iff (xp u z) (xp' u2 z2))
                    (kRel_at (kRel_trans _ _ _ _ _ _ _ _ _ H1 H2)))). }
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hw : Rel eprop (ers rho (all jj A p)) wv)
    by exact (proj2 (proj1 (propEq_iff _ _) HQ)).
  assert (Hw' : Rel eprop (ers rho (all jj A' p')) wv')
    by exact (proj2 (proj1 (propEq_iff _ _) HQ')).
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  apply (proj1 (kRel_same (propFam jj) _ _ _ _)).
  apply propEq_iff; split.
  - cbn [propVal propElem Datatypes.fst]; split.
    + intros H u2 z2.
      refine (proj1 (Key u2 _ u2 z2 (conj QA _)) (H u2 _)).
      apply kEqAt_sym.
      exact (kto_coh (kAt FA') (kAt FA) (famAtWf FA') (famAtWf FA)
               (knsymU _ _ QA) u2 z2).
    + intros H u z.
      refine (proj2 (Key u z u _ (conj QA _)) (H u _)).
      exact (kto_coh (kAt FA) (kAt FA') (famAtWf FA) (famAtWf FA') QA u z).
  - eapply Rel_trans; [apply Rel_sym; exact Hw |].
    eapply Rel_trans; [exact Hrel | exact Hw'].
Qed.

(* ---- the lambda.  The right-hand subject is typed at `pi kk A' B'` while
     the rule concludes at `pi kk A B`, so its totality is the Pi-congruence
     read backwards (isem_pi, symmetrised).  The two values are compared with
     piLam_eq, whose two premises are the Pi-families' components -- supplied
     by isem_binder_ceq, exactly as for isem_pi -- and the bodies, compared
     pointwise in the same two steps as the codomains: t against t' in the
     A-extended environment, then t' against itself across the two. ---- *)
Lemma isem_lam G kk i j A A' B B' t t' (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dA' : ty G A' (UU i)) (dB' : ty (A' :: G) B' (UU j))
  (cA : cv G A A' (UU i)) (cB : cv (A :: G) B B' (UU j))
  (dt : ty (A :: G) t B) (dt' : ty (A' :: G) t' B') (ct : cv (A :: G) t t' B)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHA' : ITot G A' (UU i)) (IHB' : ITot (A' :: G) B' (UU j))
  (IHcA : IRel G A A' (UU i)) (IHcB : IRel (A :: G) B B' (UU j))
  (IHt : ITot (A :: G) t B) (IHt2 : ITot (A :: G) t' B)
  (IHt' : ITot (A' :: G) t' B') (IHct : IRel (A :: G) t t' B) :
  ISem G (lam kk A B t) (lam kk A' B' t') (pi kk A B).
Proof.
  pose proof (isem_pi G A A' B B' kk i j W Hik Hjk dA dB dA' dB' cA cB
                IHA IHB IHA' IHB' IHcA IHcB) as Hpi.
  split.
  - split; [exact (itot_lam G A B t kk i j Hik Hjk dA dB dt IHA IHB IHt) |].
    exact (itot_conv G (lam kk A' B' t') (pi kk A' B') (pi kk A B) kk
             (t_pi G kk i j A' B' Hik Hjk dA' dB')
             (t_pi G kk i j A B Hik Hjk dA dB)
             (itot_lam G A' B' t' kk i j Hik Hjk dA' dB' dt' IHA' IHB' IHt')
             (itot_pi G A' B' kk i j W Hik Hjk dA' dB' IHA' IHB')
             (itot_pi G A B kk i j W Hik Hjk dA dB IHA IHB)
             (Datatypes.snd
                (isem_sym G (pi kk A B) (pi kk A' B') (UU kk) Hpi))).
  - intros rho Hrho k F Dpi0 x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    pose proof (LCv_of_cv G (lam kk A B t) (lam kk A' B' t') (pi kk A B)
                  (c_lam G kk i j A A' B B' t t' Hik Hjk dA dB dA' dB' cA cB
                     dt dt' ct) rho rho HEself) as Hrel.
    pose proof (itm_inv rho (lam kk A B t) k (ers rho (pi kk A B)) F
                  (ers rho (lam kk A B t)) x Dx) as E.
    pose proof (itm_inv rho (lam kk A' B' t') k (ers rho (pi kk A B)) F
                  (ers rho (lam kk A' B' t')) y Dy) as E'.
    cbn [TmInv TmShape LamVal Shaped] in E, E'.
    destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
    destruct E as [d1 Hv]; destruct E' as [d2 Hv'].
    destruct d1 as
      [i1 j1 dA1 dB1 EA1 EB1 wA FA B0 wB FB redB cohB gPi wt xt redt xtext gd
       Ekk Ew Ep DA DB Dt].
    destruct d2 as
      [i2 j2 dA2 dB2 EA2 EB2 wA' FA' B0' wB' FB' redB' cohB' gPi' wt' xt' redt'
       xtext' gd' Ekk' Ew' Ep' DA' DB' Dt'].
    cbn [cn_Sy cn_F cn_w cn_x] in Hv, Hv'.
    unfold ld_PF, ld_val in Hv, Hv'.
    cbn [ld_i ld_j ld_dA ld_dB ld_EA ld_EB ld_wA ld_FA ld_B0 ld_wB ld_FB
         ld_redB ld_cohB ld_gPi ld_wt ld_xt ld_redt ld_xtext ld_gd] in Hv, Hv'.
    assert (EwA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
    assert (EwA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
    subst wA wA'.
    (* both domains are read at the level their typing gives, so both gaps
       are the same *)
    destruct (ityT_of_ITot G A i IHA rho Hrho) as [FAc DAc].
    pose proof (ity_lvl rho rho eq_refl A i1 _ FA i _ FAc DA DAc) as Ei1;
      subst i1.
    destruct (ityT_of_ITot G A' i IHA' rho Hrho) as [FAc' DAc'].
    pose proof (ity_lvl rho rho eq_refl A' i2 _ FA' i _ FAc' DA' DAc') as Ei2;
      subst i2.
    assert (EdA : dA2 = dA1) by lia; subst dA2.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA2 EA1) as EEA; subst EA2.
    assert (QA : kceq (kAt FA) (kAt FA'))
      by exact (ceq_of_IRel_at G A A' i IHcA rho Hrho FA DA FA' DA').
    assert (HtyA : tyeq (ers rho A) (ers rho A')) by exact (ceq_ty FA FA' QA).
    destruct (isem_binder_ceq G A A' B B' k i j dB' IHB IHB' IHcA IHcB rho Hrho
                dA1 EA1 FA j1 dB1 EB1 wB FB DA DB
                dA1 EA1 FA' j2 dB2 EB2 wB' FB' DA' DB') as [HAu HBu].
    assert (Hty : tyeq (epi (ers rho A) B0) (epi (ers rho A') B0')).
    { rewrite Ep, Ep'.
      exists kk.
      exact (LCvK_of_cv G (pi kk A B) (pi kk A' B') kk
               (c_pi G kk i j A A' B B' Hik Hjk dA dB dA' dB' cA cB)
               rho rho HEself). }
    (* the two realisers are related at the Pi *)
    assert (HR : Rel (epi (ers rho A) B0) (ers rho (lam kk A B t))
                   (ers rho (lam kk A' B' t'))).
    { apply (Rel_tyeq (ers rho (pi kk A B)) (epi (ers rho A) B0));
        [| exact Hrel].
      rewrite <- Ekk in Ep; rewrite <- Ep.
      exists k; exact gPi. }
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
    split;
      [ exact (piFam_ceq k (ers rho A) B0 (upF dA1 k EA1 FA) wB
                 (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gPi
                 (ers rho A') B0' (upF dA1 k EA1 FA') wB'
                 (fun u0 y0 => upF dB2 k EB2 (FB' u0 y0)) redB' cohB' gPi'
                 Hty HAu HBu) |].
    apply (piLam_eq k (ers rho A) B0 (upF dA1 k EA1 FA) wB
             (fun u0 y0 => upF dB1 k EB1 (FB u0 y0)) redB cohB gPi
             (ers rho A') B0' (upF dA1 k EA1 FA') wB'
             (fun u0 y0 => upF dB2 k EB2 (FB' u0 y0)) redB' cohB' gPi'
             Hty HAu HBu); [exact HR |].
    (* the bodies, pointwise at a related pair of arguments *)
    intros va za va' za' Hy.
    pose proof (kRel_dn dA1 k EA1 FA FA' QA _ _ _ _ (conj HAu Hy)) as Hyd.
    pose proof (EnvITy_ext G rho A i FA DA va (dnEl dA1 k EA1 FA va za) Hrho)
      as HExA.
    pose proof (EnvITy_ext_ceq G rho A' i (ers rho A) FA FA' DA' QA va
                  (dnEl dA1 k EA1 FA va za) Hrho) as HExA'.
    pose proof (EnvITy_ext G rho A' i FA' DA' va' (dnEl dA1 k EA1 FA' va' za')
                  Hrho) as HExA2.
    (* the codomains' reading levels, and hence their gaps *)
    destruct (ityT_of_ITot (A :: G) B j IHB _ HExA) as [FBj DBj].
    pose proof (ity_lvl _ _ eq_refl B j1 _ (FB va za) j _ FBj (DB va za) DBj)
      as Ej1.
    destruct (ityT_of_ITot (A' :: G) B' j IHB' _ HExA2) as [FBj' DBj'].
    pose proof (ity_lvl _ _ eq_refl B' j2 _ (FB' va' za') j _ FBj' (DB' va' za')
                  DBj') as Ej2.
    subst j1; subst j2.
    assert (EdB : dB2 = dB1) by lia; subst dB2.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB2 EB1) as EEB; subst EB2.
    assert (HEr : EnvRelOf (A' :: G)
                    (ext rho FA va (dnEl dA1 k EA1 FA va za))
                    (ext rho FA' va' (dnEl dA1 k EA1 FA' va' za'))).
    { apply (EnvRelOf_ext_ty G rho rho A' i (ers rho A) (ers rho A')
               FA FA' va _ va' _ HEself HtyA);
        [ exists i; exact (uf_ty FA') | exact Hyd ]. }
    destruct (ityT_of_ITot (A' :: G) B' j IHB' _ HExA') as [FBm DBm].
    assert (QB : kceq (kAt (FB va za)) (kAt (FB' va' za'))).
    { eapply famCeq_tr;
        [ exact (ceq_of_IRel_at' (A :: G) B B' j IHcB _ HExA
                   _ (FB va za) (DB va za) _ FBm DBm) |].
      refine (FunTy_of_FunTm (A' :: G) B' (funtm (A' :: G) B' (UU j) dB')
                _ _ HEr j _ FBm _ (FB' va' za') DBm (DB' va' za') _).
      rewrite (ers_of_ITy _ _ _ _ _ (DB' va' za')).
      exact (LTyK_of_ty (A' :: G) B' j dB' _ _ HEr). }
    (* the bodies: t against t' in the A-extension, then t' across the two *)
    assert (EB : wB va za = ers (ext rho FA va (dnEl dA1 k EA1 FA va za)) B)
      by exact (ers_of_ITy _ _ _ _ _ (DB va za)).
    destruct (IHt2 _ HExA j (famCast EB (FB va za))
                (ITy_cast _ B j _ _ EB _ (DB va za))) as [z0 Dz0].
    destruct (ITm_uncast _ t' j _ _ EB (FB va za) _ _ Dz0) as [z Dz].
    pose proof (kRel_of_IRel' (A :: G) t t' B IHct
                  (FunTm_of_ty (A :: G) B j dB) _ HExA j
                  _ (FB va za) _ (FB va za) (DB va za) (DB va za)
                  _ (xt va za) _ z (Dt va za) Dz) as Hb1.
    assert (Hrb : Rel (wB' va' za')
                    (ers (ext rho FA va (dnEl dA1 k EA1 FA va za)) t')
                    (wt' va' za')).
    { rewrite (ers_of_ITy _ _ _ _ _ (DB' va' za')),
              (ers_of_ITm _ _ _ _ _ _ _ (Dt' va' za')).
      apply (Rel_tyeq (ers (ext rho FA va (dnEl dA1 k EA1 FA va za)) B')
               (ers (ext rho FA' va' (dnEl dA1 k EA1 FA' va' za')) B'));
        [ exact (LTy_of_ty (A' :: G) B' j dB' _ _ HEr)
        | exact (LTm_of_ty (A' :: G) t' B' dt' _ _ HEr) ]. }
    pose proof (funtm (A' :: G) t' B' dt' _ _ HEr j _ (FB va za) _ z Dz
                  _ (FB' va' za') _ (xt' va' za') (Dt' va' za') QB Hrb) as Hb2.
    exact (upEl_eq dB1 k EB1 (FB va za) _ (xt va za) (FB' va' za') _ (xt' va' za')
             QB (kRel_at (kRel_trans _ _ _ _ _ _ _ _ _ Hb1 Hb2))).
Qed.

(* ---- the Sigma computation rules.  Each is proved by CONSTRUCTING the
     canonical value of both sides and comparing them with the family's own
     law (sigFst_pair, sigSnd_pair, sigPair_surj); the values the statement is
     handed are compared to the constructed ones by functionality, which is
     what funtm says about two readings of one term.  In v2 the pair's value
     is built at the former's annotation with its components LIFTED there, so
     the projection's `dnEl` undoes the clause's `upEl` -- that is the
     `dnEl_upEl` leg below, where v1 had an elLiftN/elUnliftN round trip. ---- *)

Lemma isem_fst_beta G kk i j A B t u (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ISem G (fst A B (pair kk A B t u)) t A.
Proof.
  pose proof (t_pair G kk i j A B t u Hik Hjk dA dB dt du) as dpair.
  pose proof (t_fst G kk i j A B (pair kk A B t u) Hik Hjk dA dB dpair) as dfst.
  split;
    [split; [exact (itot_fst G A B (pair kk A B t u) kk i j Hik Hjk dA dB dpair
                      IHA IHB (itot_pair G A B t u kk i j Hik Hjk dA dB dt du
                                 IHA IHB IHt IHu))
            | exact IHt] |].
  intros rho Hrho k F DA0 x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ kk A B) kk
                  (t_sig G kk i j A B Hik Hjk dA dB) rho rho HEself).
  destruct (IHt rho Hrho i FA DFA) as [xt Dt].
  (* the second component, read at the codomain instance at t's value *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i FA DFA (ers rho t) xt Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  destruct (IHu rho Hrho j (famCast E FBu)
              (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)) as [xu' Du'].
  destruct (ITm_uncast rho u j _ _ E FBu _ _ Du') as [xu0 Du0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                  (ext rho FA (ers rho t)
                     (dnEl (kk - i) kk EA FA (ers rho t)
                        (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho t) xt (ers rho t) _ HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (LTyK_of_ty (A :: G) B j dB _ _ HEx)).
  pose proof (i_conv rho u j _ FBu _
                (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (ers rho u) xu0 P Du0) as Du.
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair kk A B t u) (sig_ kk A B) dpair rho rho HEself).
  pose proof (i_pair rho A B t u kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho t) xt (ers rho u) _ g eq_refl
                DFA DB Dt Du) as Dpair.
  pose proof (i_fst rho A B (pair kk A B t u) kk i j (kk - i) (kk - j) EA EB
                (ers rho A) FA B0 wB FB redB cohB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dfst.
  (* the two readings of A, and the level *)
  pose proof (ity_lvl rho rho eq_refl A i (ers rho A) FA k (ers rho A) F
                DFA DA0) as Ek; subst k.
  pose proof (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i F FA DA0 DFA)
    as Q.
  pose proof (funtm G (fst A B (pair kk A B t u)) A dfst rho rho HEself i
                (ers rho A) F _ x Dx (ers rho A) FA _ _ Dfst Q
                (LTm_of_ty G (fst A B (pair kk A B t u)) A dfst rho rho HEself))
    as H1.
  pose proof (funtm G t A dt rho rho HEself i (ers rho A) FA _ xt Dt
                (ers rho A) F _ y Dy (knsymU _ _ Q)
                (LTm_of_ty G t A dt rho rho HEself)) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  (* the clause's lift and the projection's unlift cancel *)
  apply (proj1 (kRel_same FA _ _ _ _)).
  (* the clause's lift and the projection's unlift cancel: the projection of
     a pair is its first component, which the clause lifted *)
  eapply (kEqAt_trans FA _ _ FA (ers rho t)
            (dnEl (kk - i) kk EA FA (ers rho t)
               (upEl (kk - i) kk EA FA (ers rho t) xt)) FA _ _);
    [ exact (famAtSelf FA)
    | refine (kRel_at (kRel_dn (kk - i) kk EA FA FA (famAtSelf FA) _ _ _ _ _));
      split; [exact (famAtSelf _) | apply sigFst_pair]
    | exact (dnEl_upEl (kk - i) kk EA FA (ers rho t) xt) ].
Qed.

(* The second projection of a pair, read at `B [t..]`.  Its own type is
   `B [(fst A B p)..]` and the rule concludes at `B [t..]`, so the value has
   to travel along the codomain's coherence at the two arguments -- the
   projection of the pair and t's own value -- which `sigFst_pair` relates.
   That is cod_ceq, once. *)
Lemma itot_snd_beta G kk i j A B t u (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ITot G (snd A B (pair kk A B t u)) (B [t..]).
Proof.
  pose proof (t_pair G kk i j A B t u Hik Hjk dA dB dt du) as dpair.
  intros rho Hrho k F DBt.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ kk A B) kk
                  (t_sig G kk i j A B Hik Hjk dA dB) rho rho HEself).
  destruct (IHt rho Hrho i FA DFA) as [xt Dt].
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i FA DFA (ers rho t) xt Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  destruct (IHu rho Hrho j (famCast E FBu)
              (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)) as [xu' Du'].
  destruct (ITm_uncast rho u j _ _ E FBu _ _ Du') as [xu0 Du0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                  (ext rho FA (ers rho t)
                     (dnEl (kk - i) kk EA FA (ers rho t)
                        (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho t) xt (ers rho t) _ HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (LTyK_of_ty (A :: G) B j dB _ _ HEx)).
  (* the second component, moved to the codomain instance the clause reads it
     at -- named, because the pair's value mentions it twice below *)
  pose (xuc := kto (kAt FBu)
                 (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt)))
                 (famAtWf FBu)
                 (famAtWf (FB (ers rho t)
                             (upEl (kk - i) kk EA FA (ers rho t) xt)))
                 P (ers rho u) xu0).
  assert (Du : ITm rho u j
                 (wB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                 (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                 (ers rho u) xuc)
    by exact (i_conv rho u j _ FBu _
                (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (ers rho u) xu0 P Du0).
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair kk A B t u) (sig_ kk A B) dpair rho rho HEself).
  pose (xpr := sigPair kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
                 (ers rho t) (ers rho u)
                 (upEl (kk - i) kk EA FA (ers rho t) xt)
                 (upEl (kk - j) kk EB
                    (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                    (ers rho u) xuc) g).
  pose proof (i_pair rho A B t u kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho t) xt (ers rho u) xuc g eq_refl
                DFA DB Dt Du) as Dpair.
  pose proof (i_snd rho A B (pair kk A B t u) kk i j (kk - i) (kk - j) EA EB
                (ers rho A) FA B0 wB FB redB cohB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dsnd0.
  (* the codomain instance the projection picks, against the one at t *)
  assert (Pfam : kceq (kAt (FB (efst (epair (ers rho t) (ers rho u)))
                               (sigFst kk (ers rho A) B0
                                  (upF (kk - i) kk EA FA) wB
                                  (fun u0 z => upF (kk - j) kk EB (FB u0 z))
                                  redB cohB gSig
                                  (epair (ers rho t) (ers rho u)) xpr)))
                  (kAt (FB (ers rho t)
                          (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { refine (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
              (funtm (A :: G) B (UU j) dB) rho rho HEself kk i j (kk - i) EA
              (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
              (famAtSelf FA) DB DB _ _ _ _ _).
    apply sigFst_pair. }
  pose proof (i_conv rho (snd A B (pair kk A B t u)) j _ _ _ _ _ _ Pfam Dsnd0)
    as Dsnd1.
  pose proof (i_conv rho (snd A B (pair kk A B t u)) j _ _ _ FBu _ _
                (knsymU _ _ P) Dsnd1) as Dsnd.
  assert (Hfun : FunTm G (B [t..])).
  { destruct (ty_subst1 G A B (UU j) t dB dt) as [dsub].
    exact (FunTm_of_ty G (B [t..]) j dsub). }
  pose proof (ITy_cast rho (B [t..]) j _ _ E FBu DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [t..]) j (ers rho (B [t..]))
                (famCast E FBu) k (ers rho (B [t..])) F DBc DBt) as Ek; subst k.
  refine (itot_move G (snd A B (pair kk A B t u)) (B [t..]) Hfun rho Hrho j F
            (famCast E FBu) DBt DBc _ _).
  refine (ITm_cast rho (snd A B (pair kk A B t u)) j _ _ E FBu _ _ _).
  exact Dsnd.
Qed.

(* `snd (pair t u) ≡ u`.  Both sides' canonical values are constructed; the
   middle leg is sigSnd_pair at the former's annotation, brought down by
   kRel_dn along the codomain's coherence at the two arguments, and then
   `dnEl_upEl` undoes the clause's lift of the second component. *)
Lemma isem_snd_beta G kk i j A B t u (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ISem G (snd A B (pair kk A B t u)) u (B [t..]).
Proof.
  pose proof (t_pair G kk i j A B t u Hik Hjk dA dB dt du) as dpair.
  pose proof (t_snd G kk i j A B (pair kk A B t u) Hik Hjk dA dB dpair) as dsnd.
  split;
    [split; [exact (itot_snd_beta G kk i j A B t u Hik Hjk W dA dB dt du
                      IHA IHB IHt IHu)
            | exact IHu] |].
  intros rho Hrho k F DBt x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ kk A B) kk
                  (t_sig G kk i j A B Hik Hjk dA dB) rho rho HEself).
  destruct (IHt rho Hrho i FA DFA) as [xt Dt].
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho t) xt)
              (EnvITy_ext G rho A i FA DFA (ers rho t) xt Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t i (ers rho A) FA (ers rho t) xt eq_refl Dt
                B j (ers (ext rho FA (ers rho t) xt) B) FBu DBu0) as DBsub.
  destruct (IHu rho Hrho j (famCast E FBu)
              (ITy_cast rho (B [t..]) j _ _ E FBu DBsub)) as [xu' Du'].
  destruct (ITm_uncast rho u j _ _ E FBu _ _ Du') as [xu0 Du0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho t) xt)
                  (ext rho FA (ers rho t)
                     (dnEl (kk - i) kk EA FA (ers rho t)
                        (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho t) xt (ers rho t) _ HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu)
                (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
                _ FBu _ _ DBu0
                (DB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (LTyK_of_ty (A :: G) B j dB _ _ HEx)).
  (* the second component, moved to the codomain instance the clause reads it
     at -- named, because the pair's value mentions it twice below *)
  pose (xuc := kto (kAt FBu)
                 (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt)))
                 (famAtWf FBu)
                 (famAtWf (FB (ers rho t)
                             (upEl (kk - i) kk EA FA (ers rho t) xt)))
                 P (ers rho u) xu0).
  assert (Du : ITm rho u j
                 (wB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                 (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                 (ers rho u) xuc)
    by exact (i_conv rho u j _ FBu _
                (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                (ers rho u) xu0 P Du0).
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair kk A B t u) (sig_ kk A B) dpair rho rho HEself).
  pose (xpr := sigPair kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
                 (ers rho t) (ers rho u)
                 (upEl (kk - i) kk EA FA (ers rho t) xt)
                 (upEl (kk - j) kk EB
                    (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                    (ers rho u) xuc) g).
  pose proof (i_pair rho A B t u kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho t) xt (ers rho u) xuc g eq_refl
                DFA DB Dt Du) as Dpair.
  pose proof (i_snd rho A B (pair kk A B t u) kk i j (kk - i) (kk - j) EA EB
                (ers rho A) FA B0 wB FB redB cohB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dsnd0.
  (* the codomain instance the projection picks, against the one at t *)
  assert (Pfam : kceq (kAt (FB (efst (epair (ers rho t) (ers rho u)))
                               (sigFst kk (ers rho A) B0
                                  (upF (kk - i) kk EA FA) wB
                                  (fun u0 z => upF (kk - j) kk EB (FB u0 z))
                                  redB cohB gSig
                                  (epair (ers rho t) (ers rho u)) xpr)))
                  (kAt (FB (ers rho t)
                          (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { refine (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
              (funtm (A :: G) B (UU j) dB) rho rho HEself kk i j (kk - i) EA
              (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
              (famAtSelf FA) DB DB _ _ _ _ _).
    apply sigFst_pair. }
  pose proof (i_conv rho (snd A B (pair kk A B t u)) j _ _ _
                (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt)) _ _
                Pfam Dsnd0) as Dsnd1.
  (* the level and the equality to the statement's family *)
  pose proof (ITy_cast rho (B [t..]) j _ _ E FBu DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [t..]) j (ers rho (B [t..]))
                (famCast E FBu) k (ers rho (B [t..])) F DBc DBt) as Ek; subst k.
  assert (Hfun : FunTm G (B [t..])).
  { destruct (ty_subst1 G A B (UU j) t dB dt) as [dsub].
    exact (FunTm_of_ty G (B [t..]) j dsub). }
  assert (Q : kceq (kAt F)
                (kAt (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt)))).
  { eapply famCeq_tr;
      [ eapply famCeq_tr;
        [ exact (ity_same_ceq G (B [t..]) Hfun rho Hrho j F (famCast E FBu)
                   DBt DBc)
        | exact (famCeq_sym _ _ (famCast_ceq E FBu)) ]
      | exact P ]. }
  assert (Hgs : Rel (ers (ext rho FA (ers rho t) xt) B)
                  (ers rho (snd A B (pair kk A B t u)))
                  (ers rho (snd A B (pair kk A B t u)))).
  { rewrite E.
    pose proof (LCv_of_cv G (snd A B (pair kk A B t u)) u (B [t..])
                  (c_snd_beta G kk i j A B t u Hik Hjk dA dB dt du)
                  rho rho HEself) as Hc.
    eapply Rel_trans; [exact Hc | apply Rel_sym; exact Hc]. }
  pose proof (funtm G (snd A B (pair kk A B t u)) (B [(fst A B (pair kk A B t u))..])
                dsnd rho rho HEself j _ F _ x Dx
                _ (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt)) _ _
                Dsnd1 Q Hgs) as H1.
  pose proof (funtm G u (B [t..]) du rho rho HEself j
                _ (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                _ xuc Du _ F _ y Dy (knsymU _ _ Q)
                (LTm_of_ty G u (B [t..]) du rho rho HEself)) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  (* the second projection of a pair is its second component *)
  eapply kRel_trans;
    [ apply kRel_sym; split; [exact Pfam | exact (kto_coh _ _ _ _ Pfam _ _)] |].
  eapply kRel_trans;
    [ refine (kRel_dn (kk - j) kk EB _ _ Pfam _ _ _ _ _);
      exact (sigSnd_pair kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
               (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
               (ers rho t) (ers rho u)
               (upEl (kk - i) kk EA FA (ers rho t) xt)
               (upEl (kk - j) kk EB
                  (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
                  (ers rho u) xuc) g) |].
  apply (proj1 (kRel_same _ _ _ _ _)).
  exact (dnEl_upEl (kk - j) kk EB
           (FB (ers rho t) (upEl (kk - i) kk EA FA (ers rho t) xt))
           (ers rho u) xuc).
Qed.

(* ---- surjective pairing.  The pair of the two projections IS the subject:
     `sigPair_surj` says so at the former's annotation, and the two pairs
     differ only in the ROUND TRIPS the clauses put on the components -- the
     projection unlifts (`dnEl`) and the pair lifts again (`upEl`) -- so
     `sigPair_eq` with `upEl_dnEl` on each component closes the gap. ---- *)
Lemma isem_surj G kk i j A B p (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dp : ty G p (sig_ kk A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHp : ITot G p (sig_ kk A B)) :
  ISem G (pair kk A B (fst A B p) (snd A B p)) p (sig_ kk A B).
Proof.
  pose proof (t_fst G kk i j A B p Hik Hjk dA dB dp) as dfst.
  pose proof (t_snd G kk i j A B p Hik Hjk dA dB dp) as dsnd.
  pose proof (t_pair G kk i j A B (fst A B p) (snd A B p) Hik Hjk dA dB
                dfst dsnd) as dpv.
  split;
    [split; [exact (itot_pair G A B (fst A B p) (snd A B p) kk i j Hik Hjk
                      dA dB dfst dsnd IHA IHB
                      (itot_fst G A B p kk i j Hik Hjk dA dB dp IHA IHB IHp)
                      (itot_snd G A B p kk i j Hik Hjk dA dB dp IHA IHB IHp))
            | exact IHp] |].
  intros rho Hrho k F Dsg x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gSig := LTyK_of_ty G (sig_ kk A B) kk
                  (t_sig G kk i j A B Hik Hjk dA dB) rho rho HEself).
  pose proof (ity_sig rho A B kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho kk
              (sigFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig)
              Dsig) as [xp Dp].
  pose proof (i_fst rho A B p kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  pose proof (i_snd rho A B p kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gSig (ers rho p) xp eq_refl DFA DB Dp) as Dsnd.
  (* the first projection's round trip moves the codomain instance *)
  assert (Pfam : kceq
                  (kAt (FB (efst (ers rho p))
                          (upEl (kk - i) kk EA FA (efst (ers rho p))
                             (dnEl (kk - i) kk EA FA (efst (ers rho p))
                                (sigFst kk (ers rho A) B0
                                   (upF (kk - i) kk EA FA) wB
                                   (fun u0 z => upF (kk - j) kk EB (FB u0 z))
                                   redB cohB gSig (ers rho p) xp)))))
                  (kAt (FB (efst (ers rho p))
                          (sigFst kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                             (fun u0 z => upF (kk - j) kk EB (FB u0 z))
                             redB cohB gSig (ers rho p) xp)))).
  { refine (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
              (funtm (A :: G) B (UU j) dB) rho rho HEself kk i j (kk - i) EA
              (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
              (famAtSelf FA) DB DB _ _ _ _ _).
    apply upEl_dnEl. }
  pose proof (i_conv rho (snd A B p) j _ _ _ _ _ _ (knsymU _ _ Pfam) Dsnd)
    as Dsnd'.
  assert (gT : Good_ty (esig (ers rho A) B0)) by (exists kk; exact gSig).
  pose proof (LTm_of_ty G p (sig_ kk A B) dp rho rho HEself) as Hgp.
  pose proof (sig_eta_rel _ _ _ _ _ gT (ev_sig _ _) Hgp) as gr.
  assert (g2 : Good (esig (ers rho A) B0)
                 (epair (efst (ers rho p)) (esnd (ers rho p))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (i_pair rho A B (fst A B p) (snd A B p) kk i j (kk - i) (kk - j)
                EA EB (ers rho A) FA B0 wB FB redB cohB gSig
                (efst (ers rho p)) _ (esnd (ers rho p)) _ g2 eq_refl DFA DB
                Dfst Dsnd') as Dpv.
  (* the level and the equality to the statement's family *)
  pose proof (ity_lvl rho rho eq_refl (sig_ kk A B) kk
                (ers rho (sig_ kk A B)) _ k (ers rho (sig_ kk A B)) F Dsig Dsg)
    as Ek; subst k.
  pose proof (ity_same_ceq G (sig_ kk A B)
                (FunTm_of_ty G (sig_ kk A B) kk
                   (t_sig G kk i j A B Hik Hjk dA dB))
                rho Hrho kk F _ Dsg Dsig) as Q.
  pose proof (funtm G (pair kk A B (fst A B p) (snd A B p)) (sig_ kk A B) dpv
                rho rho HEself kk _ F _ x Dx _ _ _ _ Dpv Q g2) as H1.
  pose proof (funtm G p (sig_ kk A B) dp rho rho HEself kk _ _ _ xp Dp
                _ F _ y Dy (knsymU _ _ Q) Hgp) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  apply (proj1 (kRel_same _ _ _ _ _)).
  (* the constructed pair against the pair of the projections, and then the
     surjectivity law *)
  eapply kEqAt_trans;
    [ exact (famAtSelf _)
    | refine (sigPair_eq kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
                (efst (ers rho p)) (esnd (ers rho p)) _ _ g2
                (efst (ers rho p)) (esnd (ers rho p))
                (sigFst kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                   (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
                   (ers rho p) xp)
                (sigSnd kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                   (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
                   (ers rho p) xp) g2 _ _ _)
    | exact (sigPair_surj kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
               (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig
               (ers rho p) xp g2 gr) ].
  - (* the two pairs are layer-1 related: they have the same realiser *)
    exact g2.
  - (* the first components: the round trip *)
    apply upEl_dnEl.
  - (* the second components: the coercion's coherence, then the round trip *)
    eapply kRel_trans;
      [ refine (kRel_up (kk - j) kk EB _ _ _ _ _ _ _);
        split;
        [ exact Pfam
        | apply kEqAt_sym;
          exact (kto_coh _ _ _ _ (knsymU _ _ Pfam) _ _) ] |].
    apply (proj1 (kRel_same _ _ _ _ _)).
    apply upEl_dnEl.
Qed.

(* ---- beta.  The lambda's value is BUILT (piLam), applied (piApp), and the
     application's own clause brings the result back down through the
     codomain's gap; `piLam_app` says the application of a built lambda is the
     body's value, and `dnEl_upEl` undoes the gap's round trip.  The
     right-hand side is a substitution instance, and its value is the body's
     in the extended environment, carried down by isubst_ITm. ---- *)

Lemma ITm_vcast rho t k w (F : kUFam k w) v v' (Ev : v = v') (x : kElAt F v) :
  ITm rho t k w F v x -> { y : kElAt F v' & ITm rho t k w F v' y }.
Proof. destruct Ev; intros D; exists x; exact D. Qed.

Lemma itot_subst1 G A B t u i j (dA : ty G A (UU i))
  (dB : ty (A :: G) B (UU j)) (dt : ty (A :: G) t B) (du : ty G u A)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot (A :: G) t B) (IHu : ITot G u A) : ITot G (t [u..]) (B [u..]).
Proof.
  intros rho Hrho k F DBu.
  destruct (ityT_of_ITot G A i IHA rho Hrho) as [FA DFA].
  destruct (IHu rho Hrho i FA DFA) as [xu Du].
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  assert (Ev : ers (ext rho FA (ers rho u) xu) t = ers rho (t [u..]))
    by exact (eq_sym (ers_sub1 rho t u FA xu)).
  pose proof (isubst_ITy rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                B j _ FBu DBu0) as DBsub.
  destruct (IHt (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho) j FBu DBu0)
    as [z Dz].
  pose proof (isubst_ITm rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                t j _ FBu _ z Dz) as Dzs.
  destruct (ITm_vcast rho (t [u..]) j _ FBu _ _ Ev z Dzs) as [z' Dz'].
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (UU j) u dB du) as [dsub].
    exact (FunTm_of_ty G (B [u..]) j dsub). }
  pose proof (ITy_cast rho (B [u..]) j _ _ E FBu DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [u..]) j (ers rho (B [u..]))
                (famCast E FBu) k (ers rho (B [u..])) F DBc DBu) as Ek; subst k.
  refine (itot_move G (t [u..]) (B [u..]) Hfun rho Hrho j F
            (famCast E FBu) DBu DBc _ _).
  refine (ITm_cast rho (t [u..]) j _ _ E FBu _ _ _).
  exact Dz'.
Qed.

Lemma isem_beta G kk i j A B t u (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (dt : ty (A :: G) t B) (du : ty G u A)
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHt : ITot (A :: G) t B) (IHu : ITot G u A) :
  ISem G (app A B (lam kk A B t) u) (t [u..]) (B [u..]).
Proof.
  pose proof (t_lam G kk i j A B t Hik Hjk dA dB dt) as dlam.
  pose proof (t_app G kk i j A B (lam kk A B t) u Hik Hjk dA dB dlam du) as dapp.
  split;
    [split; [exact (itot_app G A B (lam kk A B t) u kk i j Hik Hjk dA dB dlam du
                      IHA IHB (itot_lam G A B t kk i j Hik Hjk dA dB dt
                                 IHA IHB IHt) IHu)
            | exact (itot_subst1 G A B t u i j dA dB dt du IHA IHB IHt IHu)] |].
  intros rho Hrho k F DBu x y Dx Dy.
  (* the two substitution instances' typing derivations: `ty_subst1` lands in
     `inhabited`, so they can only be opened where the goal is a Prop *)
  destruct (ty_subst1 G A t B u dt du) as [dsub].
  destruct (ty_subst1 G A B (UU j) u dB du) as [dBsub0].
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gPi := LTyK_of_ty G (pi kk A B) kk
                 (t_pi G kk i j A B Hik Hjk dA dB) rho rho HEself).
  (* the body's value at every argument, and the lambda it makes *)
  pose (wt := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) t).
  pose (xt := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                projT1 (IHt (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z))
                          (EnvITy_ext G rho A i FA DFA u0 _ Hrho) j (FB u0 z)
                          (DB u0 z))).
  assert (Dt : forall u0 z,
             ITm (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) t j
               (wB u0 z) (FB u0 z) (wt u0 z) (xt u0 z))
    by (intros u0 z;
        exact (projT2 (IHt (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z))
                         (EnvITy_ext G rho A i FA DFA u0 _ Hrho) j (FB u0 z)
                         (DB u0 z)))).
  assert (xtext : forall u0 z u0' z',
             kEqAt (upF (kk - i) kk EA FA) u0 z (upF (kk - i) kk EA FA) u0' z' ->
             kEqAt (upF (kk - j) kk EB (FB u0 z)) (wt u0 z)
                     (upEl (kk - j) kk EB (FB u0 z) (wt u0 z) (xt u0 z))
                   (upF (kk - j) kk EB (FB u0' z')) (wt u0' z')
                     (upEl (kk - j) kk EB (FB u0' z') (wt u0' z') (xt u0' z'))).
  { intros u0 z u0' z' Hzz.
    assert (HEz : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z))
                    (ext rho FA u0' (dnEl (kk - i) kk EA FA u0' z'))).
    { apply (EnvRelOf_ext G rho rho A i FA FA _ _ _ _ HEself).
      exact (kRel_dn (kk - i) kk EA FA FA (famAtSelf FA) _ _ _ _
               (conj (famAtSelf (upF (kk - i) kk EA FA)) Hzz)). }
    refine (kRel_at (kRel_up (kk - j) kk EB _ _ _ _ _ _ _)).
    refine (funtm (A :: G) t B dt _ _ HEz j _ (FB u0 z) _ (xt u0 z) (Dt u0 z)
              _ (FB u0' z') _ (xt u0' z') (Dt u0' z')
              (cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
                 (funtm (A :: G) B (UU j) dB) rho rho HEself kk i j (kk - i) EA
                 _ FA wB FB _ FA wB FB DFA DFA (famAtSelf FA) DB DB
                 _ _ _ _ Hzz) _).
    apply (Rel_tyeq (ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B)
             (ers (ext rho FA u0' (dnEl (kk - i) kk EA FA u0' z')) B));
      [ exact (LTy_of_ty (A :: G) B j dB _ _ HEz)
      | exact (LTm_of_ty (A :: G) t B dt _ _ HEz) ]. }
  assert (gd : Good (epi (ers rho A) B0) (ers rho (lam kk A B t)))
    by exact (LTm_of_ty G (lam kk A B t) (pi kk A B) dlam rho rho HEself).
  pose proof (i_lam rho A B t kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gPi (ers rho (lam kk A B t)) wt xt
                (fun u0 z => reds_lam_app (er t) (rsub rho) u0) xtext gd
                eq_refl eq_refl DFA DB Dt) as Dlam.
  destruct (IHu rho Hrho i FA DFA) as [xu Du].
  pose proof (i_app rho A B (lam kk A B t) u kk i j (kk - i) (kk - j) EA EB
                (ers rho A) FA B0 wB FB redB cohB gPi
                (ers rho (lam kk A B t)) _ (ers rho u) xu eq_refl DFA DB
                Dlam Du) as Dapp.
  (* the substituted body, read in the environment that carries the argument's
     own value, and the two readings' equality *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho)) as [FBu DBu0].
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  assert (Ev : ers (ext rho FA (ers rho u) xu) t = ers rho (t [u..]))
    by exact (eq_sym (ers_sub1 rho t u FA xu)).
  pose proof (isubst_ITy rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                B j _ FBu DBu0) as DBsub.
  destruct (IHt (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A i FA DFA (ers rho u) xu Hrho) j FBu DBu0)
    as [z Dz].
  pose proof (isubst_ITm rho u i (ers rho A) FA (ers rho u) xu eq_refl Du
                t j _ FBu _ z Dz) as Dzs.
  assert (HEx : EnvRelOf (A :: G)
                  (ext rho FA (ers rho u)
                     (dnEl (kk - i) kk EA FA (ers rho u)
                        (upEl (kk - i) kk EA FA (ers rho u) xu)))
                  (ext rho FA (ers rho u) xu)).
  { apply (EnvRelOf_ext G rho rho A i FA FA _ _ (ers rho u) xu HEself).
    split; [exact (famAtSelf FA) | apply dnEl_upEl]. }
  assert (P : kceq (kAt (FB (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu)))
                (kAt FBu))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
                _ _ _ FBu
                (DB (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu)) DBu0
                (LTyK_of_ty (A :: G) B j dB _ _ HEx)).
  (* the level, and the statement's family *)
  pose proof (ITy_cast rho (B [u..]) j _ _ E FBu DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [u..]) j (ers rho (B [u..]))
                (famCast E FBu) k (ers rho (B [u..])) F DBc DBu) as Ek; subst k.
  assert (Q : kceq (kAt F) (kAt FBu)).
  { eapply famCeq_tr;
      [ exact (ity_same_ceq G (B [u..]) (FunTm_of_ty G (B [u..]) j dBsub0)
                 rho Hrho j F (famCast E FBu) DBu DBc)
      | exact (famCeq_sym _ _ (famCast_ceq E FBu)) ]. }
  assert (Hg1 : Rel (ers (ext rho FA (ers rho u) xu) B)
                  (ers rho (app A B (lam kk A B t) u))
                  (eapp (ers rho (lam kk A B t)) (ers rho u))).
  { rewrite E.
    exact (LTm_of_ty G (app A B (lam kk A B t) u) (B [u..]) dapp
             rho rho HEself). }
  pose proof (funtm G (app A B (lam kk A B t) u) (B [u..]) dapp rho rho HEself
                j _ F _ x Dx
                _ (FB (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu)) _ _
                Dapp (famCeq_tr _ _ _ Q (famCeq_sym _ _ P)) Hg1) as H1.
  assert (Hg3 : Rel (ers rho (B [u..]))
                  (ers (ext rho FA (ers rho u) xu) t) (ers rho (t [u..]))).
  { rewrite Ev. exact (LTm_of_ty G (t [u..]) (B [u..]) dsub rho rho HEself). }
  pose proof (funtm G (t [u..]) (B [u..]) dsub rho rho HEself j _ FBu _ z Dzs
                _ F _ y Dy (knsymU _ _ Q) Hg3) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  (* the application of the built lambda IS the body's value, once the gap's
     round trip is undone *)
  eapply kRel_trans;
    [ apply (proj1 (kRel_same
                      (FB (ers rho u)
                         (upEl (kk - i) kk EA FA (ers rho u) xu)) _ _ _ _));
      eapply kEqAt_trans;
      [ exact (famAtSelf _)
      | refine (kRel_at (kRel_dn (kk - j) kk EB _ _ (famAtSelf _) _ _ _ _ _));
        split;
        [ exact (famAtSelf _)
        | exact (piLam_app kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                   (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi
                   (ers rho (lam kk A B t)) wt
                   (fun u0 z =>
                      upEl (kk - j) kk EB (FB u0 z) (wt u0 z) (xt u0 z))
                   (fun u0 z => reds_lam_app (er t) (rsub rho) u0) xtext gd
                   (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu)) ]
      | apply dnEl_upEl ] |].
  (* and the body's two readings agree *)
  refine (funtm (A :: G) t B dt _ _ HEx j
            _ (FB (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu)) _ _
            (Dt (ers rho u) (upEl (kk - i) kk EA FA (ers rho u) xu))
            _ FBu _ z Dz P _).
  apply (Rel_tyeq (ers (ext rho FA (ers rho u) xu) B)
           (ers (ext rho FA (ers rho u) xu) B));
    [ exists j; exact (uf_ty FBu)
    | exact (LTm_of_ty (A :: G) t B dt _ _ HEx) ].
Qed.

(* ---- the lift's computation rules at the BINDER formers.  The two sides
     of `up kk (pi kk A B) ≡ pi (S kk) A B` are genuinely different shapes in
     v2 -- the lift of the whole Pi family against the Pi family of the lifted
     components -- and `Interp/LiftFam.v` is the proof that they agree.  Here
     the two readings the statement is handed are first compared to CANONICAL
     ones (functionality on the diagonal), which is what lets the proof choose
     the components: the same `FA`/`FB` appear on both sides, with the gaps
     `kk - i` and `S (kk - i)`, and `famLiftK_upF`/`dnEl_famLiftK` are the
     gap bookkeeping. ---- *)

Lemma isem_up_pi G kk i j A B (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ISem G (up kk (pi kk A B)) (pi (S kk) A B) (UU (S kk)).
Proof.
  pose proof (t_pi G kk i j A B Hik Hjk dA dB) as dpi.
  pose proof (t_pi G (S kk) i j A B (le_S i kk Hik) (le_S j kk Hjk) dA dB)
    as dpi'.
  apply (isem_former_cv G (up kk (pi kk A B)) (pi (S kk) A B) (S kk)
           (itot_up G (pi kk A B) kk W dpi
              (itot_pi G A B kk i j W Hik Hjk dA dB IHA IHB))
           (itot_pi G A B (S kk) i j W (le_S i kk Hik) (le_S j kk Hjk) dA dB
              IHA IHB)
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  split.
  - exact (LCvK_of_cv G (up kk (pi kk A B)) (pi (S kk) A B) (S kk)
             (c_up_pi G kk i j A B Hik Hjk dA dB) rho rho HEself).
  - assert (EA : (kk - i) + i = kk) by lia.
    assert (EB : (kk - j) + j = kk) by lia.
    assert (EA1 : S (kk - i) + i = S kk) by lia.
    assert (EB1 : S (kk - j) + j = S kk) by lia.
    destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
                rho Hrho) as [FA [FB [[DFA DB] cohB]]].
    destruct (build_fam_data G A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                dA dB IHA IHB rho Hrho) as [FA2 [FB2 [[DFA2 DB2] cohB2]]].
    pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
    pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
    pose (wB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                   ers (ext rho FA2 u0
                          (dnEl (S (kk - i)) (S kk) EA1 FA2 u0 z)) B).
    pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                    reds_lam_app (er B) (rsub rho) u0).
    pose (redB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                     reds_lam_app (er B) (rsub rho) u0).
    pose (gPi := LTyK_of_ty G (pi kk A B) kk dpi rho rho HEself).
    pose (gPi2 := LTyK_of_ty G (pi (S kk) A B) (S kk) dpi' rho rho HEself).
    (* the two canonical readings *)
    pose proof (ity_pi rho A B kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                  wB FB redB cohB gPi eq_refl DFA DB) as DPi.
    pose proof (ity_up rho (pi kk A B) kk (ers rho (pi kk A B)) _ DPi) as DC1.
    pose proof (ity_pi rho A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                  (ers rho A) FA2 B0 wB2 FB2 redB2 cohB2 gPi2 eq_refl DFA2 DB2)
      as DC2.
    (* the domains, and the codomains at a related pair of arguments *)
    assert (QA : kceq (kAt FA) (kAt FA2))
      by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i FA FA2
                  DFA DFA2).
    assert (HA : kceq (kAt (famLiftK (upF (kk - i) kk EA FA)))
                   (kAt (upF (S (kk - i)) (S kk) EA1 FA2))).
    { eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - i) kk EA EA1 FA)
        | exact (upF_ceq (S (kk - i)) (S kk) EA1 FA FA2 QA) ]. }
    assert (HB : forall u x u' x',
               kEqAt (famLiftK (upF (kk - i) kk EA FA)) u x
                     (upF (S (kk - i)) (S kk) EA1 FA2) u' x' ->
               kceq (kAt (liftFB kk (ers rho A) (upF (kk - i) kk EA FA) wB
                            (fun u0 z => upF (kk - j) kk EB (FB u0 z)) u x))
                    (kAt (upF (S (kk - j)) (S kk) EB1 (FB2 u' x')))).
    { intros u x u' x' Hxx.
      pose proof (dnEl_famLiftK (kk - i) kk EA EA1 FA FA2 QA u x u' x' Hxx)
        as Hd.
      assert (HEx : EnvRelOf (A :: G)
                      (ext rho FA u
                         (dnEl (kk - i) kk EA FA u
                            (elUnlift (upF (kk - i) kk EA FA) u x)))
                      (ext rho FA2 u'
                         (dnEl (S (kk - i)) (S kk) EA1 FA2 u' x')))
        by exact (EnvRelOf_ext G rho rho A i FA FA2 _ _ _ _ HEself
                    (conj QA Hd)).
      unfold liftFB.
      eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - j) kk EB EB1
                   (FB u (elUnlift (upF (kk - i) kk EA FA) u x)))
        | apply (upF_ceq (S (kk - j)) (S kk) EB1) ].
      exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
               _ _ _ _ (DB u (elUnlift (upF (kk - i) kk EA FA) u x))
               (DB2 u' x') (LTyK_of_ty (A :: G) B j dB _ _ HEx)). }
    (* and the three legs *)
    refine (famCeq_tr _ _ _
              (ity_same_ceq G (up kk (pi kk A B))
                 (funtm G (up kk (pi kk A B)) (UU (S kk))
                    (t_up G kk (pi kk A B) dpi)) rho Hrho (S kk) F1 _ D1 DC1)
              (famCeq_tr _ _ _ _
                 (famCeq_sym _ _
                    (ity_same_ceq G (pi (S kk) A B)
                       (funtm G (pi (S kk) A B) (UU (S kk)) dpi')
                       rho Hrho (S kk) F2 _ D2 DC2)))).
    eapply famCeq_tr;
      [ exact (famLiftK_piFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi) |].
    apply piFam_ceq; [ exists (S kk); exact gPi2 | exact HA | exact HB ].
Qed.

Lemma isem_up_sig G kk i j A B (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ISem G (up kk (sig_ kk A B)) (sig_ (S kk) A B) (UU (S kk)).
Proof.
  pose proof (t_sig G kk i j A B Hik Hjk dA dB) as dsig.
  pose proof (t_sig G (S kk) i j A B (le_S i kk Hik) (le_S j kk Hjk) dA dB)
    as dsig'.
  apply (isem_former_cv G (up kk (sig_ kk A B)) (sig_ (S kk) A B) (S kk)
           (itot_up G (sig_ kk A B) kk W dsig
              (itot_sig G A B kk i j W Hik Hjk dA dB IHA IHB))
           (itot_sig G A B (S kk) i j W (le_S i kk Hik) (le_S j kk Hjk) dA dB
              IHA IHB)
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  split.
  - exact (LCvK_of_cv G (up kk (sig_ kk A B)) (sig_ (S kk) A B) (S kk)
             (c_up_sig G kk i j A B Hik Hjk dA dB) rho rho HEself).
  - assert (EA : (kk - i) + i = kk) by lia.
    assert (EB : (kk - j) + j = kk) by lia.
    assert (EA1 : S (kk - i) + i = S kk) by lia.
    assert (EB1 : S (kk - j) + j = S kk) by lia.
    destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
                rho Hrho) as [FA [FB [[DFA DB] cohB]]].
    destruct (build_fam_data G A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                dA dB IHA IHB rho Hrho) as [FA2 [FB2 [[DFA2 DB2] cohB2]]].
    pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
    pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
    pose (wB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                   ers (ext rho FA2 u0
                          (dnEl (S (kk - i)) (S kk) EA1 FA2 u0 z)) B).
    pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                    reds_lam_app (er B) (rsub rho) u0).
    pose (redB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                     reds_lam_app (er B) (rsub rho) u0).
    pose (gSig := LTyK_of_ty G (sig_ kk A B) kk dsig rho rho HEself).
    pose (gSig2 := LTyK_of_ty G (sig_ (S kk) A B) (S kk) dsig' rho rho HEself).
    (* the two canonical readings *)
    pose proof (ity_sig rho A B kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                  wB FB redB cohB gSig eq_refl DFA DB) as DSig.
    pose proof (ity_up rho (sig_ kk A B) kk (ers rho (sig_ kk A B)) _ DSig) as DC1.
    pose proof (ity_sig rho A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                  (ers rho A) FA2 B0 wB2 FB2 redB2 cohB2 gSig2 eq_refl DFA2 DB2)
      as DC2.
    (* the domains, and the codomains at a related pair of arguments *)
    assert (QA : kceq (kAt FA) (kAt FA2))
      by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i FA FA2
                  DFA DFA2).
    assert (HA : kceq (kAt (famLiftK (upF (kk - i) kk EA FA)))
                   (kAt (upF (S (kk - i)) (S kk) EA1 FA2))).
    { eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - i) kk EA EA1 FA)
        | exact (upF_ceq (S (kk - i)) (S kk) EA1 FA FA2 QA) ]. }
    assert (HB : forall u x u' x',
               kEqAt (famLiftK (upF (kk - i) kk EA FA)) u x
                     (upF (S (kk - i)) (S kk) EA1 FA2) u' x' ->
               kceq (kAt (liftFB kk (ers rho A) (upF (kk - i) kk EA FA) wB
                            (fun u0 z => upF (kk - j) kk EB (FB u0 z)) u x))
                    (kAt (upF (S (kk - j)) (S kk) EB1 (FB2 u' x')))).
    { intros u x u' x' Hxx.
      pose proof (dnEl_famLiftK (kk - i) kk EA EA1 FA FA2 QA u x u' x' Hxx)
        as Hd.
      assert (HEx : EnvRelOf (A :: G)
                      (ext rho FA u
                         (dnEl (kk - i) kk EA FA u
                            (elUnlift (upF (kk - i) kk EA FA) u x)))
                      (ext rho FA2 u'
                         (dnEl (S (kk - i)) (S kk) EA1 FA2 u' x')))
        by exact (EnvRelOf_ext G rho rho A i FA FA2 _ _ _ _ HEself
                    (conj QA Hd)).
      unfold liftFB.
      eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - j) kk EB EB1
                   (FB u (elUnlift (upF (kk - i) kk EA FA) u x)))
        | apply (upF_ceq (S (kk - j)) (S kk) EB1) ].
      exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
               _ _ _ _ (DB u (elUnlift (upF (kk - i) kk EA FA) u x))
               (DB2 u' x') (LTyK_of_ty (A :: G) B j dB _ _ HEx)). }
    (* and the three legs *)
    refine (famCeq_tr _ _ _
              (ity_same_ceq G (up kk (sig_ kk A B))
                 (funtm G (up kk (sig_ kk A B)) (UU (S kk))
                    (t_up G kk (sig_ kk A B) dsig)) rho Hrho (S kk) F1 _ D1 DC1)
              (famCeq_tr _ _ _ _
                 (famCeq_sym _ _
                    (ity_same_ceq G (sig_ (S kk) A B)
                       (funtm G (sig_ (S kk) A B) (UU (S kk)) dsig')
                       rho Hrho (S kk) F2 _ D2 DC2)))).
    eapply famCeq_tr;
      [ exact (famLiftK_sigFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gSig) |].
    apply sigFam_ceq; [ exists (S kk); exact gSig2 | exact HA | exact HB ].
Qed.

Lemma isem_up_w G kk i j A B (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j)) :
  ISem G (up kk (wt kk A B)) (wt (S kk) A B) (UU (S kk)).
Proof.
  pose proof (t_w G kk i j A B Hik Hjk dA dB) as dw.
  pose proof (t_w G (S kk) i j A B (le_S i kk Hik) (le_S j kk Hjk) dA dB)
    as dw'.
  apply (isem_former_cv G (up kk (wt kk A B)) (wt (S kk) A B) (S kk)
           (itot_up G (wt kk A B) kk W dw
              (itot_wt G A B kk i j W Hik Hjk dA dB IHA IHB))
           (itot_wt G A B (S kk) i j W (le_S i kk Hik) (le_S j kk Hjk) dA dB
              IHA IHB)
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H)).
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  split.
  - exact (LCvK_of_cv G (up kk (wt kk A B)) (wt (S kk) A B) (S kk)
             (c_up_w G kk i j A B Hik Hjk dA dB) rho rho HEself).
  - assert (EA : (kk - i) + i = kk) by lia.
    assert (EB : (kk - j) + j = kk) by lia.
    assert (EA1 : S (kk - i) + i = S kk) by lia.
    assert (EB1 : S (kk - j) + j = S kk) by lia.
    destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
                rho Hrho) as [FA [FB [[DFA DB] cohB]]].
    destruct (build_fam_data G A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                dA dB IHA IHB rho Hrho) as [FA2 [FB2 [[DFA2 DB2] cohB2]]].
    pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
    pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
    pose (wB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                   ers (ext rho FA2 u0
                          (dnEl (S (kk - i)) (S kk) EA1 FA2 u0 z)) B).
    pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                    reds_lam_app (er B) (rsub rho) u0).
    pose (redB2 := fun u0 (z : kElAt (upF (S (kk - i)) (S kk) EA1 FA2) u0) =>
                     reds_lam_app (er B) (rsub rho) u0).
    pose (gW := LTyK_of_ty G (wt kk A B) kk dw rho rho HEself).
    pose (gW2 := LTyK_of_ty G (wt (S kk) A B) (S kk) dw' rho rho HEself).
    (* the two canonical readings *)
    pose proof (ity_w rho A B kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                  wB FB redB cohB gW eq_refl DFA DB) as DW.
    pose proof (ity_up rho (wt kk A B) kk (ers rho (wt kk A B)) _ DW) as DC1.
    pose proof (ity_w rho A B (S kk) i j (S (kk - i)) (S (kk - j)) EA1 EB1
                  (ers rho A) FA2 B0 wB2 FB2 redB2 cohB2 gW2 eq_refl DFA2 DB2)
      as DC2.
    (* the domains, and the codomains at a related pair of arguments *)
    assert (QA : kceq (kAt FA) (kAt FA2))
      by exact (ity_same_ceq G A (funtm G A (UU i) dA) rho Hrho i FA FA2
                  DFA DFA2).
    assert (HA : kceq (kAt (famLiftK (upF (kk - i) kk EA FA)))
                   (kAt (upF (S (kk - i)) (S kk) EA1 FA2))).
    { eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - i) kk EA EA1 FA)
        | exact (upF_ceq (S (kk - i)) (S kk) EA1 FA FA2 QA) ]. }
    assert (HB : forall u x u' x',
               kEqAt (famLiftK (upF (kk - i) kk EA FA)) u x
                     (upF (S (kk - i)) (S kk) EA1 FA2) u' x' ->
               kceq (kAt (liftFB kk (ers rho A) (upF (kk - i) kk EA FA) wB
                            (fun u0 z => upF (kk - j) kk EB (FB u0 z)) u x))
                    (kAt (upF (S (kk - j)) (S kk) EB1 (FB2 u' x')))).
    { intros u x u' x' Hxx.
      pose proof (dnEl_famLiftK (kk - i) kk EA EA1 FA FA2 QA u x u' x' Hxx)
        as Hd.
      assert (HEx : EnvRelOf (A :: G)
                      (ext rho FA u
                         (dnEl (kk - i) kk EA FA u
                            (elUnlift (upF (kk - i) kk EA FA) u x)))
                      (ext rho FA2 u'
                         (dnEl (S (kk - i)) (S kk) EA1 FA2 u' x')))
        by exact (EnvRelOf_ext G rho rho A i FA FA2 _ _ _ _ HEself
                    (conj QA Hd)).
      unfold liftFB.
      eapply famCeq_tr;
        [ exact (famLiftK_upF (kk - j) kk EB EB1
                   (FB u (elUnlift (upF (kk - i) kk EA FA) u x)))
        | apply (upF_ceq (S (kk - j)) (S kk) EB1) ].
      exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dB) _ _ HEx j
               _ _ _ _ (DB u (elUnlift (upF (kk - i) kk EA FA) u x))
               (DB2 u' x') (LTyK_of_ty (A :: G) B j dB _ _ HEx)). }
    (* and the three legs *)
    refine (famCeq_tr _ _ _
              (ity_same_ceq G (up kk (wt kk A B))
                 (funtm G (up kk (wt kk A B)) (UU (S kk))
                    (t_up G kk (wt kk A B) dw)) rho Hrho (S kk) F1 _ D1 DC1)
              (famCeq_tr _ _ _ _
                 (famCeq_sym _ _
                    (ity_same_ceq G (wt (S kk) A B)
                       (funtm G (wt (S kk) A B) (UU (S kk)) dw')
                       rho Hrho (S kk) F2 _ D2 DC2)))).
    eapply famCeq_tr;
      [ exact (famLiftK_wFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gW) |].
    apply wFam_ceq; [ exists (S kk); exact gW2 | exact HA | exact HB ].
Qed.

(* ---- the lift's computation rules at the component-free formers.  All four
     have the same shape: the subject's reading is lifted, the right-hand
     side's is canonical one level up, and the two agree by the one-step
     commutation of Interp/Lift.v (nat, prop, Prf) or by famLiftK_upF (the
     universe, whose reading is a gap-lift of `univFam`). ---- *)

Lemma isem_up_former G k (X X' : tm) (W : Rules.wfc G) (dX : ty G X (UU k))
  (HX : ITot G X (UU k)) (HX' : ITot G X' (UU (S k)))
  (Hshu : forall rho k' Sy (F : kUFam k' Sy) w (x : kElAt F w),
            TmShape rho X' k' Sy F w x -> TyVal rho X' k' Sy F w x)
  (Hty : forall rho, EnvITy G rho ->
           eqty (S k) (ers rho (up k X)) (ers rho X'))
  (Hceq : forall rho (Hrho : EnvITy G rho)
            (F1 : kUFam k (ers rho (up k X))) (F2 : kUFam (S k) (ers rho X')),
            ITy rho X k (ers rho (up k X)) F1 ->
            ITy rho X' (S k) (ers rho X') F2 ->
            kceq (kAt (famLiftK F1)) (kAt F2)) :
  ISem G (up k X) X' (UU (S k)).
Proof.
  apply (isem_former_cv G (up k X) X' (S k)
           (itot_up G X k W dX HX) HX'
           (fun rho k' Sy F w x H => H) Hshu).
  intros rho Hrho F1 F2 D1 D2.
  split; [exact (Hty rho Hrho) |].
  destruct (ity_up_inv rho (up k X) (S k) (ers rho (up k X)) F1 D1)
    as [F1a [[Ej DX0] Hc1]].
  refine (famCeq_tr _ _ _ Hc1 _).
  exact (Hceq rho Hrho F1a F2 DX0 D2).
Qed.

Lemma isem_up_nat G k (W : Rules.wfc G) :
  ISem G (up k (nat_ k)) (nat_ (S k)) (UU (S k)).
Proof.
  apply (isem_up_former G k (nat_ k) (nat_ (S k)) W (t_nat G k W)
           (itot_nat G W k) (itot_nat G W (S k))
           (fun rho k' Sy F w x H => H));
    [ intros rho Hrho; apply eqty_nat; apply eval_whnf; exact whnf_nat |].
  intros rho Hrho F1 F2 D1 D2.
  pose proof (ity_nat_inv rho (nat_ k) k (ers rho (up k (nat_ k))) F1 D1) as Q1.
  pose proof (ity_nat_inv rho (nat_ (S k)) (S k) (ers rho (nat_ (S k))) F2 D2)
    as Q2.
  cbn [NatDec] in Q1, Q2.
  eapply famCeq_tr; [exact (famLiftK_ceq F1 (natFam k) Q1) |].
  eapply famCeq_tr; [apply famLiftK_natFam | exact (famCeq_sym _ _ Q2)].
Qed.

Lemma isem_up_prop G k (W : Rules.wfc G) :
  ISem G (up k (prop k)) (prop (S k)) (UU (S k)).
Proof.
  apply (isem_up_former G k (prop k) (prop (S k)) W (t_prop G k W)
           (itot_prop G W k) (itot_prop G W (S k))
           (fun rho k' Sy F w x H => H));
    [ intros rho Hrho; apply eqty_prop; apply eval_whnf; exact whnf_prop |].
  intros rho Hrho F1 F2 D1 D2.
  pose proof (ity_prop_inv rho (prop k) k (ers rho (up k (prop k))) F1 D1) as Q1.
  pose proof (ity_prop_inv rho (prop (S k)) (S k) (ers rho (prop (S k))) F2 D2)
    as Q2.
  cbn [PropDec] in Q1, Q2.
  eapply famCeq_tr; [exact (famLiftK_ceq F1 (propFam k) Q1) |].
  eapply famCeq_tr; [apply famLiftK_propFam | exact (famCeq_sym _ _ Q2)].
Qed.

Lemma isem_up_univ G k j (Hjk : j < k) (W : Rules.wfc G) :
  ISem G (up k (univ k j)) (univ (S k) j) (UU (S k)).
Proof.
  apply (isem_up_former G k (univ k j) (univ (S k) j) W (t_univ G k j Hjk W)
           (itot_univ G W k j Hjk)
           (itot_univ G W (S k) j (Nat.lt_lt_succ_r j k Hjk))
           (fun rho k' Sy F w x H => H));
    [ intros rho Hrho; apply (eqty_univ (S k) j);
      [ lia | apply eval_whnf; exact (whnf_univ j)
      | apply eval_whnf; exact (whnf_univ j) ] |].
  intros rho Hrho F1 F2 D1 D2.
  destruct (ity_univ_ceq rho (univ k j) k (ers rho (up k (univ k j))) F1 D1)
    as [d [E Q1]].
  destruct (ity_univ_ceq rho (univ (S k) j) (S k) (ers rho (univ (S k) j)) F2 D2)
    as [d' [E' Q2]].
  assert (Ed : d' = S d) by lia; subst d'.
  eapply famCeq_tr; [exact (famLiftK_ceq F1 _ Q1) |].
  eapply famCeq_tr;
    [ exact (famLiftK_upF d k E E' (univFam j)) | exact (famCeq_sym _ _ Q2) ].
Qed.

Lemma isem_up_prf G k j p (Hjk : j <= k) (W : Rules.wfc G)
  (dp : ty G p (prop j)) (IHp : ITot G p (prop j)) :
  ISem G (up k (prf k p)) (prf (S k) p) (UU (S k)).
Proof.
  apply (isem_up_former G k (prf k p) (prf (S k) p) W (t_prf G k j p Hjk dp)
           (itot_prf G k j p Hjk W dp IHp)
           (itot_prf G (S k) j p (le_S j k Hjk) W dp IHp)
           (fun rho k' Sy F w x H => H)).
  - intros rho Hrho.
    destruct (IHp rho Hrho j (propFam j)
                (ity_prop rho j (ers rho (prop j)) eq_refl)) as [xp Dp].
    apply (eqty_prf (S k) (ers rho (up k (prf k p))) (ers rho (prf (S k) p))
             (ers rho p) (ers rho p));
      [ apply eval_whnf; exact (whnf_prf _)
      | apply eval_whnf; exact (whnf_prf _)
      | exact (Rel_prop_elim eprop _ _ (eval_whnf _ whnf_prop)
                 (propGood xp)) ].
  - intros rho Hrho F1 F2 D1 D2.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    destruct (ity_prf_inv rho (prf k p) k (ers rho (up k (prf k p))) F1 D1)
      as [j1 [wp [xp [Dp Q1]]]].
    destruct (ity_prf_inv rho (prf (S k) p) (S k) (ers rho (prf (S k) p)) F2 D2)
      as [j2 [wp2 [xp2 [Dp2 Q2]]]].
    pose proof (itm_lvl p rho rho eq_refl _ _ _ _ _ NotPrfR_prop Dp
                  _ _ _ _ _ NotPrfR_prop Dp2) as Ej; subst j2.
    assert (Ep : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
    assert (Ep2 : wp2 = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp2).
    subst wp wp2.
    assert (Hiff : propVal xp <-> propVal xp2).
    { exact (proj1 (proj1 (propEq_iff xp xp2)
                      (kRel_at (funtm G p (prop j) dp rho rho HEself j1 eprop
                                  (propFam j1) _ xp Dp eprop (propFam j1) _ xp2
                                  Dp2 (famAtSelf (propFam j1))
                                  (LTm_of_ty G p (prop j) dp rho rho
                                     HEself))))). }
    eapply famCeq_tr; [exact (famLiftK_ceq F1 (prfF k xp) Q1) |].
    eapply famCeq_tr; [apply famLiftK_prfFam |].
    eapply famCeq_tr; [| exact (famCeq_sym _ _ Q2)].
    apply prfFam_ceq;
      [ exists (S k); exact (uf_ty (prfF (S k) xp)) | exact Hiff ].
Qed.

(* ---- eta.  The eta-expansion's value is BUILT (piLam) with the body's data
     given by applying f's value, and `piEl_ext` -- the Pi code's own element
     relation, which says two functions are equal when their applications are
     -- identifies it with f's value.  `ty_eta_lam` is the typing derivation
     the layer-1 facts and functionality need. ---- *)

Lemma ty_eta_lam G kk i j A B f (Hik : i <= kk) (Hjk : j <= kk)
  (W : Rules.wfc G) (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j))
  (df : ty G f (pi kk A B)) :
  inhabited (ty G (lam kk A B
                     (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))
               (pi kk A B)).
Proof.
  pose proof (w_cons G A i W dA) as WA.
  destruct (proj1 (proj2 renaming) G A (UU i) dA (A :: G) ↑
              (ren_ok_shift G A) (inhabits WA)) as [dA1].
  destruct (proj1 (proj2 renaming) (A :: G) B (UU j) dB ((A ⟨↑⟩) :: A :: G)
              (up_ren ↑)
              (ren_ok_up ↑ G (A :: G) A (ren_ok_shift G A))
              (inhabits (w_cons (A :: G) (A ⟨↑⟩) i WA dA1))) as [dB1].
  destruct (proj1 (proj2 renaming) G f (pi kk A B) df (A :: G) ↑
              (ren_ok_shift G A) (inhabits WA)) as [df1].
  pose proof (t_app (A :: G) kk i j (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩)
                (var_tm 0) Hik Hjk dA1 dB1 df1
                (t_var (A :: G) 0 (A ⟨↑⟩) WA (lookup_O G A))) as dap.
  rewrite eta_cod_sub in dap.
  exact (inhabits (t_lam G kk i j A B _ Hik Hjk dA dB dap)).
Qed.

Lemma eta_value G kk i j A B f (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j)) (df : ty G f (pi kk A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHf : ITot G f (pi kk A B)) rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam kk S1 &
  { xl : kElAt F1 (ers rho (lam kk A B
           (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))) &
  { xf : kElAt F1 (ers rho f) &
    (ITy rho (pi kk A B) kk S1 F1 *
     ITm rho (lam kk A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))
         kk S1 F1 (ers rho (lam kk A B
           (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))) xl *
     ITm rho f kk S1 F1 (ers rho f) xf *
     kEqAt F1 (ers rho (lam kk A B
           (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))) xl
          F1 (ers rho f) xf)%type } } } }.
Proof.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (kk - i) + i = kk) by lia.
  assert (EB : (kk - j) + j = kk) by lia.
  destruct (build_fam_data G A B kk i j (kk - i) (kk - j) EA EB dA dB IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z)) B).
  pose (redB := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gPi := LTyK_of_ty G (pi kk A B) kk (t_pi G kk i j A B Hik Hjk dA dB)
                 rho rho HEself).
  pose proof (ity_pi rho A B kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gPi eq_refl DFA DB) as Dpi.
  destruct (IHf rho Hrho kk
              (piFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi) Dpi)
    as [xf Df].
  (* the codomain instance at an argument against the one at its round trip *)
  pose (Qrt := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                 cod_ceq G A B (LTy_of_ty (A :: G) B j dB)
                   (funtm (A :: G) B (UU j) dB) rho rho HEself kk i j (kk - i)
                   EA (ers rho A) FA wB FB (ers rho A) FA wB FB DFA DFA
                   (famAtSelf FA) DB DB
                   u0 (upEl (kk - i) kk EA FA u0
                         (dnEl (kk - i) kk EA FA u0 z)) u0 z
                   (upEl_dnEl (kk - i) kk EA FA u0 z)).
  (* the body's value: f applied to the argument, brought down the gap and
     moved from the round-tripped instance to the argument's own *)
  pose (wt := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                eapp (ers rho f) u0).
  pose (xt := fun u0 (z : kElAt (upF (kk - i) kk EA FA) u0) =>
                kto (kAt (FB u0 (upEl (kk - i) kk EA FA u0
                                   (dnEl (kk - i) kk EA FA u0 z))))
                  (kAt (FB u0 z))
                  (famAtWf (FB u0 (upEl (kk - i) kk EA FA u0
                                     (dnEl (kk - i) kk EA FA u0 z))))
                  (famAtWf (FB u0 z)) (Qrt u0 z) (eapp (ers rho f) u0)
                  (dnEl (kk - j) kk EB
                     (FB u0 (upEl (kk - i) kk EA FA u0
                               (dnEl (kk - i) kk EA FA u0 z)))
                     (eapp (ers rho f) u0)
                     (piApp kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                        (fun u1 y => upF (kk - j) kk EB (FB u1 y)) redB cohB gPi
                        (ers rho f) xf u0
                        (upEl (kk - i) kk EA FA u0
                           (dnEl (kk - i) kk EA FA u0 z))))).
  assert (Dt : forall u0 z,
             ITm (ext rho FA u0 (dnEl (kk - i) kk EA FA u0 z))
               (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)) j
               (wB u0 z) (FB u0 z) (wt u0 z) (xt u0 z)).
  { intros u0 z.
    pose (y := dnEl (kk - i) kk EA FA u0 z).
    pose proof (weaken1_ITy rho A i (ers rho A) FA
                  (Build_Entry i (ers rho A) FA u0 y) DFA) as DAw.
    assert (DBw : forall u1 x1,
               ITy (ext (ext rho FA u0 y) FA u1
                      (dnEl (kk - i) kk EA FA u1 x1))
                 (B ⟨up_ren ↑⟩) j (wB u1 x1) (FB u1 x1)).
    { intros u1 x1.
      exact (weaken_ITy (ext rho FA u1 (dnEl (kk - i) kk EA FA u1 x1)) B j
               (wB u1 x1) (FB u1 x1) (DB u1 x1)
               (Build_Entry i (ers rho A) FA u1
                  (dnEl (kk - i) kk EA FA u1 x1) :: nil)
               rho (Build_Entry i (ers rho A) FA u0 y) eq_refl). }
    pose proof (weaken1 rho f kk (epi (ers rho A) B0) _ (ers rho f) xf
                  (Build_Entry i (ers rho A) FA u0 y) Df) as Dfw.
    assert (Ep : epi (ers rho A) B0
                 = ers (ext rho FA u0 y) (pi kk (A ⟨↑⟩) (B ⟨up_ren ↑⟩)))
      by exact (eq_sym (ers_shift_en (Build_Entry i (ers rho A) FA u0 y) rho
                          (pi kk A B))).
    pose proof (i_app (ext rho FA u0 y) (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩)
                  (var_tm 0) kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0
                  wB FB redB cohB gPi (ers rho f) xf u0 y Ep DAw DBw Dfw
                  (i_var0 rho i (ers rho A) FA u0 y)) as Dap.
    exact (i_conv (ext rho FA u0 y)
             (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)) j
             _ (FB u0 (upEl (kk - i) kk EA FA u0 y)) _ (FB u0 z)
             (eapp (ers rho f) u0) _ (Qrt u0 z) Dap). }
  (* the lambda's realiser applies to the body's *)
  assert (redt : forall u0 z,
             reds (eapp (ers rho (lam kk A B
                     (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))) u0)
                  (wt u0 z)).
  { intros u0 z.
    unfold wt.
    rewrite <- (f_equal (fun w => eapp w u0)
                  (ers_shift_en (Build_Entry i (ers rho A) FA u0
                                   (dnEl (kk - i) kk EA FA u0 z)) rho f)).
    exact (reds_lam_app
             (er (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))
             (rsub rho) u0). }
  assert (xtext : forall u0 z u0' z',
             kEqAt (upF (kk - i) kk EA FA) u0 z (upF (kk - i) kk EA FA) u0' z' ->
             kEqAt (upF (kk - j) kk EB (FB u0 z)) (wt u0 z)
                     (upEl (kk - j) kk EB (FB u0 z) (wt u0 z) (xt u0 z))
                   (upF (kk - j) kk EB (FB u0' z')) (wt u0' z')
                     (upEl (kk - j) kk EB (FB u0' z') (wt u0' z') (xt u0' z'))).
  { intros u0 z u0' z' Hzz.
    refine (kRel_at _).
    (* undo the move at each end, and compare the two applications at the
       round-tripped arguments *)
    eapply kRel_trans;
      [ apply kRel_sym;
        exact (kRel_up (kk - j) kk EB _ _ _ _ _ _
                 (conj (Qrt u0 z) (kto_coh _ _ _ _ (Qrt u0 z) _ _))) |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same _ _ _ _ _));
        exact (upEl_dnEl (kk - j) kk EB
                 (FB u0 (upEl (kk - i) kk EA FA u0
                           (dnEl (kk - i) kk EA FA u0 z))) _ _) |].
    eapply kRel_trans;
      [ exact (piApp_eq kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u1 y => upF (kk - j) kk EB (FB u1 y)) redB cohB gPi
                 _ xf _ xf _ _ _ _ (kEqAt_refl _ (ers rho f) xf)
                 (upEl_eq (kk - i) kk EA FA _ _ FA _ _ (famAtSelf FA)
                    (dnEl_eq (kk - i) kk EA FA _ z FA _ z'
                       (famAtSelf FA) Hzz))) |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same _ _ _ _ _)); apply kEqAt_sym;
        exact (upEl_dnEl (kk - j) kk EB
                 (FB u0' (upEl (kk - i) kk EA FA u0'
                            (dnEl (kk - i) kk EA FA u0' z'))) _ _) |].
    exact (kRel_up (kk - j) kk EB _ _ _ _ _ _
             (conj (Qrt u0' z') (kto_coh _ _ _ _ (Qrt u0' z') _ _))). }
  assert (gd : Good (epi (ers rho A) B0)
                 (ers rho (lam kk A B
                    (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))))).
  { destruct (ty_eta_lam G kk i j A B f Hik Hjk W dA dB df) as [dl].
    exact (LTm_of_ty G _ (pi kk A B) dl rho rho HEself). }
  pose proof (i_lam rho A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))
                kk i j (kk - i) (kk - j) EA EB (ers rho A) FA B0 wB FB redB
                cohB gPi _ wt xt redt xtext gd eq_refl eq_refl DFA DB Dt) as Dl.
  exists (epi (ers rho A) B0),
         (piFam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
            (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi),
         (piLam kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
            (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi
            (ers rho (lam kk A B
               (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0)))) wt
            (fun u0 z => upEl (kk - j) kk EB (FB u0 z) (wt u0 z) (xt u0 z))
            redt xtext gd),
         xf.
  split; [split; [split; [exact Dpi | exact Dl] | exact Df] |].
  (* and the two values agree, because their applications do: the lambda's
     application is the body's value (piLam_app), which is f's application at
     the round-tripped argument, moved -- and the moves cancel *)
  apply (piEl_ext kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
           (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi).
  - exact (LCv_of_cv G _ f (pi kk A B)
             (c_eta G kk i j A B f Hik Hjk dA dB df) rho rho HEself).
  - intros v1 y1 v1' y1' Hy.
    refine (kRel_at _).
    eapply kRel_trans;
      [ apply (proj1 (kRel_same _ _ _ _ _));
        exact (piLam_app kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u0 z => upF (kk - j) kk EB (FB u0 z)) redB cohB gPi
                 _ wt (fun u0 z => upEl (kk - j) kk EB (FB u0 z) (wt u0 z)
                                     (xt u0 z)) redt xtext gd v1 y1) |].
    eapply kRel_trans;
      [ apply kRel_sym;
        exact (kRel_up (kk - j) kk EB _ _ _ _ _ _
                 (conj (Qrt v1 y1) (kto_coh _ _ _ _ (Qrt v1 y1) _ _))) |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same _ _ _ _ _));
        exact (upEl_dnEl (kk - j) kk EB
                 (FB v1 (upEl (kk - i) kk EA FA v1
                           (dnEl (kk - i) kk EA FA v1 y1))) _ _) |].
    eapply kRel_trans;
      [ exact (piApp_eq kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
                 (fun u1 y => upF (kk - j) kk EB (FB u1 y)) redB cohB gPi
                 _ xf _ xf _ _ _ _ (kEqAt_refl _ (ers rho f) xf)
                 (upEl_dnEl (kk - i) kk EA FA v1 y1)) |].
    exact (piApp_eq kk (ers rho A) B0 (upF (kk - i) kk EA FA) wB
             (fun u1 y => upF (kk - j) kk EB (FB u1 y)) redB cohB gPi
             _ xf _ xf _ _ _ _ (kEqAt_refl _ (ers rho f) xf) Hy).
Qed.

Lemma isem_eta G kk i j A B f (Hik : i <= kk) (Hjk : j <= kk) (W : Rules.wfc G)
  (dA : ty G A (UU i)) (dB : ty (A :: G) B (UU j)) (df : ty G f (pi kk A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHf : ITot G f (pi kk A B)) :
  ISem G (lam kk A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))) f
    (pi kk A B).
Proof.
  assert (fT : FunTm G (pi kk A B))
    by exact (FunTm_of_ty G (pi kk A B) kk (t_pi G kk i j A B Hik Hjk dA dB)).
  split.
  - split.
    + intros rho Hrho k F DPi.
      destruct (eta_value G kk i j A B f Hik Hjk W dA dB df IHA IHB IHf rho
                  Hrho) as [S1 [F1 [xl [xf [[[DT Dl] Df] Hcv]]]]].
      assert (ES1 : S1 = ers rho (pi kk A B))
        by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      pose proof (ity_lvl rho rho eq_refl (pi kk A B) kk _ F1 k _ F DT DPi)
        as Ek; subst k.
      pose proof (ity_same_ceq G (pi kk A B) fT rho Hrho kk F1 F DT DPi) as P.
      exists (kto (kAt F1) (kAt F) (famAtWf F1) (famAtWf F) P _ xl).
      exact (i_conv rho _ kk _ F1 _ F _ xl P Dl).
    + exact IHf.
  - intros rho Hrho k F DPi x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    destruct (eta_value G kk i j A B f Hik Hjk W dA dB df IHA IHB IHf rho Hrho)
      as [S1 [F1 [xl [xf [[[DT Dl] Df] Hcv]]]]].
    assert (ES1 : S1 = ers rho (pi kk A B)) by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    pose proof (ity_lvl rho rho eq_refl (pi kk A B) kk _ F1 k _ F DT DPi) as Ek;
      subst k.
    pose proof (ity_same_ceq G (pi kk A B) fT rho Hrho kk F F1 DPi DT) as P.
    destruct (ty_eta_lam G kk i j A B f Hik Hjk W dA dB df) as [dl].
    pose proof (funtm G _ (pi kk A B) dl rho rho HEself kk _ F _ x Dx
                  _ F1 _ xl Dl P
                  (LTm_of_ty G _ (pi kk A B) dl rho rho HEself)) as H1.
    pose proof (funtm G f (pi kk A B) df rho rho HEself kk _ F1 _ xf Df
                  _ F _ y Dy (knsymU _ _ P)
                  (LTm_of_ty G f (pi kk A B) df rho rho HEself)) as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same F1 _ _ _ _)); exact Hcv | exact H2 ].
Qed.

(* ================================================================== *)
(* N: the three conversion rules.                                      *)
(*                                                                    *)
(* All three share the recursor's data at one environment, which        *)
(* `build_rec_data` assembles once: the motive at every natural, the     *)
(* two branches' values, and the step's congruence.  `isem_rec_zero`      *)
(* and `isem_rec_succ` then only have to say which value the recursion    *)
(* computes to, and `isem_natrec` compares two recursions through          *)
(* `semrec_rel`.                                                          *)
(* ================================================================== *)

Lemma build_rec_data G C z s k j
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHz : ITot G z (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C))
  rho (Hrho : EnvITy G rho) :
  { FC : forall m (x : kElAt (natFam j) m),
           kUFam k (subst_etm (scons m (rsub rho)) (er C)) &
  { cohC : forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
             kceq (kAt (FC m x)) (kAt (FC m' x')) &
  { xz : kElAt (FC ezero (natE 0 NatAt_zero)) (ers rho z) &
  { xs : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w),
           kElAt (FC (esucc m) (natSucc x))
             (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) &
    ((forall m x, ITy (ext rho (natFam j) m x) C k
                    (subst_etm (scons m (rsub rho)) (er C)) (FC m x)) *
     ITm rho z k (subst_etm (scons ezero (rsub rho)) (er C))
         (FC ezero (natE 0 NatAt_zero)) (ers rho z) xz *
     (forall m x w y,
        ITm (ext (ext rho (natFam j) m x) (FC m x) w y) s k
            (subst_etm (scons (esucc m) (rsub rho)) (er C))
            (FC (esucc m) (natSucc x))
            (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) (xs m x w y)) *
     (forall m x w y m' x' w' y',
        kEqAt (natFam j) m x (natFam j) m' x' ->
        kRel (FC m x) w y (FC m' x') w' y' ->
        kRel (FC (esucc m) (natSucc x))
             (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) (xs m x w y)
             (FC (esucc m') (natSucc x'))
             (ers (ext (ext rho (natFam j) m' x') (FC m' x') w' y') s)
             (xs m' x' w' y')))%type
  } } } }.
Proof.
  pose (SC := fun m : etm => subst_etm (scons m (rsub rho)) (er C)).
  assert (HEm : forall m (x : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x)).
  { intros m x.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam j) m) =>
                projT1 (ityT_of_ITot (nat_ j :: G) C k IHC
                          (ext rho (natFam j) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam j) m x) C k (SC m) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ j :: G) C k IHC
                         (ext rho (natFam j) m x) (HEm m x)))).
  assert (cohC : forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
             kceq (kAt (FC m x)) (kAt (FC m' x'))).
  { intros m x m' x' Hm.
    assert (HEx : EnvRelOf (nat_ j :: G) (ext rho (natFam j) m x)
                    (ext rho (natFam j) m' x')).
    { apply (EnvRelOf_ext G rho rho (nat_ j) j (natFam j) (natFam j) m x m' x'
               (EnvRelOf_selfE G rho Hrho)).
      split; [exact (famAtSelf (natFam j)) | exact Hm]. }
    exact (FunTy_of_FunTm (nat_ j :: G) C (funtm (nat_ j :: G) C (UU k) dC)
             _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
             (LTyK_of_ty (nat_ j :: G) C k dC _ _ HEx)). }
  assert (E0 : SC ezero = ers rho (C [(zero j)..]))
    by exact (eq_sym (ers_sub1 rho C (zero j) (natFam j) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho (zero j) j enat (natFam j) ezero
                (natE 0 NatAt_zero) eq_refl (i_zero rho j) C k (SC ezero)
                (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [(zero j)..]) k _ _ E0 _ DCz)) as [xz' Dz'].
  destruct (ITm_uncast rho z k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dz')
    as [xz Dz].
  assert (Hstep : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w),
             { xs : kElAt (FC (esucc m) (natSucc x))
                      (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) &
               ITm (ext (ext rho (natFam j) m x) (FC m x) w y) s k
                   (SC (esucc m)) (FC (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s) xs }).
  { intros m x w y.
    pose proof (ity_nrec_succ rho C k j m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k (SC m) (FC m x) w y) as DS.
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam j) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs (ext (ext rho (natFam j) m x) (FC m x) w y)
                (EnvITy_ext (nat_ j :: G) (ext rho (natFam j) m x) C k (FC m x)
                   (DC m x) w y (HEm m x))
                k (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [xs' Ds'].
    destruct (ITm_uncast _ s k _ _ Es (FC (esucc m) (natSucc x)) _ _ Ds')
      as [xs Ds].
    exists xs; exact Ds. }
  assert (Hfs : forall m x w y m' x' w' y',
             kEqAt (natFam j) m x (natFam j) m' x' ->
             kRel (FC m x) w y (FC m' x') w' y' ->
             kRel (FC (esucc m) (natSucc x))
                  (ers (ext (ext rho (natFam j) m x) (FC m x) w y) s)
                  (projT1 (Hstep m x w y))
                  (FC (esucc m') (natSucc x'))
                  (ers (ext (ext rho (natFam j) m' x') (FC m' x') w' y') s)
                  (projT1 (Hstep m' x' w' y'))).
  { intros m x w y m' x' w' y' Hm Hy.
    assert (HE0 : EnvRelOf (nat_ j :: G) (ext rho (natFam j) m x)
                    (ext rho (natFam j) m' x')).
    { apply (EnvRelOf_ext G rho rho (nat_ j) j (natFam j) (natFam j) m x m' x'
               (EnvRelOf_selfE G rho Hrho)).
      split; [exact (famAtSelf (natFam j)) | exact Hm]. }
    assert (HEr : EnvRelOf (C :: nat_ j :: G)
                    (ext (ext rho (natFam j) m x) (FC m x) w y)
                    (ext (ext rho (natFam j) m' x') (FC m' x') w' y'))
      by exact (EnvRelOf_ext (nat_ j :: G) (ext rho (natFam j) m x)
                  (ext rho (natFam j) m' x') C k (FC m x) (FC m' x') w y w' y'
                  HE0 Hy).
    assert (Q : kceq (kAt (FC (esucc m) (natSucc x)))
                     (kAt (FC (esucc m') (natSucc x'))))
      by exact (cohC (esucc m) (natSucc x) (esucc m') (natSucc x')
                  (natSucc_eq x x' Hm)).
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam j) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    refine (funtm (C :: nat_ j :: G) s (nrec_succ C) ds _ _ HEr k
              _ (FC (esucc m) (natSucc x)) _ (projT1 (Hstep m x w y))
              (projT2 (Hstep m x w y))
              _ (FC (esucc m') (natSucc x')) _ (projT1 (Hstep m' x' w' y'))
              (projT2 (Hstep m' x' w' y')) Q _).
    apply (Rel_tyeq (ers (ext (ext rho (natFam j) m x) (FC m x) w y)
                      (nrec_succ C)) (SC (esucc m'))).
    - rewrite <- Es; exact (ceq_ty _ _ Q).
    - exact (LTm_of_ty (C :: nat_ j :: G) s (nrec_succ C) ds _ _ HEr). }
  exists FC, cohC, xz, (fun m x w y => projT1 (Hstep m x w y)).
  split; [split; [split; [exact DC | exact Dz] |] |].
  - intros m x w y; exact (projT2 (Hstep m x w y)).
  - exact Hfs.
Qed.

Lemma ity_same_ceq' G A (HA : FunTm G A) rho (H : EnvITy G rho)
  k w (F : kUFam k w) w' (F0 : kUFam k w')
  (D : ITy rho A k w F) (D0 : ITy rho A k w' F0) : kceq (kAt F) (kAt F0).
Proof.
  assert (E : w = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D).
  assert (E' : w' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D0).
  subst w w'.
  exact (ity_same_ceq G A HA rho H k F F0 D D0).
Qed.

Lemma isem_rec_zero G C z s k j (W : Rules.wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHz : ITot G z (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C)) :
  ISem G (natrec C z s (zero j)) z (C [(zero j)..]).
Proof.
  pose proof (t_natrec G C z s (zero j) k j dC dz ds (t_zero G j W)) as dnr.
  split;
    [split; [exact (itot_natrec G C z s (zero j) k j dC dz ds (t_zero G j W)
                      IHC IHz IHs (itot_zero G W j))
            | exact IHz] |].
  intros rho Hrho k' F DCz x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  destruct (build_rec_data G C z s k j dC dz ds IHC IHz IHs rho Hrho)
    as [FC [cohC [xz [xs [[[DC Dz] Ds] Hfs]]]]].
  pose proof (i_natrec rho C z s (zero j) k j
                (fun m => subst_etm (scons m (rsub rho)) (er C)) FC cohC
                (ers rho (stepWrap s)) (ers rho z) xz
                (fun m x w y => ers (ext (ext rho (natFam j) m x) (FC m x) w y) s)
                xs (fun m x w y => reds_lam2_app (er s) (rsub rho) m w)
                ezero (natE 0 NatAt_zero) eq_refl DC Dz Ds (i_zero rho j)) as Dnr.
  assert (E0 : subst_etm (scons ezero (rsub rho)) (er C)
               = ers rho (C [(zero j)..]))
    by exact (eq_sym (ers_sub1 rho C (zero j) (natFam j) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho (zero j) j enat (natFam j) ezero
                (natE 0 NatAt_zero) eq_refl (i_zero rho j) C k _
                (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz0.
  assert (fCz : FunTm G (C [(zero j)..])).
  { destruct (ty_subst1 G (nat_ j) C (UU k) (zero j) dC (t_zero G j W))
      as [dsub].
    exact (FunTm_of_ty G (C [(zero j)..]) k dsub). }
  pose proof (ity_lvl rho rho eq_refl (C [(zero j)..]) k _
                (FC ezero (natE 0 NatAt_zero)) k' (ers rho (C [(zero j)..])) F
                DCz0 DCz) as Ek; subst k'.
  pose proof (ity_same_ceq' G (C [(zero j)..]) fCz rho Hrho k _ F _
                (FC ezero (natE 0 NatAt_zero)) DCz DCz0) as P.
  assert (Hg1 : Rel (subst_etm (scons ezero (rsub rho)) (er C))
                  (ers rho (natrec C z s (zero j)))
                  (enatrec (ers rho z) (ers rho (stepWrap s)) ezero)).
  { rewrite E0.
    exact (LTm_of_ty G (natrec C z s (zero j)) (C [(zero j)..]) dnr
             rho rho HEself). }
  pose proof (funtm G (natrec C z s (zero j)) (C [(zero j)..]) dnr rho rho
                HEself k _ F _ x Dx _ (FC ezero (natE 0 NatAt_zero)) _ _ Dnr
                P Hg1) as H1.
  pose proof (funtm G z (C [(zero j)..]) dz rho rho HEself k
                _ (FC ezero (natE 0 NatAt_zero)) _ xz Dz _ F _ y Dy
                (knsymU _ _ P)
                (LTm_of_ty G z (C [(zero j)..]) dz rho rho HEself)) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  cbn [semrec].
  apply kRel_sym; apply moveTo_rel.
Qed.

(* The canonical transport is related to its input: this is `moveTo_rel` with
   no expansion, i.e. exactly the equation i_conv leaves behind. *)
Lemma kRel_kto {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) :
  kRel F w x F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
Proof.
  split; [exact P | exact (kto_coh (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x)].
Qed.

(* Naming a derivation's value without spelling it out. *)
Lemma ITm_pack rho t k w (F : kUFam k w) v (x : kElAt F v) :
  ITm rho t k w F v x -> { y : kElAt F v & (ITm rho t k w F v y * (y = x))%type }.
Proof. intros D; exists x; split; [exact D | reflexivity]. Qed.

(* One unfolding of the recursor at a successor: the value is the step applied
   to the predecessor and the recursive result, up to the realiser's
   expansion. *)
Lemma semrec_succ_step (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (cohC : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
            kceq (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  j u (e : NatAt j u) :
  kRel (FC (esucc u) (natSucc (natE j e)))
       (enatrec zr sr (esucc u))
       (semrec k k0 SC FC cohC zr sr xz step (S j) (esucc u) (NatAt_succ j u e))
       (FC (esucc u) (natSucc (natE j e)))
       (eapp (eapp sr u) (enatrec zr sr u))
       (step u (natE j e) (enatrec zr sr u)
          (semrec k k0 SC FC cohC zr sr xz step j u e)).
Proof.
  cbn [semrec NatAt_pred NatAt_pred_at].
  apply kRel_sym; apply moveTo_rel.
Qed.

(* ---- the step rule ---- *)
Lemma rec_succ_data G C z s n k j (W : Rules.wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C)) (dn : ty G n (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHz : ITot G z (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C)) (IHn : ITot G n (nat_ j))
  rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam k S1 &
  { v1 : kElAt F1 (ers rho (natrec C z s (succ n))) &
  { w2 : etm & { v2 : kElAt F1 w2 &
    (ITy rho (C [(succ n)..]) k S1 F1 *
     ITm rho (natrec C z s (succ n)) k S1 F1
         (ers rho (natrec C z s (succ n))) v1 *
     ITm rho (s [(natrec C z s n) .: n ..]) k S1 F1 w2 v2 *
     kEqAt F1 (ers rho (natrec C z s (succ n))) v1 F1 w2 v2)%type } } } } }.
Proof.
  destruct (build_rec_data G C z s k j dC dz ds IHC IHz IHs rho Hrho)
    as [FC [cohC [xz [xs [[[DC Dz] Ds] Hfs]]]]].
  destruct (IHn rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)) as [xn Dn].
  pose (ws := fun m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w) =>
                ers (ext (ext rho (natFam j) m x) (FC m x) w y) s).
  pose (redS := fun m (x : kElAt (natFam j) m) w (y : kElAt (FC m x) w) =>
                  reds_lam2_app (er s) (rsub rho) m w).
  (* the recursive call, moved to the scrutinee's own value *)
  pose proof (i_natrec rho C z s n k j
                (fun m => subst_etm (scons m (rsub rho)) (er C)) FC cohC
                (ers rho (stepWrap s)) (ers rho z) xz ws xs redS
                (ers rho n) xn eq_refl DC Dz Ds Dn) as Dnr.
  pose proof (i_conv rho (natrec C z s n) k _ _ _ _ _ _
                (cohC (ers rho n) (natE (natIdx xn) (natSpec xn)) (ers rho n) xn
                   (natEq_self _ _)) Dnr) as Dyr.
  destruct (ITm_pack rho (natrec C z s n) k _ (FC (ers rho n) xn) _ _ Dyr)
    as [yrec [Dyrec Ey]].
  pose proof (Ds (ers rho n) xn (ers rho (natrec C z s n)) yrec) as Dstep.
  (* the two substitutions *)
  pose proof (subst_ITm rho n (Build_Entry j enat (natFam j) (ers rho n) xn)
                eq_refl Dn (subUniv_all rho n) _ s k _ _ _ _ Dstep
                (Build_Entry k (subst_etm (scons (ers rho n) (rsub rho)) (er C))
                   (FC (ers rho n) xn) (ers rho (natrec C z s n)) yrec :: nil)
                eq_refl) as D1.
  pose proof (subst_ITm rho (natrec C z s n)
                (Build_Entry k (subst_etm (scons (ers rho n) (rsub rho)) (er C))
                   (FC (ers rho n) xn) (ers rho (natrec C z s n)) yrec)
                eq_refl Dyrec (subUniv_all rho (natrec C z s n)) _ _ k _ _ _ _ D1
                nil eq_refl) as D2.
  assert (Esub : (s [upn 1 (n..)]) [upn 0 ((natrec C z s n)..)]
                 = s [(natrec C z s n) .: n ..])
    by (cbn [upn]; exact (rec_succ_two s n (natrec C z s n))).
  assert (D3 : ITm rho (s [(natrec C z s n) .: n ..]) k
                 (subst_etm (scons (esucc (ers rho n)) (rsub rho)) (er C))
                 (FC (esucc (ers rho n)) (natSucc xn))
                 (ers (ext (ext rho (natFam j) (ers rho n) xn) (FC (ers rho n) xn)
                         (ers rho (natrec C z s n)) yrec) s)
                 (xs (ers rho n) xn (ers rho (natrec C z s n)) yrec))
    by (rewrite <- Esub; exact D2).
  (* the left-hand side *)
  pose proof (i_succ rho j n (ers rho n) xn Dn) as Dsn.
  pose proof (i_natrec rho C z s (succ n) k j
                (fun m => subst_etm (scons m (rsub rho)) (er C)) FC cohC
                (ers rho (stepWrap s)) (ers rho z) xz ws xs redS
                (esucc (ers rho n)) (natSucc xn) eq_refl DC Dz Ds Dsn) as Dlhs.
  destruct (ITm_pack rho (natrec C z s (succ n)) k _
              (FC (esucc (ers rho n)) (natSucc xn)) _ _ Dlhs) as [v1 [Dv1 Ev1]].
  exists (subst_etm (scons (esucc (ers rho n)) (rsub rho)) (er C)),
    (FC (esucc (ers rho n)) (natSucc xn)), v1,
    (ers (ext (ext rho (natFam j) (ers rho n) xn) (FC (ers rho n) xn)
            (ers rho (natrec C z s n)) yrec) s),
    (xs (ers rho n) xn (ers rho (natrec C z s n)) yrec).
  split; [split; [split |] |].
  - exact (isubst_ITy rho (succ n) j enat (natFam j) (esucc (ers rho n))
             (natSucc xn) eq_refl Dsn C k _
             (FC (esucc (ers rho n)) (natSucc xn))
             (DC (esucc (ers rho n)) (natSucc xn))).
  - exact Dv1.
  - exact D3.
  - rewrite Ev1.
    apply (proj2 (kRel_same _ _ _ _ _)).
    eapply kRel_trans;
      [ exact (semrec_succ_step k j
                 (fun m => subst_etm (scons m (rsub rho)) (er C)) FC cohC
                 (ers rho z) (ers rho (stepWrap s)) xz
                 (fun m x w y =>
                    moveTo (FC (esucc m) (natSucc x)) (FC (esucc m) (natSucc x))
                      (famAtSelf (FC (esucc m) (natSucc x))) (ws m x w y)
                      (xs m x w y) (eapp (eapp (ers rho (stepWrap s)) m) w)
                      (redS m x w y))
                 (natIdx xn) (ers rho n) (natSpec xn)) |].
    eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
    rewrite Ey.
    apply Hfs; [apply natEq_self | apply kRel_kto].
Qed.

Lemma isem_rec_succ G C z s n k j (W : Rules.wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dz : ty G z (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C)) (dn : ty G n (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHz : ITot G z (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C)) (IHn : ITot G n (nat_ j)) :
  ISem G (natrec C z s (succ n)) (s [(natrec C z s n) .: n ..]) (C [(succ n)..]).
Proof.
  pose proof (t_natrec G C z s (succ n) k j dC dz ds (t_succ G j n dn)) as dL.
  assert (fL : FunTm G (natrec C z s (succ n)))
    by exact (funtm G (natrec C z s (succ n)) (C [(succ n)..]) dL).
  assert (fR : FunTm G (s [(natrec C z s n) .: n ..])).
  { destruct (ty_rec_succ_rhs G C z s n k j W dC dz ds dn) as [d].
    exact (funtm G (s [(natrec C z s n) .: n ..]) (C [(succ n)..]) d). }
  assert (fT : FunTm G (C [(succ n)..])).
  { destruct (ty_subst1 G (nat_ j) C (UU k) (succ n) dC (t_succ G j n dn)) as [d].
    exact (FunTm_of_ty G (C [(succ n)..]) k d). }
  assert (gR : forall rho, EnvRelOf G rho rho ->
             Rel (ers rho (C [(succ n)..]))
               (ers rho (s [(natrec C z s n) .: n ..]))
               (ers rho (s [(natrec C z s n) .: n ..]))).
  { intros rho HE.
    destruct (ty_rec_succ_rhs G C z s n k j W dC dz ds dn) as [d].
    exact (LTm_of_ty G (s [(natrec C z s n) .: n ..]) (C [(succ n)..]) d
             rho rho HE). }
  split.
  - split.
    + exact (itot_natrec G C z s (succ n) k j dC dz ds (t_succ G j n dn)
               IHC IHz IHs (itot_succ G W j n IHn)).
    + intros rho Hrho k' F DCn.
      destruct (rec_succ_data G C z s n k j W dC dz ds dn IHC IHz IHs IHn
                  rho Hrho)
        as [S1 [F1 [v1 [w2 [v2 [[[DT Dv1] Dv2] Hmid]]]]]].
      assert (ES1 : S1 = ers rho (C [(succ n)..]))
        by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      assert (E2 : w2 = ers rho (s [(natrec C z s n) .: n ..]))
        by exact (ers_of_ITm _ _ _ _ _ _ _ Dv2).
      subst w2.
      pose proof (ity_lvl rho rho eq_refl (C [(succ n)..]) k _ F1 k' _ F DT DCn)
        as Ek; subst k'.
      pose proof (ity_same_ceq G (C [(succ n)..]) fT rho Hrho k F1 F DT DCn)
        as P.
      exists (kto (kAt F1) (kAt F) (famAtWf F1) (famAtWf F) P _ v2).
      exact (i_conv rho (s [(natrec C z s n) .: n ..]) k _ F1 _ F _ v2 P Dv2).
  - intros rho Hrho k' F DCn x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    destruct (rec_succ_data G C z s n k j W dC dz ds dn IHC IHz IHs IHn rho Hrho)
      as [S1 [F1 [v1 [w2 [v2 [[[DT Dv1] Dv2] Hmid]]]]]].
    assert (ES1 : S1 = ers rho (C [(succ n)..]))
      by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    assert (E2 : w2 = ers rho (s [(natrec C z s n) .: n ..]))
      by exact (ers_of_ITm _ _ _ _ _ _ _ Dv2).
    subst w2.
    pose proof (ity_lvl rho rho eq_refl (C [(succ n)..]) k _ F1 k' _ F DT DCn)
      as Ek; subst k'.
    pose proof (ity_same_ceq G (C [(succ n)..]) fT rho Hrho k F F1 DCn DT) as P.
    pose proof (fL rho rho HEself k _ F _ x Dx _ F1 _ v1 Dv1 P
                  (LTm_of_ty G (natrec C z s (succ n)) (C [(succ n)..]) dL
                     rho rho HEself)) as H1.
    pose proof (fR rho rho HEself k _ F1 _ v2 Dv2 _ F _ y Dy (knsymU _ _ P)
                  (gR rho HEself)) as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans;
      [exact (proj1 (kRel_same F1 _ _ _ _) Hmid) | exact H2].
Qed.

(* The motive alone, which the congruence needs for both motives. *)
Lemma build_motive G C k j (dC : ty (nat_ j :: G) C (UU k))
  (IHC : ITot (nat_ j :: G) C (UU k)) rho (Hrho : EnvITy G rho) :
  { FC : forall m (x : kElAt (natFam j) m),
           kUFam k (subst_etm (scons m (rsub rho)) (er C)) &
    ((forall m x, ITy (ext rho (natFam j) m x) C k
                    (subst_etm (scons m (rsub rho)) (er C)) (FC m x)) *
     (forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
        kceq (kAt (FC m x)) (kAt (FC m' x'))))%type }.
Proof.
  assert (HEm : forall m (x : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x)).
  { intros m x.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam j) m) =>
                projT1 (ityT_of_ITot (nat_ j :: G) C k IHC
                          (ext rho (natFam j) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam j) m x) C k
                             (subst_etm (scons m (rsub rho)) (er C)) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ j :: G) C k IHC
                         (ext rho (natFam j) m x) (HEm m x)))).
  exists FC; split; [exact DC |].
  intros m x m' x' Hm.
  assert (HEx : EnvRelOf (nat_ j :: G) (ext rho (natFam j) m x)
                  (ext rho (natFam j) m' x')).
  { apply (EnvRelOf_ext G rho rho (nat_ j) j (natFam j) (natFam j) m x m' x'
             (EnvRelOf_selfE G rho Hrho)).
    split; [exact (famAtSelf (natFam j)) | exact Hm]. }
  exact (FunTy_of_FunTm (nat_ j :: G) C (funtm (nat_ j :: G) C (UU k) dC)
           _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
           (LTyK_of_ty (nat_ j :: G) C k dC _ _ HEx)).
Qed.

(* The step's type is well typed: a renaming, a substitution and a weakening of
   the motive's derivation. *)
Lemma ty_nrec_succ G C k j (W : Rules.wfc G) (dC : ty (nat_ j :: G) C (UU k)) :
  inhabited (ty (C :: nat_ j :: G) (nrec_succ C) (UU k)).
Proof.
  pose proof (w_cons G (nat_ j) j W (t_nat G j W)) as W1.
  pose proof (w_cons (nat_ j :: G) (nat_ j) j W1 (t_nat (nat_ j :: G) j W1)) as W2.
  destruct (ty_ren (nat_ j :: G) C (UU k) dC (nat_ j :: nat_ j :: G) (up_ren ↑)
              (ren_ok_up ↑ G (nat_ j :: G) (nat_ j) (ren_ok_shift G (nat_ j)))
              (inhabits W2)) as [d1].
  destruct (ty_subst1 (nat_ j :: G) (nat_ j) (C ⟨up_ren ↑⟩) (UU k)
              (succ (var_tm 0)) d1
              (t_succ (nat_ j :: G) j (var_tm 0)
                 (t_var (nat_ j :: G) 0 (nat_ j) W1 (lookup_O G (nat_ j))))) as [d2].
  destruct (ty_ren (nat_ j :: G) _ (UU k) d2 (C :: nat_ j :: G) ↑
              (ren_ok_shift (nat_ j :: G) C)
              (inhabits (w_cons (nat_ j :: G) C k W1 dC))) as [d3].
  rewrite <- nrec_succ_as in d3.
  exact (inhabits d3).
Qed.

Lemma funtm_nrec_succ G C k j (W : Rules.wfc G) (dC : ty (nat_ j :: G) C (UU k)) :
  FunTm (C :: nat_ j :: G) (nrec_succ C).
Proof.
  destruct (ty_nrec_succ G C k j W dC) as [d].
  exact (FunTm_of_ty (C :: nat_ j :: G) (nrec_succ C) k d).
Qed.

(* semrec_rel at two indices that are only PROVABLY equal, which is what the
   scrutinees' relatedness gives. *)
Lemma semrec_rel_idx (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (cohC : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
            kceq (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  (SC' : etm -> etm) (FC' : forall m (x : kElAt (natFam k0) m), kUFam k (SC' m))
  (cohC' : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             kceq (kAt (FC' m x)) (kAt (FC' m' x')))
  (zr' sr' : etm) (xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) zr')
  (step' : forall m x w (y : kElAt (FC' m x) w),
             kElAt (FC' (esucc m) (natSucc x)) (eapp (eapp sr' m) w))
  (Hz : kRel (FC ezero (natE 0 NatAt_zero)) zr xz
             (FC' ezero (natE 0 NatAt_zero)) zr' xz')
  (Hstep : forall m x m' x', kEqAt (natFam k0) m x (natFam k0) m' x' ->
             forall w y w' y', kRel (FC m x) w y (FC' m' x') w' y' ->
             kRel (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w) (step m x w y)
                  (FC' (esucc m') (natSucc x')) (eapp (eapp sr' m') w')
                  (step' m' x' w' y'))
  j m (e : NatAt j m) j' m' (e' : NatAt j' m') (Ej : j = j') :
  kRel (FC m (natE j e)) (enatrec zr sr m)
         (semrec k k0 SC FC cohC zr sr xz step j m e)
       (FC' m' (natE j' e')) (enatrec zr' sr' m')
         (semrec k k0 SC' FC' cohC' zr' sr' xz' step' j' m' e').
Proof.
  destruct Ej.
  exact (semrec_rel k k0 SC FC cohC zr sr xz step SC' FC' cohC' zr' sr' xz' step'
           Hz Hstep j m e m' e').
Qed.

Lemma ITy_uncast rho A k w w' (E : w = w') (F : kUFam k w) :
  ITy rho A k w' (famCast E F) -> ITy rho A k w F.
Proof. destruct E; intros D; exact D. Qed.

(* The primed recursor's data: the motive is C', but the branches are typed at
   C's instances -- that is how the rule is stated -- so their values are the
   C-values moved along the motives' equality. *)
Lemma build_rec_data' G C C' z' s' k j
  (dC : ty (nat_ j :: G) C (UU k)) (dC' : ty (nat_ j :: G) C' (UU k))
  (dz' : ty G z' (C [(zero j)..]))
  (ds' : ty (C :: nat_ j :: G) s' (nrec_succ C))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHC' : ITot (nat_ j :: G) C' (UU k))
  (IHz' : ITot G z' (C [(zero j)..]))
  (IHs' : ITot (C :: nat_ j :: G) s' (nrec_succ C))
  (IHcC : IRel (nat_ j :: G) C C' (UU k))
  rho (Hrho : EnvITy G rho) :
  { FC' : forall m (x : kElAt (natFam j) m),
            kUFam k (subst_etm (scons m (rsub rho)) (er C')) &
  { cohC' : forall m x m' x', kEqAt (natFam j) m x (natFam j) m' x' ->
              kceq (kAt (FC' m x)) (kAt (FC' m' x')) &
  { xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) (ers rho z') &
  { xs' : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC' m x) w),
            kElAt (FC' (esucc m) (natSucc x))
              (ers (ext (ext rho (natFam j) m x) (FC' m x) w y) s') &
    ((forall m x, ITy (ext rho (natFam j) m x) C' k
                    (subst_etm (scons m (rsub rho)) (er C')) (FC' m x)) *
     ITm rho z' k (subst_etm (scons ezero (rsub rho)) (er C'))
         (FC' ezero (natE 0 NatAt_zero)) (ers rho z') xz' *
     (forall m x w y,
        ITm (ext (ext rho (natFam j) m x) (FC' m x) w y) s' k
            (subst_etm (scons (esucc m) (rsub rho)) (er C'))
            (FC' (esucc m) (natSucc x))
            (ers (ext (ext rho (natFam j) m x) (FC' m x) w y) s')
            (xs' m x w y)))%type
  } } } }.
Proof.
  assert (HEm : forall m (x : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x)).
  { intros m x.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x Hrho). }
  destruct (build_motive G C k j dC IHC rho Hrho) as [FC [DC cohC]].
  destruct (build_motive G C' k j dC' IHC' rho Hrho) as [FC' [DC' cohC']].
  assert (PCC : forall m x, kceq (kAt (FC m x)) (kAt (FC' m x))).
  { intros m x.
    exact (ceq_of_IRel_at' (nat_ j :: G) C C' k IHcC (ext rho (natFam j) m x)
             (HEm m x) _ (FC m x) (DC m x) _ (FC' m x) (DC' m x)). }
  (* the base branch *)
  assert (E0 : subst_etm (scons ezero (rsub rho)) (er C)
               = ers rho (C [(zero j)..]))
    by exact (eq_sym (ers_sub1 rho C (zero j) (natFam j) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho (zero j) j enat (natFam j) ezero
                (natE 0 NatAt_zero) eq_refl (i_zero rho j) C k _
                (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz' rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [(zero j)..]) k _ _ E0 _ DCz)) as [w0 Dw0].
  destruct (ITm_uncast rho z' k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dw0)
    as [xz0 Dz0].
  (* the step branch *)
  assert (Hstep : forall m (x : kElAt (natFam j) m) w (y : kElAt (FC' m x) w),
             { v : kElAt (FC' (esucc m) (natSucc x))
                     (ers (ext (ext rho (natFam j) m x) (FC' m x) w y) s') &
               ITm (ext (ext rho (natFam j) m x) (FC' m x) w y) s' k
                   (subst_etm (scons (esucc m) (rsub rho)) (er C'))
                   (FC' (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam j) m x) (FC' m x) w y) s') v }).
  { intros m x w y.
    pose proof (EnvITy_ext_ceq (nat_ j :: G) (ext rho (natFam j) m x) C k _
                  (FC' m x) (FC m x) (DC m x) (famCeq_sym _ _ (PCC m x)) w y
                  (HEm m x)) as HE1.
    pose proof (ity_nrec_succ rho C k j m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k _ (FC' m x) w y) as DS.
    assert (Es : subst_etm (scons (esucc m) (rsub rho)) (er C)
                 = ers (ext (ext rho (natFam j) m x) (FC' m x) w y)
                     (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs' (ext (ext rho (natFam j) m x) (FC' m x) w y) HE1 k
                (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [v0 Dv0].
    destruct (ITm_uncast _ s' k _ _ Es (FC (esucc m) (natSucc x)) _ _ Dv0)
      as [v1 Dv1].
    exists (kto (kAt (FC (esucc m) (natSucc x))) (kAt (FC' (esucc m) (natSucc x)))
              (famAtWf (FC (esucc m) (natSucc x)))
              (famAtWf (FC' (esucc m) (natSucc x)))
              (PCC (esucc m) (natSucc x)) _ v1).
    exact (i_conv _ s' k _ _ _ _ _ _ (PCC (esucc m) (natSucc x)) Dv1). }
  exists FC', cohC',
    (kto (kAt (FC ezero (natE 0 NatAt_zero)))
       (kAt (FC' ezero (natE 0 NatAt_zero)))
       (famAtWf (FC ezero (natE 0 NatAt_zero)))
       (famAtWf (FC' ezero (natE 0 NatAt_zero)))
       (PCC ezero (natE 0 NatAt_zero)) _ xz0),
    (fun m x w y => projT1 (Hstep m x w y)).
  split;
    [split; [exact DC'
            | exact (i_conv rho z' k _ _ _ _ _ _
                       (PCC ezero (natE 0 NatAt_zero)) Dz0)] |].
  intros m x w y; exact (projT2 (Hstep m x w y)).
Qed.

(* ---- the recursor's congruence.  Both subjects are decoded; the two
     recursions are compared by semrec_rel, whose two hypotheses are the
     branches' relatedness -- each obtained in the two steps the conversion
     cases use: the induction hypothesis in one environment, then the
     right-hand branch's own functionality across the two. ---- *)
Lemma isem_natrec_core G C C' z z' s s' n n' k j (W : Rules.wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dC' : ty (nat_ j :: G) C' (UU k))
  (dz : ty G z (C [(zero j)..])) (dz' : ty G z' (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C))
  (ds' : ty (C :: nat_ j :: G) s' (nrec_succ C))
  (dn : ty G n (nat_ j)) (dn' : ty G n' (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHcC : IRel (nat_ j :: G) C C' (UU k))
  (IHz' : ITot G z' (C [(zero j)..])) (IHcz : IRel G z z' (C [(zero j)..]))
  (IHs' : ITot (C :: nat_ j :: G) s' (nrec_succ C))
  (IHcs : IRel (C :: nat_ j :: G) s s' (nrec_succ C))
  (IHcn : IRel G n n' (nat_ j))
  (IHn : ITot G n (nat_ j)) (IHn' : ITot G n' (nat_ j))
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : RecVal rho C z s n k' Sy F (ers rho (natrec C z s n)) x)
  (E' : RecVal rho C' z' s' n' k' Sy F (ers rho (natrec C' z' s' n')) y) :
  kEqAt F (ers rho (natrec C z s n)) x F (ers rho (natrec C' z' s' n')) y.
Proof.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (w_cons G (nat_ j) j W (t_nat G j W)) as W1.
  pose proof (w_cons (nat_ j :: G) C k W1 dC) as WC.
  destruct E as [d1 Hv1]; destruct E' as [d2 Hv2].
  destruct d1 as
    [j1 SC1 FC1 cohC1 S01 wz1 xz1 ws1 xs1 redS1 wn1 xn1 Ep1 DC1 Dz1 Ds1 Dn1].
  destruct d2 as
    [j2 SC2 FC2 cohC2 S02 wz2 xz2 ws2 xs2 redS2 wn2 xn2 Ep2 DC2 Dz2 Ds2 Dn2].
  cbn [cn_Sy cn_F cn_w cn_x] in Hv1, Hv2.
  unfold rd_val in Hv1, Hv2.
  cbn [rd_j rd_SC rd_FC rd_cohC rd_S0 rd_wz rd_xz rd_ws rd_xs rd_redS rd_wn
       rd_xn] in Hv1, Hv2.
  (* the scrutinee's level is the one its type records *)
  pose proof (lvl_of_ITot G n (nat_ j) IHn rho Hrho j (natFam j)
                (ity_nat rho _ _ eq_refl) NotPrfR_nat j1 _ _ _ xn1
                NotPrfR_nat Dn1) as Ej1; subst j1.
  pose proof (lvl_of_ITot G n' (nat_ j) IHn' rho Hrho j (natFam j)
                (ity_nat rho _ _ eq_refl) NotPrfR_nat j2 _ _ _ xn2
                NotPrfR_nat Dn2) as Ej2; subst j2.
  assert (En1 : wn1 = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn1).
  assert (En2 : wn2 = ers rho n') by exact (ers_of_ITm _ _ _ _ _ _ _ Dn2).
  assert (Ez1 : wz1 = ers rho z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz1).
  assert (Ez2 : wz2 = ers rho z') by exact (ers_of_ITm _ _ _ _ _ _ _ Dz2).
  subst wn1 wn2 wz1 wz2.
  assert (HEm : forall m (x0 : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x0)).
  { intros m x0.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x0 Hrho). }
  (* the shapes' level is the motive's *)
  destruct (build_motive G C k j dC IHC rho Hrho) as [FCc [DCc cohCc]].
  pose proof (IHcn rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)
                xn1 xn2 Dn1 Dn2) as Hnn.
  assert (Eidx : natIdx xn1 = natIdx xn2)
    by exact (proj1 (proj1 (natEq_iff xn1 xn2) Hnn)).
  pose proof (ity_lvl (ext rho (natFam j) (ers rho n) xn1)
                (ext rho (natFam j) (ers rho n) xn1) eq_refl C k _
                (FCc (ers rho n) xn1) k' _ (FC1 (ers rho n) xn1)
                (DCc (ers rho n) xn1) (DC1 (ers rho n) xn1)) as Ek; subst k'.
  (* the motives' instances agree *)
  assert (PCC : forall m x0, kceq (kAt (FC1 m x0)) (kAt (FC2 m x0))).
  { intros m x0.
    exact (ceq_of_IRel_at' (nat_ j :: G) C C' k IHcC (ext rho (natFam j) m x0)
             (HEm m x0) _ (FC1 m x0) (DC1 m x0) _ (FC2 m x0) (DC2 m x0)). }
  assert (EC1 : forall m (x0 : kElAt (natFam j) m),
             SC1 m = ers (ext rho (natFam j) m x0) C)
    by (intros m x0; exact (ers_of_ITy _ _ _ _ _ (DC1 m x0))).
  (* the base branches *)
  assert (E0 : SC1 ezero = ers rho (C [(zero j)..])).
  { rewrite (EC1 ezero (natE 0 NatAt_zero)).
    exact (eq_sym (ers_sub1 rho C (zero j) (natFam j) (natE 0 NatAt_zero))). }
  pose proof (isubst_ITy rho (zero j) j enat (natFam j) ezero
                (natE 0 NatAt_zero) eq_refl (i_zero rho j) C k _
                (FC1 ezero (natE 0 NatAt_zero))
                (DC1 ezero (natE 0 NatAt_zero))) as DCz1.
  assert (fCz : FunTm G (C [(zero j)..])).
  { destruct (ty_subst1 G (nat_ j) C (UU k) (zero j) dC (t_zero G j W))
      as [dsub].
    exact (FunTm_of_ty G (C [(zero j)..]) k dsub). }
  destruct (IHz' rho Hrho k (famCast E0 (FC1 ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [(zero j)..]) k _ _ E0 _ DCz1)) as [w0 Dw0].
  destruct (ITm_uncast rho z' k _ _ E0 (FC1 ezero (natE 0 NatAt_zero)) _ _ Dw0)
    as [xz0 Dz0].
  assert (Hz : kRel (FC1 ezero (natE 0 NatAt_zero)) (ers rho z) xz1
                 (FC2 ezero (natE 0 NatAt_zero)) (ers rho z') xz2).
  { eapply kRel_trans;
      [ exact (kRel_of_IRel' G z z' (C [(zero j)..]) IHcz fCz rho Hrho k _ _ _ _
                 DCz1 DCz1 _ xz1 _ xz0 Dz1 Dz0) |].
    refine (funtm G z' (C [(zero j)..]) dz' rho rho HEself k
              _ (FC1 ezero (natE 0 NatAt_zero)) _ xz0 Dz0
              _ (FC2 ezero (natE 0 NatAt_zero)) _ xz2 Dz2
              (PCC ezero (natE 0 NatAt_zero)) _).
    apply (Rel_tyeq (SC1 ezero) (SC2 ezero));
      [ exact (ceq_ty (FC1 ezero (natE 0 NatAt_zero))
                 (FC2 ezero (natE 0 NatAt_zero)) (PCC ezero (natE 0 NatAt_zero)))
      | rewrite E0; exact (LTm_of_ty G z' (C [(zero j)..]) dz' rho rho HEself) ]. }
  (* the step branches *)
  assert (fS : FunTm (C :: nat_ j :: G) (nrec_succ C))
    by exact (funtm_nrec_succ G C k j W dC).
  assert (Hst : forall m x0 m' x0', kEqAt (natFam j) m x0 (natFam j) m' x0' ->
             forall w y0 w' y0', kRel (FC1 m x0) w y0 (FC2 m' x0') w' y0' ->
             kRel (FC1 (esucc m) (natSucc x0)) (ws1 m x0 w y0) (xs1 m x0 w y0)
                  (FC2 (esucc m') (natSucc x0')) (ws2 m' x0' w' y0')
                  (xs2 m' x0' w' y0')).
  { intros m x0 m' x0' Hm w y0 w' y0' Hy.
    (* the interpretation of the step's type in the unprimed environment *)
    pose proof (ITy_uncast _ (nrec_succ C) k _ _ (EC1 (esucc m) (natSucc x0))
                  (FC1 (esucc m) (natSucc x0))
                  (ity_nrec_succ rho C k j m x0
                     (famCast (EC1 (esucc m) (natSucc x0))
                        (FC1 (esucc m) (natSucc x0)))
                     (ITy_cast _ C k _ _ (EC1 (esucc m) (natSucc x0)) _
                        (DC1 (esucc m) (natSucc x0)))
                     k _ (FC1 m x0) w y0)) as DS1.
    assert (Es1 : SC1 (esucc m)
                  = ers (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0)
                      (nrec_succ C))
      by exact (eq_trans (EC1 (esucc m) (natSucc x0))
                  (eq_sym (er_nrec_succ C (rsub rho) m w))).
    pose proof (EnvITy_ext_ceq (nat_ j :: G) (ext rho (natFam j) m x0) C k _
                  (FC1 m x0) (famCast (EC1 m x0) (FC1 m x0))
                  (ITy_cast _ C k _ _ (EC1 m x0) _ (DC1 m x0))
                  (famCast_ceq (EC1 m x0) (FC1 m x0)) w y0 (HEm m x0)) as HE1.
    destruct (IHs' (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0) HE1 k
                (famCast Es1 (FC1 (esucc m) (natSucc x0)))
                (ITy_cast _ (nrec_succ C) k _ _ Es1 _ DS1)) as [v0 Dv0].
    destruct (ITm_uncast _ s' k _ _ Es1 (FC1 (esucc m) (natSucc x0)) _ _ Dv0)
      as [v1 Dv1].
    (* s against s' in the unprimed environment *)
    pose proof (kRel_of_IRel' (C :: nat_ j :: G) s s' (nrec_succ C) IHcs fS
                  (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0) HE1 k
                  _ (FC1 (esucc m) (natSucc x0)) _ (FC1 (esucc m) (natSucc x0))
                  DS1 DS1 _ (xs1 m x0 w y0) _ v1 (Ds1 m x0 w y0) Dv1) as Hb1.
    (* s' across the two environments *)
    assert (HE0 : EnvRelOf (nat_ j :: G) (ext rho (natFam j) m x0)
                    (ext rho (natFam j) m' x0')).
    { apply (EnvRelOf_ext G rho rho (nat_ j) j (natFam j) (natFam j) m x0 m' x0'
               HEself).
      split; [exact (famAtSelf (natFam j)) | exact Hm]. }
    assert (T1 : tyeq (SC1 m) (ers (ext rho (natFam j) m x0) C)).
    { pose proof (uf_ty (FC1 m x0)) as U.
      rewrite (EC1 m x0) in U |- *; exists k; exact U. }
    assert (T2 : tyeq (SC2 m') (ers (ext rho (natFam j) m' x0') C)).
    { rewrite <- (EC1 m' x0').
      apply tyeq_sym; exact (ceq_ty (FC1 m' x0') (FC2 m' x0') (PCC m' x0')). }
    assert (HEr : EnvRelOf (C :: nat_ j :: G)
                    (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0)
                    (ext (ext rho (natFam j) m' x0') (FC2 m' x0') w' y0')).
    { apply (EnvRelOf_ext_ty (nat_ j :: G) (ext rho (natFam j) m x0)
               (ext rho (natFam j) m' x0') C k (SC1 m) (SC2 m')
               (FC1 m x0) (FC2 m' x0') w y0 w' y0' HE0 T1 T2 Hy). }
    assert (Q : kceq (kAt (FC1 (esucc m) (natSucc x0)))
                     (kAt (FC2 (esucc m') (natSucc x0')))).
    { eapply famCeq_tr; [exact (PCC (esucc m) (natSucc x0)) |].
      exact (cohC2 (esucc m) (natSucc x0) (esucc m') (natSucc x0')
               (natSucc_eq x0 x0' Hm)). }
    assert (Ew2 : ws2 m' x0' w' y0'
                  = ers (ext (ext rho (natFam j) m' x0') (FC2 m' x0') w' y0') s')
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds2 m' x0' w' y0')).
    assert (Hr : Rel (SC2 (esucc m'))
                   (ers (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0) s')
                   (ws2 m' x0' w' y0')).
    { rewrite Ew2.
      apply (Rel_tyeq (ers (ext (ext rho (natFam j) m x0) (FC1 m x0) w y0)
                         (nrec_succ C)) (SC2 (esucc m'))).
      - rewrite <- Es1; exact (ceq_ty _ _ Q).
      - exact (LTm_of_ty (C :: nat_ j :: G) s' (nrec_succ C) ds' _ _ HEr). }
    pose proof (funtm (C :: nat_ j :: G) s' (nrec_succ C) ds' _ _ HEr k
                  _ (FC1 (esucc m) (natSucc x0)) _ v1 Dv1
                  _ (FC2 (esucc m') (natSucc x0')) _ (xs2 m' x0' w' y0')
                  (Ds2 m' x0' w' y0') Q Hr) as Hb2.
    eapply kRel_trans; [exact Hb1 | exact Hb2]. }
  (* and the two recursions *)
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv1 | exact Hv2 |].
  eapply semrec_rel_idx; [exact Hz | | exact Eidx].
  intros m x0 m' x0' Hm w y0 w' y0' Hy.
  eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
  eapply kRel_trans; [| apply moveTo_rel].
  exact (Hst m x0 m' x0' Hm w y0 w' y0' Hy).
Qed.

(* the primed recursor at the LEFT-hand type *)
Lemma itot_natrec' G C C' z' s' n n' k j
  (dC : ty (nat_ j :: G) C (UU k)) (dC' : ty (nat_ j :: G) C' (UU k))
  (dz' : ty G z' (C [(zero j)..]))
  (ds' : ty (C :: nat_ j :: G) s' (nrec_succ C))
  (dn : ty G n (nat_ j)) (dn' : ty G n' (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHC' : ITot (nat_ j :: G) C' (UU k))
  (IHz' : ITot G z' (C [(zero j)..]))
  (IHs' : ITot (C :: nat_ j :: G) s' (nrec_succ C))
  (IHcC : IRel (nat_ j :: G) C C' (UU k))
  (IHn : ITot G n (nat_ j)) (IHn' : ITot G n' (nat_ j))
  (IHcn : IRel G n n' (nat_ j)) :
  ITot G (natrec C' z' s' n') (C [n..]).
Proof.
  intros rho Hrho k' F DCn.
  destruct (build_motive G C k j dC IHC rho Hrho) as [FC [DC cohC]].
  destruct (build_rec_data' G C C' z' s' k j dC dC' dz' ds' IHC IHC' IHz' IHs'
              IHcC rho Hrho) as [FC' [cohC' [xz' [xs' [[DC' Dz'] Ds']]]]].
  assert (HEm : forall m (x : kElAt (natFam j) m),
             EnvITy (nat_ j :: G) (ext rho (natFam j) m x)).
  { intros m x.
    exact (EnvITy_ext G rho (nat_ j) j (natFam j)
             (ity_nat rho _ _ eq_refl) m x Hrho). }
  assert (PCC : forall m x, kceq (kAt (FC m x)) (kAt (FC' m x))).
  { intros m x.
    exact (ceq_of_IRel_at' (nat_ j :: G) C C' k IHcC (ext rho (natFam j) m x)
             (HEm m x) _ (FC m x) (DC m x) _ (FC' m x) (DC' m x)). }
  destruct (IHn rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)) as [xn Dn].
  destruct (IHn' rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)) as [xn' Dn'].
  pose proof (IHcn rho Hrho j (natFam j) (ity_nat rho _ _ eq_refl)
                xn xn' Dn Dn') as Hnn.
  pose proof (i_natrec rho C' z' s' n' k j
                (fun m => subst_etm (scons m (rsub rho)) (er C')) FC' cohC'
                (ers rho (stepWrap s')) (ers rho z') xz'
                (fun m x w y =>
                   ers (ext (ext rho (natFam j) m x) (FC' m x) w y) s')
                xs' (fun m x w y => reds_lam2_app (er s') (rsub rho) m w)
                (ers rho n') xn' eq_refl DC' Dz' Ds' Dn') as Dnr'.
  assert (Q : kceq (kAt (FC' (ers rho n') (natE (natIdx xn') (natSpec xn'))))
                   (kAt (FC (ers rho n) xn))).
  { apply famCeq_sym.
    eapply famCeq_tr; [exact (PCC (ers rho n) xn) |].
    apply cohC'.
    eapply kEqAt_trans;
      [exact (famAtSelf (natFam j)) | exact Hnn | apply natEq_self]. }
  pose proof (i_conv rho (natrec C' z' s' n') k _ _ _ _ _ _ Q Dnr') as Dnr.
  assert (En : subst_etm (scons (ers rho n) (rsub rho)) (er C)
               = ers rho (C [n..]))
    by exact (eq_sym (ers_sub1 rho C n (natFam j) xn)).
  pose proof (isubst_ITy rho n j enat (natFam j) (ers rho n) xn eq_refl Dn
                C k _ (FC (ers rho n) xn) (DC (ers rho n) xn)) as DCsub.
  pose proof (ITy_cast rho (C [n..]) k _ _ En _ DCsub) as DCc.
  assert (Hfun : FunTm G (C [n..])).
  { destruct (ty_subst1 G (nat_ j) C (UU k) n dC dn) as [d].
    exact (FunTm_of_ty G (C [n..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (C [n..]) k (ers rho (C [n..]))
                (famCast En (FC (ers rho n) xn)) k' (ers rho (C [n..])) F
                DCc DCn) as Ek; subst k'.
  refine (itot_move G (natrec C' z' s' n') (C [n..]) Hfun rho Hrho k F
            (famCast En (FC (ers rho n) xn)) DCn DCc _ _).
  refine (ITm_cast rho (natrec C' z' s' n') k _ _ En (FC (ers rho n) xn) _ _ _).
  exact Dnr.
Qed.

Lemma isem_natrec G C C' z z' s s' n n' k j (W : Rules.wfc G)
  (dC : ty (nat_ j :: G) C (UU k)) (dC' : ty (nat_ j :: G) C' (UU k))
  (cC : cv (nat_ j :: G) C C' (UU k))
  (dz : ty G z (C [(zero j)..])) (dz' : ty G z' (C [(zero j)..]))
  (cz : cv G z z' (C [(zero j)..]))
  (ds : ty (C :: nat_ j :: G) s (nrec_succ C))
  (ds' : ty (C :: nat_ j :: G) s' (nrec_succ C))
  (cs : cv (C :: nat_ j :: G) s s' (nrec_succ C))
  (dn : ty G n (nat_ j)) (dn' : ty G n' (nat_ j)) (cn : cv G n n' (nat_ j))
  (IHC : ITot (nat_ j :: G) C (UU k)) (IHC' : ITot (nat_ j :: G) C' (UU k))
  (IHcC : IRel (nat_ j :: G) C C' (UU k))
  (IHz : ITot G z (C [(zero j)..])) (IHz' : ITot G z' (C [(zero j)..]))
  (IHcz : IRel G z z' (C [(zero j)..]))
  (IHs : ITot (C :: nat_ j :: G) s (nrec_succ C))
  (IHs' : ITot (C :: nat_ j :: G) s' (nrec_succ C))
  (IHcs : IRel (C :: nat_ j :: G) s s' (nrec_succ C))
  (IHn : ITot G n (nat_ j)) (IHn' : ITot G n' (nat_ j))
  (IHcn : IRel G n n' (nat_ j)) :
  ISem G (natrec C z s n) (natrec C' z' s' n') (C [n..]).
Proof.
  split;
    [split; [exact (itot_natrec G C z s n k j dC dz ds dn IHC IHz IHs IHn)
            | exact (itot_natrec' G C C' z' s' n n' k j dC dC' dz' ds' dn dn'
                       IHC IHC' IHz' IHs' IHcC IHn IHn' IHcn)] |].
  intros rho Hrho k' F DCn x y Dx Dy.
  pose proof (LCv_of_cv G (natrec C z s n) (natrec C' z' s' n') (C [n..])
                (c_natrec G C C' z z' s s' n n' k j dC dC' cC dz dz' cz ds ds' cs
                   dn dn' cn) rho rho (EnvRelOf_selfE G rho Hrho)) as Hrel.
  pose proof (itm_inv rho (natrec C z s n) k' (ers rho (C [n..])) F
                (ers rho (natrec C z s n)) x Dx) as E.
  pose proof (itm_inv rho (natrec C' z' s' n') k' (ers rho (C [n..])) F
                (ers rho (natrec C' z' s' n')) y Dy) as E'.
  cbn [TmInv] in E, E'.
  destruct E as [[HT _] | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [[HT' _] | E']; [exact (HT' _ x _ y Hrel) |].
  exact (isem_natrec_core G C C' z z' s s' n n' k j W dC dC' dz dz' ds ds' dn dn'
           IHC IHcC IHz' IHcz IHs' IHcs IHcn IHn IHn' rho Hrho k' _ F x y E E').
Qed.

(* ================================================================== *)
(* W: the node's congruence.                                           *)
(* ================================================================== *)

(* ---- the primed node, at the LEFT-hand branching type.  The rule types f'
     at `B [a..]`, not at `B [a'..]`, so its value has to be moved along the
     two branching Pi families' equality before `i_sup` will take it. ---- *)
Lemma itot_sup' G A B a a' f f' k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (da : ty G a A) (da' : ty G a' A) (ca : cv G a a' A)
  (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (df' : ty G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (cf : cv G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHa : ITot G a A) (IHa' : ITot G a' A) (IHca : IRel G a a' A)
  (IHf' : ITot G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  ITot G (sup k A B a' f') (wt k A B).
Proof.
  intros rho Hrho k' F DW'.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho HEself).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* the two labels *)
  destruct (IHa rho Hrho i FA DFA) as [xa Da].
  destruct (IHa' rho Hrho i FA DFA) as [xa' Da'].
  pose proof (IHca rho Hrho i FA DFA xa xa' Da Da') as A3.
  pose (Xa := upEl (k - i) k EA FA (ers rho a) xa).
  pose (Xa' := upEl (k - i) k EA FA (ers rho a') xa').
  assert (A3u : kEqAt (upF (k - i) k EA FA) (ers rho a) Xa
                  (upF (k - i) k EA FA) (ers rho a') Xa')
    by exact (upEl_eq (k - i) k EA FA _ xa FA _ xa' (famAtSelf FA) A3).
  (* the branching type at the left label, where f' is read *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho a) xa)
              (EnvITy_ext G rho A i FA DFA (ers rho a) xa Hrho)) as [FBu DBu0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho a) xa)
                  (ext rho FA (ers rho a)
                     (dnEl (k - i) k EA FA (ers rho a) Xa))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho a) xa (ers rho a) _
             HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu) (kAt (FB (ers rho a) Xa)))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0 (DB (ers rho a) Xa)
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  pose proof (ity_conv rho (B [a..]) j _ FBu (FB (ers rho a) Xa) P
                (isubst_ITy rho a i (ers rho A) FA (ers rho a) xa eq_refl Da
                   B j (ers (ext rho FA (ers rho a) xa) B) FBu DBu0)) as DBa.
  pose proof (ity_pi rho (B [a..]) ((wt k A B) ⟨↑⟩) k j k (k - j) 0 EB eq_refl
                (wB (ers rho a) Xa) (FB (ers rho a) Xa) Bbr
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho a) Xa)
                (eq_sym (er_wsup_fun_sub k A B a (rsub rho)))
                DBa
                (fun u0 x =>
                   weaken1_ITy rho (wt k A B) k (ew (ers rho A) B0) WF
                     (Build_Entry j (wB (ers rho a) Xa) (FB (ers rho a) Xa) u0
                        (dnEl (k - j) k EB (FB (ers rho a) Xa) u0 x)) DW))
    as Dfpi.
  assert (Ef : epi (wB (ers rho a) Xa) Bbr
               = ers rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
    by exact (eq_sym (er_wsup_fun_sub k A B a (rsub rho))).
  destruct (IHf' rho Hrho k (famCast Ef _)
              (ITy_cast rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) k _ _ Ef _ Dfpi))
    as [xf0 Df0].
  destruct (ITm_uncast rho f' k _ _ Ef _ _ _ Df0) as [xf1 Df1].
  (* the two branching Pi families agree: equal codomains, and domains the
     codomain's functionality at the two labels *)
  assert (QB : kceq (kAt (FB (ers rho a) Xa)) (kAt (FB (ers rho a') Xa')))
    by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) rho rho HEself k i j (k - i) EA
                _ FA wB FB _ FA wB FB DFA DFA (famAtSelf FA) DB DB _ _ _ _ A3u).
  assert (Htb : tyeq (wB (ers rho a) Xa) (wB (ers rho a') Xa'))
    by exact (ceq_ty _ _ QB).
  assert (Htp : tyeq (epi (wB (ers rho a) Xa) Bbr)
                  (epi (wB (ers rho a') Xa') Bbr)).
  { exists k; apply eqty_pi.
    - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB (ers rho a) Xa)))
               (uf_ty (upF (k - j) k EB (FB (ers rho a') Xa'))) Htb).
    - intros u u' _.
      eapply eqty_exp; [exact (redBbr u) | exact (redBbr u') | exact gW]. }
  assert (Qpi : kceq
                  (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                          wB FB redB cohB gW Bbr redBbr gBr (ers rho a) Xa))
                  (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                          wB FB redB cohB gW Bbr redBbr gBr (ers rho a') Xa'))).
  { unfold brFam.
    apply (piFam_ceq k (wB (ers rho a) Xa) Bbr
             (upF (k - j) k EB (FB (ers rho a) Xa))
             (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
             (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
             (gBr (ers rho a) Xa)
             (wB (ers rho a') Xa') Bbr (upF (k - j) k EB (FB (ers rho a') Xa'))
             (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
             (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
             (gBr (ers rho a') Xa') Htp);
      [ exact (upF_ceq (k - j) k EB (FB (ers rho a) Xa) (FB (ers rho a') Xa') QB)
      | intros u x u' x' _; exact (famAtSelf WF) ]. }
  pose proof (i_conv rho f' k _
                (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho a) Xa) _
                (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho a') Xa') _ xf1 Qpi Df1)
    as Df2.
  (* the primed node is layer-1 good: it is related to the unprimed one *)
  assert (gr : Rel (ers rho (wt k A B)) (ers rho (sup k A B a f))
                 (ers rho (sup k A B a' f')))
    by exact (LCv_of_cv G (sup k A B a f) (sup k A B a' f') (wt k A B)
                (c_sup G k i j A B a a' f f' Hik Hjk dAt dBt da da' ca df df' cf)
                rho rho HEself).
  assert (gd : Good (ew (ers rho A) B0) (esup (ers rho a') (ers rho f')))
    by (eapply Rel_trans; [apply Rel_sym; exact gr | exact gr]).
  pose proof (ity_lvl rho rho eq_refl (wt k A B) k (ers rho (wt k A B)) WF
                k' (ers rho (wt k A B)) F DW DW') as Ek; subst k'.
  refine (itot_move G (sup k A B a' f') (wt k A B)
            (FunTm_of_ty G (wt k A B) k (t_w G k i j A B Hik Hjk dAt dBt))
            rho Hrho k F WF DW' DW _ _).
  exact (i_sup rho A B a' f' k i j (k - i) (k - j) EA EB (ers rho A) FA B0
           wB FB redB cohB gW Bbr redBbr gBr (ers rho a') xa' (ers rho f') _
           gd eq_refl DFA DB Da' Df2).
Qed.

(* ---- the node's congruence.  Both subjects are built from ONE set of
     canonical data -- the same label family, the same branching family and
     the same tree family -- so `wSup_congX` compares them with all three of
     its equalities on the diagonal: what is left is the two labels'
     relatedness and the two branching functions', and the latter is the
     induction hypothesis for the conversion read at the branching Pi, which
     here IS the clause's own family. ---- *)
Lemma sup_data G A B a a' f f' k i j (Hik : i <= k) (Hjk : j <= k)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (da : ty G a A) (da' : ty G a' A) (ca : cv G a a' A)
  (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (df' : ty G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (cf : cv G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (fPi : FunTm G (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHa : ITot G a A) (IHa' : ITot G a' A) (IHca : IRel G a a' A)
  (IHf : ITot G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHf' : ITot G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHcf : IRel G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam k S1 &
  { v1 : kElAt F1 (ers rho (sup k A B a f)) &
  { v2 : kElAt F1 (ers rho (sup k A B a' f')) &
    (ITy rho (wt k A B) k S1 F1 *
     ITm rho (sup k A B a f) k S1 F1 (ers rho (sup k A B a f)) v1 *
     ITm rho (sup k A B a' f') k S1 F1 (ers rho (sup k A B a' f')) v2 *
     kEqAt F1 (ers rho (sup k A B a f)) v1
           F1 (ers rho (sup k A B a' f')) v2)%type } } } }.
Proof.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho HEself).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* the two labels *)
  destruct (IHa rho Hrho i FA DFA) as [xa Da].
  destruct (IHa' rho Hrho i FA DFA) as [xa' Da'].
  pose proof (IHca rho Hrho i FA DFA xa xa' Da Da') as A3.
  pose (Xa := upEl (k - i) k EA FA (ers rho a) xa).
  pose (Xa' := upEl (k - i) k EA FA (ers rho a') xa').
  assert (A3u : kEqAt (upF (k - i) k EA FA) (ers rho a) Xa
                  (upF (k - i) k EA FA) (ers rho a') Xa')
    by exact (upEl_eq (k - i) k EA FA _ xa FA _ xa' (famAtSelf FA) A3).
  (* the branching Pi at the left label, where both functions are read *)
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho a) xa)
              (EnvITy_ext G rho A i FA DFA (ers rho a) xa Hrho)) as [FBu DBu0].
  assert (HEx : EnvRelOf (A :: G) (ext rho FA (ers rho a) xa)
                  (ext rho FA (ers rho a)
                     (dnEl (k - i) k EA FA (ers rho a) Xa))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho a) xa (ers rho a) _
             HEself).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (P : kceq (kAt FBu) (kAt (FB (ers rho a) Xa)))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HEx j
                _ FBu _ _ DBu0 (DB (ers rho a) Xa)
                (LTyK_of_ty (A :: G) B j dBt _ _ HEx)).
  pose proof (ity_conv rho (B [a..]) j _ FBu (FB (ers rho a) Xa) P
                (isubst_ITy rho a i (ers rho A) FA (ers rho a) xa eq_refl Da
                   B j (ers (ext rho FA (ers rho a) xa) B) FBu DBu0)) as DBa.
  pose proof (ity_pi rho (B [a..]) ((wt k A B) ⟨↑⟩) k j k (k - j) 0 EB eq_refl
                (wB (ers rho a) Xa) (FB (ers rho a) Xa) Bbr
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho a) Xa)
                (eq_sym (er_wsup_fun_sub k A B a (rsub rho)))
                DBa
                (fun u0 x =>
                   weaken1_ITy rho (wt k A B) k (ew (ers rho A) B0) WF
                     (Build_Entry j (wB (ers rho a) Xa) (FB (ers rho a) Xa) u0
                        (dnEl (k - j) k EB (FB (ers rho a) Xa) u0 x)) DW))
    as Dfpi.
  assert (Ef : epi (wB (ers rho a) Xa) Bbr
               = ers rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
    by exact (eq_sym (er_wsup_fun_sub k A B a (rsub rho))).
  destruct (IHf rho Hrho k (famCast Ef _)
              (ITy_cast rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) k _ _ Ef _ Dfpi))
    as [xg0 Dg0].
  destruct (ITm_uncast rho f k _ _ Ef _ _ _ Dg0) as [xg Dg].
  destruct (IHf' rho Hrho k (famCast Ef _)
              (ITy_cast rho (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) k _ _ Ef _ Dfpi))
    as [xg0' Dg0'].
  destruct (ITm_uncast rho f' k _ _ Ef _ _ _ Dg0') as [xg' Dg'].
  pose proof (kRel_of_IRel' G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) IHcf fPi
                rho Hrho k _ _ _ _ Dfpi Dfpi _ xg _ xg' Dg Dg') as Hgg.
  (* the right-hand function, moved to the branching Pi at its OWN label *)
  assert (QB : kceq (kAt (FB (ers rho a) Xa)) (kAt (FB (ers rho a') Xa')))
    by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) rho rho HEself k i j (k - i) EA
                _ FA wB FB _ FA wB FB DFA DFA (famAtSelf FA) DB DB _ _ _ _ A3u).
  assert (Htb : tyeq (wB (ers rho a) Xa) (wB (ers rho a') Xa'))
    by exact (ceq_ty _ _ QB).
  assert (Htp : tyeq (epi (wB (ers rho a) Xa) Bbr)
                  (epi (wB (ers rho a') Xa') Bbr)).
  { exists k; apply eqty_pi.
    - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB (ers rho a) Xa)))
               (uf_ty (upF (k - j) k EB (FB (ers rho a') Xa'))) Htb).
    - intros u u' _.
      eapply eqty_exp; [exact (redBbr u) | exact (redBbr u') | exact gW]. }
  assert (Qpi : kceq
                  (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                          wB FB redB cohB gW Bbr redBbr gBr (ers rho a) Xa))
                  (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                          wB FB redB cohB gW Bbr redBbr gBr (ers rho a') Xa'))).
  { unfold brFam.
    apply (piFam_ceq k (wB (ers rho a) Xa) Bbr
             (upF (k - j) k EB (FB (ers rho a) Xa))
             (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
             (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
             (gBr (ers rho a) Xa)
             (wB (ers rho a') Xa') Bbr (upF (k - j) k EB (FB (ers rho a') Xa'))
             (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
             (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
             (gBr (ers rho a') Xa') Htp);
      [ exact (upF_ceq (k - j) k EB (FB (ers rho a) Xa) (FB (ers rho a') Xa') QB)
      | intros u x u' x' _; exact (famAtSelf WF) ]. }
  pose (xg2 := kto
                 (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                         wB FB redB cohB gW Bbr redBbr gBr (ers rho a) Xa))
                 (kAt (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                         wB FB redB cohB gW Bbr redBbr gBr (ers rho a') Xa'))
                 (famAtWf (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                             wB FB redB cohB gW Bbr redBbr gBr (ers rho a) Xa))
                 (famAtWf (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                             wB FB redB cohB gW Bbr redBbr gBr (ers rho a') Xa'))
                 Qpi (ers rho f') xg').
  pose proof (i_conv rho f' k _
                (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho a) Xa) _
                (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho a') Xa') _ xg' Qpi Dg')
    as Dg2.
  pose proof (kRel_trans _ _ _ _ _ _ _ _ _ Hgg
                (kRel_kto
                   (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                      redB cohB gW Bbr redBbr gBr (ers rho a) Xa)
                   (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                      redB cohB gW Bbr redBbr gBr (ers rho a') Xa')
                   Qpi _ xg')) as Hgg2.
  (* the two nodes are layer-1 related, which the conversion itself gives *)
  assert (gr : Rel (ers rho (wt k A B)) (ers rho (sup k A B a f))
                 (ers rho (sup k A B a' f')))
    by exact (LCv_of_cv G (sup k A B a f) (sup k A B a' f') (wt k A B)
                (c_sup G k i j A B a a' f f' Hik Hjk dAt dBt da da' ca df df' cf)
                rho rho HEself).
  assert (gd : Good (ew (ers rho A) B0) (esup (ers rho a) (ers rho f)))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  assert (gd' : Good (ew (ers rho A) B0) (esup (ers rho a') (ers rho f')))
    by (eapply Rel_trans; [apply Rel_sym; exact gr | exact gr]).
  exists (ew (ers rho A) B0), WF,
    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
       (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW
       (ers rho a) (ers rho f) Xa
       (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          Bbr redBbr gBr (ers rho a) Xa (ers rho f) xg)
       (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          Bbr redBbr gBr (ers rho a) Xa (ers rho f) xg)
       gd),
    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
       (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW
       (ers rho a') (ers rho f') Xa'
       (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          Bbr redBbr gBr (ers rho a') Xa' (ers rho f') xg2)
       (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          Bbr redBbr gBr (ers rho a') Xa' (ers rho f') xg2)
       gd').
  split; [split; [split |] |].
  - exact DW.
  - exact (i_sup rho A B a f k i j (k - i) (k - j) EA EB (ers rho A) FA B0
             wB FB redB cohB gW Bbr redBbr gBr (ers rho a) xa (ers rho f) xg
             gd eq_refl DFA DB Da Dg).
  - exact (i_sup rho A B a' f' k i j (k - i) (k - j) EA EB (ers rho A) FA B0
             wB FB redB cohB gW Bbr redBbr gBr (ers rho a') xa' (ers rho f')
             xg2 gd' eq_refl DFA DB Da' Dg2).
  - apply (wSup_congX k (ers rho A) B0 (upF (k - i) k EA FA) wB
             (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW
             (ers rho A) B0 (upF (k - i) k EA FA) wB
             (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW
             (famAtSelf WF) (famAtSelf (upF (k - i) k EA FA)) cohB);
      [ exact A3u | | exact gr ].
    intros v0 y0 v0' y0' Hy.
    exact (kRel_at
             (piApp_eqX k (wB (ers rho a) Xa) Bbr
                (upF (k - j) k EB (FB (ers rho a) Xa))
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho a) Xa)
                (wB (ers rho a') Xa') Bbr
                (upF (k - j) k EB (FB (ers rho a') Xa'))
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho a') Xa')
                (upF_ceq (k - j) k EB (FB (ers rho a) Xa)
                   (FB (ers rho a') Xa') QB)
                (fun v y v' y' _ => famAtSelf WF)
                _ xg _ xg2 v0 y0 v0' y0' (kRel_at Hgg2) Hy)).
Qed.

Lemma isem_sup G k i j A B a a' f f' (Hik : i <= k) (Hjk : j <= k)
  (W : Rules.wfc G)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (da : ty G a A) (da' : ty G a' A) (ca : cv G a a' A)
  (df : ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (df' : ty G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (cf : cv G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHa : ITot G a A) (IHa' : ITot G a' A) (IHca : IRel G a a' A)
  (IHf : ITot G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHf' : ITot G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  (IHcf : IRel G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩))) :
  ISem G (sup k A B a f) (sup k A B a' f') (wt k A B).
Proof.
  pose proof (t_w G k i j A B Hik Hjk dAt dBt) as dW.
  (* the branching function's own type is well formed, which is what the
     induction hypothesis for the conversion f = f' is read at *)
  assert (fPi : FunTm G (pi k (B [a..]) ((wt k A B) ⟨↑⟩))).
  { destruct (ty_subst1 G A B (UU j) a dBt da) as [dBa].
    destruct (ty_ren G (wt k A B) (UU k) dW ((B [a..]) :: G) ↑
                (ren_ok_shift G (B [a..]))
                (inhabits (w_cons G (B [a..]) j W dBa))) as [dWs].
    exact (FunTm_of_ty G (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) k
             (t_pi G k j k (B [a..]) ((wt k A B) ⟨↑⟩) Hjk (le_n k) dBa dWs)). }
  assert (fL : FunTm G (sup k A B a f))
    by exact (funtm G (sup k A B a f) (wt k A B)
                (t_sup G k i j A B a f Hik Hjk dAt dBt da df)).
  assert (fR : FunTm G (sup k A B a' f'))
    by exact (funtm_sup G k A B a' f' (LTy_of_ty G A i dAt)
                (funtm G A (UU i) dAt) (LTy_of_ty (A :: G) B j dBt)
                (funtm (A :: G) B (UU j) dBt) (LTy_of_ty G (wt k A B) k dW)
                (LTm_of_ty G a' A da') (funtm G a' A da')
                (funtm G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) df')).
  split;
    [split; [exact (itot_sup G A B a f k i j Hik Hjk dAt dBt da df
                      IHA IHB IHa IHf)
            | exact (itot_sup' G A B a a' f f' k i j Hik Hjk dAt dBt da da' ca
                       df df' cf IHA IHB IHa IHa' IHca IHf')] |].
  intros rho Hrho kr F DW x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
  pose proof (LCv_of_cv G (sup k A B a f) (sup k A B a' f') (wt k A B)
                (c_sup G k i j A B a a' f f' Hik Hjk dAt dBt da da' ca df df' cf)
                rho rho HEself) as gr.
  destruct (sup_data G A B a a' f f' k i j Hik Hjk dAt dBt da da' ca df df' cf
              fPi IHA IHB IHa IHa' IHca IHf IHf' IHcf rho Hrho)
    as [S1 [F1 [v1 [v2 [[[DT Dv1] Dv2] Hmid]]]]].
  assert (ES1 : S1 = ers rho (wt k A B))
    by exact (ers_of_ITy _ _ _ _ _ DT).
  subst S1.
  pose proof (ity_lvl rho rho eq_refl (wt k A B) k _ F1 kr _ F DT DW) as Ek;
    subst kr.
  pose proof (ity_same_ceq G (wt k A B) (funtm G (wt k A B) (UU k) dW) rho Hrho
                k F F1 DW DT) as P.
  pose proof (fL rho rho HEself k _ F _ x Dx _ F1 _ v1 Dv1 P
                (LTm_of_ty G (sup k A B a f) (wt k A B)
                   (t_sup G k i j A B a f Hik Hjk dAt dBt da df)
                   rho rho HEself)) as H1.
  pose proof (fR rho rho HEself k _ F1 _ v2 Dv2 _ F _ y Dy (knsymU _ _ P)
                (Rel_trans _ _ _ _ (Rel_sym _ _ _ gr) gr)) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans;
    [ exact (proj1 (kRel_same F1 _ _ _ _) Hmid) | exact H2 ].
Qed.

(* ================================================================== *)
(* W: the recursion's congruence.                                      *)
(*                                                                    *)
(* One construction does the work: `wrec_data` builds BOTH recursors    *)
(* at one environment -- the unprimed one from its own motive and step,  *)
(* the primed one from the primed motive with the primed step read where  *)
(* the rule types it (the UNPRIMED context, at the unprimed motive) and   *)
(* then moved along the motives' equality -- and compares them with        *)
(* `wRecS_relX`.  The decoder is no use here for the same reason as at     *)
(* `sup`: the step's two Pi-typed context entries are not ITy-recognised   *)
(* in a decoded reading, so the conversion's induction hypothesis cannot   *)
(* be read there.                                                         *)
(* ================================================================== *)

Lemma wrec_data G A B C C' s s' w0 w0' k i j m nn
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= nn) (Hmn : m <= nn)
  (En : nn = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m)) (dCt' : ty (wt k A B :: G) C' (UU m))
  (cC : cv (wt k A B :: G) C C' (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih nn k A B C) (UU nn))
  (ds : ty (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (ds' : ty (wih nn k A B C :: wbr k A B :: A :: G) s' (wsup_ty k A B C))
  (cs : cv (wih nn k A B C :: wbr k A B :: A :: G) s s' (wsup_ty k A B C))
  (dw : ty G w0 (wt k A B)) (dw' : ty G w0' (wt k A B))
  (cw : cv G w0 w0' (wt k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHC : ITot (wt k A B :: G) C (UU m)) (IHC' : ITot (wt k A B :: G) C' (UU m))
  (IHcC : IRel (wt k A B :: G) C C' (UU m))
  (IHs : ITot (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (IHs' : ITot (wih nn k A B C :: wbr k A B :: A :: G) s' (wsup_ty k A B C))
  (IHcs : IRel (wih nn k A B C :: wbr k A B :: A :: G) s s' (wsup_ty k A B C))
  (IHw : ITot G w0 (wt k A B)) (IHw' : ITot G w0' (wt k A B))
  (IHcw : IRel G w0 w0' (wt k A B))
  rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam m S1 &
  { v1 : kElAt F1 (ers rho (wrec A B C s w0)) &
  { v2 : kElAt F1 (ers rho (wrec A B C' s' w0')) &
    (ITy rho (C [w0..]) m S1 F1 *
     ITm rho (wrec A B C s w0) m S1 F1 (ers rho (wrec A B C s w0)) v1 *
     ITm rho (wrec A B C' s' w0') m S1 F1 (ers rho (wrec A B C' s' w0')) v2 *
     kEqAt F1 (ers rho (wrec A B C s w0)) v1
           F1 (ers rho (wrec A B C' s' w0')) v2)%type
  } } } }.
Proof.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* ---- the motive ---- *)
  pose (SC := fun w1 : etm => subst_etm (scons w1 (rsub rho)) (er C)).
  assert (HEw : forall w1 (x : kElAt WF w1),
             EnvITy (wt k A B :: G) (ext rho WF w1 x)).
  { intros w1 x.
    exact (EnvITy_ext_ceq G rho (wt k A B) k (ers rho (wt k A B)) WF WF DW
             (famAtSelf WF) w1 x Hrho). }
  pose (FC := fun w1 (x : kElAt WF w1) =>
                projT1 (ityT_of_ITot (wt k A B :: G) C m IHC
                          (ext rho WF w1 x) (HEw w1 x))).
  assert (DC : forall w1 x, ITy (ext rho WF w1 x) C m (SC w1) (FC w1 x))
    by (intros w1 x;
        exact (projT2 (ityT_of_ITot (wt k A B :: G) C m IHC
                         (ext rho WF w1 x) (HEw w1 x)))).
  assert (cohC : forall w1 x w1' x', kEqAt WF w1 x WF w1' x' ->
             kceq (kAt (FC w1 x)) (kAt (FC w1' x'))).
  { intros w1 x w1' x' Hx.
    assert (HExx : EnvRelOf (wt k A B :: G) (ext rho WF w1 x) (ext rho WF w1' x'))
      by exact (EnvRelOf_ext' G rho rho (wt k A B) k _ _ WF WF w1 x w1' x'
                  (EnvRelOf_selfE G rho Hrho) eq_refl eq_refl
                  (conj (famAtSelf WF) Hx)).
    exact (FunTy_of_FunTm (wt k A B :: G) C
             (funtm (wt k A B :: G) C (UU m) dCt) _ _ HExx m _ (FC w1 x) _
             (FC w1' x') (DC w1 x) (DC w1' x')
             (LTyK_of_ty (wt k A B :: G) C m dCt _ _ HExx)). }
  (* ---- the layer-1 side, for the guarded goodness premises ---- *)
  pose proof (proj2 (proj2 (proj2 (EnvRelOf_selfE G rho Hrho)))) as HS.
  assert (HBg : forall u u', Rel (subst_etm (rsub rho) (er A)) u u' ->
                  eqty j (subst_etm (scons u (rsub rho)) (er B))
                          (subst_etm (scons u' (rsub rho)) (er B)))
    by (intros u u' Hu;
        exact (fundamental_U (A :: G) B j dBt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hu))).
  assert (HCg : forall x1 y1, Rel (ers rho (wt k A B)) x1 y1 ->
                  eqty m (SC x1) (SC y1))
    by (intros x1 y1 Hxy;
        exact (fundamental_U (wt k A B :: G) C m dCt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hxy))).
  pose proof (sem_wrec k m A B C (rsub rho) _ _ (gt_of k _ gW) HCg
                (sem_wrec_step G k j m nn A B C s s (rsub rho) (rsub rho)
                   Hjk Hjn Hmn HS HBg gW HCg
                   (fundamental_ty _ s (wsup_ty k A B C) ds))) as Hrec0.
  (* the branches of a node are trees, which is what the two guarded
     premises are about *)
  assert (Hbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f v')).
  { intros u0 z f gd v v' Hv.
    apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
             (kFam_good_ty WF) (ev_w _ _) _ _ gd u0 f u0 f
             (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
  (* ---- the induction hypothesis's type ---- *)
  assert (EBn : (nn - j) + j = nn) by lia.
  assert (EC : (nn - m) + m = nn) by lia.
  pose (Cih := C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                     (var_tm 1) (var_tm 0) .:s sh3 ]).
  pose (Bih := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) (f : etm) =>
                 subst_etm (scons f (scons u0 (rsub rho))) (elam (er Cih))).
  assert (Bih_red : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f v,
             reds (eapp (Bih u0 z f) v) (SC (eapp f v))).
  { intros u0 z f v; unfold SC.
    rewrite <- (er_wih_cod k A B C (rsub rho) u0 f v).
    exact (reds_lam_app (er Cih) (scons f (scons u0 (rsub rho))) v). }
  assert (gIh : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             eqty nn (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0 z) (Bih u0 z f))).
  { intros u0 z f gd.
    apply (eqty_dfun nn (wB u0 z) _ (fun v => SC (eapp f v)));
      [ exact (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
      | exact (Bih_red u0 z f)
      | intros v v' Hv;
        exact (eqty_cumul m nn _ _ Hmn
                 (HCg _ _ (Hbr u0 z f gd v v' Hv))) ]. }
  assert (gf : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) Bbr) f).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) Bbr);
      [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (redBbr v) |].
    exact (Hbr u0 z f gd v v' Hv). }
  assert (gih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) (Bih u0 z f))
                  (ihR (ers rho (stepWrap3 s)) f)).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
      [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
    eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
    exact (Hrec0 _ _ (Hbr u0 z f gd v v' Hv)). }
  (* ---- the step's first context type, interpreted: it IS the clause's
       own branching-function family ---- *)
  assert (Dbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             ITy (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B) k
                 (epi (wB u0 z) Bbr)
                 (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW Bbr redBbr gBr u0 z)).
  { intros u0 z; unfold brFam.
    apply (ity_pi (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) B
             ((wt k A B) ⟨↑⟩ ⟨↑⟩) k j k (k - j) 0 EB eq_refl
             (wB u0 z) (FB u0 z) Bbr (fun v _ => ew (ers rho A) B0)
             (fun v _ => WF) (fun v _ => redBbr v)
             (fun v y v' y' _ => famAtSelf WF) (gBr u0 z));
      [ exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))
      | exact (DB u0 z)
      | intros v y;
        exact (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                 (weaken1_ITy rho (wt k A B) k _ WF _ DW)) ]. }
  (* abbreviations for the two Pi-typed entries *)
  pose (BRF := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z).
  pose (BRE := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext =>
                 brEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z f sub subext
                   (gf u0 z f gd)).
  (* ---- the motive at a SUBTREE, which is the codomain of the induction
       hypothesis's type: the subtree is the branching function applied to the
       branch, read by i_app in the four-entry environment ---- *)
  assert (Dsub : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext v
                   (y : kElAt (upF (nn - j) nn EBn (FB u0 z)) v),
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                 (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                        (var_tm 1) (var_tm 0) .:s sh3 ])
                 m (SC (eapp f v))
                 (FC (eapp f v)
                    (sub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                              wB FB nn (nn - j) EBn u0 z v y)))).
  { intros u0 z f gd sub subext v y.
    pose (Xa := ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                  nn (nn - j) EBn u0 z v y).
    (* the application *)
    pose proof (i_app
                  (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                     (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                  (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                  (var_tm 1) (var_tm 0) k j k (k - j) 0 EB eq_refl
                  (wB u0 z) (FB u0 z) Bbr (fun v' _ => ew (ers rho A) B0)
                  (fun v' _ => WF) (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext)
                  v (dnEl (nn - j) nn EBn (FB u0 z) v y)
                  (eq_sym (ers_wbr_app_ty rho A B k _ _ _))
                  (weaken1_ITy _ (B ⟨↑⟩) j _ (FB u0 z) _
                     (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z)))
                  (fun u x =>
                     weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) k _ WF _
                       (weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩) k _ WF _
                          (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                             (weaken1_ITy rho (wt k A B) k _ WF _ DW))))
                  (i_varS _ _ 0 k _ (BRF u0 z) f (BRE u0 z f gd sub subext)
                     (i_var0 _ k _ (BRF u0 z) f (BRE u0 z f gd sub subext)))
                  (i_var0 _ j _ (FB u0 z) v
                     (dnEl (nn - j) nn EBn (FB u0 z) v y))) as Dapp.
    (* the value the application names, and the motive's index at it *)
    pose (Xv := piApp k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext) v Xa).
    assert (Hidx : kEqAt WF (eapp f v) Xv WF (eapp f v) (sub v Xa))
      by exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (fun v' _ => eapp f v') sub
                  (fun v' y' => reds_refl (eapp f v')) subext (gf u0 z f gd)
                  v Xa).
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry j (wB u0 z) (FB u0 z) v
                  (dnEl (nn - j) nn EBn (FB u0 z) v y)).
    pose (em := Build_Entry k (ew (ers rho A) B0) WF (eapp f v) Xv).
    rewrite wsub3_as, <- ren3_as.
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                 (var_tm 1) (var_tm 0))
              k (ew (ers rho A) B0) WF (eapp f v) Xv eq_refl Dapp
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (eapp f v)) _ _).
    refine (ity_conv _ _ _ _ (FC (eapp f v) Xv) (FC (eapp f v) (sub v Xa))
              (cohC (eapp f v) Xv (eapp f v) (sub v Xa) Hidx) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e1 :: rho) e2 eq_refl).
    exact (weaken_ITy _ C m _ _ (DC (eapp f v) Xv)
             (em :: nil) rho e1 eq_refl). }
  assert (Epi2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             epi (wB u0 z) (Bih u0 z f)
             = ers (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                      (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C)).
  { intros u0 z f gd sub subext.
    unfold wB, Bih, ers, wih; cbn [rsub ext].
    rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity. }
  (* ---- the step's second context type, interpreted: it IS the clause's
       own induction-hypothesis family ---- *)
  assert (Dih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             ITy (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C) nn
                 (epi (wB u0 z) (Bih u0 z f))
                 (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                    Bih gIh Bih_red u0 z f gd sub subext)).
  { intros u0 z f gd sub subext.
    unfold ihFam, wih.
    apply (ity_pi _ (B ⟨↑⟩)
             (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                    (var_tm 1) (var_tm 0) .:s sh3 ])
             nn j m (nn - j) (nn - m) EBn EC
             (wB u0 z) (FB u0 z) (Bih u0 z f) _ _ _ _ _);
      [ exact (Epi2 u0 z f gd sub subext)
      | exact (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z))
      | exact (Dsub u0 z f gd sub subext) ]. }
  (* ---- and hence the step's environment carries an interpretation of every
       one of its context types ---- *)
  assert (Ebr2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             epi (wB u0 z) Bbr
             = ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B))
    by (intros u0 z; exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))).
  assert (HE3 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                  ih ihext,
             EnvITy (wih nn k A B C :: wbr k A B :: A :: G)
               (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd)))).
  { intros u0 z f gd sub subext ih ihext.
    refine (EnvITy_ext_ceq (wbr k A B :: A :: G) _ (wih nn k A B C) nn _ _
              (famCast (Epi2 u0 z f gd sub subext) _) _ _ _ _ _).
    - exact (ITy_cast _ (wih nn k A B C) nn _ _
               (Epi2 u0 z f gd sub subext) _ (Dih u0 z f gd sub subext)).
    - apply famCast_ceq.
    - refine (EnvITy_ext_ceq (A :: G) _ (wbr k A B) k _ _
                (famCast (Ebr2 u0 z) _) _ _ _ _ _).
      + exact (ITy_cast _ (wbr k A B) k _ _ (Ebr2 u0 z) _ (Dbr u0 z)).
      + apply famCast_ceq.
      + exact (EnvITy_ext G rho A i FA DFA u0
                 (dnEl (k - i) k EA FA u0 z) Hrho). }
  (* ---- the motive at the TREE the step builds ---- *)
  assert (Dwsup : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                    ih ihext,
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR (ers rho (stepWrap3 s)) f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                       subext ih ihext (gih u0 z f gd)))
                 (wsup_ty k A B C) m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))).
  { intros u0 z f gd sub subext ih ihext.
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry nn (epi (wB u0 z) (Bih u0 z f))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd))).
    (* the tree, read in the step's own environment *)
    pose (Z' := upEl (k - i) k EA FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (HzZ : kEqAt (upF (k - i) k EA FA) u0 z (upF (k - i) k EA FA) u0 Z')
      by (apply kEqAt_sym; apply upEl_dnEl).
    assert (Hbrceq : kceq (kAt (BRF u0 z)) (kAt (BRF u0 Z'))).
    { unfold BRF, brFam; apply piFam_ceq.
      - exists k; apply eqty_pi.
        + exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                   (uf_ty (upF (k - j) k EB (FB u0 Z')))
                   (ceq_ty (upF (k - j) k EB (FB u0 z))
                      (upF (k - j) k EB (FB u0 Z')) (cohB u0 z u0 Z' HzZ))).
        + intros v v' _.
          eapply eqty_exp; [ apply redBbr | apply redBbr |].
          exact gW.
      - exact (cohB u0 z u0 Z' HzZ).
      - intros v y v' y' _; exact (famAtSelf WF). }
    pose (ea := Build_Entry i (ers rho A) FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (DA3 : ITy (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) i (ers rho A) FA).
    { rewrite <- sh3_as.
      exact (weaken1_ITy _ ((A ⟨↑⟩) ⟨↑⟩) i _ FA _
               (weaken1_ITy _ (A ⟨↑⟩) i _ FA _
                  (weaken1_ITy rho A i _ FA _ DFA))). }
    assert (DB3 : forall u x,
               ITy (ext (e3 :: e2 :: e1 :: rho) FA u
                      (dnEl (k - i) k EA FA u x))
                   (B ⟨up_ren sh3⟩) j (wB u x) (FB u x)).
    { intros u x; rewrite <- ren3_as.
      refine (weaken_ITy _ ((B ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e2 :: e1 :: rho) e3 eq_refl).
      refine (weaken_ITy _ (B ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e1 :: rho) e2 eq_refl).
      exact (weaken_ITy _ B j _ _ (DB u x)
               (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
               rho e1 eq_refl). }
    pose proof (i_sup (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)
                  (var_tm 2) (var_tm 1) k i j (k - i) (k - j) EA EB
                  (ers rho A) FA B0 wB FB redB cohB gW Bbr redBbr gBr
                  u0 (dnEl (k - i) k EA FA u0 z) f
                  (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z')) (famAtWf (BRF u0 z))
                     (famAtWf (BRF u0 Z')) Hbrceq f
                     (BRE u0 z f gd sub subext))
                  gd (eq_sym (ers_wt_sh3 rho A B k e1 e2 e3))
                  DA3 DB3
                  (i_varS _ e3 1 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                     (i_varS _ e2 0 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                        (i_var0 rho i _ FA u0 (dnEl (k - i) k EA FA u0 z))))
                  (i_conv _ (var_tm 1) k (epi (wB u0 z) Bbr) (BRF u0 z) _
                     (BRF u0 Z') f (BRE u0 z f gd sub subext) Hbrceq
                     (i_varS _ e3 0 k _ (BRF u0 z) f
                        (BRE u0 z f gd sub subext)
                        (i_var0 (e1 :: rho) k _ (BRF u0 z) f
                           (BRE u0 z f gd sub subext))))) as Dsup3.
    (* i_sup's value is the clause's own tree: its label is the round trip of
       the entry's, and its branches are the branching function's semantic
       value applied -- which is what it was built from *)
    assert (Hsups : kEqAt WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f Z'
                         (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         gd)
                      WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd)).
    { apply (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW);
        [ apply upEl_dnEl | intros v0 y v0' y' Hy | exact gd ].
      eapply kEqAt_trans; [ exact (famAtSelf WF) |
        exact (kRel_at
                 (piApp_eqX k (wB u0 Z') Bbr (upF (k - j) k EB (FB u0 Z'))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 Z')
                    (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 z)
                    (cohB u0 Z' u0 z (upEl_dnEl (k - i) k EA FA u0 z))
                    (fun v y1 v' y1' _ => famAtSelf WF)
                    f (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                         (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                         (BRE u0 z f gd sub subext))
                    f (BRE u0 z f gd sub subext) v0 y v0' y'
                    (kEqAt_sym (BRF u0 z) f (BRE u0 z f gd sub subext) _ _ _
                       (kto_coh (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                          (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                          (BRE u0 z f gd sub subext)))
                    Hy)) |].
      exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
               (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
               (fun v _ => redBbr v) (fun v y1 v' y1' _ => famAtSelf WF)
               (gBr u0 z) f (fun v _ => eapp f v) sub
               (fun v y1 => reds_refl (eapp f v)) subext (gf u0 z f gd)
               v0' y'). }
    (* and then the motive, substituted and weakened as at the subtree *)
    unfold wsup_ty; rewrite wsub3_as, <- (ren3_as C).
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1))
              k (ew (ers rho A) B0) WF (esup u0 f) _ eq_refl Dsup3
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (esup u0 f)) _ _).
    refine (ity_conv _ _ _ _ _ _
              (cohC (esup u0 f) _ (esup u0 f) _ Hsups) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e1 :: rho) e2 eq_refl).
    refine (weaken_ITy _ C m _ _ _ (_ :: nil) rho e1 eq_refl).
    exact (DC (esup u0 f) _). }
  (* ---- the step's realiser and value ---- *)
  assert (Hstep : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                    ih ihext,
             { xs : kElAt (FC (esup u0 f)
                             (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                (fun u x => upF (k - j) k EB (FB u x)) redB
                                cohB gW u0 f z sub subext gd))
                      (ers (ext (ext (ext rho FA u0
                                        (dnEl (k - i) k EA FA u0 z))
                                   (BRF u0 z) f (BRE u0 z f gd sub subext))
                              (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red u0 z f gd sub
                                 subext)
                              (ihR (ers rho (stepWrap3 s)) f)
                              (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red
                                 (ers rho (stepWrap3 s)) u0 z f gd sub subext
                                 ih ihext (gih u0 z f gd))) s) &
               ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                      (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red u0 z f gd sub subext)
                      (ihR (ers rho (stepWrap3 s)) f)
                      (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                         subext ih ihext (gih u0 z f gd)))
                   s m (SC (esup u0 f))
                   (FC (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd))
                   (ers _ s) xs }).
  { intros u0 z f sub subext gd ih ihext.
    assert (Es : SC (esup u0 f)
                 = ers (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                              (BRF u0 z) f (BRE u0 z f gd sub subext))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                         (ihR (ers rho (stepWrap3 s)) f)
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red (ers rho (stepWrap3 s))
                            u0 z f gd sub subext ih ihext (gih u0 z f gd)))
                     (wsup_ty k A B C))
      by exact (eq_sym (er_wsup_ty k A B C (rsub rho) u0 f
                          (ihR (ers rho (stepWrap3 s)) f))).
    destruct (IHs _ (HE3 u0 z f gd sub subext ih ihext) m (famCast Es _)
                (ITy_cast _ (wsup_ty k A B C) m _ _ Es _
                   (Dwsup u0 z f gd sub subext ih ihext))) as [xs' Ds'].
    destruct (ITm_uncast _ s m _ _ Es _ _ _ Ds') as [xs Ds].
    exists xs; exact Ds. }
  pose (Sr := ers rho (stepWrap3 s)).
  pose (ws := (fun u0 z f sub subext gd ih ihext =>
                 subst_etm (scons (ihR Sr f) (scons f (scons u0 (rsub rho))))
                   (er s))
              : WsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr).
  pose (xs := (fun u0 z f sub subext gd ih ihext =>
                 projT1 (Hstep u0 z f sub subext gd ih ihext))
              : XsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr ws).
  pose (redS := (fun u0 z f sub subext gd ih ihext =>
                   reds_lam3_app (er s) (rsub rho) u0 f (ihR Sr f))
                : RedSTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC Sr ws).
  assert (Ds : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                 ih ihext,
             ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR Sr f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                       (gih u0 z f gd)))
                 s m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))
                 (ws u0 z f sub subext gd ih ihext)
                 (xs u0 z f sub subext gd ih ihext))
    by (intros u0 z f sub subext gd ih ihext;
        exact (projT2 (Hstep u0 z f sub subext gd ih ihext))).
  (* ---- the step's congruence, within this one reading ---- *)
  assert (stepSrel : StepRelTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                       wB FB redB cohB gW m SC FC Sr ws xs redS).
  { intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
           Hz Hsub HRsup Hih.
    (* the branching type at the two labels, at its own level *)
    assert (QB : kceq (kAt (FB u0 z)) (kAt (FB u0' z')))
      by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                  (funtm (A :: G) B (UU j) dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA (ers rho A) FA
                  wB FB (ers rho A) FA wB FB DFA DFA (famAtSelf FA) DB DB
                  u0 z u0' z' Hz).
    assert (Htb : tyeq (wB u0 z) (wB u0' z'))
      by exact (ceq_ty (FB u0 z) (FB u0' z') QB).
    (* the two branching Pi types, and the two branching functions *)
    assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB u0' z') Bbr)).
    { exists k; apply eqty_pi.
      - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                 (uf_ty (upF (k - j) k EB (FB u0' z'))) Htb).
      - intros v v' _.
        eapply eqty_exp; [ apply redBbr | apply redBbr |]; exact gW. }
    assert (Hbr2 : forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f' v')).
    { intros v v' Hv.
      apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
               (kFam_good_ty WF) (ev_w _ _) _ _ HRsup u0 f u0' f'
               (ev_sup _ _) (ev_sup _ _)).
      eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
    assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
    { apply (Rel_pi_intro _ (wB u0 z) Bbr);
        [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (redBbr v) |].
      exact (Hbr2 v v' Hv). }
    assert (HRih : Rel (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f) (ihR Sr f')).
    { apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
        [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
      eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
      exact (Hrec0 _ _ (Hbr2 v v' Hv)). }
    (* the two IH types *)
    assert (Htih : tyeq (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0' z') (Bih u0' z' f'))).
    { exists nn; apply eqty_pi.
      - exact (eqty_at_lvl nn _ _ (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
                 (uf_ty (upF (nn - j) nn EBn (FB u0' z'))) Htb).
      - intros v v' Hv.
        eapply eqty_exp;
          [ exact (Bih_red u0 z f v) | exact (Bih_red u0' z' f' v') |].
        exact (eqty_cumul m nn _ _ Hmn (HCg _ _ (Hbr2 v v' Hv))). }
    (* the three entries of the step's context, related *)
    assert (HE1 : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' z')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (kRel_dn (k - i) k EA FA FA (famAtSelf FA) _ _ _ _
                     (conj (famAtSelf (upF (k - i) k EA FA)) Hz))).
    assert (T2 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1),
               tyeq (epi (wB u1 z1) Bbr)
                 (ers (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1)) (wbr k A B)))
      by (intros u1 z1; rewrite <- (Ebr2 u1 z1); exists k; exact (gBr u1 z1)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G)
                    (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                       (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 (T2 u0 z) (T2 u0' z')).
      split.
      - unfold BRF, brFam; apply piFam_ceq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF) ].
      - unfold BRE, brEl, BRF, brFam; apply piLam_eq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF)
          | exact HRf | exact Hsub ]. }
    assert (T3 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1) f1 gd1 sub1
                   subext1,
               tyeq (epi (wB u1 z1) (Bih u1 z1 f1))
                 (ers (ext (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1))
                         (BRF u1 z1) f1 (BRE u1 z1 f1 gd1 sub1 subext1))
                    (wih nn k A B C)))
      by (intros u1 z1 f1 gd1 sub1 subext1;
          rewrite <- (Epi2 u1 z1 f1 gd1 sub1 subext1);
          exists nn; exact (gIh u1 z1 f1 gd1)).
    assert (HE3r : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                     (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                             (BRF u0 z) f (BRE u0 z f gd sub subext))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                        (ihR Sr f)
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih
                           ihext (gih u0 z f gd)))
                     (ext (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                             (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0' z' f' gd' sub' subext')
                        (ihR Sr f')
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0' z' f' gd' sub' subext'
                           ih' ihext' (gih u0' z' f' gd')))).
    { apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
               _ _ _ _ _ _ _ _ HE2 (T3 u0 z f gd sub subext)
               (T3 u0' z' f' gd' sub' subext')).
      split.
      - unfold ihFam; apply piFam_ceq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy)) ].
      - unfold ihEl, ihFam; apply piLam_eq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy))
          | exact HRih
          | intros v y v' y' Hy;
            exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                     (kRel_ceq (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)
                                  v' (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0' z' v' y')
                                  (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                     (nn - j) nn EBn v y v' y' QB Hy)))
                     (kRel_at (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0 z v y)
                                 v' (ihIdx k i j (k - i) (k - j) EA EB
                                       (ers rho A) FA wB FB nn (nn - j) EBn
                                       u0' z' v' y')
                                 (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                    (nn - j) nn EBn v y v' y' QB Hy)))) ]. }
    (* the two motives at the two trees, and the step's own realisers *)
    assert (Hmot : kceq (kAt (FC (esup u0 f)
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0 f z sub subext gd)))
                        (kAt (FC (esup u0' f')
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0' f' z' sub' subext' gd'))))
      by exact (cohC _ _ _ _
                  (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
                     (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                     u0 z f sub subext gd u0' z' f' sub' subext' gd'
                     Hz Hsub HRsup)).
    assert (Hrs : Rel (SC (esup u0' f')) (ws u0 z f sub subext gd ih ihext)
                    (ws u0' z' f' sub' subext' gd' ih' ihext')).
    { apply (Rel_tyeq (SC (esup u0 f)) (SC (esup u0' f')));
        [ exists m;
          exact (ceq_eqty (FC (esup u0 f) _) (FC (esup u0' f') _) Hmot) |].
      unfold ws, SC.
      rewrite <- (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr f)).
      exact (fundamental_ty _ s (wsup_ty k A B C) ds _ _
               (proj2 (proj2 (proj2 HE3r)))). }
    pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s
                  (wsup_ty k A B C) ds _ _ HE3r m _ _ _
                  (xs u0 z f sub subext gd ih ihext)
                  (Ds u0 z f sub subext gd ih ihext) _ _ _
                  (xs u0' z' f' sub' subext' gd' ih' ihext')
                  (Ds u0' z' f' sub' subext' gd' ih' ihext')
                  Hmot Hrs) as Hxs.
    (* and the two expansions come off *)
    unfold stepOf.
    eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
    eapply kRel_trans; [ exact Hxs |].
    split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ]. }
  (* ---- the primed motive ---- *)
  pose (SC2 := fun w1 : etm => subst_etm (scons w1 (rsub rho)) (er C')).
  pose (FC2 := fun w1 (x : kElAt WF w1) =>
                projT1 (ityT_of_ITot (wt k A B :: G) C' m IHC'
                          (ext rho WF w1 x) (HEw w1 x))).
  assert (DC2 : forall w1 x, ITy (ext rho WF w1 x) C' m (SC2 w1) (FC2 w1 x))
    by (intros w1 x;
        exact (projT2 (ityT_of_ITot (wt k A B :: G) C' m IHC'
                         (ext rho WF w1 x) (HEw w1 x)))).
  assert (cohC2 : forall w1 x w1' x', kEqAt WF w1 x WF w1' x' ->
             kceq (kAt (FC2 w1 x)) (kAt (FC2 w1' x'))).
  { intros w1 x w1' x' Hx.
    assert (HExx : EnvRelOf (wt k A B :: G) (ext rho WF w1 x) (ext rho WF w1' x'))
      by exact (EnvRelOf_ext' G rho rho (wt k A B) k _ _ WF WF w1 x w1' x'
                  (EnvRelOf_selfE G rho Hrho) eq_refl eq_refl
                  (conj (famAtSelf WF) Hx)).
    exact (FunTy_of_FunTm (wt k A B :: G) C'
             (funtm (wt k A B :: G) C' (UU m) dCt') _ _ HExx m _ (FC2 w1 x) _
             (FC2 w1' x') (DC2 w1 x) (DC2 w1' x')
             (LTyK_of_ty (wt k A B :: G) C' m dCt' _ _ HExx)). }
  (* ---- the primed layer-1 side ---- *)
  assert (HCg2 : forall x1 y1, Rel (ers rho (wt k A B)) x1 y1 ->
                  eqty m (SC2 x1) (SC2 y1))
    by (intros x1 y1 Hxy;
        exact (fundamental_U (wt k A B :: G) C' m dCt' _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hxy))).
  (* the two motives are layer-1 equal at related trees, which is the
     conversion C = C' read at layer 1 -- and it is what carries every
     primed goodness premise over from the UNPRIMED motive, where the
     primed step's own type puts it *)
  assert (HCCg : forall x1 y1, Rel (ers rho (wt k A B)) x1 y1 ->
                   eqty m (SC x1) (SC2 y1))
    by (intros x1 y1 Hxy;
        exact (fundamental_cv_U (wt k A B :: G) C C' m cC _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hxy))).
  pose proof (sem_wrec k m A B C (rsub rho) _ _ (gt_of k _ gW) HCg
                (sem_wrec_step G k j m nn A B C s' s' (rsub rho) (rsub rho)
                   Hjk Hjn Hmn HS HBg gW HCg
                   (fundamental_ty _ s' (wsup_ty k A B C) ds'))) as Hrec0C2.
  assert (Hrec02 : forall x y, Rel (ers rho (wt k A B)) x y ->
                     Rel (SC2 x) (ewrec (ers rho (stepWrap3 s')) x)
                         (ewrec (ers rho (stepWrap3 s')) y)).
  { intros x y Hxy.
    eapply Rel_cast;
      [ exact (HCCg x x (Rel_refl_l _ _ _ Hxy)) | exact (Hrec0C2 x y Hxy) ]. }
  (* the branches of a node are trees, which is what the two guarded
     premises are about *)
  (* ---- the primed induction hypothesis's type ---- *)
  pose (Cih2 := C' [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                     (var_tm 1) (var_tm 0) .:s sh3 ]).
  pose (Bih2 := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) (f : etm) =>
                 subst_etm (scons f (scons u0 (rsub rho))) (elam (er Cih2))).
  assert (Bih_red2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f v,
             reds (eapp (Bih2 u0 z f) v) (SC2 (eapp f v))).
  { intros u0 z f v; unfold SC2.
    rewrite <- (er_wih_cod k A B C' (rsub rho) u0 f v).
    exact (reds_lam_app (er Cih2) (scons f (scons u0 (rsub rho))) v). }
  assert (gIh2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             eqty nn (epi (wB u0 z) (Bih2 u0 z f))
                     (epi (wB u0 z) (Bih2 u0 z f))).
  { intros u0 z f gd.
    apply (eqty_dfun nn (wB u0 z) _ (fun v => SC2 (eapp f v)));
      [ exact (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
      | exact (Bih_red2 u0 z f)
      | intros v v' Hv;
        exact (eqty_cumul m nn _ _ Hmn
                 (HCg2 _ _ (Hbr u0 z f gd v v' Hv))) ]. }
  assert (gih2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) (Bih2 u0 z f))
                  (ihR (ers rho (stepWrap3 s')) f)).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) (Bih2 u0 z f));
      [ exists nn; exact (gIh2 u0 z f gd) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (Bih_red2 u0 z f v) |].
    eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
    exact (Hrec02 _ _ (Hbr u0 z f gd v v' Hv)). }
  (* ---- the primed motive at a subtree, and the primed ih type ---- *)
  assert (Dsub2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext v
                   (y : kElAt (upF (nn - j) nn EBn (FB u0 z)) v),
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                 (C' [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                        (var_tm 1) (var_tm 0) .:s sh3 ])
                 m (SC2 (eapp f v))
                 (FC2 (eapp f v)
                    (sub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                              wB FB nn (nn - j) EBn u0 z v y)))).
  { intros u0 z f gd sub subext v y.
    pose (Xa := ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                  nn (nn - j) EBn u0 z v y).
    (* the application *)
    pose proof (i_app
                  (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                     (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                  (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                  (var_tm 1) (var_tm 0) k j k (k - j) 0 EB eq_refl
                  (wB u0 z) (FB u0 z) Bbr (fun v' _ => ew (ers rho A) B0)
                  (fun v' _ => WF) (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext)
                  v (dnEl (nn - j) nn EBn (FB u0 z) v y)
                  (eq_sym (ers_wbr_app_ty rho A B k _ _ _))
                  (weaken1_ITy _ (B ⟨↑⟩) j _ (FB u0 z) _
                     (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z)))
                  (fun u x =>
                     weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) k _ WF _
                       (weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩) k _ WF _
                          (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                             (weaken1_ITy rho (wt k A B) k _ WF _ DW))))
                  (i_varS _ _ 0 k _ (BRF u0 z) f (BRE u0 z f gd sub subext)
                     (i_var0 _ k _ (BRF u0 z) f (BRE u0 z f gd sub subext)))
                  (i_var0 _ j _ (FB u0 z) v
                     (dnEl (nn - j) nn EBn (FB u0 z) v y))) as Dapp.
    (* the value the application names, and the motive's index at it *)
    pose (Xv := piApp k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext) v Xa).
    assert (Hidx : kEqAt WF (eapp f v) Xv WF (eapp f v) (sub v Xa))
      by exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (fun v' _ => eapp f v') sub
                  (fun v' y' => reds_refl (eapp f v')) subext (gf u0 z f gd)
                  v Xa).
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry j (wB u0 z) (FB u0 z) v
                  (dnEl (nn - j) nn EBn (FB u0 z) v y)).
    pose (em := Build_Entry k (ew (ers rho A) B0) WF (eapp f v) Xv).
    rewrite wsub3_as, <- ren3_as.
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                 (var_tm 1) (var_tm 0))
              k (ew (ers rho A) B0) WF (eapp f v) Xv eq_refl Dapp
              ((C' ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC2 (eapp f v)) _ _).
    refine (ity_conv _ _ _ _ (FC2 (eapp f v) Xv) (FC2 (eapp f v) (sub v Xa))
              (cohC2 (eapp f v) Xv (eapp f v) (sub v Xa) Hidx) _).
    refine (weaken_ITy _ ((C' ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C' ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e1 :: rho) e2 eq_refl).
    exact (weaken_ITy _ C' m _ _ (DC2 (eapp f v) Xv)
             (em :: nil) rho e1 eq_refl). }
  assert (EpiI2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             epi (wB u0 z) (Bih2 u0 z f)
             = ers (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                      (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C')).
  { intros u0 z f gd sub subext.
    unfold wB, Bih2, ers, wih; cbn [rsub ext].
    rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity. }
  assert (Dih2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             ITy (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C') nn
                 (epi (wB u0 z) (Bih2 u0 z f))
                 (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                    Bih2 gIh2 Bih_red2 u0 z f gd sub subext)).
  { intros u0 z f gd sub subext.
    unfold ihFam, wih.
    apply (ity_pi _ (B ⟨↑⟩)
             (C' [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                    (var_tm 1) (var_tm 0) .:s sh3 ])
             nn j m (nn - j) (nn - m) EBn EC
             (wB u0 z) (FB u0 z) (Bih2 u0 z f) _ _ _ _ _);
      [ exact (EpiI2 u0 z f gd sub subext)
      | exact (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z))
      | exact (Dsub2 u0 z f gd sub subext) ]. }
  (* ---- the two motives' instances agree, which is the conversion ---- *)
  assert (PCC : forall w1 (x : kElAt WF w1),
             kceq (kAt (FC w1 x)) (kAt (FC2 w1 x)))
    by (intros w1 x;
        exact (ceq_of_IRel_at' (wt k A B :: G) C C' m IHcC
                 (ext rho WF w1 x) (HEw w1 x) _ (FC w1 x) (DC w1 x)
                 _ (FC2 w1 x) (DC2 w1 x))).
  (* ---- the primed induction hypothesis's family is the unprimed one up to
       the motives' equality, which is how the step's environment is still an
       interpretation of its UNPRIMED context ---- *)
  assert (Qih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             kceq (kAt (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                          redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                          EBn EC Bih2 gIh2 Bih_red2 u0 z f gd sub subext))
                  (kAt (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                          redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                          EBn EC Bih gIh Bih_red u0 z f gd sub subext))).
  { intros u0 z f gd sub subext.
    unfold ihFam; apply piFam_ceq.
    - exists nn; apply eqty_pi;
        [ exact (uf_ty (upF (nn - j) nn EBn (FB u0 z))) | intros v v' Hv ].
      eapply eqty_exp;
        [ exact (Bih_red2 u0 z f v) | exact (Bih_red u0 z f v') |].
      apply (eqty_cumul m nn _ _ Hmn), eqty_sym.
      exact (HCCg (eapp f v') (eapp f v)
               (Hbr u0 z f gd v' v (Rel_sym _ _ _ Hv))).
    - exact (famAtSelf (upF (nn - j) nn EBn (FB u0 z))).
    - intros v y v' y' Hy.
      apply upF_ceq.
      eapply famCeq_tr;
        [ exact (famCeq_sym _ _ (PCC (eapp f v) (sub v (ihIdx k i j (k - i)
                   (k - j) EA EB (ers rho A) FA wB FB nn (nn - j) EBn u0 z v y))))
        |].
      apply cohC.
      exact (subext v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                        nn (nn - j) EBn u0 z v y)
               v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                     nn (nn - j) EBn u0 z v' y')
               (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                  nn (nn - j) EBn u0 z v y v' y' Hy)). }
  assert (HE32 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                   ih ihext,
             EnvITy (wih nn k A B C :: wbr k A B :: A :: G)
               (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                     Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s')) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                     Bih2 gIh2 Bih_red2 (ers rho (stepWrap3 s')) u0 z f gd sub
                     subext ih ihext (gih2 u0 z f gd)))).
  { intros u0 z f gd sub subext ih ihext.
    refine (EnvITy_ext_ceq (wbr k A B :: A :: G) _ (wih nn k A B C) nn _ _
              (famCast (Epi2 u0 z f gd sub subext) _) _ _ _ _ _).
    - exact (ITy_cast _ (wih nn k A B C) nn _ _
               (Epi2 u0 z f gd sub subext) _ (Dih u0 z f gd sub subext)).
    - eapply famCeq_tr;
        [ exact (Qih u0 z f gd sub subext)
        | apply famCast_ceq ].
    - refine (EnvITy_ext_ceq (A :: G) _ (wbr k A B) k _ _
                (famCast (Ebr2 u0 z) _) _ _ _ _ _).
      + exact (ITy_cast _ (wbr k A B) k _ _ (Ebr2 u0 z) _ (Dbr u0 z)).
      + apply famCast_ceq.
      + exact (EnvITy_ext G rho A i FA DFA u0
                 (dnEl (k - i) k EA FA u0 z) Hrho). }
  assert (Dwsup2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                    ih ihext,
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                       Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                    (ihR (ers rho (stepWrap3 s')) f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                       Bih2 gIh2 Bih_red2 (ers rho (stepWrap3 s')) u0 z f gd sub
                       subext ih ihext (gih2 u0 z f gd)))
                 (wsup_ty k A B C) m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))).
  { intros u0 z f gd sub subext ih ihext.
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry nn (epi (wB u0 z) (Bih2 u0 z f))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                     Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s')) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                     Bih2 gIh2 Bih_red2 (ers rho (stepWrap3 s')) u0 z f gd sub
                     subext ih ihext (gih2 u0 z f gd))).
    (* the tree, read in the step's own environment *)
    pose (Z' := upEl (k - i) k EA FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (HzZ : kEqAt (upF (k - i) k EA FA) u0 z (upF (k - i) k EA FA) u0 Z')
      by (apply kEqAt_sym; apply upEl_dnEl).
    assert (Hbrceq : kceq (kAt (BRF u0 z)) (kAt (BRF u0 Z'))).
    { unfold BRF, brFam; apply piFam_ceq.
      - exists k; apply eqty_pi.
        + exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                   (uf_ty (upF (k - j) k EB (FB u0 Z')))
                   (ceq_ty (upF (k - j) k EB (FB u0 z))
                      (upF (k - j) k EB (FB u0 Z')) (cohB u0 z u0 Z' HzZ))).
        + intros v v' _.
          eapply eqty_exp; [ apply redBbr | apply redBbr |].
          exact gW.
      - exact (cohB u0 z u0 Z' HzZ).
      - intros v y v' y' _; exact (famAtSelf WF). }
    pose (ea := Build_Entry i (ers rho A) FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (DA3 : ITy (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) i (ers rho A) FA).
    { rewrite <- sh3_as.
      exact (weaken1_ITy _ ((A ⟨↑⟩) ⟨↑⟩) i _ FA _
               (weaken1_ITy _ (A ⟨↑⟩) i _ FA _
                  (weaken1_ITy rho A i _ FA _ DFA))). }
    assert (DB3 : forall u x,
               ITy (ext (e3 :: e2 :: e1 :: rho) FA u
                      (dnEl (k - i) k EA FA u x))
                   (B ⟨up_ren sh3⟩) j (wB u x) (FB u x)).
    { intros u x; rewrite <- ren3_as.
      refine (weaken_ITy _ ((B ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e2 :: e1 :: rho) e3 eq_refl).
      refine (weaken_ITy _ (B ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e1 :: rho) e2 eq_refl).
      exact (weaken_ITy _ B j _ _ (DB u x)
               (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
               rho e1 eq_refl). }
    pose proof (i_sup (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)
                  (var_tm 2) (var_tm 1) k i j (k - i) (k - j) EA EB
                  (ers rho A) FA B0 wB FB redB cohB gW Bbr redBbr gBr
                  u0 (dnEl (k - i) k EA FA u0 z) f
                  (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z')) (famAtWf (BRF u0 z))
                     (famAtWf (BRF u0 Z')) Hbrceq f
                     (BRE u0 z f gd sub subext))
                  gd (eq_sym (ers_wt_sh3 rho A B k e1 e2 e3))
                  DA3 DB3
                  (i_varS _ e3 1 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                     (i_varS _ e2 0 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                        (i_var0 rho i _ FA u0 (dnEl (k - i) k EA FA u0 z))))
                  (i_conv _ (var_tm 1) k (epi (wB u0 z) Bbr) (BRF u0 z) _
                     (BRF u0 Z') f (BRE u0 z f gd sub subext) Hbrceq
                     (i_varS _ e3 0 k _ (BRF u0 z) f
                        (BRE u0 z f gd sub subext)
                        (i_var0 (e1 :: rho) k _ (BRF u0 z) f
                           (BRE u0 z f gd sub subext))))) as Dsup3.
    (* i_sup's value is the clause's own tree: its label is the round trip of
       the entry's, and its branches are the branching function's semantic
       value applied -- which is what it was built from *)
    assert (Hsups : kEqAt WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f Z'
                         (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         gd)
                      WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd)).
    { apply (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW);
        [ apply upEl_dnEl | intros v0 y v0' y' Hy | exact gd ].
      eapply kEqAt_trans; [ exact (famAtSelf WF) |
        exact (kRel_at
                 (piApp_eqX k (wB u0 Z') Bbr (upF (k - j) k EB (FB u0 Z'))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 Z')
                    (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 z)
                    (cohB u0 Z' u0 z (upEl_dnEl (k - i) k EA FA u0 z))
                    (fun v y1 v' y1' _ => famAtSelf WF)
                    f (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                         (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                         (BRE u0 z f gd sub subext))
                    f (BRE u0 z f gd sub subext) v0 y v0' y'
                    (kEqAt_sym (BRF u0 z) f (BRE u0 z f gd sub subext) _ _ _
                       (kto_coh (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                          (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                          (BRE u0 z f gd sub subext)))
                    Hy)) |].
      exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
               (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
               (fun v _ => redBbr v) (fun v y1 v' y1' _ => famAtSelf WF)
               (gBr u0 z) f (fun v _ => eapp f v) sub
               (fun v y1 => reds_refl (eapp f v)) subext (gf u0 z f gd)
               v0' y'). }
    (* and then the motive, substituted and weakened as at the subtree *)
    unfold wsup_ty; rewrite wsub3_as, <- (ren3_as C).
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1))
              k (ew (ers rho A) B0) WF (esup u0 f) _ eq_refl Dsup3
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (esup u0 f)) _ _).
    refine (ity_conv _ _ _ _ _ _
              (cohC (esup u0 f) _ (esup u0 f) _ Hsups) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e1 :: rho) e2 eq_refl).
    refine (weaken_ITy _ C m _ _ _ (_ :: nil) rho e1 eq_refl).
    exact (DC (esup u0 f) _). }
  assert (Hstep2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                    ih ihext,
             { xs2 : kElAt (FC2 (esup u0 f)
                             (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                (fun u x => upF (k - j) k EB (FB u x)) redB
                                cohB gW u0 f z sub subext gd))
                      (ers (ext (ext (ext rho FA u0
                                        (dnEl (k - i) k EA FA u0 z))
                                   (BRF u0 z) f (BRE u0 z f gd sub subext))
                              (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j)
                                 (nn - m) EBn EC Bih2 gIh2 Bih_red2 u0 z f gd sub
                                 subext)
                              (ihR (ers rho (stepWrap3 s')) f)
                              (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j)
                                 (nn - m) EBn EC Bih2 gIh2 Bih_red2
                                 (ers rho (stepWrap3 s')) u0 z f gd sub subext
                                 ih ihext (gih2 u0 z f gd))) s') &
               ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                      (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                         Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                      (ihR (ers rho (stepWrap3 s')) f)
                      (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                         Bih2 gIh2 Bih_red2 (ers rho (stepWrap3 s')) u0 z f gd sub
                         subext ih ihext (gih2 u0 z f gd)))
                   s' m (SC2 (esup u0 f))
                   (FC2 (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd))
                   (ers _ s') xs2 }).
  { intros u0 z f sub subext gd ih ihext.
    assert (Es2 : SC (esup u0 f)
                 = ers (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                              (BRF u0 z) f (BRE u0 z f gd sub subext))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                            EBn EC Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                         (ihR (ers rho (stepWrap3 s')) f)
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                            EBn EC Bih2 gIh2 Bih_red2 (ers rho (stepWrap3 s'))
                            u0 z f gd sub subext ih ihext (gih2 u0 z f gd)))
                     (wsup_ty k A B C))
      by exact (eq_sym (er_wsup_ty k A B C (rsub rho) u0 f
                          (ihR (ers rho (stepWrap3 s')) f))).
    destruct (IHs' _ (HE32 u0 z f gd sub subext ih ihext) m (famCast Es2 _)
                (ITy_cast _ (wsup_ty k A B C) m _ _ Es2 _
                   (Dwsup2 u0 z f gd sub subext ih ihext))) as [xs' Ds'].
    destruct (ITm_uncast _ s' m _ _ Es2 _ _ _ Ds') as [xs0 Ds0].
    (* and the primed step's value, moved from the motive its TYPE names to
       the primed motive the primed clause reads it at *)
    exists (kto (kAt (FC (esup u0 f)
                        (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                           (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                           u0 f z sub subext gd)))
              (kAt (FC2 (esup u0 f)
                        (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                           (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                           u0 f z sub subext gd)))
              (famAtWf _) (famAtWf _)
              (PCC (esup u0 f) _) _ xs0).
    exact (i_conv _ s' m _ _ _ _ _ xs0 (PCC (esup u0 f) _) Ds0). }
  pose (Sr2 := ers rho (stepWrap3 s')).
  pose (ws2 := (fun u0 z f sub subext gd ih ihext =>
                 subst_etm (scons (ihR Sr2 f) (scons f (scons u0 (rsub rho))))
                   (er s'))
              : WsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC2 FC2 Sr2).
  pose (xs2 := (fun u0 z f sub subext gd ih ihext =>
                 projT1 (Hstep2 u0 z f sub subext gd ih ihext))
              : XsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC2 FC2 Sr2 ws2).
  pose (redS2 := (fun u0 z f sub subext gd ih ihext =>
                   reds_lam3_app (er s') (rsub rho) u0 f (ihR Sr2 f))
                : RedSTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC2 FC2 Sr2 ws2).
  assert (Ds2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                 ih ihext,
             ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                       Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                    (ihR Sr2 f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m) EBn EC
                       Bih2 gIh2 Bih_red2 Sr2 u0 z f gd sub subext ih ihext
                       (gih2 u0 z f gd)))
                 s' m (SC2 (esup u0 f))
                 (FC2 (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))
                 (ws2 u0 z f sub subext gd ih ihext)
                 (xs2 u0 z f sub subext gd ih ihext))
    by (intros u0 z f sub subext gd ih ihext;
        exact (projT2 (Hstep2 u0 z f sub subext gd ih ihext))).
  (* ---- the step's congruence, within this one reading ---- *)
  assert (stepSrel2 : StepRelTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                       wB FB redB cohB gW m SC2 FC2 Sr2 ws2 xs2 redS2).
  { intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
           Hz Hsub HRsup Hih.
    (* the branching type at the two labels, at its own level *)
    assert (QB : kceq (kAt (FB u0 z)) (kAt (FB u0' z')))
      by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                  (funtm (A :: G) B (UU j) dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA (ers rho A) FA
                  wB FB (ers rho A) FA wB FB DFA DFA (famAtSelf FA) DB DB
                  u0 z u0' z' Hz).
    assert (Htb : tyeq (wB u0 z) (wB u0' z'))
      by exact (ceq_ty (FB u0 z) (FB u0' z') QB).
    (* the two branching Pi types, and the two branching functions *)
    assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB u0' z') Bbr)).
    { exists k; apply eqty_pi.
      - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                 (uf_ty (upF (k - j) k EB (FB u0' z'))) Htb).
      - intros v v' _.
        eapply eqty_exp; [ apply redBbr | apply redBbr |]; exact gW. }
    assert (Hbr2 : forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f' v')).
    { intros v v' Hv.
      apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
               (kFam_good_ty WF) (ev_w _ _) _ _ HRsup u0 f u0' f'
               (ev_sup _ _) (ev_sup _ _)).
      eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
    assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
    { apply (Rel_pi_intro _ (wB u0 z) Bbr);
        [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (redBbr v) |].
      exact (Hbr2 v v' Hv). }
    assert (HRih2 : Rel (epi (wB u0 z) (Bih2 u0 z f)) (ihR Sr2 f) (ihR Sr2 f')).
    { apply (Rel_pi_intro _ (wB u0 z) (Bih2 u0 z f));
        [ exists nn; exact (gIh2 u0 z f gd) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (Bih_red2 u0 z f v) |].
      eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
      exact (Hrec02 _ _ (Hbr2 v v' Hv)). }
    (* the two IH types *)
    assert (Htih2 : tyeq (epi (wB u0 z) (Bih2 u0 z f))
                     (epi (wB u0' z') (Bih2 u0' z' f'))).
    { exists nn; apply eqty_pi.
      - exact (eqty_at_lvl nn _ _ (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
                 (uf_ty (upF (nn - j) nn EBn (FB u0' z'))) Htb).
      - intros v v' Hv.
        eapply eqty_exp;
          [ exact (Bih_red2 u0 z f v) | exact (Bih_red2 u0' z' f' v') |].
        exact (eqty_cumul m nn _ _ Hmn (HCg2 _ _ (Hbr2 v v' Hv))). }
    (* the three entries of the step's context, related *)
    assert (HE1 : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' z')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (kRel_dn (k - i) k EA FA FA (famAtSelf FA) _ _ _ _
                     (conj (famAtSelf (upF (k - i) k EA FA)) Hz))).
    assert (T2 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1),
               tyeq (epi (wB u1 z1) Bbr)
                 (ers (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1)) (wbr k A B)))
      by (intros u1 z1; rewrite <- (Ebr2 u1 z1); exists k; exact (gBr u1 z1)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G)
                    (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                       (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 (T2 u0 z) (T2 u0' z')).
      split.
      - unfold BRF, brFam; apply piFam_ceq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF) ].
      - unfold BRE, brEl, BRF, brFam; apply piLam_eq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF)
          | exact HRf | exact Hsub ]. }
    assert (T32 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1) f1 gd1 sub1
                   subext1,
               tyeq (epi (wB u1 z1) (Bih2 u1 z1 f1))
                 (ers (ext (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1))
                         (BRF u1 z1) f1 (BRE u1 z1 f1 gd1 sub1 subext1))
                    (wih nn k A B C)))
      by (intros u1 z1 f1 gd1 sub1 subext1;
          rewrite <- (Epi2 u1 z1 f1 gd1 sub1 subext1);
          exact (ceq_ty _ _ (Qih u1 z1 f1 gd1 sub1 subext1))).
    assert (HE3r2 : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                     (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                             (BRF u0 z) f (BRE u0 z f gd sub subext))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                           EBn EC Bih2 gIh2 Bih_red2 u0 z f gd sub subext)
                        (ihR Sr2 f)
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                           EBn EC Bih2 gIh2 Bih_red2 Sr2 u0 z f gd sub subext ih
                           ihext (gih2 u0 z f gd)))
                     (ext (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                             (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                           EBn EC Bih2 gIh2 Bih_red2 u0' z' f' gd' sub' subext')
                        (ihR Sr2 f')
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j) (nn - m)
                           EBn EC Bih2 gIh2 Bih_red2 Sr2 u0' z' f' gd' sub' subext'
                           ih' ihext' (gih2 u0' z' f' gd')))).
    { apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
               _ _ _ _ _ _ _ _ HE2 (T32 u0 z f gd sub subext)
               (T32 u0' z' f' gd' sub' subext')).
      split.
      - unfold ihFam; apply piFam_ceq;
          [ exact Htih2
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC2;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy)) ].
      - unfold ihEl, ihFam; apply piLam_eq;
          [ exact Htih2
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC2;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy))
          | exact HRih2
          | intros v y v' y' Hy;
            exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                     (kRel_ceq (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)
                                  v' (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0' z' v' y')
                                  (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                     (nn - j) nn EBn v y v' y' QB Hy)))
                     (kRel_at (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0 z v y)
                                 v' (ihIdx k i j (k - i) (k - j) EA EB
                                       (ers rho A) FA wB FB nn (nn - j) EBn
                                       u0' z' v' y')
                                 (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                    (nn - j) nn EBn v y v' y' QB Hy)))) ]. }
    (* the two motives at the two trees, and the step's own realisers *)
    assert (Hmot2 : kceq (kAt (FC2 (esup u0 f)
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0 f z sub subext gd)))
                        (kAt (FC2 (esup u0' f')
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0' f' z' sub' subext' gd'))))
      by exact (cohC2 _ _ _ _
                  (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
                     (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                     u0 z f sub subext gd u0' z' f' sub' subext' gd'
                     Hz Hsub HRsup)).
    assert (Hrs2 : Rel (SC2 (esup u0' f')) (ws2 u0 z f sub subext gd ih ihext)
                    (ws2 u0' z' f' sub' subext' gd' ih' ihext')).
    { apply (Rel_tyeq (SC (esup u0 f)) (SC2 (esup u0' f')));
        [ exists m; exact (HCCg (esup u0 f) (esup u0' f') HRsup) |].
      unfold ws2, SC.
      rewrite <- (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr2 f)).
      exact (fundamental_ty _ s' (wsup_ty k A B C) ds' _ _
               (proj2 (proj2 (proj2 HE3r2)))). }
    pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s'
                  (wsup_ty k A B C) ds' _ _ HE3r2 m _ _ _
                  (xs2 u0 z f sub subext gd ih ihext)
                  (Ds2 u0 z f sub subext gd ih ihext) _ _ _
                  (xs2 u0' z' f' sub' subext' gd' ih' ihext')
                  (Ds2 u0' z' f' sub' subext' gd' ih' ihext')
                  Hmot2 Hrs2) as Hxs2.
    (* and the two expansions come off *)
    unfold stepOf.
    eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
    eapply kRel_trans; [ exact Hxs2 |].
    split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ]. }
  (* ---- the two subjects, and the two recursors ---- *)
  destruct (IHw rho Hrho k WF DW) as [xw Dw'].
  destruct (IHw' rho Hrho k WF DW) as [xw2 Dw2'].
  pose proof (IHcw rho Hrho k WF DW xw xw2 Dw' Dw2') as Hww.
  pose proof (i_wrec rho A B C s w0 k i j m nn (k - i) (k - j) (nn - j) (nn - m)
                EA EB EBn EC En (ers rho A) FA B0 wB FB redB cohB gW
                SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr gf gih
                ws xs redS stepSrel (ers rho w0) xw
                eq_refl eq_refl (fun _ => eq_refl) DFA DB DC Ds Dw') as Dwrec.
  pose proof (i_wrec rho A B C' s' w0' k i j m nn (k - i) (k - j) (nn - j)
                (nn - m) EA EB EBn EC En (ers rho A) FA B0 wB FB redB cohB gW
                SC2 FC2 cohC2 Bbr redBbr gBr Bih2 gIh2 Bih_red2 Sr2 gf gih2
                ws2 xs2 redS2 stepSrel2 (ers rho w0') xw2
                eq_refl eq_refl (fun _ => eq_refl) DFA DB DC2 Ds2 Dw2') as Dwrec2.
  (* the layer-1 recursor fact ACROSS the two steps, which is what relates the
     two induction hypotheses the step's third entry carries *)
  pose proof (sem_wrec k m A B C (rsub rho) _ _ (gt_of k _ gW) HCg
                (sem_wrec_step G k j m nn A B C s s' (rsub rho) (rsub rho)
                   Hjk Hjn Hmn HS HBg gW HCg
                   (fun si si' H =>
                      proj1 (fundamental_cv _ s s' (wsup_ty k A B C) cs
                               si si' H)))) as Hrec0X.
  (* ---- the two recursions are related ---- *)
  assert (Hcmp : kRel (FC (ers rho w0) xw) (ewrec Sr (ers rho w0))
                   (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
                      (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                      (fun w1 _ => SC w1) FC cohC
                      (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                         FB redB cohB gW m SC FC Sr ws xs redS)
                      stepSrel (ers rho w0) xw)
                   (FC2 (ers rho w0') xw2) (ewrec Sr2 (ers rho w0'))
                   (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
                      (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr2
                      (fun w1 _ => SC2 w1) FC2 cohC2
                      (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                         FB redB cohB gW m SC2 FC2 Sr2 ws2 xs2 redS2)
                      stepSrel2 (ers rho w0') xw2)).
  { refine (wRecS_relX k (ers rho A) B0 (upF (k - i) k EA FA) wB
              (fun u y => upF (k - j) k EB (FB u y)) redB cohB gW
              (ers rho A) B0 (upF (k - i) k EA FA) wB
              (fun u y => upF (k - j) k EB (FB u y)) redB cohB gW
              (famAtSelf WF) (famAtSelf (upF (k - i) k EA FA)) cohB
              m Sr Sr2 (fun w1 _ => SC w1) FC cohC (fun w1 _ => SC2 w1) FC2
              cohC2
              (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                 cohB gW m SC FC Sr ws xs redS) stepSrel
              (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                 cohB gW m SC2 FC2 Sr2 ws2 xs2 redS2) stepSrel2
              _ (ers rho w0) xw (ers rho w0') xw2 Hww).
    (* ---- the step's congruence ACROSS the two subjects: the conversion in
         the left environment, then the right-hand step's own functionality
         between the two ---- *)
    intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
           Hz Hsub HRsup Hih.
    assert (QB : kceq (kAt (FB u0 z)) (kAt (FB u0' z')))
      by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                  (funtm (A :: G) B (UU j) dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA (ers rho A) FA
                  wB FB (ers rho A) FA wB FB DFA DFA (famAtSelf FA) DB DB
                  u0 z u0' z' Hz).
    assert (Htb : tyeq (wB u0 z) (wB u0' z'))
      by exact (ceq_ty (FB u0 z) (FB u0' z') QB).
    assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB u0' z') Bbr)).
    { exists k; apply eqty_pi.
      - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                 (uf_ty (upF (k - j) k EB (FB u0' z'))) Htb).
      - intros v v' _.
        eapply eqty_exp; [ apply redBbr | apply redBbr |]; exact gW. }
    assert (Hbr2 : forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f' v')).
    { intros v v' Hv.
      apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
               (kFam_good_ty WF) (ev_w _ _) _ _ HRsup u0 f u0' f'
               (ev_sup _ _) (ev_sup _ _)).
      eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
    assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
    { apply (Rel_pi_intro _ (wB u0 z) Bbr);
        [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (redBbr v) |].
      exact (Hbr2 v v' Hv). }
    assert (HRih : Rel (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f) (ihR Sr2 f')).
    { apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
        [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
      eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
      exact (Hrec0X _ _ (Hbr2 v v' Hv)). }
    assert (Htih : tyeq (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0' z') (Bih2 u0' z' f'))).
    { exists nn; apply eqty_pi.
      - exact (eqty_at_lvl nn _ _ (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
                 (uf_ty (upF (nn - j) nn EBn (FB u0' z'))) Htb).
      - intros v v' Hv.
        eapply eqty_exp;
          [ exact (Bih_red u0 z f v) | exact (Bih_red2 u0' z' f' v') |].
        exact (eqty_cumul m nn _ _ Hmn (HCCg _ _ (Hbr2 v v' Hv))). }
    (* the three entries of the two step environments, related *)
    assert (HE1 : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' z')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (kRel_dn (k - i) k EA FA FA (famAtSelf FA) _ _ _ _
                     (conj (famAtSelf (upF (k - i) k EA FA)) Hz))).
    assert (T2 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1),
               tyeq (epi (wB u1 z1) Bbr)
                 (ers (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1)) (wbr k A B)))
      by (intros u1 z1; rewrite <- (Ebr2 u1 z1); exists k; exact (gBr u1 z1)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G)
                    (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                       (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 (T2 u0 z) (T2 u0' z')).
      split.
      - unfold BRF, brFam; apply piFam_ceq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF) ].
      - unfold BRE, brEl, BRF, brFam; apply piLam_eq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF)
          | exact HRf | exact Hsub ]. }
    assert (Hcod : forall v y v' y',
               kEqAt (upF (nn - j) nn EBn (FB u0 z)) v y
                     (upF (nn - j) nn EBn (FB u0' z')) v' y' ->
               kceq (kAt (upF (nn - m) nn EC
                            (FC (eapp f v)
                               (sub v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)))))
                    (kAt (upF (nn - m) nn EC
                            (FC2 (eapp f' v')
                               (sub' v' (ihIdx k i j (k - i) (k - j) EA EB
                                           (ers rho A) FA wB FB nn (nn - j) EBn
                                           u0' z' v' y')))))).
    { intros v y v' y' Hy; apply upF_ceq.
      eapply famCeq_tr;
        [ apply cohC;
          exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                           nn (nn - j) EBn u0 z v y)
                   v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                         nn (nn - j) EBn u0' z' v' y')
                   (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn EBn
                      v y v' y' QB Hy))
        | exact (PCC (eapp f' v') _) ]. }
    assert (T3 : tyeq (epi (wB u0 z) (Bih u0 z f))
                   (ers (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                           (BRF u0 z) f (BRE u0 z f gd sub subext))
                      (wih nn k A B C)))
      by (rewrite <- (Epi2 u0 z f gd sub subext);
          exists nn; exact (gIh u0 z f gd)).
    assert (T3x : tyeq (epi (wB u0' z') (Bih2 u0' z' f'))
                    (ers (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                            (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                       (wih nn k A B C)))
      by (rewrite <- (Epi2 u0' z' f' gd' sub' subext');
          exact (ceq_ty _ _ (Qih u0' z' f' gd' sub' subext'))).
    assert (HE3rX : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                      (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                              (BRF u0 z) f (BRE u0 z f gd sub subext))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                         (ihR Sr f)
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih
                            ihext (gih u0 z f gd)))
                      (ext (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                              (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j)
                            (nn - m) EBn EC Bih2 gIh2 Bih_red2 u0' z' f' gd'
                            sub' subext')
                         (ihR Sr2 f')
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC2 FC2 cohC2 nn (nn - j)
                            (nn - m) EBn EC Bih2 gIh2 Bih_red2 Sr2 u0' z' f' gd'
                            sub' subext' ih' ihext' (gih2 u0' z' f' gd')))).
    { apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
               _ _ _ _ _ _ _ _ HE2 T3 T3x).
      split.
      - unfold ihFam; apply piFam_ceq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | exact Hcod ].
      - unfold ihEl, ihFam; apply piLam_eq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | exact Hcod
          | exact HRih
          | intros v y v' y' Hy;
            exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                     (kRel_ceq (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)
                                  v' (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0' z' v' y')
                                  (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                     (nn - j) nn EBn v y v' y' QB Hy)))
                     (kRel_at (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0 z v y)
                                 v' (ihIdx k i j (k - i) (k - j) EA EB
                                       (ers rho A) FA wB FB nn (nn - j) EBn
                                       u0' z' v' y')
                                 (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                    (nn - j) nn EBn v y v' y' QB Hy)))) ]. }
    (* the conversion, in the LEFT environment *)
    assert (Es : SC (esup u0 f)
                 = ers (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                               (BRF u0 z) f (BRE u0 z f gd sub subext))
                          (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                             wB FB redB cohB gW m SC FC cohC nn (nn - j)
                             (nn - m) EBn EC Bih gIh Bih_red u0 z f gd sub
                             subext)
                          (ihR Sr f)
                          (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                             wB FB redB cohB gW m SC FC cohC nn (nn - j)
                             (nn - m) EBn EC Bih gIh Bih_red Sr u0 z f gd sub
                             subext ih ihext (gih u0 z f gd)))
                     (wsup_ty k A B C))
      by exact (eq_sym (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr f))).
    destruct (IHs' _ (HE3 u0 z f gd sub subext ih ihext) m (famCast Es _)
                (ITy_cast _ (wsup_ty k A B C) m _ _ Es _
                   (Dwsup u0 z f gd sub subext ih ihext))) as [v0 Dv0].
    destruct (ITm_uncast _ s' m _ _ Es _ _ _ Dv0) as [v1 Dv1].
    pose proof (kRel_of_IRel_ceq (wih nn k A B C :: wbr k A B :: A :: G) s s'
                  (wsup_ty k A B C) IHcs _
                  (HE3 u0 z f gd sub subext ih ihext) m _ (famCast Es _)
                  (ITy_cast _ (wsup_ty k A B C) m _ _ Es _
                     (Dwsup u0 z f gd sub subext ih ihext))
                  _ (FC (esup u0 f)
                       (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                          (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                          u0 f z sub subext gd))
                  _ (FC (esup u0 f)
                       (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                          (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                          u0 f z sub subext gd))
                  (famCast_ceq Es _) (famCast_ceq Es _)
                  _ (xs u0 z f sub subext gd ih ihext) _ v1
                  (Ds u0 z f sub subext gd ih ihext) Dv1) as Hb1.
    (* and the right-hand step across the two environments *)
    assert (Hmotx : kceq (kAt (FC (esup u0 f)
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                    (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0 f z sub subext gd)))
                         (kAt (FC2 (esup u0' f')
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                    (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0' f' z' sub' subext' gd')))).
    { eapply famCeq_tr;
        [ exact (cohC _ _ _ _
                   (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
                      (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                      u0 z f sub subext gd u0' z' f' sub' subext' gd'
                      Hz Hsub HRsup))
        | exact (PCC (esup u0' f') _) ]. }
    assert (Hrsx : Rel (SC2 (esup u0' f'))
                     (ers (ext (ext (ext rho FA u0
                                       (dnEl (k - i) k EA FA u0 z))
                                  (BRF u0 z) f (BRE u0 z f gd sub subext))
                             (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA
                                B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                (nn - m) EBn EC Bih gIh Bih_red u0 z f gd sub
                                subext)
                             (ihR Sr f)
                             (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA
                                B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                (nn - m) EBn EC Bih gIh Bih_red Sr u0 z f gd
                                sub subext ih ihext (gih u0 z f gd))) s')
                     (ws2 u0' z' f' sub' subext' gd' ih' ihext')).
    { apply (Rel_tyeq (SC (esup u0 f)) (SC2 (esup u0' f')));
        [ exists m; exact (HCCg (esup u0 f) (esup u0' f') HRsup) |].
      unfold ws2, SC, ers; cbn [rsub ext].
      rewrite <- (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr f)).
      exact (fundamental_ty _ s' (wsup_ty k A B C) ds' _ _
               (proj2 (proj2 (proj2 HE3rX)))). }
    pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s'
                  (wsup_ty k A B C) ds' _ _ HE3rX m _ _ _ v1 Dv1 _ _ _
                  (xs2 u0' z' f' sub' subext' gd' ih' ihext')
                  (Ds2 u0' z' f' sub' subext' gd' ih' ihext')
                  Hmotx Hrsx) as Hb2.
    unfold stepOf.
    eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
    eapply kRel_trans; [ eapply kRel_trans; [exact Hb1 | exact Hb2] |].
    split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ]. }
  (* ---- and the package: both values at the LEFT motive's instance ---- *)
  assert (Qfin : kceq (kAt (FC2 (ers rho w0') xw2))
                      (kAt (FC (ers rho w0) xw))).
  { eapply famCeq_tr;
      [ exact (famCeq_sym _ _ (PCC (ers rho w0') xw2))
      | exact (cohC (ers rho w0') xw2 (ers rho w0) xw
                 (kEqAt_sym WF (ers rho w0) xw WF (ers rho w0') xw2 Hww)) ]. }
  exists (SC (ers rho w0)), (FC (ers rho w0) xw),
    (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
       (fun w1 _ => SC w1) FC cohC
       (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          m SC FC Sr ws xs redS)
       stepSrel (ers rho w0) xw),
    (kto (kAt (FC2 (ers rho w0') xw2)) (kAt (FC (ers rho w0) xw))
       (famAtWf (FC2 (ers rho w0') xw2)) (famAtWf (FC (ers rho w0) xw)) Qfin
       (ewrec Sr2 (ers rho w0'))
       (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
          (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr2
          (fun w1 _ => SC2 w1) FC2 cohC2
          (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB
             gW m SC2 FC2 Sr2 ws2 xs2 redS2)
          stepSrel2 (ers rho w0') xw2)).
  split; [split; [split |] |].
  - exact (isubst_ITy rho w0 k (ers rho (wt k A B)) WF (ers rho w0) xw
             eq_refl Dw' C m (SC (ers rho w0)) (FC (ers rho w0) xw)
             (DC (ers rho w0) xw)).
  - exact Dwrec.
  - exact (i_conv rho (wrec A B C' s' w0') m _ (FC2 (ers rho w0') xw2) _
             (FC (ers rho w0) xw) _ _ Qfin Dwrec2).
  - apply (proj2 (kRel_same (FC (ers rho w0) xw) _ _ _ _)).
    eapply kRel_trans;
      [ exact Hcmp
      | exact (kRel_kto (FC2 (ers rho w0') xw2) (FC (ers rho w0) xw) Qfin _ _) ].
Qed.

(* ================================================================== *)
(* The motive's conversion, propagated through the two types the W     *)
(* recursion's step lives at.                                          *)
(*                                                                    *)
(* `wih n k A B C` and `wsup_ty k A B C` are both substitution         *)
(* instances of the motive with a FIXED substitution, so the           *)
(* conversion C = C' propagates through them -- at layer 1, by         *)
(* `fundamental_cv_U`, once the substitution is presented as a related  *)
(* one for `wt k A B :: G`.  That is what lets the primed recursor's    *)
(* FUNCTIONALITY be read off `funtm_wrec`, whose hypotheses live in the *)
(* PRIMED context while the rule types `s'` in the unprimed one.        *)
(* ================================================================== *)

Lemma subst_etm_cons1 (g : nat -> etm) (t : etm) :
  subst_etm g t = subst_etm (scons (g 0) (rscomp ↑ g)) t.
Proof. apply ext_etm; intros [| x]; reflexivity. Qed.

Lemma subst_etm_cons2 (g : nat -> etm) (t : etm) :
  subst_etm g t
  = subst_etm (scons (g 0) (scons (rscomp ↑ g 0) (rscomp ↑ (rscomp ↑ g)))) t.
Proof. apply ext_etm; intros [| [| x]]; reflexivity. Qed.

Lemma subst_etm_cons3 (g : nat -> etm) (t : etm) :
  subst_etm g t
  = subst_etm (scons (g 0)
                 (scons (rscomp ↑ g 0)
                    (scons (rscomp ↑ (rscomp ↑ g) 0)
                       (rscomp ↑ (rscomp ↑ (rscomp ↑ g)))))) t.
Proof. apply ext_etm; intros [| [| [| x]]]; reflexivity. Qed.

Lemma eqty_wih_cv G k j m nn A B C C'
  (Hjn : j <= nn) (Hmn : m <= nn)
  (dBt : ty (A :: G) B (UU j)) (cC : cv (wt k A B :: G) C C' (UU m)) :
  forall g, SubstRel (wbr k A B :: A :: G) g g ->
    eqty nn (subst_etm g (er (wih nn k A B C)))
            (subst_etm g (er (wih nn k A B C'))).
Proof.
  intros g [HS1 Hf]; destruct HS1 as [HS2 Ha].
  rewrite (subst_etm_cons2 g (er (wih nn k A B C))),
          (subst_etm_cons2 g (er (wih nn k A B C'))).
  rewrite (subst_etm_cons1 (rscomp ↑ g) (er (wbr k A B))) in Hf.
  destruct (er_wih_sub nn k A B C (rscomp ↑ (rscomp ↑ g)) (rscomp ↑ g 0) (g 0))
    as [Y [EY HY]].
  destruct (er_wih_sub nn k A B C' (rscomp ↑ (rscomp ↑ g)) (rscomp ↑ g 0) (g 0))
    as [Y' [EY' HY']].
  rewrite EY, EY'.
  apply eqty_pi.
  - exact (eqty_cumul j nn _ _ Hjn
             (fundamental_U (A :: G) B j dBt _ _
                (SubstRel_cons G A _ _ _ _ HS2 Ha))).
  - intros u u' Hu.
    eapply eqty_exp; [exact (HY u) | exact (HY' u') |].
    apply (eqty_cumul m nn _ _ Hmn).
    apply (fundamental_cv_U (wt k A B :: G) C C' m cC).
    apply SubstRel_cons; [exact HS2 |].
    rewrite er_wbr_sub in Hf.
    exact (Rel_cfun_elim _ _ _ _ Hf u u' Hu).
Qed.

Lemma eqty_wsup_ty_cv G k j m nn A B C C'
  (dAt : ty G A (UU j)) (dW : ty G (wt k A B) (UU k))
  (cC : cv (wt k A B :: G) C C' (UU m)) :
  forall sigma,
    SubstRel (wih nn k A B C :: wbr k A B :: A :: G) sigma sigma ->
    eqty m (subst_etm sigma (er (wsup_ty k A B C)))
           (subst_etm sigma (er (wsup_ty k A B C'))).
Proof.
  intros sigma [HS1 _]; destruct HS1 as [HS2 Hf]; destruct HS2 as [HS3 Ha].
  rewrite (subst_etm_cons1 (rscomp ↑ (rscomp ↑ sigma)) (er (wbr k A B))) in Hf.
  rewrite (subst_etm_cons3 sigma (er (wsup_ty k A B C))),
          (subst_etm_cons3 sigma (er (wsup_ty k A B C'))).
  rewrite !er_wsup_ty.
  apply (fundamental_cv_U (wt k A B :: G) C C' m cC).
  apply SubstRel_cons; [exact HS3 |].
  apply (sem_sup k A B _ _ _ _ _
           (gt_of k _ (fundamental_U G (wt k A B) k dW _ _ HS3)) Ha).
  intros u u' Hu.
  rewrite er_wbr_sub in Hf.
  exact (Rel_cfun_elim _ _ _ _ Hf u u' Hu).
Qed.

(* and the three transfers the conversion buys: a related substitution, an
   environment and a related pair of environments for the PRIMED step context
   are one for the unprimed one *)
Lemma substrel_wih_cv G k j m nn A B C C'
  (Hjn : j <= nn) (Hmn : m <= nn)
  (dBt : ty (A :: G) B (UU j)) (cC : cv (wt k A B :: G) C C' (UU m)) :
  forall sigma sigma',
    SubstRel (wih nn k A B C' :: wbr k A B :: A :: G) sigma sigma' ->
    SubstRel (wih nn k A B C :: wbr k A B :: A :: G) sigma sigma'.
Proof.
  intros sigma sigma' [HS1 Hy]; split; [exact HS1 |].
  eapply Rel_cast; [| exact Hy].
  apply eqty_sym.
  exact (eqty_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC _
           (SubstRel_refl _ _ _ HS1)).
Qed.

Lemma envof_wih_cv G k j m nn A B C C'
  (Hjn : j <= nn) (Hmn : m <= nn)
  (dBt : ty (A :: G) B (UU j)) (cC : cv (wt k A B :: G) C C' (UU m)) :
  forall rho, EnvOf (wih nn k A B C' :: wbr k A B :: A :: G) rho ->
    EnvOf (wih nn k A B C :: wbr k A B :: A :: G) rho.
Proof.
  intros rho; destruct rho as [| en rho0]; [intros []|].
  intros [H1 H2]; split; [exact H1 |].
  eapply tyeq_trans; [exact H2 |].
  exists nn; apply eqty_sym.
  exact (eqty_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC (rsub rho0)
           (EnvOf_SubstRel (wbr k A B :: A :: G) rho0 rho0 H1 H1
              (EnvRel_refl rho0))).
Qed.

Lemma envrelof_wih_cv G k j m nn A B C C'
  (Hjn : j <= nn) (Hmn : m <= nn)
  (dBt : ty (A :: G) B (UU j)) (cC : cv (wt k A B :: G) C C' (UU m)) :
  forall rho rho', EnvRelOf (wih nn k A B C' :: wbr k A B :: A :: G) rho rho' ->
    EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G) rho rho'.
Proof.
  intros rho rho' [HO [HO' [HR HS]]]; split; [| split; [| split]].
  - exact (envof_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC rho HO).
  - exact (envof_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC rho' HO').
  - exact HR.
  - exact (substrel_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC _ _ HS).
Qed.

(* ---- the recursor's congruence ---- *)
Lemma isem_wrec G k i j m nn A B C C' s s' w0 w0'
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= nn) (Hmn : m <= nn)
  (En : nn = Nat.max j m) (W : Rules.wfc G)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m)) (dCt' : ty (wt k A B :: G) C' (UU m))
  (cC : cv (wt k A B :: G) C C' (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih nn k A B C) (UU nn))
  (ds : ty (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (ds' : ty (wih nn k A B C :: wbr k A B :: A :: G) s' (wsup_ty k A B C))
  (cs : cv (wih nn k A B C :: wbr k A B :: A :: G) s s' (wsup_ty k A B C))
  (dw : ty G w0 (wt k A B)) (dw' : ty G w0' (wt k A B))
  (cw : cv G w0 w0' (wt k A B))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHC : ITot (wt k A B :: G) C (UU m)) (IHC' : ITot (wt k A B :: G) C' (UU m))
  (IHcC : IRel (wt k A B :: G) C C' (UU m))
  (IHs : ITot (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (IHs' : ITot (wih nn k A B C :: wbr k A B :: A :: G) s' (wsup_ty k A B C))
  (IHcs : IRel (wih nn k A B C :: wbr k A B :: A :: G) s s' (wsup_ty k A B C))
  (IHw : ITot G w0 (wt k A B)) (IHw' : ITot G w0' (wt k A B))
  (IHcw : IRel G w0 w0' (wt k A B)) :
  ISem G (wrec A B C s w0) (wrec A B C' s' w0') (C [w0..]).
Proof.
  pose proof (t_w G k i j A B Hik Hjk dAt dBt) as dW.
  pose proof (t_wrec G k i j m nn A B C s w0 Hik Hjk Hjn Hmn En dAt dBt dCt
                dbr dih ds dw) as dL.
  assert (fL : FunTm G (wrec A B C s w0))
    by exact (funtm G (wrec A B C s w0) (C [w0..]) dL).
  (* the primed subject's functionality: `funtm_wrec` asks for the step's
     side conditions in the PRIMED context, and the conversion transfers them
     from the unprimed one, where the rule puts s' *)
  assert (Lsm2 : forall sigma sigma',
             SubstRel (wih nn k A B C' :: wbr k A B :: A :: G) sigma sigma' ->
             Rel (subst_etm sigma (er (wsup_ty k A B C')))
                 (subst_etm sigma (er s')) (subst_etm sigma' (er s'))).
  { intros sigma sigma' HS.
    pose proof (substrel_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC _ _ HS)
      as HS0.
    eapply Rel_cast;
      [ exact (eqty_wsup_ty_cv G k i m nn A B C C' dAt dW cC sigma
                 (SubstRel_refl _ _ _ HS0))
      | exact (fundamental_ty _ s' (wsup_ty k A B C) ds' sigma sigma' HS0) ]. }
  assert (IHs2 : FunTm (wih nn k A B C' :: wbr k A B :: A :: G) s').
  { intros rho rho' HE.
    exact (funtm (wih nn k A B C :: wbr k A B :: A :: G) s'
             (wsup_ty k A B C) ds' rho rho'
             (envrelof_wih_cv G k j m nn A B C C' Hjn Hmn dBt cC rho rho' HE)). }
  assert (fR : FunTm G (wrec A B C' s' w0'))
    by exact (funtm_wrec G k i j m nn A B C' s' w0' Hik Hjk Hjn Hmn
                (fundamental_U G A i dAt) (fundamental_U (A :: G) B j dBt)
                (fundamental_U (wt k A B :: G) C' m dCt') Lsm2
                (fundamental_ty G w0' (wt k A B) dw')
                (funtm G A (UU i) dAt) (funtm (A :: G) B (UU j) dBt)
                (funtm (wt k A B :: G) C' (UU m) dCt') IHs2
                (funtm G w0' (wt k A B) dw')).
  assert (fT : FunTm G (C [w0..])).
  { destruct (ty_subst1 G (wt k A B) C (UU m) w0 dCt dw) as [d].
    exact (FunTm_of_ty G (C [w0..]) m d). }
  assert (gr : forall rho, EnvITy G rho ->
             Rel (ers rho (C [w0..])) (ers rho (wrec A B C s w0))
               (ers rho (wrec A B C' s' w0'))).
  { intros rho Hrho.
    exact (LCv_of_cv G (wrec A B C s w0) (wrec A B C' s' w0') (C [w0..])
             (c_wrec G k i j m nn A B C C' s s' w0 w0' Hik Hjk Hjn Hmn En
                dAt dBt dCt dCt' cC dbr dih ds ds' cs dw dw' cw)
             rho rho (EnvRelOf_selfE G rho Hrho)). }
  split.
  - split.
    + exact (itot_wrec G A B C s w0 k i j m nn Hik Hjk Hjn Hmn En dAt dBt dCt
               dbr dih ds dw IHA IHB IHC IHs IHw).
    + intros rho Hrho k' F DCw.
      destruct (wrec_data G A B C C' s s' w0 w0' k i j m nn Hik Hjk Hjn Hmn En
                  dAt dBt dCt dCt' cC dbr dih ds ds' cs dw dw' cw
                  IHA IHB IHC IHC' IHcC IHs IHs' IHcs IHw IHw' IHcw rho Hrho)
        as [S1 [F1 [v1 [v2 [[[DT Dv1] Dv2] Hmid]]]]].
      assert (ES1 : S1 = ers rho (C [w0..]))
        by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      pose proof (ity_lvl rho rho eq_refl (C [w0..]) m _ F1 k' _ F DT DCw)
        as Ek; subst k'.
      pose proof (ity_same_ceq G (C [w0..]) fT rho Hrho m F1 F DT DCw) as P.
      exists (kto (kAt F1) (kAt F) (famAtWf F1) (famAtWf F) P _ v2).
      exact (i_conv rho (wrec A B C' s' w0') m _ F1 _ F _ v2 P Dv2).
  - intros rho Hrho k' F DCw x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    destruct (wrec_data G A B C C' s s' w0 w0' k i j m nn Hik Hjk Hjn Hmn En
                dAt dBt dCt dCt' cC dbr dih ds ds' cs dw dw' cw
                IHA IHB IHC IHC' IHcC IHs IHs' IHcs IHw IHw' IHcw rho Hrho)
      as [S1 [F1 [v1 [v2 [[[DT Dv1] Dv2] Hmid]]]]].
    assert (ES1 : S1 = ers rho (C [w0..]))
      by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    pose proof (ity_lvl rho rho eq_refl (C [w0..]) m _ F1 k' _ F DT DCw)
      as Ek; subst k'.
    pose proof (ity_same_ceq G (C [w0..]) fT rho Hrho m F F1 DCw DT) as P.
    pose proof (fL rho rho HEself m _ F _ x Dx _ F1 _ v1 Dv1 P
                  (LTm_of_ty G (wrec A B C s w0) (C [w0..]) dL
                     rho rho HEself)) as H1.
    pose proof (fR rho rho HEself m _ F1 _ v2 Dv2 _ F _ y Dy (knsymU _ _ P)
                  (Rel_trans _ _ _ _ (Rel_sym _ _ _ (gr rho Hrho))
                     (gr rho Hrho))) as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans;
      [ exact (proj1 (kRel_same F1 _ _ _ _) Hmid) | exact H2 ].
Qed.

(* ================================================================== *)
(* W: the computation rule.                                            *)
(*                                                                    *)
(* `wrec_sup_data` builds both sides at one environment.  The left one  *)
(* is the recursion at the canonical node, and `wRecS_sup`              *)
(* (Interp/WEl.v) is its computation rule: the step applied to the       *)
(* label, the branching function and the recursive results.  The right   *)
(* one is that same step, read where the rule puts it -- in the           *)
(* three-entry context, through three substitutions -- and the one         *)
(* genuinely new ingredient is the middle datum: `wih_val` is a lambda     *)
(* whose body is the recursor AT THE SUBTREE, so its reading is `i_lam`    *)
(* over an `i_wrec` one entry up, with every component the weakening of    *)
(* one the recursion already has.                                          *)
(* ================================================================== *)

(* ---- the erasures the computation rule's own recursive call needs: the
     body of `wih_val` is the recursor at the subtree, read one entry up,
     and everything it mentions is the weakening of what the recursion
     already has ---- *)
Lemma ers_wt_sh1 (rho : Env) (A B : tm) (k : nat) (e1 : Entry) :
  ers (e1 :: rho) (wt k (A ⟨↑⟩) (B ⟨up_ren ↑⟩))
  = ew (ers rho A) (elam (subst_etm (up_etm (rsub rho)) (er B))).
Proof.
  unfold ers; cbn [rsub].
  rewrite (er_w_sub k (A ⟨↑⟩) (B ⟨up_ren ↑⟩)).
  rewrite !er_ren, !subst_ren_etm.
  apply (f_equal2 ew).
  - apply ext_etm; intros i; reflexivity.
  - apply (f_equal elam); apply ext_etm; intros [| i]; reflexivity.
Qed.

Lemma ers_C_sh1 (rho : Env) (C : tm) (e1 : Entry) (w1 : etm) :
  subst_etm (scons w1 (rsub (e1 :: rho))) (er (C ⟨up_ren ↑⟩))
  = subst_etm (scons w1 (rsub rho)) (er C).
Proof.
  cbn [rsub]; rewrite er_ren, subst_ren_etm.
  apply ext_etm; intros [| i]; reflexivity.
Qed.

Lemma ers_step_sh1 (rho : Env) (s : tm) (e1 : Entry) :
  ers (e1 :: rho) (stepWrap3 (s ⟨up_ren (up_ren (up_ren ↑))⟩))
  = ers rho (stepWrap3 s).
Proof.
  unfold ers; cbn [rsub].
  rewrite !er_stepWrap3, !sub_lam, er_ren, subst_ren_etm.
  apply (f_equal elam); apply (f_equal elam); apply (f_equal elam).
  apply ext_etm; intros [| [| [| i]]]; reflexivity.
Qed.

Lemma ers_sh1_pi_wsup (k : nat) (A B la bf : tm) (rho : Env) (e1 : Entry) :
  ers (e1 :: rho) (pi k ((B [la..]) ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩))
  = ers rho (pi k (B [la..]) ((wt k A B) ⟨↑⟩)).
Proof.
  unfold ers; cbn [rsub].
  rewrite !er_pi_sub, !er_ren, !subst_ren_etm.
  apply (f_equal2 epi).
  - apply ext_etm; intros i; reflexivity.
  - apply (f_equal elam); apply ext_etm; intros [| i]; reflexivity.
Qed.

(* the induction hypothesis's own type, as an INSTANCE at the node: this is
   the type `wih_val` is read at, and it is the Pi the clause's `ihFam`
   already lives at *)
Lemma ers_wih_inst (rho : Env) (k nn : nat) (A B C la bf : tm) :
  epi (subst_etm (scons (ers rho la) (rsub rho)) (er B))
      (subst_etm (scons (ers rho bf) (scons (ers rho la) (rsub rho)))
         (elam (er (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                          (var_tm 1) (var_tm 0) .:s sh3 ]))))
  = ers rho (pi nn (B [la..]) (C [ wsub k A B la bf .:s ↑ ])).
Proof.
  unfold ers; rewrite er_pi_sub; apply (f_equal2 epi).
  - rewrite er_sub1; reflexivity.
  - rewrite sub_lam; apply (f_equal elam).
    etransitivity.
    + apply (er_subst_ext C _
               (scons (eapp (ren_etm ↑ (subst_etm (rsub rho) (er bf)))
                         (var_etm 0))
                  (fun i => ren_etm ↑ (rsub rho i)))).
      intros [| i]; reflexivity.
    + symmetry; apply (er_subst_ext C _ _).
      intros [| i]; [| reflexivity].
      change (subst_etm (up_etm (rsub rho))
                 (eapp (er (bf ⟨↑⟩)) (var_etm 0))
              = eapp (ren_etm ↑ (subst_etm (rsub rho) (er bf))) (var_etm 0)).
      rewrite sub_app, er_ren, sub_shift_up; reflexivity.
Qed.

Lemma ers_wsub_sh1 (rho : Env) (k : nat) (A B la bf : tm) (e1 : Entry) :
  ers (e1 :: rho) (wsub k A B la bf) = eapp (ers rho bf) (en_u e1).
Proof.
  unfold wsub, ers; cbn [rsub].
  change (subst_etm (scons (en_u e1) (rsub rho))
            (eapp (er (bf ⟨↑⟩)) (var_etm 0))
          = eapp (subst_etm (rsub rho) (er bf)) (en_u e1)).
  rewrite sub_app, er_ren, subst_ren_etm; reflexivity.
Qed.

Lemma ers_wih_val_ihR (rho : Env) (nn k : nat) (A B C s la bf : tm) :
  ers rho (wih_val nn k A B C s la bf)
  = ihR (ers rho (stepWrap3 s)) (ers rho bf).
Proof.
  unfold ers, ihR; rewrite er_wih_val, er_stepWrap3; reflexivity.
Qed.

Lemma ers_wih_two (rho : Env) (nn k : nat) (A B C : tm) (e1 e2 : Entry) :
  epi (subst_etm (scons (en_u e1) (rsub rho)) (er B))
      (subst_etm (scons (en_u e2) (scons (en_u e1) (rsub rho)))
         (elam (er (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                          (var_tm 1) (var_tm 0) .:s sh3 ]))))
  = ers (e2 :: e1 :: rho) (wih nn k A B C).
Proof.
  unfold ers, wih; cbn [rsub].
  rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity.
Qed.

Lemma wrec_sup_data G A B C s la bf k i j m nn
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= nn) (Hmn : m <= nn)
  (En : nn = Nat.max j m)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih nn k A B C) (UU nn))
  (ds : ty (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (da : ty G la A) (df : ty G bf (pi k (B [la..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHC : ITot (wt k A B :: G) C (UU m))
  (IHs : ITot (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (IHa : ITot G la A) (IHf : ITot G bf (pi k (B [la..]) ((wt k A B) ⟨↑⟩)))
  rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam m S1 &
  { v1 : kElAt F1 (ers rho (wrec A B C s (sup k A B la bf))) &
  { v2 : kElAt F1 (ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])) &
    (ITy rho (C [(sup k A B la bf)..]) m S1 F1 *
     ITm rho (wrec A B C s (sup k A B la bf)) m S1 F1
         (ers rho (wrec A B C s (sup k A B la bf))) v1 *
     ITm rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ]) m S1 F1
         (ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])) v2 *
     kEqAt F1 (ers rho (wrec A B C s (sup k A B la bf))) v1
           F1 (ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ]))
           v2)%type } } } }.
Proof.
  assert (EA : (k - i) + i = k) by lia.
  assert (EB : (k - j) + j = k) by lia.
  destruct (build_fam_data G A B k i j (k - i) (k - j) EA EB dAt dBt IHA IHB
              rho Hrho) as [FA [FB [[DFA DB] cohB]]].
  pose (B0 := elam (subst_etm (up_etm (rsub rho)) (er B))).
  pose (wB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 x)) B).
  pose (redB := fun u0 (x : kElAt (upF (k - i) k EA FA) u0) =>
                  reds_lam_app (er B) (rsub rho) u0).
  pose (gW := LTyK_of_ty G (wt k A B) k
                (t_w G k i j A B Hik Hjk dAt dBt) rho rho
                (EnvRelOf_selfE G rho Hrho)).
  pose proof (ity_w rho A B k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW eq_refl DFA DB) as DW.
  pose (WF := wFam k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u0 x => upF (k - j) k EB (FB u0 x)) redB cohB gW).
  pose (Bbr := elam (ren_etm ↑ (ew (ers rho A) B0))).
  pose (redBbr := fun v => reds_const_cod (ew (ers rho A) B0) v).
  pose (gBr := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 eqty_cfun k (wB u0 z) (ew (ers rho A) B0)
                   (uf_ty (upF (k - j) k EB (FB u0 z))) gW).
  (* ---- the motive ---- *)
  pose (SC := fun w1 : etm => subst_etm (scons w1 (rsub rho)) (er C)).
  assert (HEw : forall w1 (x : kElAt WF w1),
             EnvITy (wt k A B :: G) (ext rho WF w1 x)).
  { intros w1 x.
    exact (EnvITy_ext_ceq G rho (wt k A B) k (ers rho (wt k A B)) WF WF DW
             (famAtSelf WF) w1 x Hrho). }
  pose (FC := fun w1 (x : kElAt WF w1) =>
                projT1 (ityT_of_ITot (wt k A B :: G) C m IHC
                          (ext rho WF w1 x) (HEw w1 x))).
  assert (DC : forall w1 x, ITy (ext rho WF w1 x) C m (SC w1) (FC w1 x))
    by (intros w1 x;
        exact (projT2 (ityT_of_ITot (wt k A B :: G) C m IHC
                         (ext rho WF w1 x) (HEw w1 x)))).
  assert (cohC : forall w1 x w1' x', kEqAt WF w1 x WF w1' x' ->
             kceq (kAt (FC w1 x)) (kAt (FC w1' x'))).
  { intros w1 x w1' x' Hx.
    assert (HExx : EnvRelOf (wt k A B :: G) (ext rho WF w1 x) (ext rho WF w1' x'))
      by exact (EnvRelOf_ext' G rho rho (wt k A B) k _ _ WF WF w1 x w1' x'
                  (EnvRelOf_selfE G rho Hrho) eq_refl eq_refl
                  (conj (famAtSelf WF) Hx)).
    exact (FunTy_of_FunTm (wt k A B :: G) C
             (funtm (wt k A B :: G) C (UU m) dCt) _ _ HExx m _ (FC w1 x) _
             (FC w1' x') (DC w1 x) (DC w1' x')
             (LTyK_of_ty (wt k A B :: G) C m dCt _ _ HExx)). }
  (* ---- the layer-1 side, for the guarded goodness premises ---- *)
  pose proof (proj2 (proj2 (proj2 (EnvRelOf_selfE G rho Hrho)))) as HS.
  assert (HBg : forall u u', Rel (subst_etm (rsub rho) (er A)) u u' ->
                  eqty j (subst_etm (scons u (rsub rho)) (er B))
                          (subst_etm (scons u' (rsub rho)) (er B)))
    by (intros u u' Hu;
        exact (fundamental_U (A :: G) B j dBt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hu))).
  assert (HCg : forall x1 y1, Rel (ers rho (wt k A B)) x1 y1 ->
                  eqty m (SC x1) (SC y1))
    by (intros x1 y1 Hxy;
        exact (fundamental_U (wt k A B :: G) C m dCt _ _
                 (SubstRel_cons _ _ _ _ _ _ HS Hxy))).
  pose proof (sem_wrec k m A B C (rsub rho) _ _ (gt_of k _ gW) HCg
                (sem_wrec_step G k j m nn A B C s s (rsub rho) (rsub rho)
                   Hjk Hjn Hmn HS HBg gW HCg
                   (fundamental_ty _ s (wsup_ty k A B C) ds))) as Hrec0.
  (* the branches of a node are trees, which is what the two guarded
     premises are about *)
  assert (Hbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f v')).
  { intros u0 z f gd v v' Hv.
    apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
             (kFam_good_ty WF) (ev_w _ _) _ _ gd u0 f u0 f
             (ev_sup _ _) (ev_sup _ _)).
    eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
  (* ---- the induction hypothesis's type ---- *)
  assert (EBn : (nn - j) + j = nn) by lia.
  assert (EC : (nn - m) + m = nn) by lia.
  pose (Cih := C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                     (var_tm 1) (var_tm 0) .:s sh3 ]).
  pose (Bih := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) (f : etm) =>
                 subst_etm (scons f (scons u0 (rsub rho))) (elam (er Cih))).
  assert (Bih_red : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f v,
             reds (eapp (Bih u0 z f) v) (SC (eapp f v))).
  { intros u0 z f v; unfold SC.
    rewrite <- (er_wih_cod k A B C (rsub rho) u0 f v).
    exact (reds_lam_app (er Cih) (scons f (scons u0 (rsub rho))) v). }
  assert (gIh : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             eqty nn (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0 z) (Bih u0 z f))).
  { intros u0 z f gd.
    apply (eqty_dfun nn (wB u0 z) _ (fun v => SC (eapp f v)));
      [ exact (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
      | exact (Bih_red u0 z f)
      | intros v v' Hv;
        exact (eqty_cumul m nn _ _ Hmn
                 (HCg _ _ (Hbr u0 z f gd v v' Hv))) ]. }
  assert (gf : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) Bbr) f).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) Bbr);
      [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (redBbr v) |].
    exact (Hbr u0 z f gd v v' Hv). }
  assert (gih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f,
             Good (ew (ers rho A) B0) (esup u0 f) ->
             Good (epi (wB u0 z) (Bih u0 z f))
                  (ihR (ers rho (stepWrap3 s)) f)).
  { intros u0 z f gd.
    apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
      [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
    eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
    eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
    exact (Hrec0 _ _ (Hbr u0 z f gd v v' Hv)). }
  (* ---- the step's first context type, interpreted: it IS the clause's
       own branching-function family ---- *)
  assert (Dbr : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             ITy (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B) k
                 (epi (wB u0 z) Bbr)
                 (brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW Bbr redBbr gBr u0 z)).
  { intros u0 z; unfold brFam.
    apply (ity_pi (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) B
             ((wt k A B) ⟨↑⟩ ⟨↑⟩) k j k (k - j) 0 EB eq_refl
             (wB u0 z) (FB u0 z) Bbr (fun v _ => ew (ers rho A) B0)
             (fun v _ => WF) (fun v _ => redBbr v)
             (fun v y v' y' _ => famAtSelf WF) (gBr u0 z));
      [ exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))
      | exact (DB u0 z)
      | intros v y;
        exact (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                 (weaken1_ITy rho (wt k A B) k _ WF _ DW)) ]. }
  (* abbreviations for the two Pi-typed entries *)
  pose (BRF := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) =>
                 brFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z).
  pose (BRE := fun u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext =>
                 brEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr u0 z f sub subext
                   (gf u0 z f gd)).
  (* ---- the motive at a SUBTREE, which is the codomain of the induction
       hypothesis's type: the subtree is the branching function applied to the
       branch, read by i_app in the four-entry environment ---- *)
  assert (Dsub : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext v
                   (y : kElAt (upF (nn - j) nn EBn (FB u0 z)) v),
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                 (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                        (var_tm 1) (var_tm 0) .:s sh3 ])
                 m (SC (eapp f v))
                 (FC (eapp f v)
                    (sub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                              wB FB nn (nn - j) EBn u0 z v y)))).
  { intros u0 z f gd sub subext v y.
    pose (Xa := ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                  nn (nn - j) EBn u0 z v y).
    (* the application *)
    pose proof (i_app
                  (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                     (FB u0 z) v (dnEl (nn - j) nn EBn (FB u0 z) v y))
                  (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                  (var_tm 1) (var_tm 0) k j k (k - j) 0 EB eq_refl
                  (wB u0 z) (FB u0 z) Bbr (fun v' _ => ew (ers rho A) B0)
                  (fun v' _ => WF) (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext)
                  v (dnEl (nn - j) nn EBn (FB u0 z) v y)
                  (eq_sym (ers_wbr_app_ty rho A B k _ _ _))
                  (weaken1_ITy _ (B ⟨↑⟩) j _ (FB u0 z) _
                     (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z)))
                  (fun u x =>
                     weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) k _ WF _
                       (weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩) k _ WF _
                          (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                             (weaken1_ITy rho (wt k A B) k _ WF _ DW))))
                  (i_varS _ _ 0 k _ (BRF u0 z) f (BRE u0 z f gd sub subext)
                     (i_var0 _ k _ (BRF u0 z) f (BRE u0 z f gd sub subext)))
                  (i_var0 _ j _ (FB u0 z) v
                     (dnEl (nn - j) nn EBn (FB u0 z) v y))) as Dapp.
    (* the value the application names, and the motive's index at it *)
    pose (Xv := piApp k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (BRE u0 z f gd sub subext) v Xa).
    assert (Hidx : kEqAt WF (eapp f v) Xv WF (eapp f v) (sub v Xa))
      by exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v')
                  (fun v' y' v'' y'' _ => famAtSelf WF) (gBr u0 z)
                  f (fun v' _ => eapp f v') sub
                  (fun v' y' => reds_refl (eapp f v')) subext (gf u0 z f gd)
                  v Xa).
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry j (wB u0 z) (FB u0 z) v
                  (dnEl (nn - j) nn EBn (FB u0 z) v y)).
    pose (em := Build_Entry k (ew (ers rho A) B0) WF (eapp f v) Xv).
    rewrite wsub3_as, <- ren3_as.
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                 (var_tm 1) (var_tm 0))
              k (ew (ers rho A) B0) WF (eapp f v) Xv eq_refl Dapp
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (eapp f v)) _ _).
    refine (ity_conv _ _ _ _ (FC (eapp f v) Xv) (FC (eapp f v) (sub v Xa))
              (cohC (eapp f v) Xv (eapp f v) (sub v Xa) Hidx) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (em :: nil) (e1 :: rho) e2 eq_refl).
    exact (weaken_ITy _ C m _ _ (DC (eapp f v) Xv)
             (em :: nil) rho e1 eq_refl). }
  assert (Epi2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             epi (wB u0 z) (Bih u0 z f)
             = ers (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                      (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C)).
  { intros u0 z f gd sub subext.
    unfold wB, Bih, ers, wih; cbn [rsub ext].
    rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity. }
  (* ---- the step's second context type, interpreted: it IS the clause's
       own induction-hypothesis family ---- *)
  assert (Dih : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext,
             ITy (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (BRF u0 z) f (BRE u0 z f gd sub subext))
                 (wih nn k A B C) nn
                 (epi (wB u0 z) (Bih u0 z f))
                 (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                    Bih gIh Bih_red u0 z f gd sub subext)).
  { intros u0 z f gd sub subext.
    unfold ihFam, wih.
    apply (ity_pi _ (B ⟨↑⟩)
             (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                    (var_tm 1) (var_tm 0) .:s sh3 ])
             nn j m (nn - j) (nn - m) EBn EC
             (wB u0 z) (FB u0 z) (Bih u0 z f) _ _ _ _ _);
      [ exact (Epi2 u0 z f gd sub subext)
      | exact (weaken1_ITy _ B j _ (FB u0 z) _ (DB u0 z))
      | exact (Dsub u0 z f gd sub subext) ]. }
  (* ---- and hence the step's environment carries an interpretation of every
       one of its context types ---- *)
  assert (Ebr2 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0),
             epi (wB u0 z) Bbr
             = ers (ext rho FA u0 (dnEl (k - i) k EA FA u0 z)) (wbr k A B))
    by (intros u0 z; exact (eq_sym (er_wbr_sub k A B (rsub rho) u0))).
  assert (HE3 : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                  ih ihext,
             EnvITy (wih nn k A B C :: wbr k A B :: A :: G)
               (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd)))).
  { intros u0 z f gd sub subext ih ihext.
    refine (EnvITy_ext_ceq (wbr k A B :: A :: G) _ (wih nn k A B C) nn _ _
              (famCast (Epi2 u0 z f gd sub subext) _) _ _ _ _ _).
    - exact (ITy_cast _ (wih nn k A B C) nn _ _
               (Epi2 u0 z f gd sub subext) _ (Dih u0 z f gd sub subext)).
    - apply famCast_ceq.
    - refine (EnvITy_ext_ceq (A :: G) _ (wbr k A B) k _ _
                (famCast (Ebr2 u0 z) _) _ _ _ _ _).
      + exact (ITy_cast _ (wbr k A B) k _ _ (Ebr2 u0 z) _ (Dbr u0 z)).
      + apply famCast_ceq.
      + exact (EnvITy_ext G rho A i FA DFA u0
                 (dnEl (k - i) k EA FA u0 z) Hrho). }
  (* ---- the motive at the TREE the step builds ---- *)
  assert (Dwsup : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f gd sub subext
                    ih ihext,
             ITy (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR (ers rho (stepWrap3 s)) f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                       subext ih ihext (gih u0 z f gd)))
                 (wsup_ty k A B C) m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))).
  { intros u0 z f gd sub subext ih ihext.
    pose (e1 := Build_Entry i (ers rho A) FA u0
                  (dnEl (k - i) k EA FA u0 z)).
    pose (e2 := Build_Entry k (epi (wB u0 z) Bbr) (BRF u0 z) f
                  (BRE u0 z f gd sub subext)).
    pose (e3 := Build_Entry nn (epi (wB u0 z) (Bih u0 z f))
                  (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red u0 z f gd sub subext)
                  (ihR (ers rho (stepWrap3 s)) f)
                  (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                     Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                     subext ih ihext (gih u0 z f gd))).
    (* the tree, read in the step's own environment *)
    pose (Z' := upEl (k - i) k EA FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (HzZ : kEqAt (upF (k - i) k EA FA) u0 z (upF (k - i) k EA FA) u0 Z')
      by (apply kEqAt_sym; apply upEl_dnEl).
    assert (Hbrceq : kceq (kAt (BRF u0 z)) (kAt (BRF u0 Z'))).
    { unfold BRF, brFam; apply piFam_ceq.
      - exists k; apply eqty_pi.
        + exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                   (uf_ty (upF (k - j) k EB (FB u0 Z')))
                   (ceq_ty (upF (k - j) k EB (FB u0 z))
                      (upF (k - j) k EB (FB u0 Z')) (cohB u0 z u0 Z' HzZ))).
        + intros v v' _.
          eapply eqty_exp; [ apply redBbr | apply redBbr |].
          exact gW.
      - exact (cohB u0 z u0 Z' HzZ).
      - intros v y v' y' _; exact (famAtSelf WF). }
    pose (ea := Build_Entry i (ers rho A) FA u0 (dnEl (k - i) k EA FA u0 z)).
    assert (DA3 : ITy (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) i (ers rho A) FA).
    { rewrite <- sh3_as.
      exact (weaken1_ITy _ ((A ⟨↑⟩) ⟨↑⟩) i _ FA _
               (weaken1_ITy _ (A ⟨↑⟩) i _ FA _
                  (weaken1_ITy rho A i _ FA _ DFA))). }
    assert (DB3 : forall u x,
               ITy (ext (e3 :: e2 :: e1 :: rho) FA u
                      (dnEl (k - i) k EA FA u x))
                   (B ⟨up_ren sh3⟩) j (wB u x) (FB u x)).
    { intros u x; rewrite <- ren3_as.
      refine (weaken_ITy _ ((B ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e2 :: e1 :: rho) e3 eq_refl).
      refine (weaken_ITy _ (B ⟨up_ren ↑⟩) j _ _ _
                (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
                (e1 :: rho) e2 eq_refl).
      exact (weaken_ITy _ B j _ _ (DB u x)
               (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
               rho e1 eq_refl). }
    pose proof (i_sup (e3 :: e2 :: e1 :: rho) (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)
                  (var_tm 2) (var_tm 1) k i j (k - i) (k - j) EA EB
                  (ers rho A) FA B0 wB FB redB cohB gW Bbr redBbr gBr
                  u0 (dnEl (k - i) k EA FA u0 z) f
                  (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z')) (famAtWf (BRF u0 z))
                     (famAtWf (BRF u0 Z')) Hbrceq f
                     (BRE u0 z f gd sub subext))
                  gd (eq_sym (ers_wt_sh3 rho A B k e1 e2 e3))
                  DA3 DB3
                  (i_varS _ e3 1 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                     (i_varS _ e2 0 i _ FA u0 (dnEl (k - i) k EA FA u0 z)
                        (i_var0 rho i _ FA u0 (dnEl (k - i) k EA FA u0 z))))
                  (i_conv _ (var_tm 1) k (epi (wB u0 z) Bbr) (BRF u0 z) _
                     (BRF u0 Z') f (BRE u0 z f gd sub subext) Hbrceq
                     (i_varS _ e3 0 k _ (BRF u0 z) f
                        (BRE u0 z f gd sub subext)
                        (i_var0 (e1 :: rho) k _ (BRF u0 z) f
                           (BRE u0 z f gd sub subext))))) as Dsup3.
    (* i_sup's value is the clause's own tree: its label is the round trip of
       the entry's, and its branches are the branching function's semantic
       value applied -- which is what it was built from *)
    assert (Hsups : kEqAt WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f Z'
                         (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                            wB FB redB cohB gW Bbr redBbr gBr u0 Z' f
                            (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                               (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z'))
                               Hbrceq f (BRE u0 z f gd sub subext)))
                         gd)
                      WF (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd)).
    { apply (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
               (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW);
        [ apply upEl_dnEl | intros v0 y v0' y' Hy | exact gd ].
      eapply kEqAt_trans; [ exact (famAtSelf WF) |
        exact (kRel_at
                 (piApp_eqX k (wB u0 Z') Bbr (upF (k - j) k EB (FB u0 Z'))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 Z')
                    (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
                    (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                    (fun v _ => redBbr v)
                    (fun v y1 v' y1' _ => famAtSelf WF) (gBr u0 z)
                    (cohB u0 Z' u0 z (upEl_dnEl (k - i) k EA FA u0 z))
                    (fun v y1 v' y1' _ => famAtSelf WF)
                    f (kto (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                         (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                         (BRE u0 z f gd sub subext))
                    f (BRE u0 z f gd sub subext) v0 y v0' y'
                    (kEqAt_sym (BRF u0 z) f (BRE u0 z f gd sub subext) _ _ _
                       (kto_coh (kAt (BRF u0 z)) (kAt (BRF u0 Z'))
                          (famAtWf (BRF u0 z)) (famAtWf (BRF u0 Z')) Hbrceq f
                          (BRE u0 z f gd sub subext)))
                    Hy)) |].
      exact (piLam_app k (wB u0 z) Bbr (upF (k - j) k EB (FB u0 z))
               (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
               (fun v _ => redBbr v) (fun v y1 v' y1' _ => famAtSelf WF)
               (gBr u0 z) f (fun v _ => eapp f v) sub
               (fun v y1 => reds_refl (eapp f v)) subext (gf u0 z f gd)
               v0' y'). }
    (* and then the motive, substituted and weakened as at the subtree *)
    unfold wsup_ty; rewrite wsub3_as, <- (ren3_as C).
    refine (isubst_ITy (e3 :: e2 :: e1 :: rho)
              (sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1))
              k (ew (ers rho A) B0) WF (esup u0 f) _ eq_refl Dsup3
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m (SC (esup u0 f)) _ _).
    refine (ity_conv _ _ _ _ _ _
              (cohC (esup u0 f) _ (esup u0 f) _ Hsups) _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e2 :: e1 :: rho) e3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (_ :: nil) (e1 :: rho) e2 eq_refl).
    refine (weaken_ITy _ C m _ _ _ (_ :: nil) rho e1 eq_refl).
    exact (DC (esup u0 f) _). }
  (* ---- the step's realiser and value ---- *)
  assert (Hstep : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                    ih ihext,
             { xs : kElAt (FC (esup u0 f)
                             (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                                (fun u x => upF (k - j) k EB (FB u x)) redB
                                cohB gW u0 f z sub subext gd))
                      (ers (ext (ext (ext rho FA u0
                                        (dnEl (k - i) k EA FA u0 z))
                                   (BRF u0 z) f (BRE u0 z f gd sub subext))
                              (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red u0 z f gd sub
                                 subext)
                              (ihR (ers rho (stepWrap3 s)) f)
                              (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA
                                 B0 wB FB redB cohB gW m SC FC cohC nn (nn - j)
                                 (nn - m) EBn EC Bih gIh Bih_red
                                 (ers rho (stepWrap3 s)) u0 z f gd sub subext
                                 ih ihext (gih u0 z f gd))) s) &
               ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                          (BRF u0 z) f (BRE u0 z f gd sub subext))
                      (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red u0 z f gd sub subext)
                      (ihR (ers rho (stepWrap3 s)) f)
                      (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                         redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                         Bih gIh Bih_red (ers rho (stepWrap3 s)) u0 z f gd sub
                         subext ih ihext (gih u0 z f gd)))
                   s m (SC (esup u0 f))
                   (FC (esup u0 f)
                      (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                         (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                         u0 f z sub subext gd))
                   (ers _ s) xs }).
  { intros u0 z f sub subext gd ih ihext.
    assert (Es : SC (esup u0 f)
                 = ers (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                              (BRF u0 z) f (BRE u0 z f gd sub subext))
                         (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                         (ihR (ers rho (stepWrap3 s)) f)
                         (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                            FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                            EBn EC Bih gIh Bih_red (ers rho (stepWrap3 s))
                            u0 z f gd sub subext ih ihext (gih u0 z f gd)))
                     (wsup_ty k A B C))
      by exact (eq_sym (er_wsup_ty k A B C (rsub rho) u0 f
                          (ihR (ers rho (stepWrap3 s)) f))).
    destruct (IHs _ (HE3 u0 z f gd sub subext ih ihext) m (famCast Es _)
                (ITy_cast _ (wsup_ty k A B C) m _ _ Es _
                   (Dwsup u0 z f gd sub subext ih ihext))) as [xs' Ds'].
    destruct (ITm_uncast _ s m _ _ Es _ _ _ Ds') as [xs Ds].
    exists xs; exact Ds. }
  pose (Sr := ers rho (stepWrap3 s)).
  pose (ws := (fun u0 z f sub subext gd ih ihext =>
                 subst_etm (scons (ihR Sr f) (scons f (scons u0 (rsub rho))))
                   (er s))
              : WsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr).
  pose (xs := (fun u0 z f sub subext gd ih ihext =>
                 projT1 (Hstep u0 z f sub subext gd ih ihext))
              : XsTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW m SC FC Sr ws).
  pose (redS := (fun u0 z f sub subext gd ih ihext =>
                   reds_lam3_app (er s) (rsub rho) u0 f (ihR Sr f))
                : RedSTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                    redB cohB gW m SC FC Sr ws).
  assert (Ds : forall u0 (z : kElAt (upF (k - i) k EA FA) u0) f sub subext gd
                 ih ihext,
             ITm (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                        (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red u0 z f gd sub subext)
                    (ihR Sr f)
                    (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                       (gih u0 z f gd)))
                 s m (SC (esup u0 f))
                 (FC (esup u0 f)
                    (wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                       u0 f z sub subext gd))
                 (ws u0 z f sub subext gd ih ihext)
                 (xs u0 z f sub subext gd ih ihext))
    by (intros u0 z f sub subext gd ih ihext;
        exact (projT2 (Hstep u0 z f sub subext gd ih ihext))).
  (* ---- the step's congruence, within this one reading ---- *)
  assert (stepSrel : StepRelTy k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                       wB FB redB cohB gW m SC FC Sr ws xs redS).
  { intros u0 z f sub subext gd ih ihext u0' z' f' sub' subext' gd' ih' ihext'
           Hz Hsub HRsup Hih.
    (* the branching type at the two labels, at its own level *)
    assert (QB : kceq (kAt (FB u0 z)) (kAt (FB u0' z')))
      by exact (cod_ceq G A B (LTy_of_ty (A :: G) B j dBt)
                  (funtm (A :: G) B (UU j) dBt) rho rho
                  (EnvRelOf_selfE G rho Hrho) k i j (k - i) EA (ers rho A) FA
                  wB FB (ers rho A) FA wB FB DFA DFA (famAtSelf FA) DB DB
                  u0 z u0' z' Hz).
    assert (Htb : tyeq (wB u0 z) (wB u0' z'))
      by exact (ceq_ty (FB u0 z) (FB u0' z') QB).
    (* the two branching Pi types, and the two branching functions *)
    assert (Htp : tyeq (epi (wB u0 z) Bbr) (epi (wB u0' z') Bbr)).
    { exists k; apply eqty_pi.
      - exact (eqty_at_lvl k _ _ (uf_ty (upF (k - j) k EB (FB u0 z)))
                 (uf_ty (upF (k - j) k EB (FB u0' z'))) Htb).
      - intros v v' _.
        eapply eqty_exp; [ apply redBbr | apply redBbr |]; exact gW. }
    assert (Hbr2 : forall v v', Rel (wB u0 z) v v' ->
               Rel (ers rho (wt k A B)) (eapp f v) (eapp f' v')).
    { intros v v' Hv.
      apply (Rel_w_br2 (ew (ers rho A) B0) (ers rho A) B0
               (kFam_good_ty WF) (ev_w _ _) _ _ HRsup u0 f u0' f'
               (ev_sup _ _) (ev_sup _ _)).
      eapply Rel_exp_ty; [ exact (redB u0 z) | exact Hv ]. }
    assert (HRf : Rel (epi (wB u0 z) Bbr) f f').
    { apply (Rel_pi_intro _ (wB u0 z) Bbr);
        [ exists k; exact (gBr u0 z) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (redBbr v) |].
      exact (Hbr2 v v' Hv). }
    assert (HRih : Rel (epi (wB u0 z) (Bih u0 z f)) (ihR Sr f) (ihR Sr f')).
    { apply (Rel_pi_intro _ (wB u0 z) (Bih u0 z f));
        [ exists nn; exact (gIh u0 z f gd) | apply ev_pi | intros v v' Hv ].
      eapply Rel_exp_ty; [ exact (Bih_red u0 z f v) |].
      eapply Rel_exp; [ apply reds_wih_beta | apply reds_wih_beta |].
      exact (Hrec0 _ _ (Hbr2 v v' Hv)). }
    (* the two IH types *)
    assert (Htih : tyeq (epi (wB u0 z) (Bih u0 z f))
                     (epi (wB u0' z') (Bih u0' z' f'))).
    { exists nn; apply eqty_pi.
      - exact (eqty_at_lvl nn _ _ (uf_ty (upF (nn - j) nn EBn (FB u0 z)))
                 (uf_ty (upF (nn - j) nn EBn (FB u0' z'))) Htb).
      - intros v v' Hv.
        eapply eqty_exp;
          [ exact (Bih_red u0 z f v) | exact (Bih_red u0' z' f' v') |].
        exact (eqty_cumul m nn _ _ Hmn (HCg _ _ (Hbr2 v v' Hv))). }
    (* the three entries of the step's context, related *)
    assert (HE1 : EnvRelOf (A :: G)
                    (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                    (ext rho FA u0' (dnEl (k - i) k EA FA u0' z')))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (kRel_dn (k - i) k EA FA FA (famAtSelf FA) _ _ _ _
                     (conj (famAtSelf (upF (k - i) k EA FA)) Hz))).
    assert (T2 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1),
               tyeq (epi (wB u1 z1) Bbr)
                 (ers (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1)) (wbr k A B)))
      by (intros u1 z1; rewrite <- (Ebr2 u1 z1); exists k; exact (gBr u1 z1)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G)
                    (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                       (BRF u0 z) f (BRE u0 z f gd sub subext))
                    (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                       (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 (T2 u0 z) (T2 u0' z')).
      split.
      - unfold BRF, brFam; apply piFam_ceq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF) ].
      - unfold BRE, brEl, BRF, brFam; apply piLam_eq;
          [ exact Htp | exact (cohB u0 z u0' z' Hz)
          | intros v y v' y' _; exact (famAtSelf WF)
          | exact HRf | exact Hsub ]. }
    assert (T3 : forall u1 (z1 : kElAt (upF (k - i) k EA FA) u1) f1 gd1 sub1
                   subext1,
               tyeq (epi (wB u1 z1) (Bih u1 z1 f1))
                 (ers (ext (ext rho FA u1 (dnEl (k - i) k EA FA u1 z1))
                         (BRF u1 z1) f1 (BRE u1 z1 f1 gd1 sub1 subext1))
                    (wih nn k A B C)))
      by (intros u1 z1 f1 gd1 sub1 subext1;
          rewrite <- (Epi2 u1 z1 f1 gd1 sub1 subext1);
          exists nn; exact (gIh u1 z1 f1 gd1)).
    assert (HE3r : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                     (ext (ext (ext rho FA u0 (dnEl (k - i) k EA FA u0 z))
                             (BRF u0 z) f (BRE u0 z f gd sub subext))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                        (ihR Sr f)
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih
                           ihext (gih u0 z f gd)))
                     (ext (ext (ext rho FA u0' (dnEl (k - i) k EA FA u0' z'))
                             (BRF u0' z') f' (BRE u0' z' f' gd' sub' subext'))
                        (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red u0' z' f' gd' sub' subext')
                        (ihR Sr f')
                        (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                           FB redB cohB gW m SC FC cohC nn (nn - j) (nn - m)
                           EBn EC Bih gIh Bih_red Sr u0' z' f' gd' sub' subext'
                           ih' ihext' (gih u0' z' f' gd')))).
    { apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
               _ _ _ _ _ _ _ _ HE2 (T3 u0 z f gd sub subext)
               (T3 u0' z' f' gd' sub' subext')).
      split.
      - unfold ihFam; apply piFam_ceq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy)) ].
      - unfold ihEl, ihFam; apply piLam_eq;
          [ exact Htih
          | exact (upF_ceq (nn - j) nn EBn (FB u0 z) (FB u0' z') QB)
          | intros v y v' y' Hy; apply upF_ceq; apply cohC;
            exact (Hsub v (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                             wB FB nn (nn - j) EBn u0 z v y)
                     v' (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA
                           wB FB nn (nn - j) EBn u0' z' v' y')
                     (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB (nn - j) nn
                        EBn v y v' y' QB Hy))
          | exact HRih
          | intros v y v' y' Hy;
            exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                     (kRel_ceq (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                         (ers rho A) FA wB FB nn (nn - j) EBn
                                         u0 z v y)
                                  v' (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0' z' v' y')
                                  (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                     (nn - j) nn EBn v y v' y' QB Hy)))
                     (kRel_at (Hih v (ihIdx k i j (k - i) (k - j) EA EB
                                        (ers rho A) FA wB FB nn (nn - j) EBn
                                        u0 z v y)
                                 v' (ihIdx k i j (k - i) (k - j) EA EB
                                       (ers rho A) FA wB FB nn (nn - j) EBn
                                       u0' z' v' y')
                                 (reLvl_eq (FB u0 z) (FB u0' z') (k - j) k EB
                                    (nn - j) nn EBn v y v' y' QB Hy)))) ]. }
    (* the two motives at the two trees, and the step's own realisers *)
    assert (Hmot : kceq (kAt (FC (esup u0 f)
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0 f z sub subext gd)))
                        (kAt (FC (esup u0' f')
                                 (wSup k (ers rho A) B0 (upF (k - i) k EA FA)
                                    wB (fun u x => upF (k - j) k EB (FB u x))
                                    redB cohB gW u0' f' z' sub' subext' gd'))))
      by exact (cohC _ _ _ _
                  (wSup_cong k (ers rho A) B0 (upF (k - i) k EA FA) wB
                     (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                     u0 z f sub subext gd u0' z' f' sub' subext' gd'
                     Hz Hsub HRsup)).
    assert (Hrs : Rel (SC (esup u0' f')) (ws u0 z f sub subext gd ih ihext)
                    (ws u0' z' f' sub' subext' gd' ih' ihext')).
    { apply (Rel_tyeq (SC (esup u0 f)) (SC (esup u0' f')));
        [ exists m;
          exact (ceq_eqty (FC (esup u0 f) _) (FC (esup u0' f') _) Hmot) |].
      unfold ws, SC.
      rewrite <- (er_wsup_ty k A B C (rsub rho) u0 f (ihR Sr f)).
      exact (fundamental_ty _ s (wsup_ty k A B C) ds _ _
               (proj2 (proj2 (proj2 HE3r)))). }
    pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s
                  (wsup_ty k A B C) ds _ _ HE3r m _ _ _
                  (xs u0 z f sub subext gd ih ihext)
                  (Ds u0 z f sub subext gd ih ihext) _ _ _
                  (xs u0' z' f' sub' subext' gd' ih' ihext')
                  (Ds u0' z' f' sub' subext' gd' ih' ihext')
                  Hmot Hrs) as Hxs.
    (* and the two expansions come off *)
    unfold stepOf.
    eapply kRel_trans; [ split; [exact (famAtSelf _) | apply famExp_rel] |].
    eapply kRel_trans; [ exact Hxs |].
    split; [ exact (famAtSelf _) | apply kEqAt_sym; apply famExp_rel ]. }
  (* ---- the scrutinee: the node built from the label and the branching
       function, with the canonical data the recursion already has ---- *)
  destruct (IHa rho Hrho i FA DFA) as [xa Da].
  pose (Xa := upEl (k - i) k EA FA (ers rho la) xa).
  destruct (ityT_of_ITot (A :: G) B j IHB (ext rho FA (ers rho la) xa)
              (EnvITy_ext G rho A i FA DFA (ers rho la) xa Hrho)) as [FBu DBu0].
  assert (HExa : EnvRelOf (A :: G) (ext rho FA (ers rho la) xa)
                   (ext rho FA (ers rho la)
                      (dnEl (k - i) k EA FA (ers rho la) Xa))).
  { apply (EnvRelOf_ext G rho rho A i FA FA (ers rho la) xa (ers rho la) _
             (EnvRelOf_selfE G rho Hrho)).
    split; [exact (famAtSelf FA) | apply kEqAt_sym; apply dnEl_upEl]. }
  assert (Pa : kceq (kAt FBu) (kAt (FB (ers rho la) Xa)))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (UU j) dBt) _ _ HExa j
                _ FBu _ _ DBu0 (DB (ers rho la) Xa)
                (LTyK_of_ty (A :: G) B j dBt _ _ HExa)).
  pose proof (ity_conv rho (B [la..]) j _ FBu (FB (ers rho la) Xa) Pa
                (isubst_ITy rho la i (ers rho A) FA (ers rho la) xa eq_refl Da
                   B j (ers (ext rho FA (ers rho la) xa) B) FBu DBu0)) as DBa.
  pose proof (ity_pi rho (B [la..]) ((wt k A B) ⟨↑⟩) k j k (k - j) 0 EB eq_refl
                (wB (ers rho la) Xa) (FB (ers rho la) Xa) Bbr
                (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
                (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
                (gBr (ers rho la) Xa)
                (eq_sym (er_wsup_fun_sub k A B la (rsub rho)))
                DBa
                (fun u0 x =>
                   weaken1_ITy rho (wt k A B) k (ew (ers rho A) B0) WF
                     (Build_Entry j (wB (ers rho la) Xa) (FB (ers rho la) Xa) u0
                        (dnEl (k - j) k EB (FB (ers rho la) Xa) u0 x)) DW))
    as Dfpi.
  assert (Ef : epi (wB (ers rho la) Xa) Bbr
               = ers rho (pi k (B [la..]) ((wt k A B) ⟨↑⟩)))
    by exact (eq_sym (er_wsup_fun_sub k A B la (rsub rho))).
  destruct (IHf rho Hrho k (famCast Ef _)
              (ITy_cast rho (pi k (B [la..]) ((wt k A B) ⟨↑⟩)) k _ _ Ef _ Dfpi))
    as [xg0 Dg0].
  destruct (ITm_uncast rho bf k _ _ Ef _ _ _ Dg0) as [xg Dg].
  assert (gd : Good (ew (ers rho A) B0) (esup (ers rho la) (ers rho bf))).
  { pose proof (LTm_of_ty G (sup k A B la bf) (wt k A B)
                  (t_sup G k i j A B la bf Hik Hjk dAt dBt da df) rho rho
                  (EnvRelOf_selfE G rho Hrho)) as H0.
    exact H0. }
  pose proof (i_sup rho A B la bf k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                wB FB redB cohB gW Bbr redBbr gBr (ers rho la) xa (ers rho bf) xg
                gd eq_refl DFA DB Da Dg) as Dsup.
  pose (XW := wSup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW
                (ers rho la) (ers rho bf) Xa
                (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                   cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg)
                (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg)
                gd).
  (* ---- the recursor at that node ---- *)
  pose proof (i_wrec rho A B C s (sup k A B la bf) k i j m nn (k - i) (k - j)
                (nn - j) (nn - m) EA EB EBn EC En (ers rho A) FA B0 wB FB redB
                cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr gf gih
                ws xs redS stepSrel (esup (ers rho la) (ers rho bf)) XW
                eq_refl eq_refl (fun _ => eq_refl) DFA DB DC Ds Dsup) as Dwrec.
  (* ---- and the computation rule, at the semantic level ---- *)
  pose proof (wRecS_sup k (ers rho A) B0 (upF (k - i) k EA FA) wB
                (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                (fun w1 _ => SC w1) FC cohC
                (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW m SC FC Sr ws xs redS)
                stepSrel (ers rho la) Xa (ers rho bf)
                (brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                   cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg)
                (brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg)
                gd) as Hcomp.
  (* ---- the recursive call the computation rule supplies: the body of
       `wih_val` is the recursor at the subtree, read one entry up, and every
       component it mentions is the weakening of one the recursion has ---- *)
  pose (SUBB := brApp k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                  cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg).
  pose (SUBX := brApp_eq k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                  redB cohB gW Bbr redBbr gBr (ers rho la) Xa (ers rho bf) xg).
  pose (SUB := fun v (y : kElAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v) =>
                 SUBB v
                   (ihIdx k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                      nn (nn - j) EBn (ers rho la) Xa v y)).
  pose (eb := fun v (y : kElAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v) =>
                Build_Entry j (wB (ers rho la) Xa) (FB (ers rho la) Xa) v
                  (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y)).
  assert (Dsubtree : forall v y,
             ITm (eb v y :: rho) (wsub k A B la bf) k (ew (ers rho A) B0) WF
                 (eapp (ers rho bf) v) (SUB v y)).
  { intros v y; unfold wsub, SUB.
    refine (i_app (eb v y :: rho) ((B [la..]) ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩)
              (bf ⟨↑⟩) (var_tm 0) k j k (k - j) 0 EB eq_refl
              (wB (ers rho la) Xa) (FB (ers rho la) Xa) Bbr
              (fun v0 _ => ew (ers rho A) B0) (fun v0 _ => WF)
              (fun v0 _ => redBbr v0) (fun v0 y0 v0' y0' _ => famAtSelf WF)
              (gBr (ers rho la) Xa) (ers rho bf) xg v
              (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y) _ _ _ _ _).
    - rewrite (ers_sh1_pi_wsup k A B la bf rho (eb v y)).
      exact (eq_sym (er_wsup_fun_sub k A B la (rsub rho))).
    - exact (weaken1_ITy rho (B [la..]) j _ (FB (ers rho la) Xa) (eb v y) DBa).
    - intros u0 x0.
      exact (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
               (weaken1_ITy rho (wt k A B) k _ WF (eb v y) DW)).
    - exact (weaken1 rho bf k _ _ _ xg (eb v y) Dg).
    - exact (i_var0 rho j _ (FB (ers rho la) Xa) v
               (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y)). }
  (* the motive at the subtree, in the branch's environment *)
  assert (DCsub : forall v y,
             ITy (eb v y :: rho) (C [ wsub k A B la bf .:s ↑ ]) m
                 (SC (eapp (ers rho bf) v))
                 (FC (eapp (ers rho bf) v) (SUB v y))).
  { intros v y.
    rewrite <- (wih_val_cod C (wsub k A B la bf)).
    refine (isubst_ITy (eb v y :: rho) (wsub k A B la bf) k
              (ew (ers rho A) B0) WF (eapp (ers rho bf) v) (SUB v y) _
              (Dsubtree v y) (C ⟨up_ren ↑⟩) m _ _ _).
    - rewrite (ers_wsub_sh1 rho k A B la bf (eb v y)); reflexivity.
    - exact (weaken_ITy _ C m _ _ (DC (eapp (ers rho bf) v) (SUB v y))
               (Build_Entry k (ew (ers rho A) B0) WF (eapp (ers rho bf) v)
                  (SUB v y) :: nil) rho (eb v y) eq_refl). }
  assert (Dbody : forall v (y : kElAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v),
             ITm (ext rho (FB (ers rho la) Xa) v
                    (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y))
                 (wrec (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩)
                    (s ⟨up_ren (up_ren (up_ren ↑))⟩) (wsub k A B la bf))
                 m (SC (eapp (ers rho bf) v))
                 (FC (eapp (ers rho bf) v) (SUB v y))
                 (ewrec Sr (eapp (ers rho bf) v))
                 (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
                    (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                    (fun w1 _ => SC w1) FC cohC
                    (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC Sr ws xs redS)
                    stepSrel (eapp (ers rho bf) v) (SUB v y))).
  { intros v y.
    (* the recursor at the subtree *)
    pose (eA := fun u (x : kElAt (upF (k - i) k EA FA) u) =>
                  Build_Entry i (ers rho A) FA u
                    (dnEl (k - i) k EA FA u x)).
    pose (eW := fun w1 (x : kElAt WF w1) =>
                  Build_Entry k (ew (ers rho A) B0) WF w1 x).
    refine (i_wrec (eb v y :: rho) (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩)
              (s ⟨up_ren (up_ren (up_ren ↑))⟩) (wsub k A B la bf)
              k i j m nn (k - i) (k - j) (nn - j) (nn - m) EA EB EBn EC En
              (ers rho A) FA B0 wB FB redB cohB gW SC FC cohC
              Bbr redBbr gBr Bih gIh Bih_red Sr gf gih ws xs redS stepSrel
              (eapp (ers rho bf) v) (SUB v y) _ _ _ _ _ _ _ (Dsubtree v y)).
    - exact (eq_sym (ers_step_sh1 rho s (eb v y))).
    - exact (eq_sym (ers_wt_sh1 rho A B k (eb v y))).
    - intros w1; exact (eq_sym (ers_C_sh1 rho C (eb v y) w1)).
    - exact (weaken1_ITy rho A i _ FA (eb v y) DFA).
    - intros u0 x0.
      exact (weaken_ITy _ B j _ _ (DB u0 x0) (eA u0 x0 :: nil) rho (eb v y)
               eq_refl).
    - intros w1 x0.
      exact (weaken_ITy _ C m _ _ (DC w1 x0) (eW w1 x0 :: nil) rho (eb v y)
               eq_refl).
    - intros u0 z0 f0 sub0 subext0 gd0 ih0 ihext0.
      exact (weaken_ITm _ s m _ _ _ _
               (Ds u0 z0 f0 sub0 subext0 gd0 ih0 ihext0)
               (_ :: _ :: eA u0 z0 :: nil) rho (eb v y) eq_refl). }
  (* ---- and `wih_val` itself: the lambda whose body is that recursive call,
       read by `i_lam` at the very Pi the clause's induction-hypothesis
       family lives at ---- *)
  pose (RB := fun v (y : kElAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v) =>
                wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
                  (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                  (fun w1 _ => SC w1) FC cohC
                  (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                     redB cohB gW m SC FC Sr ws xs redS)
                  stepSrel (eapp (ers rho bf) v) (SUB v y)).
  assert (HcohI : forall v y v' y',
             kEqAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v y
                   (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v' y' ->
             kceq (kAt (FC (eapp (ers rho bf) v) (SUB v y)))
                  (kAt (FC (eapp (ers rho bf) v') (SUB v' y')))).
  { intros v y v' y' Hy.
    apply cohC.
    exact (SUBX _ _ _ _
             (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A) FA wB FB
                nn (nn - j) EBn (ers rho la) Xa v y v' y' Hy)). }
  assert (Hxtext : forall v y v' y',
             kEqAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v y
                   (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v' y' ->
             kEqAt (upF (nn - m) nn EC (FC (eapp (ers rho bf) v) (SUB v y)))
                   (ewrec Sr (eapp (ers rho bf) v))
                   (upEl (nn - m) nn EC
                      (FC (eapp (ers rho bf) v) (SUB v y))
                      (ewrec Sr (eapp (ers rho bf) v)) (RB v y))
                   (upF (nn - m) nn EC (FC (eapp (ers rho bf) v') (SUB v' y')))
                   (ewrec Sr (eapp (ers rho bf) v'))
                   (upEl (nn - m) nn EC
                      (FC (eapp (ers rho bf) v') (SUB v' y'))
                      (ewrec Sr (eapp (ers rho bf) v')) (RB v' y'))).
  { intros v y v' y' Hy.
    exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _ (HcohI v y v' y' Hy)
             (kRel_at
                (wRecS_rel k (ers rho A) B0 (upF (k - i) k EA FA) wB
                   (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                   (fun w1 _ => SC w1) FC cohC
                   (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB
                      FB redB cohB gW m SC FC Sr ws xs redS)
                   stepSrel (eapp (ers rho bf) v) (SUB v y)
                   (eapp (ers rho bf) v') (SUB v' y')
                   (SUBX _ _ _ _
                      (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A) FA wB
                         FB nn (nn - j) EBn (ers rho la) Xa v y v' y' Hy))))). }
  pose proof (i_lam rho (B [la..]) (C [ wsub k A B la bf .:s ↑ ])
                (wrec (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩)
                   (s ⟨up_ren (up_ren (up_ren ↑))⟩) (wsub k A B la bf))
                nn j m (nn - j) (nn - m) EBn EC
                (wB (ers rho la) Xa) (FB (ers rho la) Xa)
                (Bih (ers rho la) Xa (ers rho bf))
                (fun v _ => SC (eapp (ers rho bf) v))
                (fun v y => FC (eapp (ers rho bf) v) (SUB v y))
                (fun v _ => Bih_red (ers rho la) Xa (ers rho bf) v)
                (fun v y v' y' H =>
                   upF_ceq (nn - m) nn EC _ _
                     (cohC _ _ _ _
                        (SUBX _ _ _ _
                           (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A) FA
                              wB FB nn (nn - j) EBn (ers rho la) Xa
                              v y v' y' H))))
                (gIh (ers rho la) Xa (ers rho bf) gd)
                (ihR Sr (ers rho bf))
                (fun v _ => ewrec Sr (eapp (ers rho bf) v))
                RB
                (fun v _ => reds_wih_beta Sr (ers rho bf) v)
                Hxtext (gih (ers rho la) Xa (ers rho bf) gd)
                (eq_sym (ers_wih_val_ihR rho nn k A B C s la bf))
                (ers_wih_inst rho k nn A B C la bf)
                DBa DCsub Dbody) as Dwv.
  (* ---- the step's own environment, with the three VALUES the right-hand
       side substitutes: the label, the branching function and `wih_val` ---- *)
  pose (E1 := ext rho FA (ers rho la) xa).
  assert (DBn : ITy E1 B j (wB (ers rho la) Xa) (FB (ers rho la) Xa))
    by exact (ity_conv E1 B j _ FBu (FB (ers rho la) Xa) Pa DBu0).
  assert (Dbrn : ITy E1 (wbr k A B) k (epi (wB (ers rho la) Xa) Bbr)
                    (BRF (ers rho la) Xa)).
  { unfold BRF, brFam.
    apply (ity_pi E1 B ((wt k A B) ⟨↑⟩ ⟨↑⟩) k j k (k - j) 0 EB eq_refl
             (wB (ers rho la) Xa) (FB (ers rho la) Xa) Bbr
             (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
             (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
             (gBr (ers rho la) Xa));
      [ exact (eq_sym (er_wbr_sub k A B (rsub rho) (ers rho la)))
      | exact DBn
      | intros v y;
        exact (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                 (weaken1_ITy rho (wt k A B) k _ WF _ DW)) ]. }
  pose (E2 := ext E1 (BRF (ers rho la) Xa) (ers rho bf) xg).
  assert (Dsubn : forall v (y : kElAt (upF (nn - j) nn EBn (FB (ers rho la) Xa)) v),
             ITy (ext E2 (FB (ers rho la) Xa) v
                    (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y))
                 (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                        (var_tm 1) (var_tm 0) .:s sh3 ])
                 m (SC (eapp (ers rho bf) v))
                 (FC (eapp (ers rho bf) v) (SUB v y))).
  { intros v y.
    pose proof (i_app
                  (ext E2 (FB (ers rho la) Xa) v
                     (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y))
                  (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                  (var_tm 1) (var_tm 0) k j k (k - j) 0 EB eq_refl
                  (wB (ers rho la) Xa) (FB (ers rho la) Xa) Bbr
                  (fun v' _ => ew (ers rho A) B0) (fun v' _ => WF)
                  (fun v' _ => redBbr v') (fun v' y' v'' y'' _ => famAtSelf WF)
                  (gBr (ers rho la) Xa) (ers rho bf) xg
                  v (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y)
                  (eq_sym (ers_wbr_app_ty rho A B k _ _ _))
                  (weaken1_ITy _ (B ⟨↑⟩) j _ (FB (ers rho la) Xa) _
                     (weaken1_ITy _ B j _ (FB (ers rho la) Xa) _ DBn))
                  (fun u x =>
                     weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) k _ WF _
                       (weaken1_ITy _ ((wt k A B) ⟨↑⟩ ⟨↑⟩) k _ WF _
                          (weaken1_ITy _ ((wt k A B) ⟨↑⟩) k _ WF _
                             (weaken1_ITy rho (wt k A B) k _ WF _ DW))))
                  (i_varS _ _ 0 k _ (BRF (ers rho la) Xa) (ers rho bf) xg
                     (i_var0 _ k _ (BRF (ers rho la) Xa) (ers rho bf) xg))
                  (i_var0 _ j _ (FB (ers rho la) Xa) v
                     (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y))) as Dapp.
    pose (eN1 := Build_Entry i (ers rho A) FA (ers rho la) xa).
    pose (eN2 := Build_Entry k (epi (wB (ers rho la) Xa) Bbr)
                   (BRF (ers rho la) Xa) (ers rho bf) xg).
    pose (eN3 := Build_Entry j (wB (ers rho la) Xa) (FB (ers rho la) Xa) v
                   (dnEl (nn - j) nn EBn (FB (ers rho la) Xa) v y)).
    pose (eNm := Build_Entry k (ew (ers rho A) B0) WF
                   (eapp (ers rho bf) v) (SUB v y)).
    rewrite wsub3_as, <- ren3_as.
    refine (isubst_ITy (eN3 :: eN2 :: eN1 :: rho)
              (app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                 (var_tm 1) (var_tm 0))
              k (ew (ers rho A) B0) WF (eapp (ers rho bf) v) (SUB v y)
              eq_refl Dapp
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m
              (SC (eapp (ers rho bf) v)) _ _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (eNm :: nil) (eN2 :: eN1 :: rho) eN3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (eNm :: nil) (eN1 :: rho) eN2 eq_refl).
    exact (weaken_ITy _ C m _ _ (DC (eapp (ers rho bf) v) (SUB v y))
             (eNm :: nil) rho eN1 eq_refl). }
  assert (Dihn : ITy E2 (wih nn k A B C) nn
                    (epi (wB (ers rho la) Xa) (Bih (ers rho la) Xa (ers rho bf)))
                    (ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                       Bih gIh Bih_red (ers rho la) Xa (ers rho bf) gd
                       (SUBB)
                       (SUBX))).
  { unfold ihFam, wih.
    apply (ity_pi E2 (B ⟨↑⟩)
             (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩)
                    (var_tm 1) (var_tm 0) .:s sh3 ])
             nn j m (nn - j) (nn - m) EBn EC
             (wB (ers rho la) Xa) (FB (ers rho la) Xa)
             (Bih (ers rho la) Xa (ers rho bf)) _ _ _ _ _);
      [ exact (ers_wih_two rho nn k A B C
                 (Build_Entry i (ers rho A) FA (ers rho la) xa)
                 (Build_Entry k (epi (wB (ers rho la) Xa) Bbr)
                    (BRF (ers rho la) Xa) (ers rho bf) xg))
      | exact (weaken1_ITy _ B j _ (FB (ers rho la) Xa) _ DBn)
      | exact Dsubn ]. }
  (* ---- the step's own type at the node, read in that environment: here the
       two entries carry exactly the label and the branching function the node
       is built from, so `i_sup` rebuilds the node on the nose ---- *)
  pose (eN1 := Build_Entry i (ers rho A) FA (ers rho la) xa).
  pose (eN2 := Build_Entry k (epi (wB (ers rho la) Xa) Bbr)
                 (BRF (ers rho la) Xa) (ers rho bf) xg).
  pose (IHFAM := ihFam k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                   redB cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC
                   Bih gIh Bih_red (ers rho la) Xa (ers rho bf) gd
                   (SUBB)
                   (SUBX)).
  pose (XWV := piLam nn (wB (ers rho la) Xa)
                 (Bih (ers rho la) Xa (ers rho bf))
                 (upF (nn - j) nn EBn (FB (ers rho la) Xa))
                 (fun v _ => SC (eapp (ers rho bf) v))
                 (fun v y => upF (nn - m) nn EC
                               (FC (eapp (ers rho bf) v) (SUB v y)))
                 (fun v _ => Bih_red (ers rho la) Xa (ers rho bf) v)
                 (fun v y v' y' H =>
                    upF_ceq (nn - m) nn EC _ _
                      (cohC _ _ _ _
                         (SUBX _ _ _ _
                            (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A)
                               FA wB FB nn (nn - j) EBn (ers rho la) Xa
                               v y v' y' H))))
                 (gIh (ers rho la) Xa (ers rho bf) gd)
                 (ihR Sr (ers rho bf))
                 (fun v _ => ewrec Sr (eapp (ers rho bf) v))
                 (fun v y => upEl (nn - m) nn EC
                               (FC (eapp (ers rho bf) v) (SUB v y))
                               (ewrec Sr (eapp (ers rho bf) v)) (RB v y))
                 (fun v _ => reds_wih_beta Sr (ers rho bf) v)
                 Hxtext (gih (ers rho la) Xa (ers rho bf) gd)).
  pose (eN3 := Build_Entry nn
                 (epi (wB (ers rho la) Xa) (Bih (ers rho la) Xa (ers rho bf)))
                 IHFAM (ihR Sr (ers rho bf)) XWV).
  assert (DA3 : ITy (eN3 :: eN2 :: eN1 :: rho) (A ⟨sh3⟩) i (ers rho A) FA).
  { rewrite <- sh3_as.
    exact (weaken1_ITy _ ((A ⟨↑⟩) ⟨↑⟩) i _ FA _
             (weaken1_ITy _ (A ⟨↑⟩) i _ FA _
                (weaken1_ITy rho A i _ FA _ DFA))). }
  assert (DB3 : forall u x,
             ITy (ext (eN3 :: eN2 :: eN1 :: rho) FA u
                    (dnEl (k - i) k EA FA u x))
                 (B ⟨up_ren sh3⟩) j (wB u x) (FB u x)).
  { intros u x; rewrite <- ren3_as.
    refine (weaken_ITy _ ((B ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) j _ _ _
              (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
              (eN2 :: eN1 :: rho) eN3 eq_refl).
    refine (weaken_ITy _ (B ⟨up_ren ↑⟩) j _ _ _
              (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
              (eN1 :: rho) eN2 eq_refl).
    exact (weaken_ITy _ B j _ _ (DB u x)
             (Build_Entry i (ers rho A) FA u (dnEl (k - i) k EA FA u x) :: nil)
             rho eN1 eq_refl). }
  assert (Dwsupn : ITy (eN3 :: eN2 :: eN1 :: rho) (wsup_ty k A B C) m
                       (SC (esup (ers rho la) (ers rho bf)))
                       (FC (esup (ers rho la) (ers rho bf)) XW)).
  { pose proof (i_sup (eN3 :: eN2 :: eN1 :: rho) (A ⟨sh3⟩) (B ⟨up_ren sh3⟩)
                  (var_tm 2) (var_tm 1) k i j (k - i) (k - j) EA EB
                  (ers rho A) FA B0 wB FB redB cohB gW Bbr redBbr gBr
                  (ers rho la) xa (ers rho bf) xg gd
                  (eq_sym (ers_wt_sh3 rho A B k eN1 eN2 eN3)) DA3 DB3
                  (i_varS _ eN3 1 i _ FA (ers rho la) xa
                     (i_varS _ eN2 0 i _ FA (ers rho la) xa
                        (i_var0 rho i _ FA (ers rho la) xa)))
                  (i_varS _ eN3 0 k _ (BRF (ers rho la) Xa) (ers rho bf) xg
                     (i_var0 (eN1 :: rho) k _ (BRF (ers rho la) Xa)
                        (ers rho bf) xg))) as Dsup3.
    unfold wsup_ty; rewrite wsub3_as, <- (ren3_as C).
    refine (isubst_ITy (eN3 :: eN2 :: eN1 :: rho)
              (sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1))
              k (ew (ers rho A) B0) WF (esup (ers rho la) (ers rho bf)) XW
              eq_refl Dsup3
              ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩ ⟨up_ren ↑⟩) m
              (SC (esup (ers rho la) (ers rho bf))) _ _).
    refine (weaken_ITy _ ((C ⟨up_ren ↑⟩) ⟨up_ren ↑⟩) m _ _ _
              (Build_Entry k (ew (ers rho A) B0) WF
                 (esup (ers rho la) (ers rho bf)) XW :: nil)
              (eN2 :: eN1 :: rho) eN3 eq_refl).
    refine (weaken_ITy _ (C ⟨up_ren ↑⟩) m _ _ _
              (Build_Entry k (ew (ers rho A) B0) WF
                 (esup (ers rho la) (ers rho bf)) XW :: nil)
              (eN1 :: rho) eN2 eq_refl).
    exact (weaken_ITy _ C m _ _
             (DC (esup (ers rho la) (ers rho bf)) XW)
             (Build_Entry k (ew (ers rho A) B0) WF
                (esup (ers rho la) (ers rho bf)) XW :: nil) rho eN1 eq_refl). }
  (* ---- the step, read there, and the three substitutions ---- *)
  assert (HE3n : EnvITy (wih nn k A B C :: wbr k A B :: A :: G)
                   (eN3 :: eN2 :: eN1 :: rho)).
  { pose proof (ers_wih_two rho nn k A B C eN1 eN2) as Eih2.
    pose proof (eq_sym (er_wbr_sub k A B (rsub rho) (ers rho la))) as Ebr1.
    refine (EnvITy_ext_ceq (wbr k A B :: A :: G) (eN2 :: eN1 :: rho)
              (wih nn k A B C) nn _ IHFAM (famCast Eih2 IHFAM) _ _ _ _ _).
    - exact (ITy_cast _ (wih nn k A B C) nn _ _ Eih2 _ Dihn).
    - apply famCast_ceq.
    - refine (EnvITy_ext_ceq (A :: G) (eN1 :: rho) (wbr k A B) k _
                (BRF (ers rho la) Xa) (famCast Ebr1 (BRF (ers rho la) Xa))
                _ _ _ _ _).
      + exact (ITy_cast _ (wbr k A B) k _ _ Ebr1 _ Dbrn).
      + apply famCast_ceq.
      + exact (EnvITy_ext G rho A i FA DFA (ers rho la) xa Hrho). }
  assert (Esn : SC (esup (ers rho la) (ers rho bf))
                = ers (eN3 :: eN2 :: eN1 :: rho) (wsup_ty k A B C))
    by exact (eq_sym (er_wsup_ty k A B C (rsub rho) (ers rho la) (ers rho bf)
                        (ihR Sr (ers rho bf)))).
  destruct (IHs _ HE3n m (famCast Esn _)
              (ITy_cast _ (wsup_ty k A B C) m _ _ Esn _ Dwsupn)) as [vs0 Dvs0].
  destruct (ITm_uncast _ s m _ _ Esn _ _ _ Dvs0) as [vs Dvs].
  pose proof (subst_ITm rho la eN1 eq_refl Da (subUniv_all rho la)
                _ s m _ _ _ _ Dvs (eN3 :: eN2 :: nil) eq_refl) as Dsub1.
  pose proof (subst_ITm rho bf eN2 eq_refl Dg (subUniv_all rho bf)
                _ _ m _ _ _ _ Dsub1 (eN3 :: nil) eq_refl) as Dsub2.
  pose proof (subst_ITm rho (wih_val nn k A B C s la bf) eN3
                (eq_sym (ers_wih_val_ihR rho nn k A B C s la bf)) Dwv
                (subUniv_all rho (wih_val nn k A B C s la bf))
                _ _ m _ _ _ _ Dsub2 nil eq_refl) as Dsub3.
  cbn [upn length] in Dsub3.
  rewrite (wrec_sup_three s la bf (wih_val nn k A B C s la bf)) in Dsub3.
  assert (Ers3 : ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])
                 = ers (eN3 :: eN2 :: eN1 :: rho) s).
  { unfold ers; cbn [rsub].
    apply er_subst_ext; intros [| [| [| i0]]]; try reflexivity.
    exact (ers_wih_val_ihR rho nn k A B C s la bf). }
  (* ---- the two step readings are related: the clause's environment carries
       the round trip of the label, the eta-expansion of the branching
       function and the clause's own induction hypothesis, and each is related
       to the datum the right-hand side substitutes ---- *)
  pose (IHval := fun v0 (y : kElAt (upF (k - j) k EB (FB (ers rho la) Xa)) v0) =>
                   famExp (FC (eapp (ers rho bf) v0) (SUBB v0 y))
                     (eapp (ihR Sr (ers rho bf)) v0)
                     (ewrec Sr (eapp (ers rho bf) v0))
                     (reds_wih_beta Sr (ers rho bf) v0)
                     (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
                        (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                        (fun w1 _ => SC w1) FC cohC
                        (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0
                           wB FB redB cohB gW m SC FC Sr ws xs redS)
                        stepSrel (eapp (ers rho bf) v0) (SUBB v0 y))).
  pose (IHvext := wIh_ext k (ers rho A) B0 (upF (k - i) k EA FA) wB
                    (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
                    (fun w1 _ => SC w1) FC cohC
                    (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB
                       redB cohB gW m SC FC Sr ws xs redS)
                    stepSrel (ers rho la) Xa (ers rho bf) SUBB SUBX).
  pose (eC1 := Build_Entry i (ers rho A) FA (ers rho la)
                 (dnEl (k - i) k EA FA (ers rho la) Xa)).
  pose (eC2 := Build_Entry k (epi (wB (ers rho la) Xa) Bbr)
                 (BRF (ers rho la) Xa) (ers rho bf)
                 (BRE (ers rho la) Xa (ers rho bf) gd SUBB SUBX)).
  pose (eC3 := Build_Entry nn
                 (epi (wB (ers rho la) Xa) (Bih (ers rho la) Xa (ers rho bf)))
                 IHFAM (ihR Sr (ers rho bf))
                 (ihEl k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB
                    cohB gW m SC FC cohC nn (nn - j) (nn - m) EBn EC Bih gIh
                    Bih_red Sr (ers rho la) Xa (ers rho bf) gd SUBB SUBX
                    IHval IHvext (gih (ers rho la) Xa (ers rho bf) gd))).
  assert (HEcl : EnvRelOf (wih nn k A B C :: wbr k A B :: A :: G)
                   (eC3 :: eC2 :: eC1 :: rho) (eN3 :: eN2 :: eN1 :: rho)).
  { assert (HE1 : EnvRelOf (A :: G) (eC1 :: rho) (eN1 :: rho))
      by exact (EnvRelOf_ext G rho rho A i FA FA _ _ _ _
                  (EnvRelOf_selfE G rho Hrho)
                  (conj (famAtSelf FA) (dnEl_upEl (k - i) k EA FA _ xa))).
    assert (Ebr0 : epi (wB (ers rho la) Xa) Bbr
                   = ers (eC1 :: rho) (wbr k A B))
      by exact (eq_sym (er_wbr_sub k A B (rsub rho) (ers rho la))).
    assert (Ebr0' : epi (wB (ers rho la) Xa) Bbr
                    = ers (eN1 :: rho) (wbr k A B))
      by exact (eq_sym (er_wbr_sub k A B (rsub rho) (ers rho la))).
    assert (T2 : tyeq (epi (wB (ers rho la) Xa) Bbr)
                   (ers (eC1 :: rho) (wbr k A B)))
      by (rewrite <- Ebr0; exists k; exact (gBr (ers rho la) Xa)).
    assert (T2' : tyeq (epi (wB (ers rho la) Xa) Bbr)
                    (ers (eN1 :: rho) (wbr k A B)))
      by (rewrite <- Ebr0'; exists k; exact (gBr (ers rho la) Xa)).
    assert (HE2 : EnvRelOf (wbr k A B :: A :: G) (eC2 :: eC1 :: rho)
                    (eN2 :: eN1 :: rho)).
    { apply (EnvRelOf_ext_ty (A :: G) _ _ (wbr k A B) k _ _ _ _ _ _ _ _
               HE1 T2 T2').
      split; [exact (famAtSelf (BRF (ers rho la) Xa)) |].
      apply (piEl_ext k (wB (ers rho la) Xa) Bbr
               (upF (k - j) k EB (FB (ers rho la) Xa))
               (fun v _ => ew (ers rho A) B0) (fun v _ => WF)
               (fun v _ => redBbr v) (fun v y v' y' _ => famAtSelf WF)
               (gBr (ers rho la) Xa));
        [ exact (gf (ers rho la) Xa (ers rho bf) gd) |].
      intros v y v' y' Hy.
      eapply kEqAt_trans;
        [ exact (famAtSelf WF)
        | exact (piLam_app k (wB (ers rho la) Xa) Bbr
                   (upF (k - j) k EB (FB (ers rho la) Xa))
                   (fun v0 _ => ew (ers rho A) B0) (fun v0 _ => WF)
                   (fun v0 _ => redBbr v0)
                   (fun v0 y0 v0' y0' _ => famAtSelf WF)
                   (gBr (ers rho la) Xa) (ers rho bf)
                   (fun v0 _ => eapp (ers rho bf) v0) SUBB
                   (fun v0 y0 => reds_refl (eapp (ers rho bf) v0)) SUBX
                   (gf (ers rho la) Xa (ers rho bf) gd) v y)
        | exact (SUBX v y v' y' Hy) ]. }
    assert (Eih0 : epi (wB (ers rho la) Xa)
                     (Bih (ers rho la) Xa (ers rho bf))
                   = ers (eC2 :: eC1 :: rho) (wih nn k A B C))
      by exact (ers_wih_two rho nn k A B C eC1 eC2).
    assert (Eih0' : epi (wB (ers rho la) Xa)
                      (Bih (ers rho la) Xa (ers rho bf))
                    = ers (eN2 :: eN1 :: rho) (wih nn k A B C))
      by exact (ers_wih_two rho nn k A B C eN1 eN2).
    assert (T3 : tyeq (epi (wB (ers rho la) Xa)
                        (Bih (ers rho la) Xa (ers rho bf)))
                   (ers (eC2 :: eC1 :: rho) (wih nn k A B C)))
      by (rewrite <- Eih0; exists nn;
          exact (gIh (ers rho la) Xa (ers rho bf) gd)).
    assert (T3' : tyeq (epi (wB (ers rho la) Xa)
                         (Bih (ers rho la) Xa (ers rho bf)))
                    (ers (eN2 :: eN1 :: rho) (wih nn k A B C)))
      by (rewrite <- Eih0'; exists nn;
          exact (gIh (ers rho la) Xa (ers rho bf) gd)).
    apply (EnvRelOf_ext_ty (wbr k A B :: A :: G) _ _ (wih nn k A B C) nn
             _ _ _ _ _ _ _ _ HE2 T3 T3').
    split; [exact (famAtSelf IHFAM) |].
    unfold IHFAM, ihEl, ihFam, XWV; apply piLam_eq;
      [ exists nn; exact (gIh (ers rho la) Xa (ers rho bf) gd)
      | exact (famAtSelf (upF (nn - j) nn EBn (FB (ers rho la) Xa)))
      | intros v y v' y' Hy;
        exact (upF_ceq (nn - m) nn EC _ _
                 (cohC _ _ _ _
                    (SUBX _ _ _ _
                       (ihIdx_eq k i j (k - i) (k - j) EA EB (ers rho A) FA wB
                          FB nn (nn - j) EBn (ers rho la) Xa v y v' y' Hy))))
      | exact (gih (ers rho la) Xa (ers rho bf) gd)
      | intros v y v' y' Hy ].
    eapply kEqAt_trans;
      [ exact (famAtSelf (upF (nn - m) nn EC
                            (FC (eapp (ers rho bf) v) (SUB v y))))
      | exact (upEl_eq (nn - m) nn EC _ _ _ _ _ _
                 (famAtSelf (FC (eapp (ers rho bf) v) (SUB v y)))
                 (famExp_rel (FC (eapp (ers rho bf) v) (SUB v y)) _ _
                    (reds_wih_beta Sr (ers rho bf) v) (RB v y)))
      | exact (Hxtext v y v' y' Hy) ]. }
  assert (Hrel3 : Rel (SC (esup (ers rho la) (ers rho bf)))
                    (ws (ers rho la) Xa (ers rho bf) SUBB SUBX gd IHval IHvext)
                    (ers (eN3 :: eN2 :: eN1 :: rho) s)).
  { unfold ws, SC.
    rewrite <- (er_wsup_ty k A B C (rsub rho) (ers rho la) (ers rho bf)
                  (ihR Sr (ers rho bf))).
    exact (fundamental_ty _ s (wsup_ty k A B C) ds _ _
             (proj2 (proj2 (proj2 HEcl)))). }
  pose proof (funtm (wih nn k A B C :: wbr k A B :: A :: G) s
                (wsup_ty k A B C) ds _ _ HEcl m _ _ _
                (xs (ers rho la) Xa (ers rho bf) SUBB SUBX gd IHval IHvext)
                (Ds (ers rho la) Xa (ers rho bf) SUBB SUBX gd IHval IHvext)
                _ _ _ vs Dvs (famAtSelf _) Hrel3) as Hstepcmp.
  rewrite Ers3.
  exists (SC (esup (ers rho la) (ers rho bf))),
    (FC (esup (ers rho la) (ers rho bf)) XW),
    (wRecS k (ers rho A) B0 (upF (k - i) k EA FA) wB
       (fun u x => upF (k - j) k EB (FB u x)) redB cohB gW m Sr
       (fun w1 _ => SC w1) FC cohC
       (stepOf k i j (k - i) (k - j) EA EB (ers rho A) FA B0 wB FB redB cohB gW
          m SC FC Sr ws xs redS)
       stepSrel (esup (ers rho la) (ers rho bf)) XW), vs.
  split; [split; [split |] |].
  - exact (isubst_ITy rho (sup k A B la bf) k (ers rho (wt k A B)) WF
             (esup (ers rho la) (ers rho bf)) XW eq_refl Dsup C m _ _
             (DC _ XW)).
  - exact Dwrec.
  - exact Dsub3.
  - apply (proj2 (kRel_same _ _ _ _ _)).
    eapply kRel_trans; [exact Hcomp |].
    unfold stepOf.
    eapply kRel_trans;
      [ split; [exact (famAtSelf _) | apply famExp_rel] | exact Hstepcmp ].
Qed.

(* ---- the computation rule ---- *)
Lemma isem_wrec_sup G k i j m nn A B C s la bf
  (Hik : i <= k) (Hjk : j <= k) (Hjn : j <= nn) (Hmn : m <= nn)
  (En : nn = Nat.max j m) (W : Rules.wfc G)
  (dAt : ty G A (UU i)) (dBt : ty (A :: G) B (UU j))
  (dCt : ty (wt k A B :: G) C (UU m))
  (dbr : ty (A :: G) (wbr k A B) (UU k))
  (dih : ty (wbr k A B :: A :: G) (wih nn k A B C) (UU nn))
  (ds : ty (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (da : ty G la A) (df : ty G bf (pi k (B [la..]) ((wt k A B) ⟨↑⟩)))
  (IHA : ITot G A (UU i)) (IHB : ITot (A :: G) B (UU j))
  (IHC : ITot (wt k A B :: G) C (UU m))
  (IHs : ITot (wih nn k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C))
  (IHa : ITot G la A)
  (IHf : ITot G bf (pi k (B [la..]) ((wt k A B) ⟨↑⟩))) :
  ISem G (wrec A B C s (sup k A B la bf))
       (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])
       (C [(sup k A B la bf)..]).
Proof.
  pose proof (t_sup G k i j A B la bf Hik Hjk dAt dBt da df) as dsup.
  pose proof (t_wrec G k i j m nn A B C s (sup k A B la bf) Hik Hjk Hjn Hmn En
                dAt dBt dCt dbr dih ds dsup) as dL.
  assert (fL : FunTm G (wrec A B C s (sup k A B la bf)))
    by exact (funtm G (wrec A B C s (sup k A B la bf))
                (C [(sup k A B la bf)..]) dL).
  assert (fR : FunTm G (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])).
  { destruct (ty_wrec_sup_rhs G k i j m nn A B C s la bf W Hik Hjk Hjn Hmn En
                dAt dBt dCt dbr dih ds da df) as [dR].
    exact (funtm G (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])
             (C [(sup k A B la bf)..]) dR). }
  assert (gR : forall rho, EnvRelOf G rho rho ->
             Rel (ers rho (C [(sup k A B la bf)..]))
               (ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ]))
               (ers rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ]))).
  { intros rho0 HE.
    destruct (ty_wrec_sup_rhs G k i j m nn A B C s la bf W Hik Hjk Hjn Hmn En
                dAt dBt dCt dbr dih ds da df) as [dR].
    exact (LTm_of_ty G (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ])
             (C [(sup k A B la bf)..]) dR rho0 rho0 HE). }
  assert (fT : FunTm G (C [(sup k A B la bf)..])).
  { destruct (ty_subst1 G (wt k A B) C (UU m) (sup k A B la bf) dCt dsup)
      as [d].
    exact (FunTm_of_ty G (C [(sup k A B la bf)..]) m d). }
  split.
  - split.
    + exact (itot_wrec G A B C s (sup k A B la bf) k i j m nn Hik Hjk Hjn Hmn
               En dAt dBt dCt dbr dih ds dsup IHA IHB IHC IHs
               (itot_sup G A B la bf k i j Hik Hjk dAt dBt da df
                  IHA IHB IHa IHf)).
    + intros rho Hrho k' F DCw.
      destruct (wrec_sup_data G A B C s la bf k i j m nn Hik Hjk Hjn Hmn En
                  dAt dBt dCt dbr dih ds da df IHA IHB IHC IHs IHa IHf
                  rho Hrho) as [S1 [F1 [v1 [v2 [[[DT Dv1] Dv2] Hmid]]]]].
      assert (ES1 : S1 = ers rho (C [(sup k A B la bf)..]))
        by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      pose proof (ity_lvl rho rho eq_refl (C [(sup k A B la bf)..]) m _ F1 k' _
                    F DT DCw) as Ek; subst k'.
      pose proof (ity_same_ceq G (C [(sup k A B la bf)..]) fT rho Hrho m F1 F
                    DT DCw) as P.
      exists (kto (kAt F1) (kAt F) (famAtWf F1) (famAtWf F) P _ v2).
      exact (i_conv rho (s [ wih_val nn k A B C s la bf .: (bf .: la ..) ]) m
               _ F1 _ F _ v2 P Dv2).
  - intros rho Hrho k' F DCw x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho Hrho) as HEself.
    destruct (wrec_sup_data G A B C s la bf k i j m nn Hik Hjk Hjn Hmn En
                dAt dBt dCt dbr dih ds da df IHA IHB IHC IHs IHa IHf rho Hrho)
      as [S1 [F1 [v1 [v2 [[[DT Dv1] Dv2] Hmid]]]]].
    assert (ES1 : S1 = ers rho (C [(sup k A B la bf)..]))
      by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    pose proof (ity_lvl rho rho eq_refl (C [(sup k A B la bf)..]) m _ F1 k' _ F
                  DT DCw) as Ek; subst k'.
    pose proof (ity_same_ceq G (C [(sup k A B la bf)..]) fT rho Hrho m F F1
                  DCw DT) as P.
    pose proof (fL rho rho HEself m _ F _ x Dx _ F1 _ v1 Dv1 P
                  (LTm_of_ty G (wrec A B C s (sup k A B la bf))
                     (C [(sup k A B la bf)..]) dL rho rho HEself)) as H1.
    pose proof (fR rho rho HEself m _ F1 _ v2 Dv2 _ F _ y Dy (knsymU _ _ P)
                  (gR rho HEself)) as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans;
      [ exact (proj1 (kRel_same F1 _ _ _ _) Hmid) | exact H2 ].
Qed.

(* ================================================================== *)
(* THEOREM 9.2.                                                        *)
(*                                                                    *)
(* One induction, on the CONVERSION judgement's scheme: `c_refl` turns  *)
(* a typing derivation into a conversion, so `ISem`'s first component   *)
(* is the term's totality and the typing half needs no separate         *)
(* induction.  The context's well-formedness travels in the motive --   *)
(* no rule but the structural ones carries a `wfc` premise, and every   *)
(* rule has at least one premise in the SAME context, so `wfc G` is     *)
(* read off that premise's own conclusion.                             *)
(* ================================================================== *)

Scheme wfc_rect2 := Induction for Rules.wfc Sort Type
  with ty_rect2 := Induction for ty Sort Type
  with cv_rect2 := Induction for cv Sort Type.

Theorem fund_cv : forall G t u A (c : cv G t u A),
  (Rules.wfc G * ISem G t u A)%type.
Proof.
  apply (cv_rect2 (fun G _ => Rules.wfc G)
           (fun G t A _ => (Rules.wfc G * ITot G t A)%type)
           (fun G t u A _ => (Rules.wfc G * ISem G t u A)%type)).
  (* ---- wfc ---- *)
  - exact w_nil.
  - intros G A k W IHW dA IHA; exact (w_cons G A k W dA).
  (* ---- ty ---- *)
  - intros G i A W IHW Hl; exact (W, itot_var G i A W Hl).
  - intros G t A B k dt [W IHt] dA [_ IHA] dB [_ IHB] cAB [_ [[_ _] Hc]];
      exact (W, itot_conv G t A B k dA dB IHt IHA IHB Hc).
  - intros G k j Hjk W IHW; exact (W, itot_univ G W k j Hjk).
  - intros G j A dA [W IHA]; exact (W, itot_up G A j W dA IHA).
  - intros G j A t dA [W IHA] dt [_ IHt];
      exact (W, itot_uptm G A t j dA dt IHA IHt).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, itot_pi G A B k i j W Hik Hjk dA dB IHA IHB).
  - intros G k i j A B t Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt];
      exact (W, itot_lam G A B t k i j Hik Hjk dA dB dt IHA IHB IHt).
  - intros G k i j A B f u Hik Hjk dA [W IHA] dB [_ IHB] df [_ IHf] du [_ IHu];
      exact (W, itot_app G A B f u k i j Hik Hjk dA dB df du IHA IHB IHf IHu).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, itot_sig G A B k i j W Hik Hjk dA dB IHA IHB).
  - intros G k i j A B t u Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, itot_pair G A B t u k i j Hik Hjk dA dB dt du
               IHA IHB IHt IHu).
  - intros G k i j A B p Hik Hjk dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, itot_fst G A B p k i j Hik Hjk dA dB dp IHA IHB IHp).
  - intros G k i j A B p Hik Hjk dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, itot_snd G A B p k i j Hik Hjk dA dB dp IHA IHB IHp).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, itot_wt G A B k i j W Hik Hjk dA dB IHA IHB).
  - intros G k i j A B a f Hik Hjk dA [W IHA] dB [_ IHB] da [_ IHa]
      df [_ IHf];
      exact (W, itot_sup G A B a f k i j Hik Hjk dA dB da df
               IHA IHB IHa IHf).
  - intros G k i j m n A B C s w Hik Hjk Hjn Hmn En dA [W IHA] dB [_ IHB]
      dC [_ IHC] dbr [_ IHbr] dih [_ IHih] ds [_ IHs] dw [_ IHw];
      exact (W, itot_wrec G A B C s w k i j m n Hik Hjk Hjn Hmn En
               dA dB dC dbr dih ds dw IHA IHB IHC IHs IHw).
  - intros G k W IHW; exact (W, itot_nat G W k).
  - intros G k W IHW; exact (W, itot_zero G W k).
  - intros G k n dn [W IHn]; exact (W, itot_succ G W k n IHn).
  - intros G C z s n k j dC [_ IHC] dz [W IHz] ds [_ IHs] dn [_ IHn];
      exact (W, itot_natrec G C z s n k j dC dz ds dn IHC IHz IHs IHn).
  - intros G k W IHW; exact (W, itot_prop G W k).
  - intros G k j p Hjk dp [W IHp]; exact (W, itot_prf G k j p Hjk W dp IHp).
  - intros G A p j k dA [W IHA] dp [_ IHp];
      exact (W, itot_all G A p j k W dA dp IHA IHp).
  - intros G A p t j k dA [W IHA] dp [_ IHp] dt [_ IHt];
      exact (W, itot_plam G A p t j k dA dp dt IHA IHp IHt).
  - intros G A p f u j k dA [W IHA] dp [_ IHp] df [_ IHf] du [_ IHu];
      exact (W, itot_papp G A p f u j k dA dp df du IHA IHp IHf IHu).
  - intros G k W IHW; exact (W, itot_false G W k).
  - intros G T e k j dT [W IHT] de [_ IHe]; exact (W, itot_absurd G T j e IHe).
  (* ---- cv ---- *)
  - intros G t A d [W IHd]; exact (W, isem_refl G t A d IHd).
  - intros G t u A c [W IHc]; exact (W, isem_sym G t u A IHc).
  - intros G t u v A c1 [W IH1] c2 [_ IH2];
      exact (W, isem_trans G t u v A IH1 IH2).
  - intros G t u A B k c [W IHc] dA [_ IHA] dB [_ IHB] cAB [_ [[_ _] Hc]];
      exact (W, isem_conv G t u A B k dA dB IHc IHA IHB Hc).
  - intros G j p e e' dp [W IHp] de [_ IHe] de' [_ IHe'];
      exact (W, isem_prf_irr G j p e e' IHe IHe').
  - intros G j A A' dA [W IHA] dA' [_ IHA'] cA [_ [[_ _] HcA]];
      exact (W, isem_up G A A' j W dA dA' cA IHA IHA' HcA).
  - intros G j A t t' dA [W IHA] dt [_ IHt] dt' [_ IHt'] ct [_ [[_ _] Hct]];
      exact (W, isem_uptm G A t t' j W dA dt dt' ct IHA IHt IHt' Hct).
  (* the lift's computation rules *)
  - intros G k j Hjk W IHW; exact (W, isem_up_univ G k j Hjk W).
  - intros G k W IHW; exact (W, isem_up_nat G k W).
  - intros G k W IHW; exact (W, isem_up_prop G k W).
  - intros G k j p Hjk dp [W IHp]; exact (W, isem_up_prf G k j p Hjk W dp IHp).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, isem_up_pi G k i j A B Hik Hjk W dA dB IHA IHB).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, isem_up_sig G k i j A B Hik Hjk W dA dB IHA IHB).
  - intros G k i j A B Hik Hjk dA [W IHA] dB [_ IHB];
      exact (W, isem_up_w G k i j A B Hik Hjk W dA dB IHA IHB).
  (* the congruences and the computation rules *)
  - intros G k i j A A' B B' Hik Hjk dA [W IHA] dB [_ IHB] dA' [_ IHA']
      dB' [_ IHB'] cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]];
      exact (W, isem_pi G A A' B B' k i j W Hik Hjk dA dB dA' dB' cA cB
               IHA IHB IHA' IHB' HcA HcB).
  - intros G k i j A A' B B' t t' Hik Hjk dA [W IHA] dB [_ IHB] dA' [_ IHA']
      dB' [_ IHB'] cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]] dt [_ IHt]
      dt' [_ IHt'] ct [_ [[_ IHt2] Hct]];
      exact (W, isem_lam G k i j A A' B B' t t' Hik Hjk W dA dB dA' dB' cA cB
               dt dt' ct IHA IHB IHA' IHB' HcA HcB IHt IHt2 IHt' Hct).
  - intros G k i j A B f f' u u' Hik Hjk dA [W IHA] dB [_ IHB] df [_ IHf]
      df' [_ IHf'] cf [_ [[_ _] Hcf]] du [_ IHu] du' [_ IHu']
      cu [_ [[_ _] Hcu]];
      exact (W, isem_app G k i j A B f f' u u' Hik Hjk W dA dB df df' du du'
               cf cu IHA IHB IHf IHf' IHu IHu' Hcf Hcu).
  - intros G k i j A B t u Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_beta G k i j A B t u Hik Hjk W dA dB dt du
               IHA IHB IHt IHu).
  - intros G k i j A B f Hik Hjk dA [W IHA] dB [_ IHB] df [_ IHf];
      exact (W, isem_eta G k i j A B f Hik Hjk W dA dB df IHA IHB IHf).
  - intros G k i j A A' B B' Hik Hjk dA [W IHA] dB [_ IHB] dA' [_ IHA']
      dB' [_ IHB'] cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]];
      exact (W, isem_sig G A A' B B' k i j W Hik Hjk dA dB dA' dB' cA cB
               IHA IHB IHA' IHB' HcA HcB).
  - intros G k i j A B t t' u u' Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt]
      dt' [_ IHt'] ct [_ [[_ _] Hct]] du [_ IHu] du' [_ IHu']
      cu [_ [[_ _] Hcu]];
      exact (W, isem_pair G k i j A B t t' u u' Hik Hjk W dA dB dt dt' ct
               du du' cu IHA IHB IHt IHt' Hct IHu IHu' Hcu).
  - intros G k i j A B p p' Hik Hjk dA [W IHA] dB [_ IHB] dp [_ IHp]
      dp' [_ IHp'] cp [_ [[_ _] Hcp]];
      exact (W, isem_fst G k i j A B p p' Hik Hjk W dA dB dp dp' cp
               IHA IHB IHp IHp' Hcp).
  - intros G k i j A B p p' Hik Hjk dA [W IHA] dB [_ IHB] dp [_ IHp]
      dp' [_ IHp'] cp [_ [[_ _] Hcp]];
      exact (W, isem_snd G k i j A B p p' Hik Hjk W dA dB dp dp' cp
               IHA IHB IHp IHp' Hcp).
  - intros G k i j A B t u Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_fst_beta G k i j A B t u Hik Hjk W dA dB dt du
               IHA IHB IHt IHu).
  - intros G k i j A B t u Hik Hjk dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_snd_beta G k i j A B t u Hik Hjk W dA dB dt du
               IHA IHB IHt IHu).
  - intros G k i j A B p Hik Hjk dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, isem_surj G k i j A B p Hik Hjk W dA dB dp IHA IHB IHp).
  (* W *)
  - intros G k i j A A' B B' Hik Hjk dA [W IHA] dB [_ IHB] dA' [_ IHA']
      dB' [_ IHB'] cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]];
      exact (W, isem_w G A A' B B' k i j W Hik Hjk dA dB dA' dB' cA cB
               IHA IHB IHA' IHB' HcA HcB).
  - intros G k i j A B a a' f f' Hik Hjk dA [W IHA] dB [_ IHB] da [_ IHa]
      da' [_ IHa'] ca [_ [[_ _] Hca]] df [_ IHf] df' [_ IHf']
      cf [_ [[_ _] Hcf]];
      exact (W, isem_sup G k i j A B a a' f f' Hik Hjk W dA dB da da' ca
               df df' cf IHA IHB IHa IHa' Hca IHf IHf' Hcf).
  - intros G k i j m n A B C C' s s' w w' Hik Hjk Hjn Hmn En dA [W IHA]
      dB [_ IHB] dC [_ IHC] dC' [_ IHC'] cC [_ [[_ _] HcC]] dbr [_ IHbr]
      dih [_ IHih] ds [_ IHs] ds' [_ IHs'] cs [_ [[_ _] Hcs]] dw [_ IHw]
      dw' [_ IHw'] cw [_ [[_ _] Hcw]];
      exact (W, isem_wrec G k i j m n A B C C' s s' w w' Hik Hjk Hjn Hmn En W
               dA dB dC dC' cC dbr dih ds ds' cs dw dw' cw
               IHA IHB IHC IHC' HcC IHs IHs' Hcs IHw IHw' Hcw).
  - intros G k i j m n A B C s a f Hik Hjk Hjn Hmn En dA [W IHA] dB [_ IHB]
      dC [_ IHC] dbr [_ IHbr] dih [_ IHih] ds [_ IHs] da [_ IHa] df [_ IHf];
      exact (W, isem_wrec_sup G k i j m n A B C s a f Hik Hjk Hjn Hmn En W
               dA dB dC dbr dih ds da df IHA IHB IHC IHs IHa IHf).
  (* N *)
  - intros G k n n' dn [W IHn] dn' [_ IHn'] cn [_ [[_ _] Hcn]];
      exact (W, isem_succ G k n n' W dn dn' cn IHn IHn' Hcn).
  - intros G C C' z z' s s' n n' k j dC [_ IHC] dC' [_ IHC']
      cC [_ [[_ _] HcC]] dz [W IHz] dz' [_ IHz'] cz [_ [[_ _] Hcz]]
      ds [_ IHs] ds' [_ IHs'] cs [_ [[_ _] Hcs]] dn [_ IHn] dn' [_ IHn']
      cn [_ [[_ _] Hcn]];
      exact (W, isem_natrec G C C' z z' s s' n n' k j W dC dC' cC dz dz' cz
               ds ds' cs dn dn' cn IHC IHC' HcC IHz IHz' Hcz IHs IHs' Hcs
               IHn IHn' Hcn).
  - intros G C z s k j dC [_ IHC] dz [W IHz] ds [_ IHs];
      exact (W, isem_rec_zero G C z s k j W dC dz ds IHC IHz IHs).
  - intros G C z s n k j dC [_ IHC] dz [W IHz] ds [_ IHs] dn [_ IHn];
      exact (W, isem_rec_succ G C z s n k j W dC dz ds dn IHC IHz IHs IHn).
  (* Prop *)
  - intros G k j p p' Hjk dp [W IHp] dp' [_ IHp'] cp [_ [[_ _] Hcp]];
      exact (W, isem_prf G k j p p' Hjk W dp dp' cp IHp IHp' Hcp).
  - intros G A A' p p' j k dA [W IHA] dp [_ IHp] dA' [_ IHA'] dp' [_ IHp']
      cA [_ [[_ _] HcA]] cp2 [_ [[_ _] Hcp]];
      exact (W, isem_all G A A' p p' j k W dA dp dA' dp' cA cp2
               IHA IHp IHA' IHp' HcA Hcp).
Qed.

(* Totality, by reflexivity of conversion. *)
Theorem fund_tot G t A (d : ty G t A) : (Rules.wfc G * ITot G t A)%type.
Proof.
  destruct (fund_cv G t t A (c_refl G t A d)) as [W [[Ht _] _]].
  exact (W, Ht).
Qed.
