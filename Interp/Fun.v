From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim
  Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam
  Interp.PiFam Interp.SigFam Interp.WFam Interp.Univ Interp.Env Interp.Elem
  Interp.PiEl Interp.SigEl Interp.WEl Interp.Rec Interp.Lift Interp.LiftN
  Interp.Def Interp.Inv Interp.Ctx Interp.Subst.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* FUNCTIONALITY of the interpretation.

   Two readings of one syntactic type in two related environments give EQUAL
   families; two readings of one term give related values.  This is what the
   fundamental lemma needs at every rule with two subderivations of the same
   subject, and what the blueprint's 9.1 plans for ("define it as an inductive
   relation and prove functionality").

   Two features of the statement are forced.

   It is PROP-VALUED.  `kceq` and `kRel` are Props, so the motive may
   existentially quantify the dependent data -- the family, the value -- that
   makes ITm impossible to invert in Type (see Interp/Def.v's header).  That is
   the only reason the induction goes through at all.

   It carries the layer-1 relatedness of the two realisers as a HYPOTHESIS, at
   the level-agnostic strength `tyeq`.  Nothing at layer 2 can supply it: it is
   the statement that the two erasures of one syntactic type are equal types,
   and only the layer-1 fundamental lemma proves that.  `tyeq` rather than
   `eqty k` because the universe-lift clause interprets its subject at level k
   while concluding at level S k, and a level-indexed hypothesis would not
   descend. *)

Definition FTy (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Prop :=
  forall rho' w' (F' : kUFam k w'),
    EnvRel rho rho' -> tyeq w w' -> ITy rho' A k w' F' -> kceq (kAt F) (kAt F').

Definition FTm (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy)
               (w : etm) (x : kElAt F w) : Prop :=
  forall rho' Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w'),
    EnvRel rho rho' -> kceq (kAt F) (kAt F') -> Rel Sy' w w' ->
    ITm rho' t k Sy' F' w' x' -> kRel F w x F' w' x'.

(* Small layer-1 facts the clauses below want by name. *)
Lemma good_ty_prop : Good_ty eprop.
Proof. exists 0; apply eqty_prop; apply eval_whnf, whnf_prop. Qed.

Lemma ev_pi_self A0 B0 : eval (epi A0 B0) (epi A0 B0).
Proof. apply eval_whnf, whnf_pi. Qed.

Lemma ev_sig_self A0 B0 : eval (esig A0 B0) (esig A0 B0).
Proof. apply eval_whnf, whnf_sig. Qed.

Lemma ev_w_self A0 B0 : eval (ew A0 B0) (ew A0 B0).
Proof. apply eval_whnf, whnf_w. Qed.

Lemma ev_prf_self p : eval (eprf p) (eprf p).
Proof. apply eval_whnf, whnf_prf. Qed.

(* ------------------------------------------------------------------ *)
(* The clauses whose family is fixed by the clause itself.            *)
(* ------------------------------------------------------------------ *)

Lemma fun_nat rho k : FTy rho (nat_ k) k enat (natFam k).
Proof.
  intros rho' w' F' HR Hty D'; apply knsymU.
  exact (ity_nat_inv rho' (nat_ k) k w' F' D').
Qed.

Lemma fun_prop rho k : FTy rho (prop k) k eprop (propFam k).
Proof.
  intros rho' w' F' HR Hty D'; apply knsymU.
  exact (ity_prop_inv rho' (prop k) k w' F' D').
Qed.

(* A universe: the reading is the d-fold lift of the universe its own level
   adds, and the gap is determined -- both readings are of the same syntax,
   whose annotation IS the level.  The two gap equations are then equal by UIP
   at nat (`upF_pirr`). *)
Lemma fun_univ rho k d m (E : d + S m = k) :
  FTy rho (univ k m) k (euniv m) (upF d k E (univFam m)).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_univ_ceq rho' (univ k m) k w' F' D') as [d' [E' H]].
  assert (Ed : d' = d) by lia; subst d'.
  rewrite (upF_pirr d k E' E (univFam m)) in H.
  apply knsymU; exact H.
Qed.

(* The universe lift: the level-agnostic hypothesis descends unchanged,
   because `up` leaves the realiser alone. *)
Lemma fun_up rho A k w (F0 : kUFam k w) (IHA : FTy rho A k w F0) :
  FTy rho (up k A) (S k) w (famLiftK F0).
Proof.
  intros rho' w' F' HR Hty D'.
  pose proof (ity_up_inv rho' (up k A) (S k) w' F' D') as Hup.
  cbn [UpDec] in Hup.
  destruct Hup as [F1 [[Ej DA'] Hc']].
  eapply ktrU;
    [ exact (famAtWf (famLiftK F0)) | exact (famAtWf (famLiftK F1))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  apply famLiftK_ceq.
  exact (IHA rho' w' F1 HR Hty DA').
Qed.

(* ------------------------------------------------------------------ *)
(* And the clause that reads an arbitrary term of a universe as a type. *)
(* This is the one place that needs the layer-1 equality AT THE LEVEL   *)
(* of the family, because the universe's own equality contains it; the  *)
(* hypothesis is level-agnostic, so it has to be restricted -- which is *)
(* exactly what Layer1/Elim.v's eqty_restrict does.                     *)
(* ------------------------------------------------------------------ *)

Lemma fun_of rho A k w (v : kElAt (univFam k) w) (nf : notFormer A)
  (IHv : FTm rho A (S k) (euniv k) (univFam k) w v) :
  FTy rho A k w (elFam v).
Proof.
  intros rho' w' F' HR Hty D'.
  pose proof (ity_of_inv rho' A k w' F' D') as Hof.
  assert (Hk : eqty k w w').
  { destruct Hty as [n Hn].
    exact (eqty_restrict k n w w' Hn (uf_ty (elFam v)) (uf_ty F')). }
  assert (Hrel : Rel (euniv k) w w').
  { apply (Rel_univ_intro (euniv k) k w w');
      [ exact (univ_good_ty (S k) k (euniv k) (Nat.lt_succ_diag_r k)
                 (eval_whnf _ (whnf_univ k)))
      | apply eval_whnf, whnf_univ
      | exact Hk ]. }
  destruct A; cbn [notFormer] in nf; cbn [OfDec] in Hof;
    try (destruct nf).
  all: (destruct Hof as [v' [Dv' Ec]];
        eapply ktrU;
          [ exact (famAtWf (elFam v)) | exact (famAtWf (elFam v'))
          | exact (famAtWf F') | | apply knsymU; exact Ec ];
        apply (uEq_at v v');
        exact (kRel_at (IHv rho' (euniv k) (univFam k) w' v' HR
                          (famAtSelf (univFam k)) Hrel Dv'))).
Qed.

(* ------------------------------------------------------------------ *)
(* The term clauses need the SECOND derivation inverted, and ITm has    *)
(* three clauses that are not directed by the subject's syntax, so       *)
(* every inversion has to allow for them: i_proof, i_ty and i_conv.     *)
(* Each is handled once and for all here.                               *)
(* ------------------------------------------------------------------ *)

(* i_proof.  A Prf-family relates ALL of its elements, because the Prf-code's
   equality is the layer-1 relatedness of the realisers and nothing else.
   Stating it as a property of the family rather than as "the family is a
   prfF" keeps it cast-free and makes it transfer along equalities. *)
Definition TotalFam {k u} (F : kUFam k u) : Prop :=
  forall w (x : kElAt F w) w' (x' : kElAt F w'), Rel u w w' -> kEqAt F w x F w' x'.

Lemma prf_total k j wp (xp : kElAt (propFam j) wp) : TotalFam (prfF k xp).
Proof. intros w x w' x' Hr; apply prfEq_of; exact Hr. Qed.

(* Totality transfers along an equality of families, which is what makes it
   usable after i_conv has moved the family.  In v1 this had to go through the
   transport in both directions; here the coercion's coherence does it. *)
Lemma TotalFam_ceq {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) : TotalFam F -> TotalFam F'.
Proof.
  intros HT w y w' y' Hr.
  (* pull both elements back along P, relate them there, and push forward *)
  assert (Hrr : Rel u w w').
  { destruct (ceq_ty F F' P) as [n Hn].
    eapply Rel_cast; [apply eqty_sym; exact Hn | exact Hr]. }
  eapply ktrE;
    [ exact (famAtWf F') | exact (famAtWf F) | exact (famAtWf F')
    | apply knsymU; exact P
    | exact (kto_coh (kAt F') (kAt F) (famAtWf F') (famAtWf F)
               (knsymU (kAt F) (kAt F') P) w y) |].
  eapply ktrE;
    [ exact (famAtWf F) | exact (famAtWf F) | exact (famAtWf F')
    | exact (famAtSelf F)
    | exact (HT w (kto (kAt F') (kAt F) (famAtWf F') (famAtWf F)
                     (knsymU (kAt F) (kAt F') P) w y)
               w' (kto (kAt F') (kAt F) (famAtWf F') (famAtWf F)
                     (knsymU (kAt F) (kAt F') P) w' y') Hrr)
    | apply knsym;
      exact (kto_coh (kAt F') (kAt F) (famAtWf F') (famAtWf F)
               (knsymU (kAt F) (kAt F') P) w' y') ].
Qed.

(* What the i_proof case of every clause then reduces to. *)
Lemma kRel_of_total {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : kceq (kAt F) (kAt F')) (HT : TotalFam F') w (x : kElAt F w)
  w' (x' : kElAt F' w') : Rel u' w w' -> kRel F w x F' w' x'.
Proof.
  intros Hr; split; [exact P |].
  (* the value in hand, moved into F', is related to x' because F' relates
     all of its elements *)
  eapply ktrE;
    [ exact (famAtWf F) | exact (famAtWf F') | exact (famAtWf F')
    | exact P
    | exact (kto_coh (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x)
    | apply HT; exact Hr ].
Qed.

(* i_conv.  A conversion on the SECOND derivation is absorbed by composing
   with the coercion. *)
Lemma kRel_conv_r {k u u1 u2} (F : kUFam k u) (F1 : kUFam k u1) (F2 : kUFam k u2)
  (P : kceq (kAt F1) (kAt F2)) w (x : kElAt F w) w' (x1 : kElAt F1 w') :
  kRel F w x F1 w' x1 ->
  kRel F w x F2 w' (kto (kAt F1) (kAt F2) (famAtWf F1) (famAtWf F2) P w' x1).
Proof.
  intros H; eapply kRel_trans;
    [ exact H | split; [exact P | apply kto_coh] ].
Qed.

(* i_ty.  Reading a family as an element of the universe and back is the
   identity up to the universe's equality -- the direction Interp/Univ.v does
   NOT give as an equation, because the element carries a proof. *)
Lemma famEl_elFam_rel {k u} (v : kElAt (univFam k) u) :
  kEqAt (univFam k) u (famEl (elFam v)) (univFam k) u v.
Proof.
  revert v; cbn; intros [[F e] | [y ne]]; [| exfalso; exact (ne eq_refl)].
  exact (uEq_of F F (uf_ty F) (fun v h pf v' h' pf' => uf_coh F v h pf v' h' pf')).
Qed.

(* Moving an element along the family's own equality does nothing, up to that
   equality.  Every canonical-form statement below is phrased with a
   coercion, so this is what discharges it at the clause's own family.  v1
   needed the carried transport's identity law (`uf_idp`) here; v2's coercion
   has `kto_coh` and nothing else. *)
Lemma kto_self {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (kto (kAt F) (kAt F) (famAtWf F) (famAtWf F) (famAtSelf F) w x) F w x.
Proof.
  apply kEqAt_sym; exact (kto_coh (kAt F) (kAt F) (famAtWf F) (famAtWf F)
                            (famAtSelf F) w x).
Qed.

(* ------------------------------------------------------------------ *)
(* THE CANONICAL-FORM DECODER.                                        *)
(*                                                                    *)
(* ITm cannot be inverted by `destruct` at a fixed subject, because the *)
(* subject is an index and three clauses -- i_ty, i_proof, i_conv -- do *)
(* not constrain it.  The way round is a decoder: a family defined by    *)
(* matching on the subject, provable for every clause, whose branch at   *)
(* each shape says SEMANTICALLY what the value is.  Semantically, not by  *)
(* equations: the indices are dependent data with no decidable equality,  *)
(* so equations would need casts, whereas saying that the value, once     *)
(* moved into the shape's canonical family, IS the canonical element      *)
(* needs none.                                                           *)
(*                                                                      *)
(* It is TYPE-valued, not Prop-valued, because its branches mention ITy. *)
(* That costs nothing: what made ITm uninvertible was the need for        *)
(* EQUATIONS between dependent indices, and there are none here.         *)
(*                                                                      *)
(* Against v1: every branch is one `Shaped` -- some data, and the value in *)
(* hand IS the canonical value that data determines.  v1 wrote the two     *)
(* stability lemmas out at each of its fifteen shapes; here they are      *)
(* proved once, about `Shaped`.                                          *)
(* ------------------------------------------------------------------ *)

(* The value in hand IS the canonical one, up to the coercion between the two
   families.  This is the only place a coercion appears, which is why nothing
   below needs a cast. *)
Definition IsVal {k Sy Syc} (F : kUFam k Sy) (w : etm) (x : kElAt F w)
  (Fc : kUFam k Syc) (wc : etm) (xc : kElAt Fc wc) : Type :=
  { P : kceq (kAt F) (kAt Fc) &
        kEqAt Fc w (kto (kAt F) (kAt Fc) (famAtWf F) (famAtWf Fc) P w x)
              Fc wc xc }.

Lemma IsVal_self {k Sy} (F : kUFam k Sy) w (x : kElAt F w) : IsVal F w x F w x.
Proof. exists (famAtSelf F); apply kto_self. Qed.

(* Two coercions out of one family compose, up to the equality: both values
   are related to the element they came from.  v1 proved this from the
   transport's functoriality law; here it is two coherences. *)
Lemma kto_after {k u u' c} (F : kUFam k u) (F' : kUFam k u') (C : kUFam k c)
  (P : kceq (kAt F) (kAt F')) (Q : kceq (kAt F) (kAt C))
  (R : kceq (kAt F') (kAt C)) w (x : kElAt F w) :
  kEqAt C w (kto (kAt F') (kAt C) (famAtWf F') (famAtWf C) R w
               (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x))
        C w (kto (kAt F) (kAt C) (famAtWf F) (famAtWf C) Q w x).
Proof.
  eapply ktrE;
    [ exact (famAtWf C) | exact (famAtWf F) | exact (famAtWf C)
    | apply knsymU; exact Q
    | apply knsym;
      eapply ktrE;
        [ exact (famAtWf F) | exact (famAtWf F') | exact (famAtWf C)
        | exact P | apply kto_coh | apply kto_coh ]
    | apply kto_coh ].
Qed.

Lemma IsVal_conv {k Sy Sy' Syc} (F : kUFam k Sy) (F' : kUFam k Sy')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w)
  (Fc : kUFam k Syc) wc (xc : kElAt Fc wc) :
  IsVal F w x Fc wc xc ->
  IsVal F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x) Fc wc xc.
Proof.
  intros [Q HQ].
  exists (ktrU (kAt F') (kAt F) (kAt Fc) (famAtWf F') (famAtWf F) (famAtWf Fc)
            (knsymU (kAt F) (kAt F') P) Q).
  eapply kEqAt_trans; [exact (famAtSelf Fc) | apply kto_after | exact HQ].
Qed.

Lemma IsVal_resp {k Sy Syc} (F : kUFam k Sy) w (x x2 : kElAt F w)
  (Fc : kUFam k Syc) wc (xc : kElAt Fc wc) :
  kEqAt F w x F w x2 -> IsVal F w x Fc wc xc -> IsVal F w x2 Fc wc xc.
Proof.
  intros HE [Q HQ]; exists Q.
  eapply kEqAt_trans; [exact (famAtSelf Fc) | | exact HQ].
  exact (kto_eq (kAt F) (kAt Fc) (famAtWf F) (famAtWf Fc) Q
           (kAt F) (kAt Fc) (famAtWf F) (famAtWf Fc) Q w x2 w x
           (famAtSelf F) (kEqAt_sym F w x F w x2 HE)).
Qed.

(* ---- a shape: some data, and the canonical value it determines ---- *)

Record Canon (k : nat) : Type := mkCanon
  { cn_Sy : etm; cn_F : kUFam k cn_Sy; cn_w : etm; cn_x : kElAt cn_F cn_w }.

Definition Shaped {k Sy} (F : kUFam k Sy) (w : etm) (x : kElAt F w)
  (D : Type) (c : D -> Canon k) : Type :=
  { d : D & IsVal F w x (cn_F k (c d)) (cn_w k (c d)) (cn_x k (c d)) }.

Lemma Shaped_conv {k Sy Sy'} (F : kUFam k Sy) (F' : kUFam k Sy')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) D c :
  Shaped F w x D c ->
  Shaped F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x) D c.
Proof. intros [d H]; exists d; apply IsVal_conv; exact H. Qed.

Lemma Shaped_resp {k Sy} (F : kUFam k Sy) w (x x2 : kElAt F w) D c :
  kEqAt F w x F w x2 -> Shaped F w x D c -> Shaped F w x2 D c.
Proof.
  intros HE [d H]; exists d; exact (IsVal_resp F w x x2 _ _ _ HE H).
Qed.

(* ---- the branch at each shape ---- *)

(* A TYPE FORMER, read as an element of the universe above it: the value is the
   family the former's own ITy clause builds.  This is where i_ty lands, and it
   is confined to the formers -- at a subject that is not one, i_ty is composed
   with ity_of and the decoder passes the ITm premise's own branch through
   instead, which is what makes the shape available at every notFormer. *)
Record TyData {rho : Env} {t : tm} {k0 : nat} {w : etm} : Type := {
  ty_F0 : kUFam k0 w; ty_D : ITy rho t k0 w ty_F0 }.
Arguments TyData : clear implicits.

Definition TyVal (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun _ _ _ => Empty_set
  | S k0 => fun F w x =>
      Shaped F w x (TyData rho t k0 w)
        (fun d => mkCanon (S k0) (euniv k0) (univFam k0) w (famEl (ty_F0 d)))
  end.

(* The term lift.  It records the TYPE it lifts, so the branch hands over an
   ITy derivation for it and functionality on types supplies the equality of
   the two readings' families. *)
Record UpTmData {rho : Env} {A t0 : tm} {k0 : nat} {w : etm} : Type := {
  ut_Sy : etm; ut_F : kUFam k0 ut_Sy; ut_x : kElAt ut_F w;
  ut_DA : ITy rho A k0 ut_Sy ut_F;
  ut_D : ITm rho t0 k0 ut_Sy ut_F w ut_x }.
Arguments UpTmData : clear implicits.

Definition UpTmVal (rho : Env) (A t0 : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun _ _ _ => Empty_set
  | S k0 => fun F w x =>
      Shaped F w x (UpTmData rho A t0 k0 w)
        (fun d => mkCanon (S k0) (ut_Sy d) (famLiftK (ut_F d)) w
                    (elLift (ut_F d) w (ut_x d)))
  end.

(* The TYPE lift is a type former like any other: its annotation is the level
   of its subject, so there is nothing left to match on and the branch is
   TyVal's. *)
Definition UpShape (rho : Env) (j : nat) (t0 : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  TyVal rho (up j t0) k Sy.

(* Variables: the head entry for var 0, the tail's derivation for var (S i).
   This is the one shape that is not a `Shaped`: its branch at var 0 speaks of
   the family and the value themselves, through EntryRel. *)
Definition VarShape (rho : Env) (i : nat) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match i, rho return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0, en :: _ => fun F w x => EntryRel (Build_Entry k Sy F w x) en
  | S j, _ :: rho0 => fun F w x =>
      { x0 : kElAt F w &
        (ITm rho0 (var_tm j) k Sy F w x0 * kEqAt F w x F w x0)%type }
  | _, nil => fun _ _ _ => Empty_set
  end.

(* A shape no clause concludes at. *)
Definition NoVal (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun _ _ _ => Empty_set.

(* The level-annotated constants: the annotation IS the level, and recording
   that equation in the branch is what pins the level of a reading without any
   recursion.  `natFam k` and `propFam k` exist at every level, so the branch
   needs no lift and no cast. *)
Definition ZeroVal (kk : nat) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun F w x =>
    Shaped F w x (kk = k)
      (fun _ => mkCanon k enat (natFam k) ezero (natE 0 NatAt_zero)).

Record SuccData {rho : Env} {n : tm} {k : nat} : Type := {
  sc_wn : etm; sc_xn : kElAt (natFam k) sc_wn;
  sc_D : ITm rho n k enat (natFam k) sc_wn sc_xn }.
Arguments SuccData : clear implicits.

Definition SuccVal (rho : Env) (n : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun F w x =>
    Shaped F w x (SuccData rho n k)
      (fun d => mkCanon k enat (natFam k) (esucc (sc_wn d)) (natSucc (sc_xn d))).

Record FalseData {kk k : nat} : Type := {
  fl_g : Good eprop efalse; fl_lvl : kk = k }.
Arguments FalseData : clear implicits.

Definition FalseVal (kk : nat) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun F w x =>
    Shaped F w x (FalseData kk k)
      (fun d => mkCanon k eprop (propFam k) efalse
                  (propElem efalse False (fl_g d))).

(* Impredicative forall.  The domain's level is free -- t_all quantifies over
   it -- so it is existential here, and it is the one level in the decoder that
   the subject does not determine. *)
Record AllData {rho : Env} {jj : nat} {A p : tm} {k : nat} : Type := {
  al_kA : nat; al_wA : etm; al_FA : kUFam al_kA al_wA;
  al_wp : forall u, kElAt al_FA u -> etm;
  al_xp : forall u (y : kElAt al_FA u), kElAt (propFam k) (al_wp u y);
  al_wv : etm; al_g : Good eprop al_wv;
  al_lvl : jj = k;
  al_DA : ITy rho A al_kA al_wA al_FA;
  al_Dp : forall u y,
    ITm (ext rho al_FA u y) p k eprop (propFam k) (al_wp u y) (al_xp u y) }.
Arguments AllData : clear implicits.

Definition AllVal (rho : Env) (jj : nat) (A p : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun F w x =>
    Shaped F w x (AllData rho jj A p k)
      (fun d => mkCanon k eprop (propFam k) (al_wv d)
                  (propElem (al_wv d)
                     (forall u (y : kElAt (al_FA d) u), propVal (al_xp d u y))
                     (al_g d))).

(* ---- the binder shapes.  Their data is a RECORD rather than v1's tower of
   existentials: with two component levels and two gaps there are twenty
   fields, and named projections are what makes the functionality proof and
   the fundamental lemma readable.  Nothing else changes -- a record with one
   constructor destructs exactly as a tower does. ---- *)

Record LamData {rho : Env} {kk : nat} {A B t0 : tm} {k : nat} {w : etm} : Type := {
  ld_i : nat; ld_j : nat; ld_dA : nat; ld_dB : nat;
  ld_EA : ld_dA + ld_i = k; ld_EB : ld_dB + ld_j = k;
  ld_wA : etm; ld_FA : kUFam ld_i ld_wA; ld_B0 : etm;
  ld_wB : forall u, kElAt (upF ld_dA k ld_EA ld_FA) u -> etm;
  ld_FB : forall u (x : kElAt (upF ld_dA k ld_EA ld_FA) u), kUFam ld_j (ld_wB u x);
  ld_redB : forall u x, reds (eapp ld_B0 u) (ld_wB u x);
  ld_cohB : forall u x u' x',
    kEqAt (upF ld_dA k ld_EA ld_FA) u x (upF ld_dA k ld_EA ld_FA) u' x' ->
    kceq (kAt (upF ld_dB k ld_EB (ld_FB u x)))
         (kAt (upF ld_dB k ld_EB (ld_FB u' x')));
  ld_gPi : eqty k (epi ld_wA ld_B0) (epi ld_wA ld_B0);
  ld_wt : forall u, kElAt (upF ld_dA k ld_EA ld_FA) u -> etm;
  ld_xt : forall u x, kElAt (ld_FB u x) (ld_wt u x);
  ld_redt : forall u x, reds (eapp w u) (ld_wt u x);
  ld_xtext : forall u x u' x',
    kEqAt (upF ld_dA k ld_EA ld_FA) u x (upF ld_dA k ld_EA ld_FA) u' x' ->
    kEqAt (upF ld_dB k ld_EB (ld_FB u x)) (ld_wt u x)
            (upEl ld_dB k ld_EB (ld_FB u x) (ld_wt u x) (ld_xt u x))
          (upF ld_dB k ld_EB (ld_FB u' x')) (ld_wt u' x')
            (upEl ld_dB k ld_EB (ld_FB u' x') (ld_wt u' x') (ld_xt u' x'));
  ld_gd : Good (epi ld_wA ld_B0) w;
  ld_lvl : kk = k;
  ld_Ew : w = ers rho (lam kk A B t0);
  ld_Ep : epi ld_wA ld_B0 = ers rho (pi k A B);
  ld_DA : ITy rho A ld_i ld_wA ld_FA;
  ld_DB : forall u x,
    ITy (ext rho ld_FA u (dnEl ld_dA k ld_EA ld_FA u x)) B ld_j (ld_wB u x)
        (ld_FB u x);
  ld_Dt : forall u x,
    ITm (ext rho ld_FA u (dnEl ld_dA k ld_EA ld_FA u x)) t0 ld_j
        (ld_wB u x) (ld_FB u x) (ld_wt u x) (ld_xt u x)
}.
Arguments LamData : clear implicits.

(* the Pi family and the element a lam's data determines *)
Definition ld_PF {rho kk A B t0 k w} (d : LamData rho kk A B t0 k w)
  : kUFam k (epi (ld_wA d) (ld_B0 d)) :=
  piFam k (ld_wA d) (ld_B0 d) (upF (ld_dA d) k (ld_EA d) (ld_FA d)) (ld_wB d)
    (fun u y => upF (ld_dB d) k (ld_EB d) (ld_FB d u y))
    (ld_redB d) (ld_cohB d) (ld_gPi d).

Definition ld_val {rho kk A B t0 k w} (d : LamData rho kk A B t0 k w)
  : kElAt (ld_PF d) w :=
  piLam k (ld_wA d) (ld_B0 d) (upF (ld_dA d) k (ld_EA d) (ld_FA d)) (ld_wB d)
    (fun u y => upF (ld_dB d) k (ld_EB d) (ld_FB d u y))
    (ld_redB d) (ld_cohB d) (ld_gPi d) w (ld_wt d)
    (fun u y => upEl (ld_dB d) k (ld_EB d) (ld_FB d u y) (ld_wt d u y)
                  (ld_xt d u y))
    (ld_redt d) (ld_xtext d) (ld_gd d).

Definition LamVal (rho : Env) (kk : nat) (A B t0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (LamData rho kk A B t0 k w)
    (fun d => mkCanon k (epi (ld_wA d) (ld_B0 d)) (ld_PF d) w (ld_val d)).

(* Application.  Its level is the CODOMAIN's -- that is where t_app puts it --
   while the function's is the Pi's annotation, which the subject does not
   record: hence `ap_kp` is existential here. *)
Record AppData {rho : Env} {A B f a : tm} {k : nat} : Type := {
  ap_kp : nat; ap_i : nat; ap_dA : nat; ap_dB : nat;
  ap_EA : ap_dA + ap_i = ap_kp; ap_EB : ap_dB + k = ap_kp;
  ap_wA : etm; ap_FA : kUFam ap_i ap_wA; ap_B0 : etm;
  ap_wB : forall u, kElAt (upF ap_dA ap_kp ap_EA ap_FA) u -> etm;
  ap_FB : forall u (x : kElAt (upF ap_dA ap_kp ap_EA ap_FA) u), kUFam k (ap_wB u x);
  ap_redB : forall u x, reds (eapp ap_B0 u) (ap_wB u x);
  ap_cohB : forall u x u' x',
    kEqAt (upF ap_dA ap_kp ap_EA ap_FA) u x (upF ap_dA ap_kp ap_EA ap_FA) u' x' ->
    kceq (kAt (upF ap_dB ap_kp ap_EB (ap_FB u x)))
         (kAt (upF ap_dB ap_kp ap_EB (ap_FB u' x')));
  ap_gPi : eqty ap_kp (epi ap_wA ap_B0) (epi ap_wA ap_B0);
  ap_wf : etm;
  ap_xf : kElAt (piFam ap_kp ap_wA ap_B0 (upF ap_dA ap_kp ap_EA ap_FA) ap_wB
                   (fun u y => upF ap_dB ap_kp ap_EB (ap_FB u y))
                   ap_redB ap_cohB ap_gPi) ap_wf;
  ap_wa : etm; ap_xa : kElAt ap_FA ap_wa;
  ap_Ep : epi ap_wA ap_B0 = ers rho (pi ap_kp A B);
  ap_DA : ITy rho A ap_i ap_wA ap_FA;
  ap_DB : forall u x,
    ITy (ext rho ap_FA u (dnEl ap_dA ap_kp ap_EA ap_FA u x)) B k (ap_wB u x)
        (ap_FB u x);
  ap_Df : ITm rho f ap_kp (epi ap_wA ap_B0)
            (piFam ap_kp ap_wA ap_B0 (upF ap_dA ap_kp ap_EA ap_FA) ap_wB
               (fun u y => upF ap_dB ap_kp ap_EB (ap_FB u y))
               ap_redB ap_cohB ap_gPi) ap_wf ap_xf;
  ap_Da : ITm rho a ap_i ap_wA ap_FA ap_wa ap_xa
}.
Arguments AppData : clear implicits.

Definition ap_arg {rho A B f a k} (d : AppData rho A B f a k)
  : kElAt (upF (ap_dA d) (ap_kp d) (ap_EA d) (ap_FA d)) (ap_wa d) :=
  upEl (ap_dA d) (ap_kp d) (ap_EA d) (ap_FA d) (ap_wa d) (ap_xa d).

Definition ap_val {rho A B f a k} (d : AppData rho A B f a k)
  : kElAt (ap_FB d (ap_wa d) (ap_arg d)) (eapp (ap_wf d) (ap_wa d)) :=
  dnEl (ap_dB d) (ap_kp d) (ap_EB d) (ap_FB d (ap_wa d) (ap_arg d))
    (eapp (ap_wf d) (ap_wa d))
    (piApp (ap_kp d) (ap_wA d) (ap_B0 d) (upF (ap_dA d) (ap_kp d) (ap_EA d) (ap_FA d))
       (ap_wB d) (fun u y => upF (ap_dB d) (ap_kp d) (ap_EB d) (ap_FB d u y))
       (ap_redB d) (ap_cohB d) (ap_gPi d) (ap_wf d) (ap_xf d) (ap_wa d) (ap_arg d)).

Definition AppVal (rho : Env) (A B f a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (AppData rho A B f a k)
    (fun d => mkCanon k (ap_wB d (ap_wa d) (ap_arg d))
                (ap_FB d (ap_wa d) (ap_arg d))
                (eapp (ap_wf d) (ap_wa d)) (ap_val d)).

Record PairData {rho : Env} {kk : nat} {A B t0 a : tm} {k : nat} : Type := {
  pd_i : nat; pd_j : nat; pd_dA : nat; pd_dB : nat;
  pd_EA : pd_dA + pd_i = k; pd_EB : pd_dB + pd_j = k;
  pd_wA : etm; pd_FA : kUFam pd_i pd_wA; pd_B0 : etm;
  pd_wB : forall u, kElAt (upF pd_dA k pd_EA pd_FA) u -> etm;
  pd_FB : forall u (x : kElAt (upF pd_dA k pd_EA pd_FA) u), kUFam pd_j (pd_wB u x);
  pd_redB : forall u x, reds (eapp pd_B0 u) (pd_wB u x);
  pd_cohB : forall u x u' x',
    kEqAt (upF pd_dA k pd_EA pd_FA) u x (upF pd_dA k pd_EA pd_FA) u' x' ->
    kceq (kAt (upF pd_dB k pd_EB (pd_FB u x)))
         (kAt (upF pd_dB k pd_EB (pd_FB u' x')));
  pd_gSig : eqty k (esig pd_wA pd_B0) (esig pd_wA pd_B0);
  pd_wt : etm; pd_xt : kElAt pd_FA pd_wt;
  pd_wa : etm;
  pd_xa : kElAt (pd_FB pd_wt (upEl pd_dA k pd_EA pd_FA pd_wt pd_xt)) pd_wa;
  pd_g : Good (esig pd_wA pd_B0) (epair pd_wt pd_wa);
  pd_lvl : kk = k;
  pd_Ep : esig pd_wA pd_B0 = ers rho (sig_ k A B);
  pd_DA : ITy rho A pd_i pd_wA pd_FA;
  pd_DB : forall u x,
    ITy (ext rho pd_FA u (dnEl pd_dA k pd_EA pd_FA u x)) B pd_j (pd_wB u x)
        (pd_FB u x);
  pd_Dt : ITm rho t0 pd_i pd_wA pd_FA pd_wt pd_xt;
  pd_Da : ITm rho a pd_j (pd_wB pd_wt (upEl pd_dA k pd_EA pd_FA pd_wt pd_xt))
            (pd_FB pd_wt (upEl pd_dA k pd_EA pd_FA pd_wt pd_xt)) pd_wa pd_xa
}.
Arguments PairData : clear implicits.

Definition pd_SF {rho kk A B t0 a k} (d : PairData rho kk A B t0 a k)
  : kUFam k (esig (pd_wA d) (pd_B0 d)) :=
  sigFam k (pd_wA d) (pd_B0 d) (upF (pd_dA d) k (pd_EA d) (pd_FA d)) (pd_wB d)
    (fun u y => upF (pd_dB d) k (pd_EB d) (pd_FB d u y))
    (pd_redB d) (pd_cohB d) (pd_gSig d).

Definition pd_val {rho kk A B t0 a k} (d : PairData rho kk A B t0 a k)
  : kElAt (pd_SF d) (epair (pd_wt d) (pd_wa d)) :=
  sigPair k (pd_wA d) (pd_B0 d) (upF (pd_dA d) k (pd_EA d) (pd_FA d)) (pd_wB d)
    (fun u y => upF (pd_dB d) k (pd_EB d) (pd_FB d u y))
    (pd_redB d) (pd_cohB d) (pd_gSig d) (pd_wt d) (pd_wa d)
    (upEl (pd_dA d) k (pd_EA d) (pd_FA d) (pd_wt d) (pd_xt d))
    (upEl (pd_dB d) k (pd_EB d)
       (pd_FB d (pd_wt d) (upEl (pd_dA d) k (pd_EA d) (pd_FA d) (pd_wt d) (pd_xt d)))
       (pd_wa d) (pd_xa d))
    (pd_g d).

Definition PairVal (rho : Env) (kk : nat) (A B t0 a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (PairData rho kk A B t0 a k)
    (fun d => mkCanon k (esig (pd_wA d) (pd_B0 d)) (pd_SF d)
                (epair (pd_wt d) (pd_wa d)) (pd_val d)).

(* The projections.  `fst` is read at the DOMAIN's level and `snd` at the
   codomain's, so in each the Sigma's own annotation is existential. *)
Record FstData {rho : Env} {A B p : tm} {k : nat} : Type := {
  fd_ks : nat; fd_j : nat; fd_dA : nat; fd_dB : nat;
  fd_EA : fd_dA + k = fd_ks; fd_EB : fd_dB + fd_j = fd_ks;
  fd_wA : etm; fd_FA : kUFam k fd_wA; fd_B0 : etm;
  fd_wB : forall u, kElAt (upF fd_dA fd_ks fd_EA fd_FA) u -> etm;
  fd_FB : forall u (x : kElAt (upF fd_dA fd_ks fd_EA fd_FA) u),
            kUFam fd_j (fd_wB u x);
  fd_redB : forall u x, reds (eapp fd_B0 u) (fd_wB u x);
  fd_cohB : forall u x u' x',
    kEqAt (upF fd_dA fd_ks fd_EA fd_FA) u x (upF fd_dA fd_ks fd_EA fd_FA) u' x' ->
    kceq (kAt (upF fd_dB fd_ks fd_EB (fd_FB u x)))
         (kAt (upF fd_dB fd_ks fd_EB (fd_FB u' x')));
  fd_gSig : eqty fd_ks (esig fd_wA fd_B0) (esig fd_wA fd_B0);
  fd_wp : etm;
  fd_xp : kElAt (sigFam fd_ks fd_wA fd_B0 (upF fd_dA fd_ks fd_EA fd_FA) fd_wB
                   (fun u y => upF fd_dB fd_ks fd_EB (fd_FB u y))
                   fd_redB fd_cohB fd_gSig) fd_wp;
  fd_Ep : esig fd_wA fd_B0 = ers rho (sig_ fd_ks A B);
  fd_DA : ITy rho A k fd_wA fd_FA;
  fd_DB : forall u x,
    ITy (ext rho fd_FA u (dnEl fd_dA fd_ks fd_EA fd_FA u x)) B fd_j (fd_wB u x)
        (fd_FB u x);
  fd_Dp : ITm rho p fd_ks (esig fd_wA fd_B0)
            (sigFam fd_ks fd_wA fd_B0 (upF fd_dA fd_ks fd_EA fd_FA) fd_wB
               (fun u y => upF fd_dB fd_ks fd_EB (fd_FB u y))
               fd_redB fd_cohB fd_gSig) fd_wp fd_xp
}.
Arguments FstData : clear implicits.

Definition fd_val {rho A B p k} (d : FstData rho A B p k)
  : kElAt (fd_FA d) (efst (fd_wp d)) :=
  dnEl (fd_dA d) (fd_ks d) (fd_EA d) (fd_FA d) (efst (fd_wp d))
    (sigFst (fd_ks d) (fd_wA d) (fd_B0 d)
       (upF (fd_dA d) (fd_ks d) (fd_EA d) (fd_FA d)) (fd_wB d)
       (fun u y => upF (fd_dB d) (fd_ks d) (fd_EB d) (fd_FB d u y))
       (fd_redB d) (fd_cohB d) (fd_gSig d) (fd_wp d) (fd_xp d)).

Definition FstVal (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (FstData rho A B p k)
    (fun d => mkCanon k (fd_wA d) (fd_FA d) (efst (fd_wp d)) (fd_val d)).

Record SndData {rho : Env} {A B p : tm} {k : nat} : Type := {
  sd_ks : nat; sd_i : nat; sd_dA : nat; sd_dB : nat;
  sd_EA : sd_dA + sd_i = sd_ks; sd_EB : sd_dB + k = sd_ks;
  sd_wA : etm; sd_FA : kUFam sd_i sd_wA; sd_B0 : etm;
  sd_wB : forall u, kElAt (upF sd_dA sd_ks sd_EA sd_FA) u -> etm;
  sd_FB : forall u (x : kElAt (upF sd_dA sd_ks sd_EA sd_FA) u), kUFam k (sd_wB u x);
  sd_redB : forall u x, reds (eapp sd_B0 u) (sd_wB u x);
  sd_cohB : forall u x u' x',
    kEqAt (upF sd_dA sd_ks sd_EA sd_FA) u x (upF sd_dA sd_ks sd_EA sd_FA) u' x' ->
    kceq (kAt (upF sd_dB sd_ks sd_EB (sd_FB u x)))
         (kAt (upF sd_dB sd_ks sd_EB (sd_FB u' x')));
  sd_gSig : eqty sd_ks (esig sd_wA sd_B0) (esig sd_wA sd_B0);
  sd_wp : etm;
  sd_xp : kElAt (sigFam sd_ks sd_wA sd_B0 (upF sd_dA sd_ks sd_EA sd_FA) sd_wB
                   (fun u y => upF sd_dB sd_ks sd_EB (sd_FB u y))
                   sd_redB sd_cohB sd_gSig) sd_wp;
  sd_Ep : esig sd_wA sd_B0 = ers rho (sig_ sd_ks A B);
  sd_DA : ITy rho A sd_i sd_wA sd_FA;
  sd_DB : forall u x,
    ITy (ext rho sd_FA u (dnEl sd_dA sd_ks sd_EA sd_FA u x)) B k (sd_wB u x)
        (sd_FB u x);
  sd_Dp : ITm rho p sd_ks (esig sd_wA sd_B0)
            (sigFam sd_ks sd_wA sd_B0 (upF sd_dA sd_ks sd_EA sd_FA) sd_wB
               (fun u y => upF sd_dB sd_ks sd_EB (sd_FB u y))
               sd_redB sd_cohB sd_gSig) sd_wp sd_xp
}.
Arguments SndData : clear implicits.

Definition sd_fst {rho A B p k} (d : SndData rho A B p k)
  : kElAt (upF (sd_dA d) (sd_ks d) (sd_EA d) (sd_FA d)) (efst (sd_wp d)) :=
  sigFst (sd_ks d) (sd_wA d) (sd_B0 d)
    (upF (sd_dA d) (sd_ks d) (sd_EA d) (sd_FA d)) (sd_wB d)
    (fun u y => upF (sd_dB d) (sd_ks d) (sd_EB d) (sd_FB d u y))
    (sd_redB d) (sd_cohB d) (sd_gSig d) (sd_wp d) (sd_xp d).

Definition sd_val {rho A B p k} (d : SndData rho A B p k)
  : kElAt (sd_FB d (efst (sd_wp d)) (sd_fst d)) (esnd (sd_wp d)) :=
  dnEl (sd_dB d) (sd_ks d) (sd_EB d) (sd_FB d (efst (sd_wp d)) (sd_fst d))
    (esnd (sd_wp d))
    (sigSnd (sd_ks d) (sd_wA d) (sd_B0 d)
       (upF (sd_dA d) (sd_ks d) (sd_EA d) (sd_FA d)) (sd_wB d)
       (fun u y => upF (sd_dB d) (sd_ks d) (sd_EB d) (sd_FB d u y))
       (sd_redB d) (sd_cohB d) (sd_gSig d) (sd_wp d) (sd_xp d)).

Definition SndVal (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (SndData rho A B p k)
    (fun d => mkCanon k (sd_wB d (efst (sd_wp d)) (sd_fst d))
                (sd_FB d (efst (sd_wp d)) (sd_fst d))
                (esnd (sd_wp d)) (sd_val d)).

(* W: a sup, and the recursion on it.  The data is the clause's, which for
   `wrec` is the largest in the interpretation -- its step is typed in a
   three-entry context, and the two Pi families those entries live at carry
   their own levels and gaps. *)
Record SupData {rho : Env} {kk : nat} {A B a f : tm} {k : nat} : Type := {
  sp_i : nat; sp_j : nat; sp_dA : nat; sp_dB : nat;
  sp_EA : sp_dA + sp_i = k; sp_EB : sp_dB + sp_j = k;
  sp_wA : etm; sp_FA : kUFam sp_i sp_wA; sp_B0 : etm;
  sp_wB : forall u, kElAt (upF sp_dA k sp_EA sp_FA) u -> etm;
  sp_FB : forall u (x : kElAt (upF sp_dA k sp_EA sp_FA) u), kUFam sp_j (sp_wB u x);
  sp_redB : forall u x, reds (eapp sp_B0 u) (sp_wB u x);
  sp_cohB : forall u x u' x',
    kEqAt (upF sp_dA k sp_EA sp_FA) u x (upF sp_dA k sp_EA sp_FA) u' x' ->
    kceq (kAt (upF sp_dB k sp_EB (sp_FB u x)))
         (kAt (upF sp_dB k sp_EB (sp_FB u' x')));
  sp_gW : eqty k (ew sp_wA sp_B0) (ew sp_wA sp_B0);
  sp_Bbr : etm;
  sp_redBbr : forall v, reds (eapp sp_Bbr v) (ew sp_wA sp_B0);
  sp_gBr : forall u0 (z : kElAt (upF sp_dA k sp_EA sp_FA) u0),
    eqty k (epi (sp_wB u0 z) sp_Bbr) (epi (sp_wB u0 z) sp_Bbr);
  sp_wa : etm; sp_xa : kElAt sp_FA sp_wa;
  sp_wf : etm;
  sp_xf : kElAt (brFam k sp_i sp_j sp_dA sp_dB sp_EA sp_EB sp_wA sp_FA sp_B0
                   sp_wB sp_FB sp_redB sp_cohB sp_gW sp_Bbr sp_redBbr sp_gBr
                   sp_wa (upEl sp_dA k sp_EA sp_FA sp_wa sp_xa)) sp_wf;
  sp_gd : Good (ew sp_wA sp_B0) (esup sp_wa sp_wf);
  sp_lvl : kk = k;
  sp_Ew : ew sp_wA sp_B0 = ers rho (wt k A B);
  sp_DA : ITy rho A sp_i sp_wA sp_FA;
  sp_DB : forall u x,
    ITy (ext rho sp_FA u (dnEl sp_dA k sp_EA sp_FA u x)) B sp_j (sp_wB u x)
        (sp_FB u x);
  sp_Da : ITm rho a sp_i sp_wA sp_FA sp_wa sp_xa;
  sp_Df : ITm rho f k (epi (sp_wB sp_wa (upEl sp_dA k sp_EA sp_FA sp_wa sp_xa)) sp_Bbr)
            (brFam k sp_i sp_j sp_dA sp_dB sp_EA sp_EB sp_wA sp_FA sp_B0
               sp_wB sp_FB sp_redB sp_cohB sp_gW sp_Bbr sp_redBbr sp_gBr
               sp_wa (upEl sp_dA k sp_EA sp_FA sp_wa sp_xa)) sp_wf sp_xf
}.
Arguments SupData : clear implicits.

Definition sp_WF {rho kk A B a f k} (d : SupData rho kk A B a f k)
  : kUFam k (ew (sp_wA d) (sp_B0 d)) :=
  wFam k (sp_wA d) (sp_B0 d) (upF (sp_dA d) k (sp_EA d) (sp_FA d)) (sp_wB d)
    (fun u y => upF (sp_dB d) k (sp_EB d) (sp_FB d u y))
    (sp_redB d) (sp_cohB d) (sp_gW d).

Definition sp_val {rho kk A B a f k} (d : SupData rho kk A B a f k)
  : kElAt (sp_WF d) (esup (sp_wa d) (sp_wf d)) :=
  wSup k (sp_wA d) (sp_B0 d) (upF (sp_dA d) k (sp_EA d) (sp_FA d)) (sp_wB d)
    (fun u y => upF (sp_dB d) k (sp_EB d) (sp_FB d u y))
    (sp_redB d) (sp_cohB d) (sp_gW d) (sp_wa d) (sp_wf d)
    (upEl (sp_dA d) k (sp_EA d) (sp_FA d) (sp_wa d) (sp_xa d))
    (brApp k (sp_i d) (sp_j d) (sp_dA d) (sp_dB d) (sp_EA d) (sp_EB d) (sp_wA d)
       (sp_FA d) (sp_B0 d) (sp_wB d) (sp_FB d) (sp_redB d) (sp_cohB d) (sp_gW d)
       (sp_Bbr d) (sp_redBbr d) (sp_gBr d) (sp_wa d)
       (upEl (sp_dA d) k (sp_EA d) (sp_FA d) (sp_wa d) (sp_xa d)) (sp_wf d) (sp_xf d))
    (brApp_eq k (sp_i d) (sp_j d) (sp_dA d) (sp_dB d) (sp_EA d) (sp_EB d) (sp_wA d)
       (sp_FA d) (sp_B0 d) (sp_wB d) (sp_FB d) (sp_redB d) (sp_cohB d) (sp_gW d)
       (sp_Bbr d) (sp_redBbr d) (sp_gBr d) (sp_wa d)
       (upEl (sp_dA d) k (sp_EA d) (sp_FA d) (sp_wa d) (sp_xa d)) (sp_wf d) (sp_xf d))
    (sp_gd d).

Definition SupVal (rho : Env) (kk : nat) (A B a f : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (SupData rho kk A B a f k)
    (fun d => mkCanon k (ew (sp_wA d) (sp_B0 d)) (sp_WF d)
                (esup (sp_wa d) (sp_wf d)) (sp_val d)).


(* The recursion.  Its data is the interpretation's largest clause, and the
   five types `Interp/Def.v` names for the step are what makes it writable. *)
Record WRecData {rho : Env} {A B C s w0 : tm} {k : nat} : Type := {
  wr_kw : nat; wr_i : nat; wr_j : nat; wr_n : nat;
  wr_dA : nat; wr_dB : nat; wr_dBn : nat; wr_dC : nat;
  wr_EA : wr_dA + wr_i = wr_kw; wr_EB : wr_dB + wr_j = wr_kw;
  wr_EBn : wr_dBn + wr_j = wr_n; wr_EC : wr_dC + k = wr_n;
  wr_En : wr_n = Nat.max wr_j k;
  wr_wA : etm; wr_FA : kUFam wr_i wr_wA; wr_B0 : etm;
  wr_wB : forall u, kElAt (upF wr_dA wr_kw wr_EA wr_FA) u -> etm;
  wr_FB : forall u (x : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u),
            kUFam wr_j (wr_wB u x);
  wr_redB : forall u x, reds (eapp wr_B0 u) (wr_wB u x);
  wr_cohB : forall u x u' x',
    kEqAt (upF wr_dA wr_kw wr_EA wr_FA) u x (upF wr_dA wr_kw wr_EA wr_FA) u' x' ->
    kceq (kAt (upF wr_dB wr_kw wr_EB (wr_FB u x)))
         (kAt (upF wr_dB wr_kw wr_EB (wr_FB u' x')));
  wr_gW : eqty wr_kw (ew wr_wA wr_B0) (ew wr_wA wr_B0);
  wr_SC : etm -> etm;
  wr_FC : forall w1 x1, kUFam k (wr_SC w1);
  wr_cohC : forall w1 x1 w1' x1',
    kEqAt (wFam wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
             (fun u y => upF wr_dB wr_kw wr_EB (wr_FB u y))
             wr_redB wr_cohB wr_gW) w1 x1
          (wFam wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
             (fun u y => upF wr_dB wr_kw wr_EB (wr_FB u y))
             wr_redB wr_cohB wr_gW) w1' x1' ->
    kceq (kAt (wr_FC w1 x1)) (kAt (wr_FC w1' x1'));
  wr_Bbr : etm;
  wr_redBbr : forall v, reds (eapp wr_Bbr v) (ew wr_wA wr_B0);
  wr_gBr : forall u0 (z : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u0),
    eqty wr_kw (epi (wr_wB u0 z) wr_Bbr) (epi (wr_wB u0 z) wr_Bbr);
  wr_Bih : forall u0 (z : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u0) (f : etm), etm;
  wr_gIh : forall u0 (z : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u0) (f : etm),
    Good (ew wr_wA wr_B0) (esup u0 f) ->
    eqty wr_n (epi (wr_wB u0 z) (wr_Bih u0 z f)) (epi (wr_wB u0 z) (wr_Bih u0 z f));
  wr_Bih_red : forall u0 z f v,
    reds (eapp (wr_Bih u0 z f) v) (wr_SC (eapp f v));
  wr_Sr : etm;
  wr_gf : forall u0 (z : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u0) f,
    Good (ew wr_wA wr_B0) (esup u0 f) -> Good (epi (wr_wB u0 z) wr_Bbr) f;
  wr_gih : forall u0 (z : kElAt (upF wr_dA wr_kw wr_EA wr_FA) u0) f,
    Good (ew wr_wA wr_B0) (esup u0 f) ->
    Good (epi (wr_wB u0 z) (wr_Bih u0 z f)) (ihR wr_Sr f);
  wr_ws : WsTy wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0 wr_wB
            wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_Sr;
  wr_xs : XsTy wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0 wr_wB
            wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_Sr wr_ws;
  wr_redS : RedSTy wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0 wr_wB
              wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_Sr wr_ws;
  wr_stepSrel : StepRelTy wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA
                  wr_B0 wr_wB wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_Sr
                  wr_ws wr_xs wr_redS;
  wr_ww : etm;
  wr_xw : kElAt (wFam wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
                   (fun u y => upF wr_dB wr_kw wr_EB (wr_FB u y))
                   wr_redB wr_cohB wr_gW) wr_ww;
  wr_ESr : wr_Sr = ers rho (stepWrap3 s);
  wr_Ew : ew wr_wA wr_B0 = ers rho (wt wr_kw A B);
  wr_ESC : forall w1, wr_SC w1 = subst_etm (scons w1 (rsub rho)) (er C);
  wr_DA : ITy rho A wr_i wr_wA wr_FA;
  wr_DB : forall u x,
    ITy (ext rho wr_FA u (dnEl wr_dA wr_kw wr_EA wr_FA u x)) B wr_j (wr_wB u x)
        (wr_FB u x);
  wr_DC : forall u x,
    ITy (ext rho (wFam wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
                    (fun u1 x1 => upF wr_dB wr_kw wr_EB (wr_FB u1 x1))
                    wr_redB wr_cohB wr_gW) u x) C k (wr_SC u) (wr_FC u x);
  wr_Dstep : forall u0 z f sub subext gd ih ihext,
    ITm (ext (ext (ext rho wr_FA u0 (dnEl wr_dA wr_kw wr_EA wr_FA u0 z))
               (brFam wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0
                  wr_wB wr_FB wr_redB wr_cohB wr_gW wr_Bbr wr_redBbr wr_gBr u0 z)
               f
               (brEl wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0
                  wr_wB wr_FB wr_redB wr_cohB wr_gW wr_Bbr wr_redBbr wr_gBr
                  u0 z f sub subext (wr_gf u0 z f gd)))
           (ihFam wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0
              wr_wB wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_cohC
              wr_n wr_dBn wr_dC wr_EBn wr_EC wr_Bih wr_gIh wr_Bih_red
              u0 z f gd sub subext)
           (ihR wr_Sr f)
           (ihEl wr_kw wr_i wr_j wr_dA wr_dB wr_EA wr_EB wr_wA wr_FA wr_B0
              wr_wB wr_FB wr_redB wr_cohB wr_gW k wr_SC wr_FC wr_cohC
              wr_n wr_dBn wr_dC wr_EBn wr_EC wr_Bih wr_gIh wr_Bih_red wr_Sr
              u0 z f gd sub subext ih ihext (wr_gih u0 z f gd)))
        s k
        (wr_SC (esup u0 f))
        (wr_FC (esup u0 f)
           (wSup wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
              (fun u x => upF wr_dB wr_kw wr_EB (wr_FB u x))
              wr_redB wr_cohB wr_gW u0 f z sub subext gd))
        (wr_ws u0 z f sub subext gd ih ihext)
        (wr_xs u0 z f sub subext gd ih ihext);
  wr_Dw : ITm rho w0 wr_kw (ew wr_wA wr_B0)
            (wFam wr_kw wr_wA wr_B0 (upF wr_dA wr_kw wr_EA wr_FA) wr_wB
               (fun u y => upF wr_dB wr_kw wr_EB (wr_FB u y))
               wr_redB wr_cohB wr_gW) wr_ww wr_xw
}.
Arguments WRecData : clear implicits.

Definition wr_val {rho A B C s w0 k} (d : WRecData rho A B C s w0 k)
  : kElAt (wr_FC d (wr_ww d) (wr_xw d)) (ewrec (wr_Sr d) (wr_ww d)) :=
  wRecS (wr_kw d) (wr_wA d) (wr_B0 d)
    (upF (wr_dA d) (wr_kw d) (wr_EA d) (wr_FA d)) (wr_wB d)
    (fun u y => upF (wr_dB d) (wr_kw d) (wr_EB d) (wr_FB d u y))
    (wr_redB d) (wr_cohB d) (wr_gW d) k (wr_Sr d) (fun w1 _ => wr_SC d w1)
    (wr_FC d) (wr_cohC d)
    (stepOf (wr_kw d) (wr_i d) (wr_j d) (wr_dA d) (wr_dB d) (wr_EA d) (wr_EB d)
       (wr_wA d) (wr_FA d) (wr_B0 d) (wr_wB d) (wr_FB d) (wr_redB d) (wr_cohB d)
       (wr_gW d) k (wr_SC d) (wr_FC d) (wr_Sr d) (wr_ws d) (wr_xs d) (wr_redS d))
    (wr_stepSrel d) (wr_ww d) (wr_xw d).

Definition WRecVal (rho : Env) (A B C s w0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (WRecData rho A B C s w0 k)
    (fun d => mkCanon k (wr_SC d (wr_ww d)) (wr_FC d (wr_ww d) (wr_xw d))
                (ewrec (wr_Sr d) (wr_ww d)) (wr_val d)).

(* natrec.  Much smaller than the W recursion: with the step term carrying its
   own two binders there is no Pi-type for it, hence no second Pi family, no
   goodness premises and no step congruence -- its semantic content is one
   value per scrutinee and motive value, and `semrec` relates two of them
   outright. *)
Record RecData {rho : Env} {C z s n : tm} {k : nat} : Type := {
  rd_j : nat;
  rd_SC : etm -> etm;
  rd_FC : forall m (x0 : kElAt (natFam rd_j) m), kUFam k (rd_SC m);
  rd_cohC : forall m x0 m' x0',
    kEqAt (natFam rd_j) m x0 (natFam rd_j) m' x0' ->
    kceq (kAt (rd_FC m x0)) (kAt (rd_FC m' x0'));
  rd_S0 : etm;
  rd_wz : etm; rd_xz : kElAt (rd_FC ezero (natE 0 NatAt_zero)) rd_wz;
  rd_ws : forall m (x0 : kElAt (natFam rd_j) m) (w0 : etm)
            (y : kElAt (rd_FC m x0) w0), etm;
  rd_xs : forall m x0 w0 y,
    kElAt (rd_FC (esucc m) (natSucc x0)) (rd_ws m x0 w0 y);
  rd_redS : forall m x0 w0 y,
    reds (eapp (eapp rd_S0 m) w0) (rd_ws m x0 w0 y);
  rd_wn : etm; rd_xn : kElAt (natFam rd_j) rd_wn;
  rd_ES : rd_S0 = ers rho (stepWrap s);
  rd_DC : forall m x0, ITy (ext rho (natFam rd_j) m x0) C k (rd_SC m) (rd_FC m x0);
  rd_Dz : ITm rho z k (rd_SC ezero) (rd_FC ezero (natE 0 NatAt_zero)) rd_wz rd_xz;
  rd_Ds : forall m x0 w0 y,
    ITm (ext (ext rho (natFam rd_j) m x0) (rd_FC m x0) w0 y) s k
        (rd_SC (esucc m)) (rd_FC (esucc m) (natSucc x0))
        (rd_ws m x0 w0 y) (rd_xs m x0 w0 y);
  rd_Dn : ITm rho n rd_j enat (natFam rd_j) rd_wn rd_xn
}.
Arguments RecData : clear implicits.

Definition rd_val {rho C z s n k} (d : RecData rho C z s n k)
  : kElAt (rd_FC d (rd_wn d) (natE (natIdx (rd_xn d)) (natSpec (rd_xn d))))
          (enatrec (rd_wz d) (rd_S0 d) (rd_wn d)) :=
  semrec k (rd_j d) (rd_SC d) (rd_FC d) (rd_cohC d) (rd_wz d) (rd_S0 d) (rd_xz d)
    (fun m x0 w0 y =>
       moveTo (rd_FC d (esucc m) (natSucc x0)) (rd_FC d (esucc m) (natSucc x0))
         (famAtSelf (rd_FC d (esucc m) (natSucc x0)))
         (rd_ws d m x0 w0 y) (rd_xs d m x0 w0 y) (eapp (eapp (rd_S0 d) m) w0)
         (rd_redS d m x0 w0 y))
    (natIdx (rd_xn d)) (rd_wn d) (natSpec (rd_xn d)).

Definition RecVal (rho : Env) (C z s n : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  Shaped F w x (RecData rho C z s n k)
    (fun d => mkCanon k (rd_SC d (rd_wn d))
                (rd_FC d (rd_wn d) (natE (natIdx (rd_xn d)) (natSpec (rd_xn d))))
                (enatrec (rd_wz d) (rd_S0 d) (rd_wn d)) (rd_val d)).

(* ------------------------------------------------------------------ *)
(* And the decoder itself.  `Empty_set` at a shape means NO clause     *)
(* concludes there at that level: plam, papp and absurd have no clause *)
(* of their own and eqty, refl and transp are not in the theory, so at  *)
(* a positive level -- where i_proof, the one clause that fits any      *)
(* subject, cannot reach -- there is no derivation at all.  That is a   *)
(* fact about the interpretation, and recording it in the decoder is    *)
(* what lets a consumer use it.                                        *)
(* ------------------------------------------------------------------ *)

Definition TmShape (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match t return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | var_tm i => VarShape rho i k Sy
  | nat_ kk => TyVal rho (nat_ kk) k Sy
  | prop kk => TyVal rho (prop kk) k Sy
  | univ kk m => TyVal rho (univ kk m) k Sy
  | prf kk p => TyVal rho (prf kk p) k Sy
  | pi kk A B => TyVal rho (pi kk A B) k Sy
  | sig_ kk A B => TyVal rho (sig_ kk A B) k Sy
  | wt kk A B => TyVal rho (wt kk A B) k Sy
  | up j t0 => UpShape rho j t0 k Sy
  | uptm A t0 => UpTmVal rho A t0 k Sy
  | zero kk => ZeroVal kk k Sy
  | succ n => SuccVal rho n k Sy
  | lam kk A B t0 => LamVal rho kk A B t0 k Sy
  | app A B f a => AppVal rho A B f a k Sy
  | pair kk A B t0 a => PairVal rho kk A B t0 a k Sy
  | fst A B p => FstVal rho A B p k Sy
  | snd A B p => SndVal rho A B p k Sy
  | sup kk A B a f => SupVal rho kk A B a f k Sy
  | wrec A B C s w0 => WRecVal rho A B C s w0 k Sy
  | natrec C z s n => RecVal rho C z s n k Sy
  | false_ kk => FalseVal kk k Sy
  | all jj A p => AllVal rho jj A p k Sy
  | _ => NoVal k Sy
  end.

(* The one universal alternative is i_proof, and with Prf living at every level
   it is available at every level too.  It carries TWO facts, and both are
   used: the family relates all of its elements, which is what a functionality
   proof needs, and its realiser is a Prf, which is what LEVEL functionality
   needs -- the proof clause is the only clause of ITm whose level the subject
   does not determine, and this is what rules it out at a universe or a Prop. *)
Definition ProofAlt {k Sy} (F : kUFam k Sy) : Type :=
  (TotalFam F * { q : etm & tyeq Sy (eprf q) })%type.

Definition TmInv (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun F w x => (ProofAlt F + TmShape rho t k Sy F w x)%type.

(* ---- Conversion-stability and respect for the family's own equality.  Every
   branch but the variable's is one `Shaped`, so both proofs are one tactic
   with two exceptions. ---- *)

Lemma VarShape_conv (rho : Env) (i : nat) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : kceq (kAt F) (kAt F'))
  w (x : kElAt F w) :
  VarShape rho i k Sy F w x ->
  VarShape rho i k Sy' F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
Proof.
  destruct i as [| i]; destruct rho as [| en rho0]; cbn [VarShape];
    try (exact (fun h => match h with end)).
  - (* var 0: the entry relation travels along the coercion *)
    intros H; eapply EntryRel_trans; [| exact H].
    apply (entry_rel k Sy' F' w
             (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x) Sy F w x).
    split; [apply knsymU; exact P |].
    apply kEqAt_sym; apply kto_coh.
  - (* var (S i): the witness is the same, moved *)
    intros [x0 [D HE]].
    exists (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x0); split.
    + exact (i_conv rho0 (var_tm i) k Sy F Sy' F' w x0 P D).
    + exact (kto_eq (kAt F) (kAt F') (famAtWf F) (famAtWf F') P
               (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x w x0
               (famAtSelf F) HE).
Qed.

Lemma VarShape_resp (rho : Env) (i : nat) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x F w x2 -> VarShape rho i k Sy F w x -> VarShape rho i k Sy F w x2.
Proof.
  destruct i as [| i]; destruct rho as [| en rho0]; cbn [VarShape];
    try (exact (fun _ h => match h with end)).
  - intros HE H; eapply EntryRel_trans; [| exact H].
    apply (entry_rel k Sy F w x2 Sy F w x).
    split; [exact (famAtSelf F) | apply kEqAt_sym; exact HE].
  - intros HE [x0 [D H0]]; exists x0; split; [exact D |].
    eapply kEqAt_trans; [exact (famAtSelf F) | apply kEqAt_sym; exact HE | exact H0].
Qed.

Lemma TmShape_conv (rho : Env) (t : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : kceq (kAt F) (kAt F'))
  w (x : kElAt F w) :
  TmShape rho t k Sy F w x ->
  TmShape rho t k Sy' F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
Proof.
  destruct t; cbn [TmShape NoVal UpShape TyVal UpTmVal];
    first
      [ solve [intros []]
      | apply VarShape_conv
      | destruct k; [solve [intros []] | apply Shaped_conv]
      | apply Shaped_conv ].
Qed.

Lemma TmShape_resp (rho : Env) (t : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x F w x2 -> TmShape rho t k Sy F w x -> TmShape rho t k Sy F w x2.
Proof.
  destruct t; cbn [TmShape NoVal UpShape TyVal UpTmVal];
    first
      [ solve [intros _ []]
      | apply VarShape_resp
      | destruct k; [solve [intros _ []] | apply Shaped_resp]
      | apply Shaped_resp ].
Qed.

Lemma TmInv_conv (rho : Env) (t : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : kceq (kAt F) (kAt F'))
  w (x : kElAt F w) :
  TmInv rho t k Sy F w x ->
  TmInv rho t k Sy' F' w (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
Proof.
  intros [[HT [q Hq]] | Hs].
  - left; split; [exact (TotalFam_ceq F F' P HT) |].
    exists q; eapply tyeq_trans;
      [apply tyeq_sym; exact (ceq_ty F F' P) | exact Hq].
  - right; exact (TmShape_conv rho t k Sy Sy' F F' P w x Hs).
Qed.

Lemma TmInv_resp (rho : Env) (t : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x F w x2 -> TmInv rho t k Sy F w x -> TmInv rho t k Sy F w x2.
Proof.
  intros HE [HT | Hs];
    [ left; exact HT | right; exact (TmShape_resp rho t k Sy F w x x2 HE Hs) ].
Qed.

(* A shape branch is a decoder value. *)
Definition inShape {rho t k Sy} {F : kUFam k Sy} {w} {x : kElAt F w}
  : TmShape rho t k Sy F w x -> TmInv rho t k Sy F w x := fun H => inr H.

(* ------------------------------------------------------------------ *)
(* The decoder is total.                                              *)
(*                                                                    *)
(* The ITy motive is the decoder AT THE UNIVERSE ABOVE, which is what   *)
(* makes the two off-syntax clauses collapse: i_ty is then literally    *)
(* its induction hypothesis, and ity_of passes the ITm premise's own    *)
(* branch through (modulo famEl_elFam_rel).  So at a subject that is    *)
(* not a type former the decoder never returns the universe            *)
(* alternative, and a consumer gets the shape.                         *)
(* ------------------------------------------------------------------ *)

Definition TyD (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  TmInv rho A (S k) (euniv k) (univFam k) w (famEl F).

(* two readings of one type, read as elements of the universe *)
Lemma uEq_conv {k u} (F F' : kUFam k u) (P : kceq (kAt F) (kAt F')) :
  kEqAt (univFam k) u (famEl F) (univFam k) u (famEl F').
Proof.
  apply uEq_of;
    [ exact (uf_ty F) | intros v h pf v' h' pf'; apply famCeq_all; exact P ].
Qed.

Ltac dc_ty c := cbn [TyD TmInv]; right;
  refine (existT _ (Build_TyData _ _ _ _ c _) (IsVal_self _ _ _)).

(* a term clause: the shape's own data, and the value is the canonical one *)
Ltac dc_sh d := apply inShape; refine (existT _ d (IsVal_self _ _ _)).

Ltac dc1 := intros rho k w Ew; dc_ty (natFam k); exact (ity_nat rho k w Ew).
Ltac dc2 := intros rho k w Ew; dc_ty (propFam k); exact (ity_prop rho k w Ew).
Ltac dc3 := intros rho k dl jj EE w Ew; dc_ty (upF dl k EE (univFam jj));
  exact (ity_univ rho k dl jj EE w Ew).
Ltac dc4 := intros rho k jj p wp xp Dp IHp; dc_ty (prfF k xp);
  exact (ity_prf rho k jj p wp xp Dp).
Ltac dc5 := intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    Ew DA IHA DB IHB;
  dc_ty (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gPi);
  exact (ity_pi rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi Ew DA DB).
Ltac dc6 := intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    Ew DA IHA DB IHB;
  dc_ty (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gSig);
  exact (ity_sig rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig Ew DA DB).
Ltac dc7 := intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
    Ew DA IHA DB IHB;
  dc_ty (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
           redB cohB gW);
  exact (ity_w rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW Ew DA DB).
Ltac dc8 := intros rho A k w F DA IHA; dc_ty (famLiftK F);
  exact (ity_up rho A k w F DA).
Ltac dc9 := intros rho A k w v nf Dv IHv; unfold TyD in IHv |- *;
  eapply TmInv_resp; [apply kEqAt_sym; apply famEl_elFam_rel | exact IHv].
Ltac dc10 := intros rho A k w F F' P Dc IHc; unfold TyD in *;
  apply (TmInv_resp rho A (S k) (euniv k) (univFam k) w (famEl F) (famEl F'));
  [ exact (uEq_conv F F' P) | exact IHc ].

Ltac dc11 := intros rho A k w F D IH; exact IH.
Ltac dc12 := intros rho k Sy F w x; apply inShape;
  cbn [TmShape VarShape ext]; apply EntryRel_refl.
Ltac dc13 := intros rho en ii k Sy F w x D IH; apply inShape;
  cbn [TmShape VarShape]; exists x; split; [exact D | apply kEqAt_refl].
Ltac dc14 := intros rho k; dc_sh (@eq_refl nat k).
Ltac dc15 := intros rho k n wn x D IH;
  dc_sh (Build_SuccData rho n k wn x D).
Ltac dc16 := intros rho A B t k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    w wt xt redt xtext gd Ew Ep DA IHA DB IHB Dt IHt;
  dc_sh (Build_LamData rho k A B t k w i jj dA dB EA EB wA FA B0 wB FB redB
           cohB gPi wt xt redt xtext gd eq_refl Ew Ep DA DB Dt).
Ltac dc17 := intros rho A B f a k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    wf xf wa xa Ep DA IHA DB IHB Df IHf Da IHa;
  dc_sh (Build_AppData rho A B f a jj k i dA dB EA EB wA FA B0 wB FB redB cohB
           gPi wf xf wa xa Ep DA DB Df Da).
Ltac dc18 := intros rho A B t a k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wt xt wa xa g Ep DA IHA DB IHB Dt IHt Da IHa;
  dc_sh (Build_PairData rho k A B t a k i jj dA dB EA EB wA FA B0 wB FB redB
           cohB gSig wt xt wa xa g eq_refl Ep DA DB Dt Da).
Ltac dc19 := intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp;
  dc_sh (Build_FstData rho A B p i k jj dA dB EA EB wA FA B0 wB FB redB cohB
           gSig wp xp Ep DA DB Dp).
Ltac dc20 := intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp;
  dc_sh (Build_SndData rho A B p jj k i dA dB EA EB wA FA B0 wB FB redB cohB
           gSig wp xp Ep DA DB Dp).
Ltac dc21 := intros rho A B a f k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
    Bbr redBbr gBr wa xa wf xf gd Ew DA IHA DB IHB Da IHa Df IHf;
  dc_sh (Build_SupData rho k A B a f k i jj dA dB EA EB wA FA B0 wB FB redB
           cohB gW Bbr redBbr gBr wa xa wf xf gd eq_refl Ew DA DB Da Df).
Ltac dc22 := intros rho A B C s w0 k i jj m n dA dB dBn dC EA EB EBn EC En
    wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr
    gf gih ws xs redS stepSrel ww xw
    ESr Ew ESC DA IHA DB IHB DC IHC Dstep IHstep Dw IHw;
  dc_sh (Build_WRecData rho A B C s w0 m k i jj n dA dB dBn dC EA EB EBn EC En
           wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh
           Bih_red Sr gf gih ws xs redS stepSrel ww xw ESr Ew ESC DA DB DC
           Dstep Dw).
Ltac dc23 := intros rho C z s n k jj SC FC cohC S0 wz xz ws xs redS wn xn
    ES DC IHC Dz IHz Ds IHs Dn IHn;
  dc_sh (Build_RecData rho C z s n k jj SC FC cohC S0 wz xz ws xs redS wn xn
           ES DC Dz Ds Dn).
Ltac dc24 := intros rho k w g Ew; dc_sh (Build_FalseData k k g eq_refl).
Ltac dc25 := intros rho jj A p k wA FA wp xp w g Ew DA IHA Dp IHp;
  dc_sh (Build_AllData rho jj A p jj k wA FA wp xp w g eq_refl DA Dp).
Ltac dc26 := intros rho t p k jj wp xp h w g Ew Dp IHp;
  cbn [TmInv]; left; split;
  [ exact (prf_total k jj wp xp)
  | exists wp; exists 0; eapply eqty_prf;
      [ apply eval_whnf; exact (whnf_prf wp) | apply eval_whnf; exact (whnf_prf wp)
      | exact (Rel_prop_elim eprop wp wp ev_prop (propGood xp)) ] ].
Ltac dc27 := intros rho A t k Sy F w x DA IHA D IH;
  dc_sh (Build_UpTmData rho A t k w Sy F x DA D).
Ltac dc28 := intros rho t k Sy F Sy' F' w x P D IH;
  apply (TmInv_conv rho t k Sy Sy' F F' P w x); exact IH.

Lemma ity_dec rho A k w F (D : ITy rho A k w F) : TyD rho A k w F.
Proof.
  revert rho A k w F D.
  apply (ITy_mut (fun rho A k w F _ => TyD rho A k w F)
                 (fun rho t k Sy F w x _ => TmInv rho t k Sy F w x));
    [ dc1 | dc2 | dc3 | dc4 | dc5 | dc6 | dc7 | dc8 | dc9 | dc10
    | dc11 | dc12 | dc13 | dc14 | dc15 | dc16 | dc17 | dc18 | dc19 | dc20
    | dc21 | dc22 | dc23 | dc24 | dc25 | dc26 | dc27 | dc28 ].
Qed.

Lemma itm_inv rho t k Sy F w x (D : ITm rho t k Sy F w x) : TmInv rho t k Sy F w x.
Proof.
  revert rho t k Sy F w x D.
  apply (ITm_mut (fun rho A k w F _ => TyD rho A k w F)
                 (fun rho t k Sy F w x _ => TmInv rho t k Sy F w x));
    [ dc1 | dc2 | dc3 | dc4 | dc5 | dc6 | dc7 | dc8 | dc9 | dc10
    | dc11 | dc12 | dc13 | dc14 | dc15 | dc16 | dc17 | dc18 | dc19 | dc20
    | dc21 | dc22 | dc23 | dc24 | dc25 | dc26 | dc27 | dc28 ].
Qed.

(* ------------------------------------------------------------------ *)
(* UNIQUENESS OF THE LEVEL.                                           *)
(*                                                                    *)
(* What the fundamental lemma's variable case needs: the environment     *)
(* records the family it was built with, at the level it was built at,   *)
(* and the statement of 9.2 is handed some other reading of the same     *)
(* context type.  A variable's level is pinned to its entry's -- i_var0  *)
(* reads the entry's own family and i_varS and i_conv preserve the level  *)
(* -- so the two levels have to be shown equal before anything else can  *)
(* happen.                                                              *)
(*                                                                    *)
(* Only the LEVELS of the environment matter, so that is all the         *)
(* statement asks agree; the two readings of the type may be in          *)
(* genuinely different environments.                                    *)
(*                                                                    *)
(* Positive levels only.  At level 0 nothing is unique: layer 1's Prf     *)
(* clause relates every realiser, so i_proof reads any subject whatever   *)
(* as a proof.  That is what the NotPrfR hypothesis rules out.           *)
(* ------------------------------------------------------------------ *)

Fixpoint lvls (rho : Env) : list nat :=
  match rho with
  | nil => nil
  | en :: r => en_k en :: lvls r
  end.

Lemma lvls_ext rho {k S0} (F : kUFam k S0) w (x : kElAt F w) :
  lvls (ext rho F w x) = k :: lvls rho.
Proof. reflexivity. Qed.

Lemma lvls_of_EnvRel : forall rho rho', EnvRel rho rho' -> lvls rho = lvls rho'.
Proof.
  induction rho as [| en r IH]; intros [| en' r'] H; cbn in H |- *;
    try (solve [destruct H]); [reflexivity |].
  destruct H as [HR HE]; f_equal;
    [exact (EntryRel_k _ _ HE) | exact (IH r' HR)].
Qed.

(* ---- the side condition: not a Prf.  The proof clause is the ONE clause of
     ITm whose level the subject does not determine -- `prf k p` is a type at
     every k above the proposition's own level, and a proof term records none
     of that -- so level functionality has to rule it out, and what rules it
     out is the shape of the type's realiser. ---- *)

Definition NotPrfR (Sy : etm) : Prop := forall q, tyeq Sy (eprf q) -> False.

Lemma tyeq_prf_eval T q : tyeq T (eprf q) -> exists p, eval T (eprf p).
Proof.
  intros H; destruct (tyeq_sym _ _ H) as [n [P HP]].
  destruct (LR_inv_prf _ _ _ _ _ _ HP (eval_whnf _ (whnf_prf q))) as [p [Hp _]].
  exists p; exact Hp.
Qed.

Lemma NotPrfR_nat : NotPrfR enat.
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf enat whnf_nat) Hp).
Qed.

Lemma NotPrfR_prop : NotPrfR eprop.
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf eprop whnf_prop) Hp).
Qed.

Lemma NotPrfR_univ m : NotPrfR (euniv m).
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf _ (whnf_univ m)) Hp).
Qed.

Lemma NotPrfR_pi A0 B0 : NotPrfR (epi A0 B0).
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf _ (whnf_pi A0 B0)) Hp).
Qed.

Lemma NotPrfR_sig A0 B0 : NotPrfR (esig A0 B0).
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf _ (whnf_sig A0 B0)) Hp).
Qed.

Lemma NotPrfR_w A0 B0 : NotPrfR (ew A0 B0).
Proof.
  intros q Hq; destruct (tyeq_prf_eval _ q Hq) as [p Hp].
  discriminate (eval_det _ _ _ (eval_whnf _ (whnf_w A0 B0)) Hp).
Qed.

(* Variables: an induction on the INDEX, which the induction on the term
   cannot supply -- var_tm i is not a subterm of var_tm (S i). *)
Lemma var_lvl : forall i rho rho', lvls rho = lvls rho' ->
  forall k Sy (F : kUFam k Sy) w (x : kElAt F w), NotPrfR Sy ->
    ITm rho (var_tm i) k Sy F w x ->
  forall k' Sy' (F' : kUFam k' Sy') w' (x' : kElAt F' w'), NotPrfR Sy' ->
    ITm rho' (var_tm i) k' Sy' F' w' x' ->
  k = k'.
Proof.
  induction i as [| i IH];
    intros rho rho' HL k Sy F w x HN D k' Sy' F' w' x' HN' D';
    pose proof (itm_inv rho _ _ _ _ _ _ D) as E;
    pose proof (itm_inv rho' _ _ _ _ _ _ D') as E';
    destruct E as [[_ [q0 Hq0]] | E]; try (solve [destruct (HN q0 Hq0)]);
    destruct E' as [[_ [q0 Hq0]] | E']; try (solve [destruct (HN' q0 Hq0)]);
    destruct rho as [| en rho0]; destruct rho' as [| en' rho0'];
    cbn [TmShape VarShape lvls] in E, E', HL;
    try (solve [destruct E]); try (solve [destruct E']);
    injection HL as Hk HL0.
  - pose proof (EntryRel_k _ _ E) as Ee; pose proof (EntryRel_k _ _ E') as Ee'.
    cbn [en_k] in Ee, Ee'.
    exact (eq_trans Ee (eq_trans Hk (eq_sym Ee'))).
  - destruct E as [x0 [D0 _]]; destruct E' as [x0' [D0' _]].
    exact (IH rho0 rho0' HL0 k Sy F w x0 HN D0 k' Sy' F' w' x0' HN' D0').
Qed.

Ltac lvl_shapes D1 D2 Hnp Hnp' :=
  pose proof (itm_inv _ _ _ _ _ _ _ D1) as E;
  pose proof (itm_inv _ _ _ _ _ _ _ D2) as E';
  destruct E as [[_ [q0 Hq0]] | E]; try (solve [destruct (Hnp q0 Hq0)]);
  destruct E' as [[_ [q0 Hq0]] | E']; try (solve [destruct (Hnp' q0 Hq0)]);
  cbn [TmShape VarShape TyVal UpTmVal UpShape ZeroVal SuccVal FalseVal
       AllVal LamVal AppVal PairVal FstVal SndVal SupVal WRecVal RecVal NoVal]
    in E, E'.

(* A type former, read as a term of the universe above it: its level is the
   annotation, and Interp/Inv.v's LvlDec says so. *)
Ltac lvl_by_dec ka kb Ea Eb :=
  destruct ka as [| k0]; [solve [destruct Ea] |];
  destruct kb as [| k0']; [solve [destruct Eb] |];
  destruct Ea as [d0 Hv]; destruct Eb as [d2 Hv2];
  pose proof (ity_lvl_dec _ _ _ _ (ty_F0 d0) (ty_D d0)) as Ej;
  pose proof (ity_lvl_dec _ _ _ _ (ty_F0 d2) (ty_D d2)) as Ej';
  cbn [LvlDec] in Ej, Ej'; lia.

(* An induction on the TERM, with the decoder standing in for inversion at
   each shape.  Every clause but the proof clause reads its level either off
   an ANNOTATION -- the formers, lam, pair, sup, zero, false_, the forall --
   or off a subterm whose own reading the induction hypothesis covers.  In v2
   the eliminators read at a COMPONENT's level rather than the former's, so
   `app`, `snd`, `natrec` and `wrec` go through the component's own reading at
   an element the clause provides: the argument for app, the pair's first
   projection for snd, the scrutinee for the two recursors. *)
Lemma itm_lvl : forall t rho rho', lvls rho = lvls rho' ->
  forall k Sy (F : kUFam k Sy) w (x : kElAt F w), NotPrfR Sy ->
    ITm rho t k Sy F w x ->
  forall k' Sy' (F' : kUFam k' Sy') w' (x' : kElAt F' w'), NotPrfR Sy' ->
    ITm rho' t k' Sy' F' w' x' ->
  k = k'.
Proof.
  induction t as
    [ i
    | kk A IHA B IHB t1 IHt1
    | A IHA t1 IHt1
    | A IHA B IHB f IHf a IHa
    | f IHf a IHa
    | kk A IHA B IHB t1 IHt1 a IHa
    | A IHA B IHB p IHp
    | A IHA B IHB p IHp
    | kk A IHA B IHB
    | kk A IHA B IHB
    | kk A IHA B IHB
    | kk A IHA B IHB a IHa f IHf
    | A IHA B IHB C IHC s IHs w1 IHw1
    | kk | kk | n IHn
    | C IHC z IHz s IHs n IHn
    | kk m
    | jj A IHA
    | A IHA t1 IHt1
    | kk
    | kk p IHp
    | jj A IHA p IHp
    | kk
    | T IHT e IHe
    | A IHA t1 IHt1 a IHa
    | A IHA a IHa
    | A IHA B IHB t1 IHt1 a IHa e IHe b IHb ];
    intros rho rho' HL k Sy F w x HN D k' Sy' F' w' x' HN' D'.
  - (* var_tm *)
    exact (var_lvl i rho rho' HL k Sy F w x HN D k' Sy' F' w' x' HN' D').
  - (* lam: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    pose proof (ld_lvl d); pose proof (ld_lvl d2); lia.
  - (* plam *) lvl_shapes D D' HN HN'; destruct E.
  - (* app: the codomain, at the argument's own value *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    assert (Ei : S (ap_i d) = S (ap_i d2)).
    { eapply IHA;
        [ exact HL | exact (NotPrfR_univ (ap_i d))
        | exact (i_ty _ _ _ _ _ (ap_DA d)) | exact (NotPrfR_univ (ap_i d2))
        | exact (i_ty _ _ _ _ _ (ap_DA d2)) ]. }
    injection Ei as Ei.
    assert (EB : S k = S k').
    { eapply (IHB (ext rho (ap_FA d) (ap_wa d)
                    (dnEl (ap_dA d) (ap_kp d) (ap_EA d) (ap_FA d) (ap_wa d)
                       (ap_arg d)))
                 (ext rho' (ap_FA d2) (ap_wa d2)
                    (dnEl (ap_dA d2) (ap_kp d2) (ap_EA d2) (ap_FA d2) (ap_wa d2)
                       (ap_arg d2))));
        [ cbn [lvls ext en_k]; rewrite HL, Ei; reflexivity
        | exact (NotPrfR_univ k)
        | exact (i_ty _ _ _ _ _ (ap_DB d (ap_wa d) (ap_arg d)))
        | exact (NotPrfR_univ k')
        | exact (i_ty _ _ _ _ _ (ap_DB d2 (ap_wa d2) (ap_arg d2))) ]. }
    injection EB as EB; exact EB.
  - (* papp *) lvl_shapes D D' HN HN'; destruct E.
  - (* pair: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    pose proof (pd_lvl d); pose proof (pd_lvl d2); lia.
  - (* fst: the domain *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    assert (Ei : S k = S k').
    { eapply IHA;
        [ exact HL | exact (NotPrfR_univ k) | exact (i_ty _ _ _ _ _ (fd_DA d))
        | exact (NotPrfR_univ k') | exact (i_ty _ _ _ _ _ (fd_DA d2)) ]. }
    injection Ei as Ei; exact Ei.
  - (* snd: the codomain, at the pair's own first projection *)
    lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    assert (Ei : S (sd_i d) = S (sd_i d2)).
    { eapply IHA;
        [ exact HL | exact (NotPrfR_univ (sd_i d))
        | exact (i_ty _ _ _ _ _ (sd_DA d)) | exact (NotPrfR_univ (sd_i d2))
        | exact (i_ty _ _ _ _ _ (sd_DA d2)) ]. }
    injection Ei as Ei.
    assert (EB : S k = S k').
    { eapply (IHB (ext rho (sd_FA d) (efst (sd_wp d))
                    (dnEl (sd_dA d) (sd_ks d) (sd_EA d) (sd_FA d) (efst (sd_wp d))
                       (sd_fst d)))
                 (ext rho' (sd_FA d2) (efst (sd_wp d2))
                    (dnEl (sd_dA d2) (sd_ks d2) (sd_EA d2) (sd_FA d2)
                       (efst (sd_wp d2)) (sd_fst d2))));
        [ cbn [lvls ext en_k]; rewrite HL, Ei; reflexivity
        | exact (NotPrfR_univ k)
        | exact (i_ty _ _ _ _ _ (sd_DB d (efst (sd_wp d)) (sd_fst d)))
        | exact (NotPrfR_univ k')
        | exact (i_ty _ _ _ _ _ (sd_DB d2 (efst (sd_wp d2)) (sd_fst d2))) ]. }
    injection EB as EB; exact EB.
  - (* pi *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* sig_ *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* wt *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* sup: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    pose proof (sp_lvl d); pose proof (sp_lvl d2); lia.
  - (* wrec: the motive, under an entry at the tree type's level *)
    lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    assert (Ew : wr_kw d = wr_kw d2).
    { eapply IHw1;
        [ exact HL | exact (NotPrfR_w (wr_wA d) (wr_B0 d)) | exact (wr_Dw d)
        | exact (NotPrfR_w (wr_wA d2) (wr_B0 d2)) | exact (wr_Dw d2) ]. }
    assert (EC : S k = S k').
    { eapply (IHC (ext rho _ (wr_ww d) (wr_xw d)) (ext rho' _ (wr_ww d2) (wr_xw d2)));
        [ cbn [lvls ext en_k]; rewrite HL, Ew; reflexivity
        | exact (NotPrfR_univ k)
        | exact (i_ty _ _ _ _ _ (wr_DC d (wr_ww d) (wr_xw d)))
        | exact (NotPrfR_univ k')
        | exact (i_ty _ _ _ _ _ (wr_DC d2 (wr_ww d2) (wr_xw d2))) ]. }
    injection EC as EC; exact EC.
  - (* nat_ *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* zero: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2]; lia.
  - (* succ: the scrutinee *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    eapply IHn;
      [ exact HL | exact NotPrfR_nat | exact (sc_D d)
      | exact NotPrfR_nat | exact (sc_D d2) ].
  - (* natrec: the motive, under an entry at the scrutinee's level *)
    lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    assert (Ej : rd_j d = rd_j d2).
    { eapply IHn;
        [ exact HL | exact NotPrfR_nat | exact (rd_Dn d)
        | exact NotPrfR_nat | exact (rd_Dn d2) ]. }
    assert (EC : S k = S k').
    { eapply (IHC (ext rho (natFam (rd_j d)) (rd_wn d) (rd_xn d))
                 (ext rho' (natFam (rd_j d2)) (rd_wn d2) (rd_xn d2)));
        [ cbn [lvls ext en_k]; rewrite HL, Ej; reflexivity
        | exact (NotPrfR_univ k)
        | exact (i_ty _ _ _ _ _ (rd_DC d (rd_wn d) (rd_xn d)))
        | exact (NotPrfR_univ k')
        | exact (i_ty _ _ _ _ _ (rd_DC d2 (rd_wn d2) (rd_xn d2))) ]. }
    injection EC as EC; exact EC.
  - (* univ *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* up *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* uptm: the type it lifts *) lvl_shapes D D' HN HN'.
    destruct k as [| k0]; [solve [destruct E] |].
    destruct k' as [| k0']; [solve [destruct E'] |].
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    eapply IHA;
      [ exact HL | exact (NotPrfR_univ k0) | exact (i_ty _ _ _ _ _ (ut_DA d))
      | exact (NotPrfR_univ k0') | exact (i_ty _ _ _ _ _ (ut_DA d2)) ].
  - (* prop *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* prf *) lvl_shapes D D' HN HN'; lvl_by_dec k k' E E'.
  - (* all: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    pose proof (al_lvl d); pose proof (al_lvl d2); lia.
  - (* false_: the annotation *) lvl_shapes D D' HN HN'.
    destruct E as [d Hv]; destruct E' as [d2 Hv2].
    pose proof (fl_lvl d); pose proof (fl_lvl d2); lia.
  - (* absurd *) lvl_shapes D D' HN HN'; destruct E.
  - (* eqty *) lvl_shapes D D' HN HN'; destruct E.
  - (* refl *) lvl_shapes D D' HN HN'; destruct E.
  - (* transp *) lvl_shapes D D' HN HN'; destruct E.
Qed.

(* ------------------------------------------------------------------ *)
(* FUNCTIONALITY ON TERMS.                                            *)
(*                                                                    *)
(* Every clause's branch of the decoder ends in `IsVal`, so every case   *)
(* of functionality on terms ends the same way: move the second value   *)
(* into the canonical family, where the two are compared.  That is       *)
(* kRel_of_IsVal, and it is the only bookkeeping any clause needs.       *)
(* ------------------------------------------------------------------ *)

Lemma kRel_of_IsVal {k Sy Sy' Syc} (F : kUFam k Sy) (F' : kUFam k Sy')
  (Fc : kUFam k Syc) w (x : kElAt F w) wc (xc : kElAt Fc wc)
  w' (x' : kElAt F' w') :
  IsVal F' w' x' Fc wc xc -> kRel F w x Fc wc xc -> kRel F w x F' w' x'.
Proof.
  intros [P HP] H.
  eapply kRel_trans; [exact H |].
  (* the canonical value is the second one, pulled back along P *)
  apply kRel_sym; split; [exact P |].
  eapply kEqAt_trans; [exact P | apply kto_coh | exact HP].
Qed.

(* The coercion does not depend on WHICH proof of the codes' equality it is
   given: two of them are related, which is all anything here needs. *)
Lemma kto_irr {k b b'} (c : kCode k b) (c' : kCode k b') (W : kwfc c) (W' : kwfc c')
  (e e0 : kceq c c') u x :
  kcel c' u (kto c c' W W' e u x) c' u (kto c c' W W' e0 u x).
Proof.
  exact (kto_eq c c' W W' e c c' W W' e0 u x u x (proj2 W) (kcrefl c W u x)).
Qed.

(* The level of a TYPE's reading is determined too: read it as a term of the
   universe above and apply itm_lvl. *)
Lemma ity_lvl rho rho' (HL : lvls rho = lvls rho') A k wA (FA : kUFam k wA)
  k' wA' (FA' : kUFam k' wA') :
  ITy rho A k wA FA -> ITy rho' A k' wA' FA' -> k = k'.
Proof.
  intros D D'.
  assert (E : S k = S k').
  { eapply itm_lvl;
      [ exact HL | exact (NotPrfR_univ k) | exact (i_ty _ _ _ _ _ D)
      | exact (NotPrfR_univ k') | exact (i_ty _ _ _ _ _ D') ]. }
  injection E as E; exact E.
Qed.

(* A term read at (a family equal to) the universe IS a type.  The decoder
   gives it at every former; at a non-former the clause that read it was
   ity_of, and `elFam` of the value is the family. *)
Lemma itm_univ_ty rho A k Sy (F : kUFam (S k) Sy) w (x : kElAt F w)
  (P : kceq (kAt F) (kAt (univFam k))) (D : ITm rho A (S k) Sy F w x) :
  { F0 : kUFam k w & (ITy rho A k w F0 *
    kEqAt (univFam k) w
      (kto (kAt F) (kAt (univFam k)) (famAtWf F) (famAtWf (univFam k)) P w x)
      (univFam k) w (famEl F0))%type }.
Proof.
  destruct A as
    [ i | kk A1 B1 t1 | A1 t1 | A1 B1 f a | f a | kk A1 B1 t1 a | A1 B1 q | A1 B1 q
    | kk A1 B1 | kk A1 B1 | kk A1 B1 | kk A1 B1 a f | A1 B1 C1 s1 w1
    | kk | kk | n | C z s n | kk m | jj t1 | A1 t1 | kk | kk q | jj A1 p1 | kk
    | T e | A1 t1 a | A1 a | A1 B1 t1 a e b ];
    try (exists (elFam (kto (kAt F) (kAt (univFam k)) (famAtWf F)
                         (famAtWf (univFam k)) P w x)); split;
         [ apply ity_of;
           [ exact I
           | exact (i_conv rho _ (S k) Sy F (euniv k) (univFam k) w x P D) ]
         | apply kEqAt_sym; apply famEl_elFam_rel ]).
  all: pose proof (itm_inv _ _ _ _ _ _ _ D) as E;
       destruct E as [[_ [q0 Hq0]] | E];
       [ solve [exfalso; refine (NotPrfR_univ k q0 _);
                eapply tyeq_trans;
                  [apply tyeq_sym; exact (ceq_ty F (univFam k) P) | exact Hq0]] |];
       cbn [TmShape TyVal UpShape] in E;
       destruct E as [d [Q HQ]];
       exists (ty_F0 d); split;
       [ exact (ty_D d)
       | eapply kEqAt_trans;
           [ exact (famAtSelf (univFam k)) | apply kto_irr | exact HQ ] ].
Qed.

(* ---- the clauses that are pure bookkeeping ---- *)

(* Proof terms.  A Prf-family relates all of its elements, so nothing about
   the subject is needed: the layer-1 relatedness of the two realisers, which
   FTm carries, is the whole argument. *)
Lemma fun_proof rho t k j wp (xp : kElAt (propFam j) wp) (h : propVal xp)
  w (g : Good (eprf wp) w) :
  FTm rho t k (eprf wp) (prfF k xp) w (prfElem w h g).
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  exact (kRel_of_total (prfF k xp) F' Pc
           (TotalFam_ceq (prfF k xp) F' Pc (prf_total k j wp xp)) w _ w' x' Hrel).
Qed.

(* Conversion of the type: compose the coercion with the hypothesis. *)
Lemma fun_conv rho t k Sy (F : kUFam k Sy) Sy' (F' : kUFam k Sy')
  (P : kceq (kAt F) (kAt F')) w (x : kElAt F w) (IH : FTm rho t k Sy F w x) :
  FTm rho t k Sy' F' w
      (kto (kAt F) (kAt F') (famAtWf F) (famAtWf F') P w x).
Proof.
  intros rho2 Sy2 F2 w2 x2 HR Pc Hrel D2.
  eapply kRel_trans;
    [ apply kRel_sym; split; [exact P | apply kto_coh] |].
  exact (IH rho2 Sy2 F2 w2 x2 HR
           (ktrU (kAt F) (kAt F') (kAt F2) (famAtWf F) (famAtWf F') (famAtWf F2)
              P Pc) Hrel D2).
Qed.

(* Variables.  This is what EntryRel's package formulation was for: the two
   entries are related to the same entry of the second environment, and
   composing that is EntryRel_trans. *)
Lemma fun_var0 rho k Sy (F : kUFam k Sy) w (x : kElAt F w) :
  FTm (ext rho F w x) (var_tm 0) k Sy F w x.
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E.
  destruct rho' as [| en' rho0']; [cbn [ext EnvRel] in HR; destruct HR |].
  cbn [ext EnvRel] in HR; destruct HR as [_ Hen].
  cbn [TmInv TmShape VarShape] in E.
  destruct E as [[HT _] | E].
  - exact (kRel_of_total F F' Pc HT w x w' x' Hrel).
  - eapply EntryRel_at; eapply EntryRel_trans;
      [exact Hen | apply EntryRel_sym; exact E].
Qed.

Lemma fun_varS rho en i k Sy (F : kUFam k Sy) w (x : kElAt F w)
  (IH : FTm rho (var_tm i) k Sy F w x) :
  FTm (en :: rho) (var_tm (S i)) k Sy F w x.
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E.
  destruct rho' as [| en' rho0']; [cbn [EnvRel] in HR; destruct HR |].
  cbn [EnvRel] in HR; destruct HR as [HR0 _].
  cbn [TmInv TmShape VarShape] in E.
  destruct E as [[HT _] | [x0 [D0 HE]]].
  - exact (kRel_of_total F F' Pc HT w x w' x' Hrel).
  - eapply kRel_trans;
      [ exact (IH rho0' Sy' F' w' x0 HR0 Pc Hrel D0)
      | apply (proj1 (kRel_same F' w' x0 w' x')); apply kEqAt_sym; exact HE ].
Qed.

Lemma fun_zero rho k :
  FTm rho (zero k) k enat (natFam k) ezero (natE 0 NatAt_zero).
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E;
    cbn [TmInv TmShape ZeroVal Shaped] in E.
  destruct E as [[HT _] | [Ek Hv]].
  - exact (kRel_of_total (natFam k) F' Pc HT ezero _ w' x' Hrel).
  - eapply kRel_of_IsVal; [exact Hv | apply kRel_refl].
Qed.

(* A type, read as an element of the universe above it.  This is where
   functionality on types enters functionality on terms: the second
   derivation's value is a family (itm_univ_ty), the two families are equal by
   the hypothesis, and the universe's own equality IS that equality. *)
Lemma fun_ty rho A k w (F : kUFam k w) (IH : FTy rho A k w F) :
  FTm rho A (S k) (euniv k) (univFam k) w (famEl F).
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose (P' := knsymU (kAt (univFam k)) (kAt F') Pc).
  destruct (itm_univ_ty rho' A k Sy' F' w' x' P' D') as [F0' [D0' HE]].
  assert (Hty : eqty k w w').
  { apply (Rel_univ_elim (euniv k) k w w' (eval_whnf _ (whnf_univ k))).
    apply (Rel_tyeq Sy' (euniv k) w w');
      [ apply tyeq_sym; exact (ceq_ty (univFam k) F' Pc) | exact Hrel ]. }
  assert (Hc : kceq (kAt F) (kAt F0'))
    by exact (IH rho' w' F0' HR (ex_intro _ k Hty) D0').
  eapply kRel_of_IsVal; [exists P'; exact HE |].
  apply (proj1 (kRel_same (univFam k) _ _ _ _)).
  apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
  exact (famCeq_all F F0' Hc v h pf v' h' pf').
Qed.

Lemma fun_false rho k (g : Good eprop efalse) :
  FTm rho (false_ k) k eprop (propFam k) efalse (propElem efalse False g).
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E;
    cbn [TmInv TmShape FalseVal Shaped] in E.
  destruct E as [[HT _] | [d Hv]].
  - exact (kRel_of_total (propFam k) F' Pc HT efalse _ w' x' Hrel).
  - eapply kRel_of_IsVal; [exact Hv |].
    apply (proj1 (kRel_same (propFam k) _ _ _ _)).
    apply propEq_iff; split; [split; exact (fun h => h) | exact g].
Qed.

(* A successor.  The index of the two values is the successor of the
   subterms', so all that is needed is the subterm's own relatedness -- and to
   get at it, the layer-1 relation of the two realisers has to be peeled, which
   is what NatPer's succ clause says. *)
Lemma NatPer_succ_inv c d a b (Ec : c = esucc a) (Ed : d = esucc b) :
  NatPer c d -> NatPer a b.
Proof.
  intros H; destruct H as [x y Hx Hy | x y x0 y0 Hx Hy H | x y Hsx Hsy]; subst.
  - exfalso; discriminate (eval_det _ _ _ (ev_succ a) Hx).
  - injection (eval_det _ _ _ (ev_succ a) Hx) as Ea;
      injection (eval_det _ _ _ (ev_succ b) Hy) as Eb; subst; exact H.
  - exfalso; destruct Hsx as [N [HN Hst]].
    rewrite <- (eval_det _ _ _ (ev_succ a) HN) in Hst.
    exact (stuck_not_value _ Hst (v_succ a)).
Qed.

Lemma fun_succ rho k n wn (x : kElAt (natFam k) wn)
  (IH : FTm rho n k enat (natFam k) wn x) :
  FTm rho (succ n) k enat (natFam k) (esucc wn) (natSucc x).
Proof.
  intros rho' Sy' F' w' x' HR Pc Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E;
    cbn [TmInv TmShape SuccVal Shaped] in E.
  destruct E as [[HT _] | [d Hv]].
  - exact (kRel_of_total (natFam k) F' Pc HT (esucc wn) _ w' x' Hrel).
  - (* the second realiser is a successor too, so layer 1 peels *)
    assert (Hs : Rel enat (esucc wn) (esucc (sc_wn d))).
    { destruct Hv as [Q HQ].
      eapply Rel_trans;
        [ apply (Rel_tyeq Sy' enat (esucc wn) w');
            [ apply tyeq_sym; exact (ceq_ty (natFam k) F' Pc) | exact Hrel ]
        | exact (proj2 (proj1 (natEq_iff _ _) HQ)) ]. }
    assert (Hn : Rel enat wn (sc_wn d))
      by (apply Rel_nat_intro;
          [ apply gt_nat | apply ev_nat
          | apply (NatPer_succ_inv (esucc wn) (esucc (sc_wn d)) wn (sc_wn d)
                     eq_refl eq_refl);
            exact (Rel_nat_elim enat (esucc wn) (esucc (sc_wn d)) ev_nat Hs) ]).
    pose proof (IH rho' enat (natFam k) (sc_wn d) (sc_xn d) HR
                  (famAtSelf (natFam k)) Hn (sc_D d)) as Hx.
    eapply kRel_of_IsVal; [exact Hv |].
    apply (proj1 (kRel_same (natFam k) _ _ _ _)).
    apply natEq_iff; split;
      [ unfold natSucc; rewrite !natIdx_natE;
        exact (f_equal S
                 (proj1 (proj1 (natEq_iff _ _)
                           (proj2 (kRel_same (natFam k) _ _ _ _) Hx))))
      | exact Hs ].
Qed.

(* ---- Prf: the proposition's own functionality, at whatever level it was
     read, plus the layer-1 equality of the two Prf realisers. ---- *)
Lemma fun_prf rho p k j wp (xp : kElAt (propFam j) wp)
  (Dp : ITm rho p j eprop (propFam j) wp xp)
  (IHp : FTm rho p j eprop (propFam j) wp xp) :
  FTy rho (prf k p) k (eprf wp) (prfF k xp).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_prf_inv rho' (prf k p) k w' F' D') as [j' [wp' [xp' [Dp' Hc']]]].
  pose proof (itm_lvl p rho rho' (lvls_of_EnvRel _ _ HR) _ _ _ _ _
                NotPrfR_prop Dp _ _ _ _ _ NotPrfR_prop Dp') as Ej.
  subst j'.
  eapply ktrU;
    [ exact (famAtWf (prfF k xp)) | exact (famAtWf (prfF k xp'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  assert (Htp : tyeq (eprf wp) (eprf wp')).
  { eapply tyeq_trans; [exact Hty | exact (ceq_ty F' (prfF k xp') Hc')]. }
  destruct Htp as [n Hn].
  assert (Hpr : PR wp wp')
    by (eapply eqty_prf_inv; [exact Hn | apply ev_prf_self | apply ev_prf_self]).
  assert (Hrel : Rel eprop wp wp')
    by (apply Rel_prop_intro;
        [exact good_ty_prop | apply eval_whnf, whnf_prop | exact Hpr]).
  apply prfFam_ceq; [exists n; exact Hn |].
  exact (proj1 (proj1 (propEq_iff xp xp')
                  (kRel_at (IHp rho' eprop (propFam j) wp' xp' HR
                              (famAtSelf (propFam j)) Hrel Dp')))).
Qed.

(* ---- Pi, Sigma and W.  The two components' hypotheses are exactly what the
     heterogeneous layer-1 inversions produce, and the codomain's needs the
     arguments to be layer-1 related -- which is `kRel_rel` of the arguments
     brought down to the domain's own level.  Each of the two GAPS is
     determined once its component's level is, by cancellation, and the two
     equations that witness it are then equal by UIP (`upF_pirr`). ---- *)
Lemma fun_pi rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
  wA (FA : kUFam i wA) B0
  (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
  (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
  (redB : forall u x, reds (eapp B0 u) (wB u x))
  (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
     kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
  (gPi : eqty k (epi wA B0) (epi wA B0))
  (DA : ITy rho A i wA FA) (IHA : FTy rho A i wA FA)
  (DB : forall u x,
     ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x))
  (IHB : forall u x,
     FTy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) :
  FTy rho (pi k A B) k (epi wA B0)
      (piFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
         redB cohB gPi).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_pi_inv rho' (pi k A B) k w' F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gPi'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  (* the domains' level, hence the first gap; the two equations then agree *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRel _ _ HR) A i wA FA i' wA' FA' DA DA')
    as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  eapply ktrU;
    [ exact (famAtWf (piFam k wA B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gPi))
    | exact (famAtWf (piFam k wA' B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gPi'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  assert (Htp : tyeq (epi wA B0) (epi wA' B0'))
    by (eapply tyeq_trans; [exact Hty | exact Hw']).
  destruct Htp as [n Hn].
  assert (HdA : eqty n wA wA')
    by (eapply eqty_pi_dom; [exact Hn | apply ev_pi_self | apply ev_pi_self]).
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (IHA rho' wA' FA' HR (ex_intro _ n HdA) DA').
  apply piFam_ceq.
  - exists n; exact Hn.
  - apply upF_ceq; exact HA.
  - (* the codomains, at arguments brought down to the domain's own level *)
    intros u x u' y Hrel.
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    assert (Hru : Rel wA u u')
      by exact (kRel_rel FA u (dnEl dA k EA FA u x) FA' u'
                  (dnEl dA k EA FA' u' y) (conj HA Hd)).
    assert (HE : EnvRel (ext rho FA u (dnEl dA k EA FA u x))
                   (ext rho' FA' u' (dnEl dA k EA FA' u' y)))
      by (apply EnvRel_ext; [exact HR | exact (conj HA Hd)]).
    assert (Htb : tyeq (wB u x) (wB' u' y)).
    { exists n.
      eapply eqty_red;
        [ eapply eqty_pi_cod;
            [ exact Hn | apply ev_pi_self | apply ev_pi_self
            | exact Hru ]
        | apply redB | apply redB' ]. }
    (* the codomains' level, hence the second gap *)
    pose proof (ity_lvl (ext rho FA u (dnEl dA k EA FA u x))
                  (ext rho' FA' u' (dnEl dA k EA FA' u' y))
                  (lvls_of_EnvRel _ _ HE)
                  B j (wB u x) (FB u x) j' (wB' u' y) (FB' u' y)
                  (DB u x) (DB' u' y)) as Ej.
    subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    exact (IHB u x (ext rho' FA' u' (dnEl dA k EA FA' u' y)) (wB' u' y) (FB' u' y)
             HE Htb (DB' u' y)).
Qed.

Lemma fun_sig rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
  wA (FA : kUFam i wA) B0
  (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
  (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
  (redB : forall u x, reds (eapp B0 u) (wB u x))
  (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
     kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
  (gSig : eqty k (esig wA B0) (esig wA B0))
  (DA : ITy rho A i wA FA) (IHA : FTy rho A i wA FA)
  (DB : forall u x,
     ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x))
  (IHB : forall u x,
     FTy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) :
  FTy rho (sig_ k A B) k (esig wA B0)
      (sigFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
         redB cohB gSig).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_sig_inv rho' (sig_ k A B) k w' F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gSig'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  (* the domains' level, hence the first gap; the two equations then agree *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRel _ _ HR) A i wA FA i' wA' FA' DA DA')
    as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  eapply ktrU;
    [ exact (famAtWf (sigFam k wA B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gSig))
    | exact (famAtWf (sigFam k wA' B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gSig'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  assert (Htp : tyeq (esig wA B0) (esig wA' B0'))
    by (eapply tyeq_trans; [exact Hty | exact Hw']).
  destruct Htp as [n Hn].
  assert (HdA : eqty n wA wA')
    by (eapply eqty_sig_dom; [exact Hn | apply ev_sig_self | apply ev_sig_self]).
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (IHA rho' wA' FA' HR (ex_intro _ n HdA) DA').
  apply sigFam_ceq.
  - exists n; exact Hn.
  - apply upF_ceq; exact HA.
  - (* the codomains, at arguments brought down to the domain's own level *)
    intros u x u' y Hrel.
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    assert (Hru : Rel wA u u')
      by exact (kRel_rel FA u (dnEl dA k EA FA u x) FA' u'
                  (dnEl dA k EA FA' u' y) (conj HA Hd)).
    assert (HE : EnvRel (ext rho FA u (dnEl dA k EA FA u x))
                   (ext rho' FA' u' (dnEl dA k EA FA' u' y)))
      by (apply EnvRel_ext; [exact HR | exact (conj HA Hd)]).
    assert (Htb : tyeq (wB u x) (wB' u' y)).
    { exists n.
      eapply eqty_red;
        [ eapply eqty_sig_cod;
            [ exact Hn | apply ev_sig_self | apply ev_sig_self
            | exact Hru ]
        | apply redB | apply redB' ]. }
    (* the codomains' level, hence the second gap *)
    pose proof (ity_lvl (ext rho FA u (dnEl dA k EA FA u x))
                  (ext rho' FA' u' (dnEl dA k EA FA' u' y))
                  (lvls_of_EnvRel _ _ HE)
                  B j (wB u x) (FB u x) j' (wB' u' y) (FB' u' y)
                  (DB u x) (DB' u' y)) as Ej.
    subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    exact (IHB u x (ext rho' FA' u' (dnEl dA k EA FA' u' y)) (wB' u' y) (FB' u' y)
             HE Htb (DB' u' y)).
Qed.

Lemma fun_w rho A B k i j dA dB (EA : dA + i = k) (EB : dB + j = k)
  wA (FA : kUFam i wA) B0
  (wB : forall u, kElAt (upF dA k EA FA) u -> etm)
  (FB : forall u (x : kElAt (upF dA k EA FA) u), kUFam j (wB u x))
  (redB : forall u x, reds (eapp B0 u) (wB u x))
  (cohB : forall u x u' x', kEqAt (upF dA k EA FA) u x (upF dA k EA FA) u' x' ->
     kceq (kAt (upF dB k EB (FB u x))) (kAt (upF dB k EB (FB u' x'))))
  (gW : eqty k (ew wA B0) (ew wA B0))
  (DA : ITy rho A i wA FA) (IHA : FTy rho A i wA FA)
  (DB : forall u x,
     ITy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x))
  (IHB : forall u x,
     FTy (ext rho FA u (dnEl dA k EA FA u x)) B j (wB u x) (FB u x)) :
  FTy rho (wt k A B) k (ew wA B0)
      (wFam k wA B0 (upF dA k EA FA) wB (fun u x => upF dB k EB (FB u x))
         redB cohB gW).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_w_inv rho' (wt k A B) k w' F' D') as
    [i' [j' [dA' [dB' [EA' [EB' [wA' [FA' [B0' [wB' [FB' [redB' [cohB' [gW'
      [[[DA' DB'] Hw'] Hc']]]]]]]]]]]]]]].
  (* the domains' level, hence the first gap; the two equations then agree *)
  pose proof (ity_lvl rho rho' (lvls_of_EnvRel _ _ HR) A i wA FA i' wA' FA' DA DA')
    as Ei; subst i'.
  assert (EdA : dA' = dA) by lia; subst dA'.
  pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EA' EA) as EEA; subst EA'.
  eapply ktrU;
    [ exact (famAtWf (wFam k wA B0 (upF dA k EA FA) wB
                        (fun u x => upF dB k EB (FB u x)) redB cohB gW))
    | exact (famAtWf (wFam k wA' B0' (upF dA k EA FA') wB'
                        (fun u x => upF dB' k EB' (FB' u x)) redB' cohB' gW'))
    | exact (famAtWf F') | | apply knsymU; exact Hc' ].
  assert (Htp : tyeq (ew wA B0) (ew wA' B0'))
    by (eapply tyeq_trans; [exact Hty | exact Hw']).
  destruct Htp as [n Hn].
  assert (HdA : eqty n wA wA')
    by (eapply eqty_w_dom; [exact Hn | apply ev_w_self | apply ev_w_self]).
  assert (HA : kceq (kAt FA) (kAt FA'))
    by exact (IHA rho' wA' FA' HR (ex_intro _ n HdA) DA').
  apply wFam_ceq.
  - exists n; exact Hn.
  - apply upF_ceq; exact HA.
  - (* the codomains, at arguments brought down to the domain's own level *)
    intros u x u' y Hrel.
    assert (Hd : kEqAt FA u (dnEl dA k EA FA u x) FA' u' (dnEl dA k EA FA' u' y))
      by exact (dnEl_eq dA k EA FA u x FA' u' y HA Hrel).
    assert (Hru : Rel wA u u')
      by exact (kRel_rel FA u (dnEl dA k EA FA u x) FA' u'
                  (dnEl dA k EA FA' u' y) (conj HA Hd)).
    assert (HE : EnvRel (ext rho FA u (dnEl dA k EA FA u x))
                   (ext rho' FA' u' (dnEl dA k EA FA' u' y)))
      by (apply EnvRel_ext; [exact HR | exact (conj HA Hd)]).
    assert (Htb : tyeq (wB u x) (wB' u' y)).
    { exists n.
      eapply eqty_red;
        [ eapply eqty_w_cod;
            [ exact Hn | apply ev_w_self | apply ev_w_self
            | exact Hru ]
        | apply redB | apply redB' ]. }
    (* the codomains' level, hence the second gap *)
    pose proof (ity_lvl (ext rho FA u (dnEl dA k EA FA u x))
                  (ext rho' FA' u' (dnEl dA k EA FA' u' y))
                  (lvls_of_EnvRel _ _ HE)
                  B j (wB u x) (FB u x) j' (wB' u' y) (FB' u' y)
                  (DB u x) (DB' u' y)) as Ej.
    subst j'.
    assert (EdB : dB' = dB) by lia; subst dB'.
    pose proof (Eqdep_dec.UIP_dec Nat.eq_dec EB' EB) as EEB; subst EB'.
    apply upF_ceq.
    exact (IHB u x (ext rho' FA' u' (dnEl dA k EA FA' u' y)) (wB' u' y) (FB' u' y)
             HE Htb (DB' u' y)).
Qed.

(* ------------------------------------------------------------------ *)
(* THE REALISER IS THE ERASURE.                                       *)
(*                                                                    *)
(* The realisers are free indices of ITy and ITm, pinned by one        *)
(* equation per clause (Interp/Def.v's header says why: equations do    *)
(* not propagate, casts do).  This says the pins determine them        *)
(* completely -- every clause either carries its own pin or builds its  *)
(* realiser from its subderivations'.                                   *)
(*                                                                    *)
(* It is what lets LAYER 1 be applied to them.  Functionality needs the *)
(* two readings of one syntactic type to have layer-1 equal realisers,  *)
(* and only layer 1 proves that -- from a typing derivation and related *)
(* substitutions.                                                      *)
(* ------------------------------------------------------------------ *)

Definition ErsTy (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Prop :=
  w = ers rho A.

Definition ErsTm (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy)
  (w : etm) (x : kElAt F w) : Prop := w = ers rho t.

Lemma ers_of_ITm : forall rho t k Sy (F : kUFam k Sy) w (x : kElAt F w),
  ITm rho t k Sy F w x -> ErsTm rho t k Sy F w x.
Proof.
  apply (ITm_mut (fun rho A k w F _ => ErsTy rho A k w F)
                 (fun rho t k Sy F w x _ => ErsTm rho t k Sy F w x));
    unfold ErsTy, ErsTm.
  - (* ity_nat *) reflexivity.
  - (* ity_prop *) reflexivity.
  - (* ity_univ *) reflexivity.
  - (* ity_prf *) intros rho k j p wp xp Dp IHp; exact (f_equal eprf IHp).
  - (* ity_pi *) intros rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gPi
      Ew DA IHA DB IHB; exact Ew.
  - (* ity_sig *) intros rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gSig
      Ew DA IHA DB IHB; exact Ew.
  - (* ity_w *) intros rho A B k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
      Ew DA IHA DB IHB; exact Ew.
  - (* ity_up *) intros rho A k w F D IH; exact IH.
  - (* ity_of *) intros rho A k w v nf Dv IHv; exact IHv.
  - (* ity_conv *) intros rho A k w F F' P D IH; exact IH.
  - (* i_ty *) intros rho A k w F D IH; exact IH.
  - (* i_var0 *) reflexivity.
  - (* i_varS *) intros rho en i k Sy F w x D IH; exact IH.
  - (* i_zero *) reflexivity.
  - (* i_succ *) intros rho k n wn x D IH; exact (f_equal esucc IH).
  - (* i_lam *) intros rho A B t k i j dA dB EA EB wA FA B0 wB FB redB cohB gPi
      w wt xt redt xtext gd Ew Ep DA IHA DB IHB Dt IHt; exact Ew.
  - (* i_app *) intros rho A B f a k i j dA dB EA EB wA FA B0 wB FB redB cohB gPi
      wf xf wa xa Ep DA IHA DB IHB Df IHf Da IHa; exact (f_equal2 eapp IHf IHa).
  - (* i_pair *) intros rho A B t a k i j dA dB EA EB wA FA B0 wB FB redB cohB
      gSig wt xt wa xa g Ep DA IHA DB IHB Dt IHt Da IHa;
      exact (f_equal2 epair IHt IHa).
  - (* i_fst *) intros rho A B p k i j dA dB EA EB wA FA B0 wB FB redB cohB gSig
      wp xp Ep DA IHA DB IHB Dp IHp; exact (f_equal efst IHp).
  - (* i_snd *) intros rho A B p k i j dA dB EA EB wA FA B0 wB FB redB cohB gSig
      wp xp Ep DA IHA DB IHB Dp IHp; exact (f_equal esnd IHp).
  - (* i_sup *) intros rho A B a f k i j dA dB EA EB wA FA B0 wB FB redB cohB gW
      Bbr redBbr gBr wa xa wf xf gd Ew DA IHA DB IHB Da IHa Df IHf;
      exact (f_equal2 esup IHa IHf).
  - (* i_wrec *) intros rho A B C s w0 k i j m n dA dB dBn dC EA EB EBn EC En
      wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr
      gf gih ws xs redS stepSrel ww xw ESr Ew ESC DA IHA DB IHB DC IHC
      Dstep IHstep Dw IHw.
    rewrite IHw, ESr; reflexivity.
  - (* i_natrec *) intros rho C z s n k j SC FC cohC S0 wz xz ws xs redS wn xn
      ES DC IHC Dz IHz Ds IHs Dn IHn.
    rewrite IHz, IHn, ES; reflexivity.
  - (* i_false *) reflexivity.
  - (* i_all *) intros rho jj A p k wA FA wp xp w g Ew DA IHA Dp IHp; exact Ew.
  - (* i_proof *) intros rho t p k j wp xp h w g Ew Dp IHp; exact Ew.
  - (* i_up_tm *) intros rho A t k Sy F w x DA IHA D IH; exact IH.
  - (* i_conv *) intros rho t k Sy F Sy' F' w x P D IH; exact IH.
Qed.

Lemma ers_of_ITy : forall rho A k w (F : kUFam k w),
  ITy rho A k w F -> w = ers rho A.
Proof.
  intros rho A k w F D.
  exact (ers_of_ITm rho A (S k) (euniv k) (univFam k) w (famEl F)
           (i_ty rho A k w F D)).
Qed.
