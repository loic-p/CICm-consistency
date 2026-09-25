From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Lift
  Interp.PiFam Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Def Interp.Inv Interp.Ctx Interp.Subst.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* Functionality of the interpretation, up to isomorphism.

   This is what the fundamental lemma's VARIABLE case needs: the environment
   records whatever family it was built with, and the statement of 9.2 is
   handed a possibly different interpretation of the same context type, so the
   two have to be reconciled.  It is also what the blueprint's 9.1 plans for
   ("define it as an inductive relation and prove functionality").

   Two features of the statement are forced.

   It is PROP-VALUED.  `iso` and `kRel` are Props, so the motive may
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
    EnvRel rho rho' -> tyeq w w' -> ITy rho' A k w' F' -> iso (kAt F) (kAt F').

Definition FTm (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy)
               (w : etm) (x : kElAt F w) : Prop :=
  forall rho' Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w'),
    EnvRel rho rho' -> iso (kAt F) (kAt F') -> Rel Sy' w w' ->
    ITm rho' t k Sy' F' w' x' -> kRel F F' w x w' x'.

(* Small layer-1 facts the clauses below want by name. *)
Lemma good_ty_prop : Good_ty eprop.
Proof. exists 0; apply eqty_prop; apply eval_whnf, whnf_prop. Qed.

Lemma ev_pi_self A0 B0 : eval (epi A0 B0) (epi A0 B0).
Proof. apply eval_whnf, whnf_pi. Qed.

Lemma ev_sig_self A0 B0 : eval (esig A0 B0) (esig A0 B0).
Proof. apply eval_whnf, whnf_sig. Qed.

Lemma ev_prf_self p : eval (eprf p) (eprf p).
Proof. apply eval_whnf, whnf_prf. Qed.

(* ------------------------------------------------------------------ *)
(* The clauses whose family is fixed by the clause itself.            *)
(* ------------------------------------------------------------------ *)

Lemma fun_nat rho k : FTy rho nat_ k enat (natFam k).
Proof.
  intros rho' w' F' HR Hty D'; apply iso_sym.
  exact (ity_nat_inv rho' nat_ k w' F' D').
Qed.

Lemma fun_prop rho k : FTy rho prop k eprop (propFam k).
Proof.
  intros rho' w' F' HR Hty D'; apply iso_sym.
  exact (ity_prop_inv rho' prop k w' F' D').
Qed.

Lemma fun_univ rho m : FTy rho (univ m) (S m) (euniv m) (univFam m).
Proof.
  intros rho' w' F' HR Hty D'; apply iso_sym.
  exact (ity_univ_iso rho' (univ m) (S m) w' F' D').
Qed.

(* Prf: the two truth values are the same because the two readings of the
   proposition are related, and that is the induction hypothesis at p. *)
Lemma fun_prf rho p k wp (xp : kElAt (propFam 0) wp)
  (IHp : FTm rho p 0 eprop (propFam 0) wp xp) :
  FTy rho (prf p) k (eprf wp) (prfF k xp).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_prf_inv rho' (prf p) k w' F' D') as [wp' [xp' [Dp' Hiso']]].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  assert (Htp : tyeq (eprf wp) (eprf wp')).
  { eapply tyeq_trans; [exact Hty | exact (iso_ty F' (prfF k xp') Hiso')]. }
  destruct Htp as [n Hn].
  assert (Hpr : PR wp wp')
    by (eapply eqty_prf_inv; [exact Hn | apply ev_prf_self | apply ev_prf_self]).
  assert (Hrel : Rel eprop wp wp')
    by (apply Rel_prop_intro;
        [exact good_ty_prop | apply eval_whnf, whnf_prop | exact Hpr]).
  apply prfFam_iso; [exists n; exact Hn |].
  exact (proj1 (proj1 (propEq_iff xp xp')
                  (proj2 (kRel_same (propFam 0) _ _ _ _)
                     (IHp rho' eprop (propFam 0) wp' xp' HR
                        (iso_self (propFam 0)) Hrel Dp')))).
Qed.

(* The universe lift: the level-agnostic hypothesis descends unchanged,
   because `up` leaves the realiser alone. *)
Lemma fun_up rho A k w (F0 : kUFam k w) (IHA : FTy rho A k w F0) :
  FTy rho (up (univ (S k)) A) (S k) w (famLiftK F0).
Proof.
  intros rho' w' F' HR Hty D'.
  pose proof (ity_up_inv rho' (up (univ (S k)) A) (S k) w' F' D') as Hup.
  cbn [UpDec] in Hup.
  destruct Hup as [F1 [[Ej DA'] Hiso']].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply famLiftK_iso.
  exact (IHA rho' w' F1 HR Hty DA').
Qed.

(* ------------------------------------------------------------------ *)
(* Pi and Sigma.  The two components' hypotheses are exactly what the  *)
(* heterogeneous layer-1 inversions produce, and the codomain's needs   *)
(* the arguments to be layer-1 related -- which is kRel_rel, cast along *)
(* the domains' own equality.                                          *)
(* ------------------------------------------------------------------ *)

Lemma fun_pi rho A B k wA (FA : kUFam k wA) B0
  (wB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
  (redB : forall u x, reds (eapp B0 u) (wB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (epi wA B0) (epi wA B0))
  (IHA : FTy rho A k wA FA)
  (IHB : forall u x, FTy (ext rho FA u x) B k (wB u x) (FB u x)) :
  FTy rho (pi A B) k (epi wA B0) (piFam k wA B0 FA wB FB redB isoB gPi).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_pi_inv rho' (pi A B) k w' F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  assert (Htp : tyeq (epi wA B0) (epi wA' B0'))
    by (eapply tyeq_trans; [exact Hty | exact Hw']).
  destruct Htp as [n Hn].
  assert (HdA : eqty n wA wA')
    by (eapply eqty_pi_dom; [exact Hn | apply ev_pi_self | apply ev_pi_self]).
  apply piFam_iso.
  - exists n; exact Hn.
  - exact (IHA rho' wA' FA' HR (ex_intro _ n HdA) DA').
  - intros u x u' x' Hrel.
    apply (IHB u x (ext rho' FA' u' x') (wB' u' x') (FB' u' x')).
    + apply EnvRel_ext; [exact HR | exact Hrel].
    + exists n.
      eapply eqty_red;
        [ eapply eqty_pi_cod;
            [ exact Hn | apply ev_pi_self | apply ev_pi_self
            | apply (proj2 (Rel_resp n wA wA' HdA u u'));
              exact (kRel_rel FA FA' u x u' x' Hrel) ]
        | apply redB | apply redB' ].
    + apply DB'.
Qed.

Lemma fun_sig rho A B k wA (FA : kUFam k wA) B0
  (wB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (wB u x))
  (redB : forall u x, reds (eapp B0 u) (wB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gSig : eqty k (esig wA B0) (esig wA B0))
  (IHA : FTy rho A k wA FA)
  (IHB : forall u x, FTy (ext rho FA u x) B k (wB u x) (FB u x)) :
  FTy rho (sig_ A B) k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig).
Proof.
  intros rho' w' F' HR Hty D'.
  destruct (ity_sig_inv rho' (sig_ A B) k w' F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  assert (Htp : tyeq (esig wA B0) (esig wA' B0'))
    by (eapply tyeq_trans; [exact Hty | exact Hw']).
  destruct Htp as [n Hn].
  assert (HdA : eqty n wA wA')
    by (eapply eqty_sig_dom; [exact Hn | apply ev_sig_self | apply ev_sig_self]).
  apply sigFam_iso.
  - exists n; exact Hn.
  - exact (IHA rho' wA' FA' HR (ex_intro _ n HdA) DA').
  - intros u x u' x' Hrel.
    apply (IHB u x (ext rho' FA' u' x') (wB' u' x') (FB' u' x')).
    + apply EnvRel_ext; [exact HR | exact Hrel].
    + exists n.
      eapply eqty_red;
        [ eapply eqty_sig_cod;
            [ exact Hn | apply ev_sig_self | apply ev_sig_self
            | apply (proj2 (Rel_resp n wA wA' HdA u u'));
              exact (kRel_rel FA FA' u x u' x' Hrel) ]
        | apply redB | apply redB' ].
    + apply DB'.
Qed.

(* ------------------------------------------------------------------ *)
(* And the clause that reads an arbitrary term of a universe as a type. *)
(* This is the one place that needs the layer-1 equality AT THE LEVEL   *)
(* of the family, because the universe's own equality contains it; the  *)
(* hypothesis is level-agnostic, so it has to be restricted -- which is *)
(* exactly what Layer1/Elim.v's tau_restrict does.                      *)
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
  all: (destruct Hof as [v' [Dv' E]];
        eapply iso_trans; [| exact (iso_sym _ _ E)];
        apply (uEq_iso v v');
        apply (proj2 (kRel_same (univFam k) _ _ _ _));
        exact (IHv rho' (euniv k) (univFam k) w' v' HR (iso_self (univFam k))
                 Hrel Dv')).
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
   prfF" keeps it cast-free and makes it transfer along isomorphisms. *)
Definition TotalFam {k u} (F : kUFam k u) : Prop :=
  forall w (x : kElAt F w) w' (x' : kElAt F w'), Rel u w w' -> kEqAt F w x w' x'.

Lemma prf_total k wp (xp : kElAt (propFam 0) wp) : TotalFam (prfF k xp).
Proof. intros w x w' x' Hr; apply prfEq_of; exact Hr. Qed.

(* Totality transfers along an isomorphism, which is what makes it usable
   after i_conv has moved the family. *)
Lemma TotalFam_iso {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : iso (kAt F) (kAt F')) : TotalFam F -> TotalFam F'.
Proof.
  intros HT w y w' y' Hr.
  eapply kEqC_trans;
    [ apply kEqC_sym; apply (cpullK_to (kAt F) (kAt F') P) |].
  eapply kEqC_trans; [| apply (cpullK_to (kAt F) (kAt F') P)].
  apply ctoK_eq.
  apply HT.
  destruct (iso_ty F F' P) as [n Hn].
  eapply Rel_cast; [apply eqty_sym; exact Hn | exact Hr].
Qed.

(* What the i_proof case of every clause then reduces to. *)
Lemma kRel_of_total {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : iso (kAt F) (kAt F')) (HT : TotalFam F') w (x : kElAt F w) w' (x' : kElAt F' w') :
  Rel u' w w' -> kRel F F' w x w' x'.
Proof.
  intros Hr; exists P; apply HT; exact Hr.
Qed.

(* i_conv.  A conversion on the SECOND derivation is absorbed by composing
   with the transport, exactly as hetC does. *)
Lemma kRel_conv_r {k u u1 u2} (F : kUFam k u) (F1 : kUFam k u1) (F2 : kUFam k u2)
  (P : iso (kAt F1) (kAt F2)) w (x : kElAt F w) w' (x1 : kElAt F1 w') :
  kRel F F1 w x w' x1 -> kRel F F2 w x w' (ctoK (kAt F1) (kAt F2) P w' x1).
Proof.
  intros H; eapply hetC_trans; [exact H | apply hetC_to].
Qed.

(* i_ty.  Reading a family as an element of the universe and back is the
   identity up to the universe's equality -- the direction Interp/Univ.v does
   NOT give as an equation, because the element carries a proof. *)
Lemma famEl_elFam_rel {k u} (v : kElAt (univFam k) u) :
  kEqAt (univFam k) u (famEl (elFam v)) u v.
Proof.
  unfold kEqAt, kUst, kAt, univFam, uf_at, uf_c, Ust, Stage_next, kUEq,
    famEl, elFam, uBridge in *; cbn in *.
  revert v; unfold sU, sUEq in *;
    destruct (Nat.eq_dec k k) as [E | NE]; [| exfalso; exact (NE eq_refl)].
  intros v; split; [apply (uf_ty (proj1_sig v)) | intros; apply uf_coh].
Qed.

(* Transporting along the identity isomorphism does nothing, up to the
   family's own equality.  Every canonical-form statement below is phrased
   with a transport, so this is what discharges it at the clause's own
   family. *)
Lemma ctoK_self {k u} (F : kUFam k u) w (x : kElAt F w) :
  kEqAt F w (ctoK (kAt F) (kAt F) (iso_self F) w x) w x.
Proof. exact (uf_idp F u (kAcc F) (evalAg_refl u) (iso_self F) w x). Qed.

(* ------------------------------------------------------------------ *)
(* THE CANONICAL-FORM DECODER.                                        *)
(*                                                                    *)
(* ITm cannot be inverted by `destruct` at a fixed subject, because the *)
(* subject is an index and three clauses -- i_ty, i_proof, i_conv -- do *)
(* not constrain it.  The way round is a decoder: a family defined by    *)
(* matching on the subject, provable for every clause, whose branch at   *)
(* each shape says SEMANTICALLY what the value is.  Semantically, not by  *)
(* equations: the indices are dependent data with no decidable equality, *)
(* so equations would need casts, whereas saying that the value, once      *)
(* transported into the shape's canonical family, IS the canonical element *)
(* needs none.                                                            *)
(*                                                                      *)
(* It is TYPE-valued, not Prop-valued, because its branches mention ITy. *)
(* That costs nothing: what made ITm uninvertible was the need for        *)
(* EQUATIONS between dependent indices, and there are none here.         *)
(*                                                                      *)
(* Every branch has the same shape -- the clause's own data, its own      *)
(* premises, and IsVal relating the value in hand to the one the clause   *)
(* builds -- so conversion-stability and respect for the family's own     *)
(* equality are proved ONCE, about IsVal, and every branch inherits them. *)
(* ------------------------------------------------------------------ *)

(* The value in hand IS the canonical one, up to the transport between the two
   families.  This is the only place a transport appears, which is why nothing
   below needs a cast. *)
Definition IsVal {k Sy Syc} (F : kUFam k Sy) (w : etm) (x : kElAt F w)
  (Fc : kUFam k Syc) (wc : etm) (xc : kElAt Fc wc) : Type :=
  { P : iso (kAt F) (kAt Fc) & kEqAt Fc w (ctoK (kAt F) (kAt Fc) P w x) wc xc }.

Lemma IsVal_self {k Sy} (F : kUFam k Sy) w (x : kElAt F w) : IsVal F w x F w x.
Proof. exists (iso_self F); apply ctoK_self. Qed.

(* Composing two transports out of one family: the only equation the
   decoder's conversion transfer ever needs. *)
Lemma ctoK_after {k u u' c} (F : kUFam k u) (F' : kUFam k u') (C : kUFam k c)
  (P : iso (kAt F) (kAt F')) (Q : iso (kAt F) (kAt C)) w (x : kElAt F w) :
  kEqAt C w
    (ctoK (kAt F') (kAt C) (iso_trans (kAt F') (kAt F) (kAt C) (iso_sym _ _ P) Q) w
       (ctoK (kAt F) (kAt F') P w x))
    w (ctoK (kAt F) (kAt C) Q w x).
Proof.
  apply kEqC_sym.
  apply (ctoK_fun (kAt F) (kAt F') (kAt C) P
           (iso_trans (kAt F') (kAt F) (kAt C) (iso_sym _ _ P) Q) Q).
Qed.

Lemma IsVal_conv {k Sy Sy' Syc} (F : kUFam k Sy) (F' : kUFam k Sy')
  (P : iso (kAt F) (kAt F')) w (x : kElAt F w)
  (Fc : kUFam k Syc) wc (xc : kElAt Fc wc) :
  IsVal F w x Fc wc xc -> IsVal F' w (ctoK (kAt F) (kAt F') P w x) Fc wc xc.
Proof.
  intros [Q HQ]; exists (iso_trans (kAt F') (kAt F) (kAt Fc) (iso_sym _ _ P) Q).
  eapply kEqC_trans; [apply ctoK_after | exact HQ].
Qed.

Lemma IsVal_resp {k Sy Syc} (F : kUFam k Sy) w (x x2 : kElAt F w)
  (Fc : kUFam k Syc) wc (xc : kElAt Fc wc) :
  kEqAt F w x w x2 -> IsVal F w x Fc wc xc -> IsVal F w x2 Fc wc xc.
Proof.
  intros HE [Q HQ]; exists Q.
  eapply kEqC_trans; [apply ctoK_eq; apply kEqC_sym; exact HE | exact HQ].
Qed.

(* ---- the branch at each shape ---- *)

(* A TYPE FORMER, read as an element of the universe above it: the value is the
   family the former's own ITy clause builds.  This is where i_ty lands, and it
   is confined to the formers -- at a subject that is not one, i_ty is composed
   with ity_of and the decoder passes the ITm premise's own branch through
   instead, which is what makes the shape available at every notFormer. *)
Definition TyVal (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun _ _ _ => Empty_set
  | S k0 => fun F w x =>
      { F0 : kUFam k0 w &
        (ITy rho t k0 w F0 * IsVal F w x (univFam k0) w (famEl F0))%type }
  end.

(* The term lift.  It records the TYPE it lifts, so the branch hands over an
   ITy derivation for it and functionality on types supplies the isomorphism of
   the two readings' families -- which is what used to need iso-reflection
   through the lift, a lemma that does not exist. *)
Definition UpTmVal (rho : Env) (A t0 : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun _ _ _ => Empty_set
  | S k0 => fun F w x =>
      { Sy1 : etm & { F1 : kUFam k0 Sy1 & { x1 : kElAt F1 w &
        (ITy rho A k0 Sy1 F1 * ITm rho t0 k0 Sy1 F1 w x1 *
         IsVal F w x (famLiftK F1) w (elLift F1 w x1))%type } } }
  end.

(* The TYPE lift: at a subject `up A t` whose annotation is not a universe no
   clause applies at all. *)
Definition UpShape (rho : Env) (Au t0 : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match Au with
  | univ i => TyVal rho (up (univ i) t0) k Sy
  | _ => fun _ _ _ => Empty_set
  end.

(* Variables: the head entry for var 0, the tail's derivation for var (S i). *)
Definition VarShape (rho : Env) (i : nat) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match i, rho return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0, en :: _ => fun F w x => EntryRel (Build_Entry k Sy F w x) en
  | S j, _ :: rho0 => fun F w x =>
      { x0 : kElAt F w &
        (ITm rho0 (var_tm j) k Sy F w x0 * kEqAt F w x w x0)%type }
  | _, nil => fun _ _ _ => Empty_set
  end.

(* A shape no clause concludes at. *)
Definition NoVal (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  fun _ _ _ => Empty_set.

Definition ZeroVal (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun F w x => IsVal F w x (natFam 0) ezero (natE 0 NatAt_zero)
  | S _ => fun _ _ _ => Empty_set
  end.

Definition SuccVal (rho : Env) (n : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun F w x =>
      { wn : etm & { xn : kElAt (natFam 0) wn &
        (ITm rho n 0 enat (natFam 0) wn xn *
         IsVal F w x (natFam 0) (esucc wn) (natSucc xn))%type } }
  | S _ => fun _ _ _ => Empty_set
  end.

Definition FalseVal (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun F w x =>
      { g : Good eprop efalse &
        IsVal F w x (propFam 0) efalse (propElem efalse False g) }
  | S _ => fun _ _ _ => Empty_set
  end.

(* Impredicative forall.  The domain's level is free -- t_all quantifies over
   it -- so it is existential here, and it is the one level in the decoder that
   the subject does not determine. *)
Definition AllVal (rho : Env) (A p : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun F w x =>
      { kA : nat & { wA : etm & { FA : kUFam kA wA &
      { wp : forall u, kElAt FA u -> etm &
      { xp : forall u (y : kElAt FA u), kElAt (propFam 0) (wp u y) &
      { wv : etm & { g : Good eprop wv &
        (ITy rho A kA wA FA *
         (forall u y, ITm (ext rho FA u y) p 0 eprop (propFam 0) (wp u y) (xp u y)) *
         IsVal F w x (propFam 0) wv
           (propElem wv (forall u (y : kElAt FA u), propVal (xp u y)) g))%type
      } } } } } } }
  | S _ => fun _ _ _ => Empty_set
  end.

(* Pi.  The codomain's syntax B is NOT part of the subject, so the branch does
   not mention it: what the functionality proof needs is the body's value at
   every argument and the behaviour equation, both of which speak of t alone. *)
Definition LamVal (rho : Env) (A B t0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { wA : etm & { FA : kUFam k wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (y : kElAt FA u), kUFam k (wB u y) &
  { redB : forall u y, reds (eapp B0 u) (wB u y) &
  { isoB : forall u y u' y', kEqAt FA u y u' y' -> iso (kAt (FB u' y')) (kAt (FB u y)) &
  { gPi : eqty k (epi wA B0) (epi wA B0) &
  { wv : etm & { xv : kElAt (piFam k wA B0 FA wB FB redB isoB gPi) wv &
  { wt : forall u, kElAt FA u -> etm &
  { xt : forall u (y : kElAt FA u), kElAt (FB u y) (wt u y) &
    ((epi wA B0 = ers rho (pi A B)) *
     ITy rho A k wA FA *
     (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) *
     (forall u y, ITm (ext rho FA u y) t0 k (wB u y) (FB u y) (wt u y) (xt u y)) *
     (forall u y, kEqAt (FB u y) (eapp wv u)
        (piApp k wA B0 FA wB FB redB isoB gPi wv xv u y) (wt u y) (xt u y)) *
     IsVal F w x (piFam k wA B0 FA wB FB redB isoB gPi) wv xv)%type
  } } } } } } } } } } } }.

Definition AppVal (rho : Env) (A B f a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { wA : etm & { FA : kUFam k wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (y : kElAt FA u), kUFam k (wB u y) &
  { redB : forall u y, reds (eapp B0 u) (wB u y) &
  { isoB : forall u y u' y', kEqAt FA u y u' y' -> iso (kAt (FB u' y')) (kAt (FB u y)) &
  { gPi : eqty k (epi wA B0) (epi wA B0) &
  { wf : etm & { xf : kElAt (piFam k wA B0 FA wB FB redB isoB gPi) wf &
  { wa : etm & { xa : kElAt FA wa &
    ((epi wA B0 = ers rho (pi A B)) *
     ITy rho A k wA FA *
     (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) *
     ITm rho f k (epi wA B0) (piFam k wA B0 FA wB FB redB isoB gPi) wf xf *
     ITm rho a k wA FA wa xa *
     IsVal F w x (FB wa xa) (eapp wf wa)
       (piApp k wA B0 FA wB FB redB isoB gPi wf xf wa xa))%type
  } } } } } } } } } } } }.

Definition PairVal (rho : Env) (A B t0 a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { wA : etm & { FA : kUFam k wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (y : kElAt FA u), kUFam k (wB u y) &
  { redB : forall u y, reds (eapp B0 u) (wB u y) &
  { isoB : forall u y u' y', kEqAt FA u y u' y' -> iso (kAt (FB u' y')) (kAt (FB u y)) &
  { gSig : eqty k (esig wA B0) (esig wA B0) &
  { wt : etm & { xt : kElAt FA wt &
  { wa : etm & { xa : kElAt (FB wt xt) wa &
  { g : Good (esig wA B0) (epair wt wa) &
    ((esig wA B0 = ers rho (sig_ A B)) *
     ITy rho A k wA FA *
     (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) *
     ITm rho t0 k wA FA wt xt *
     ITm rho a k (wB wt xt) (FB wt xt) wa xa *
     IsVal F w x (sigFam k wA B0 FA wB FB redB isoB gSig) (epair wt wa)
       (sigPair k wA B0 FA wB FB redB isoB gSig wt wa xt xa g))%type
  } } } } } } } } } } } } }.

Definition FstVal (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { wA : etm & { FA : kUFam k wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (y : kElAt FA u), kUFam k (wB u y) &
  { redB : forall u y, reds (eapp B0 u) (wB u y) &
  { isoB : forall u y u' y', kEqAt FA u y u' y' -> iso (kAt (FB u' y')) (kAt (FB u y)) &
  { gSig : eqty k (esig wA B0) (esig wA B0) &
  { wp : etm & { xp : kElAt (sigFam k wA B0 FA wB FB redB isoB gSig) wp &
    ((esig wA B0 = ers rho (sig_ A B)) *
     ITy rho A k wA FA *
     (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) *
     ITm rho p k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig) wp xp *
     IsVal F w x FA (efst wp) (sigFst k wA B0 FA wB FB redB isoB gSig wp xp))%type
  } } } } } } } } } }.

Definition SndVal (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { wA : etm & { FA : kUFam k wA & { B0 : etm &
  { wB : forall u, kElAt FA u -> etm &
  { FB : forall u (y : kElAt FA u), kUFam k (wB u y) &
  { redB : forall u y, reds (eapp B0 u) (wB u y) &
  { isoB : forall u y u' y', kEqAt FA u y u' y' -> iso (kAt (FB u' y')) (kAt (FB u y)) &
  { gSig : eqty k (esig wA B0) (esig wA B0) &
  { wp : etm & { xp : kElAt (sigFam k wA B0 FA wB FB redB isoB gSig) wp &
    ((esig wA B0 = ers rho (sig_ A B)) *
     ITy rho A k wA FA *
     (forall u y, ITy (ext rho FA u y) B k (wB u y) (FB u y)) *
     ITm rho p k (esig wA B0) (sigFam k wA B0 FA wB FB redB isoB gSig) wp xp *
     IsVal F w x (FB (efst wp) (sigFst k wA B0 FA wB FB redB isoB gSig wp xp))
       (esnd wp) (sigSnd k wA B0 FA wB FB redB isoB gSig wp xp))%type
  } } } } } } } } } }.

(* natrec.  Much smaller than it was: with the step term carrying its own
   binders there is no Pi-type for it, hence no B02, isoB2, gPi2, redB2 or
   isoStep, and its semantic content is one value per scrutinee and motive
   value. *)
Definition RecVal (rho : Env) (C z s n : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) (w : etm) (x : kElAt F w) : Type :=
  { SC : etm -> etm &
  { FC : forall m (x0 : kElAt (natFam 0) m), kUFam k (SC m) &
  { isoC : forall m x0 m' x0', kEqAt (natFam 0) m x0 m' x0' ->
             iso (kAt (FC m x0)) (kAt (FC m' x0')) &
  { S0 : etm &
  { wz : etm & { xz : kElAt (FC ezero (natE 0 NatAt_zero)) wz &
  { ws : forall m (x0 : kElAt (natFam 0) m) (w0 : etm) (y : kElAt (FC m x0) w0), etm &
  { xs : forall m x0 w0 y, kElAt (FC (esucc m) (natSucc x0)) (ws m x0 w0 y) &
  { redS : forall m x0 w0 y, reds (eapp (eapp S0 m) w0) (ws m x0 w0 y) &
  { wn : etm & { xn : kElAt (natFam 0) wn &
    ((S0 = ers rho (stepWrap s)) *
     (forall m x0, ITy (ext rho (natFam 0) m x0) C k (SC m) (FC m x0)) *
     ITm rho z k (SC ezero) (FC ezero (natE 0 NatAt_zero)) wz xz *
     (forall m x0 w0 y,
        ITm (ext (ext rho (natFam 0) m x0) (FC m x0) w0 y) s k
            (SC (esucc m)) (FC (esucc m) (natSucc x0)) (ws m x0 w0 y) (xs m x0 w0 y)) *
     ITm rho n 0 enat (natFam 0) wn xn *
     IsVal F w x (FC wn (natE (natIdx xn) (natSpec xn))) (enatrec wz S0 wn)
       (semrec k 0 SC FC isoC wz S0 xz
          (fun m x0 w0 y =>
             moveTo (FC (esucc m) (natSucc x0)) (FC (esucc m) (natSucc x0))
               (iso_self (FC (esucc m) (natSucc x0)))
               (ws m x0 w0 y) (xs m x0 w0 y) (eapp (eapp S0 m) w0) (redS m x0 w0 y))
          (natIdx xn) wn (natSpec xn)))%type
  } } } } } } } } } } }.

(* And the decoder itself.  `Empty_set` at a shape means NO clause concludes
   there at that level: plam, papp and absurd have no clause of their own and
   eqty, refl and transp are not in the theory, so at a positive level -- where
   i_proof, the one clause that fits any subject, cannot reach -- there is no
   derivation at all.  That is a fact about the interpretation, and recording it
   in the decoder is what lets a consumer use it. *)
(* ---- Conversion-stability and respect for the family's own equality.  Every
   branch ends in IsVal and nothing else moves, so each is three lines. ---- *)

Lemma TyVal_conv (rho : Env) (t : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  TyVal rho t k Sy F w x -> TyVal rho t k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [TyVal]; [intros [] |].
  intros [F0 [Hp Hv]].
  exists F0.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma TyVal_resp (rho : Env) (t : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> TyVal rho t k Sy F w x -> TyVal rho t k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [TyVal]; [intros _ [] |].
  intros HE [F0 [Hp Hv]].
  exists F0.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma UpTmVal_conv (rho : Env) (A t0 : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  UpTmVal rho A t0 k Sy F w x ->
  UpTmVal rho A t0 k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [UpTmVal]; [intros [] |].
  intros [Sy1 [F1 [x1 [Hp Hv]]]].
  exists Sy1, F1, x1.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma UpTmVal_resp (rho : Env) (A t0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> UpTmVal rho A t0 k Sy F w x -> UpTmVal rho A t0 k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [UpTmVal]; [intros _ [] |].
  intros HE [Sy1 [F1 [x1 [Hp Hv]]]].
  exists Sy1, F1, x1.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma ZeroVal_conv (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  ZeroVal k Sy F w x -> ZeroVal k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [ZeroVal]; [| solve [intros []]].
  intros Hv; apply IsVal_conv; exact Hv.
Qed.

Lemma ZeroVal_resp (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> ZeroVal k Sy F w x -> ZeroVal k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [ZeroVal]; [| solve [intros _ []]].
  intros HE Hv; eapply IsVal_resp; [exact HE | exact Hv].
Qed.

Lemma SuccVal_conv (rho : Env) (n : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  SuccVal rho n k Sy F w x -> SuccVal rho n k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [SuccVal]; [| solve [intros []]].
  intros [wn [xn [Hp Hv]]].
  exists wn, xn.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma SuccVal_resp (rho : Env) (n : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> SuccVal rho n k Sy F w x -> SuccVal rho n k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [SuccVal]; [| solve [intros _ []]].
  intros HE [wn [xn [Hp Hv]]].
  exists wn, xn.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma FalseVal_conv (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  FalseVal k Sy F w x -> FalseVal k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [FalseVal]; [| solve [intros []]].
  intros [g Hv]; exists g; apply IsVal_conv; exact Hv.
Qed.

Lemma FalseVal_resp (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> FalseVal k Sy F w x -> FalseVal k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [FalseVal]; [| solve [intros _ []]].
  intros HE [g Hv]; exists g; eapply IsVal_resp; [exact HE | exact Hv].
Qed.

Lemma AllVal_conv (rho : Env) (A p : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  AllVal rho A p k Sy F w x -> AllVal rho A p k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [AllVal]; [| solve [intros []]].
  intros [kA [wA [FA [wp [xp [wv [g [Hp Hv]]]]]]]].
  exists kA, wA, FA, wp, xp, wv, g.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma AllVal_resp (rho : Env) (A p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> AllVal rho A p k Sy F w x -> AllVal rho A p k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [AllVal]; [| solve [intros _ []]].
  intros HE [kA [wA [FA [wp [xp [wv [g [Hp Hv]]]]]]]].
  exists kA, wA, FA, wp, xp, wv, g.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma LamVal_conv (rho : Env) (A B t0 : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  LamVal rho A B t0 k Sy F w x -> LamVal rho A B t0 k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [wA [FA [B0 [wB [FB [redB [isoB [gPi [wv [xv [wt [xt [Hp Hv]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, wv, xv, wt, xt.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma LamVal_resp (rho : Env) (A B t0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> LamVal rho A B t0 k Sy F w x -> LamVal rho A B t0 k Sy F w x2.
Proof.
  intros HE [wA [FA [B0 [wB [FB [redB [isoB [gPi [wv [xv [wt [xt [Hp Hv]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, wv, xv, wt, xt.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma AppVal_conv (rho : Env) (A B f a : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  AppVal rho A B f a k Sy F w x -> AppVal rho A B f a k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [wA [FA [B0 [wB [FB [redB [isoB [gPi [wf [xf [wa [xa [Hp Hv]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, wf, xf, wa, xa.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma AppVal_resp (rho : Env) (A B f a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> AppVal rho A B f a k Sy F w x -> AppVal rho A B f a k Sy F w x2.
Proof.
  intros HE [wA [FA [B0 [wB [FB [redB [isoB [gPi [wf [xf [wa [xa [Hp Hv]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, wf, xf, wa, xa.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma PairVal_conv (rho : Env) (A B t0 a : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  PairVal rho A B t0 a k Sy F w x -> PairVal rho A B t0 a k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [wA [FA [B0 [wB [FB [redB [isoB [gSig [wt [xt [wa [xa [g [Hp Hv]]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wt, xt, wa, xa, g.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma PairVal_resp (rho : Env) (A B t0 a : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> PairVal rho A B t0 a k Sy F w x -> PairVal rho A B t0 a k Sy F w x2.
Proof.
  intros HE [wA [FA [B0 [wB [FB [redB [isoB [gSig [wt [xt [wa [xa [g [Hp Hv]]]]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wt, xt, wa, xa, g.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma FstVal_conv (rho : Env) (A B p : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  FstVal rho A B p k Sy F w x -> FstVal rho A B p k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [Hp Hv]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma FstVal_resp (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> FstVal rho A B p k Sy F w x -> FstVal rho A B p k Sy F w x2.
Proof.
  intros HE [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [Hp Hv]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma SndVal_conv (rho : Env) (A B p : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  SndVal rho A B p k Sy F w x -> SndVal rho A B p k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [Hp Hv]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma SndVal_resp (rho : Env) (A B p : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> SndVal rho A B p k Sy F w x -> SndVal rho A B p k Sy F w x2.
Proof.
  intros HE [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [Hp Hv]]]]]]]]]]].
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.

Lemma RecVal_conv (rho : Env) (C z s n : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  RecVal rho C z s n k Sy F w x -> RecVal rho C z s n k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros [SC [FC [isoC [S0 [wz [xz [ws [xs [redS [wn [xn [Hp Hv]]]]]]]]]]]].
  exists SC, FC, isoC, S0, wz, xz, ws, xs, redS, wn, xn.
  split; [exact Hp | apply IsVal_conv; exact Hv].
Qed.

Lemma RecVal_resp (rho : Env) (C z s n : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> RecVal rho C z s n k Sy F w x -> RecVal rho C z s n k Sy F w x2.
Proof.
  intros HE [SC [FC [isoC [S0 [wz [xz [ws [xs [redS [wn [xn [Hp Hv]]]]]]]]]]]].
  exists SC, FC, isoC, S0, wz, xz, ws, xs, redS, wn, xn.
  split; [exact Hp | eapply IsVal_resp; [exact HE | exact Hv]].
Qed.


(* Variables.  The head entry's relation composes, which is what EntryRel_trans
   is for; the tail's derivation moves by i_conv. *)
Lemma VarShape_conv (rho : Env) (i : nat) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  VarShape rho i k Sy F w x ->
  VarShape rho i k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct i as [| j]; destruct rho as [| en rho0]; cbn [VarShape];
    try (solve [intros []]).
  - intros H; eapply EntryRel_trans; [| exact H].
    apply entry_rel; apply kRel_sym; apply hetC_to.
  - intros [x0 [D0 HE]].
    exists (ctoK (kAt F) (kAt F') P w x0); split.
    + exact (i_conv rho0 (var_tm j) k Sy F Sy' F' w x0 P D0).
    + apply ctoK_eq; exact HE.
Qed.

Lemma VarShape_resp (rho : Env) (i : nat) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> VarShape rho i k Sy F w x -> VarShape rho i k Sy F w x2.
Proof.
  destruct i as [| j]; destruct rho as [| en rho0]; cbn [VarShape];
    try (solve [intros _ []]).
  - intros HE H; eapply EntryRel_trans; [| exact H].
    apply entry_rel; eapply hetC_eq_l; [apply kEqC_sym; exact HE | apply kRel_refl].
  - intros HE [x0 [D0 HQ]].
    exists x0; split; [exact D0 |].
    eapply kEqC_trans; [apply kEqC_sym; exact HE | exact HQ].
Qed.

Lemma UpShape_conv (rho : Env) (Au t0 : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  UpShape rho Au t0 k Sy F w x ->
  UpShape rho Au t0 k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct Au; cbn [UpShape]; try (solve [intros []]).
  apply TyVal_conv.
Qed.

Lemma UpShape_resp (rho : Env) (Au t0 : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> UpShape rho Au t0 k Sy F w x -> UpShape rho Au t0 k Sy F w x2.
Proof.
  destruct Au; cbn [UpShape]; try (solve [intros _ []]).
  apply TyVal_resp.
Qed.

Definition TmShape (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match t return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | var_tm i => VarShape rho i k Sy
  | nat_ => TyVal rho nat_ k Sy
  | prop => TyVal rho prop k Sy
  | univ m => TyVal rho (univ m) k Sy
  | prf p => TyVal rho (prf p) k Sy
  | pi A B => TyVal rho (pi A B) k Sy
  | sig_ A B => TyVal rho (sig_ A B) k Sy
  | up Au t0 => UpShape rho Au t0 k Sy
  | uptm A t0 => UpTmVal rho A t0 k Sy
  | zero => ZeroVal k Sy
  | succ n => SuccVal rho n k Sy
  | lam A B t0 => LamVal rho A B t0 k Sy
  | app A B f a => AppVal rho A B f a k Sy
  | pair A B t0 a => PairVal rho A B t0 a k Sy
  | fst A B p => FstVal rho A B p k Sy
  | snd A B p => SndVal rho A B p k Sy
  | natrec C z s n => RecVal rho C z s n k Sy
  | false_ => FalseVal k Sy
  | all A p => AllVal rho A p k Sy
  | _ => NoVal k Sy
  end.

(* The one universal alternative left is i_proof, and it lives at level 0
   alone -- that is what pinning the levels bought. *)
Definition TmInv (rho : Env) (t : tm) (k : nat) (Sy : etm)
  : forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type :=
  match k return forall (F : kUFam k Sy) (w : etm), kElAt F w -> Type with
  | 0 => fun F w x => (TotalFam F + TmShape rho t 0 Sy F w x)%type
  | S k0 => fun F w x => TmShape rho t (S k0) Sy F w x
  end.

Lemma TmShape_conv (rho : Env) (t : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  TmShape rho t k Sy F w x ->
  TmShape rho t k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct t; cbn [TmShape NoVal];
    first
      [ solve [intros []]
      | apply VarShape_conv | apply UpShape_conv | apply UpTmVal_conv
      | apply TyVal_conv
      | apply ZeroVal_conv | apply SuccVal_conv | apply FalseVal_conv
      | apply AllVal_conv | apply LamVal_conv | apply AppVal_conv
      | apply PairVal_conv | apply FstVal_conv | apply SndVal_conv
      | apply RecVal_conv ].
Qed.

Lemma TmShape_resp (rho : Env) (t : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> TmShape rho t k Sy F w x -> TmShape rho t k Sy F w x2.
Proof.
  destruct t; cbn [TmShape NoVal];
    first
      [ solve [intros _ []]
      | apply VarShape_resp | apply UpShape_resp | apply UpTmVal_resp
      | apply TyVal_resp
      | apply ZeroVal_resp | apply SuccVal_resp | apply FalseVal_resp
      | apply AllVal_resp | apply LamVal_resp | apply AppVal_resp
      | apply PairVal_resp | apply FstVal_resp | apply SndVal_resp
      | apply RecVal_resp ].
Qed.

Lemma TmInv_conv (rho : Env) (t : tm) (k : nat) (Sy Sy' : etm)
  (F : kUFam k Sy) (F' : kUFam k Sy') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) :
  TmInv rho t k Sy F w x -> TmInv rho t k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  destruct k as [| k0]; cbn [TmInv].
  - intros [HT | Hs];
      [ left; exact (TotalFam_iso F F' P HT)
      | right; exact (TmShape_conv rho t 0 Sy Sy' F F' P w x Hs) ].
  - exact (TmShape_conv rho t (S k0) Sy Sy' F F' P w x).
Qed.

Lemma TmInv_resp (rho : Env) (t : tm) (k : nat) (Sy : etm)
  (F : kUFam k Sy) w (x x2 : kElAt F w) :
  kEqAt F w x w x2 -> TmInv rho t k Sy F w x -> TmInv rho t k Sy F w x2.
Proof.
  destruct k as [| k0]; cbn [TmInv].
  - intros HE [HT | Hs];
      [ left; exact HT
      | right; exact (TmShape_resp rho t 0 Sy F w x x2 HE Hs) ].
  - exact (TmShape_resp rho t (S k0) Sy F w x x2).
Qed.

(* A shape branch is a decoder value at every level: at 0 it is the right
   summand, above 0 the decoder IS the shape. *)
Definition inShape {rho t k Sy} {F : kUFam k Sy} {w} {x : kElAt F w}
  : TmShape rho t k Sy F w x -> TmInv rho t k Sy F w x :=
  match k return forall (F0 : kUFam k Sy) (w0 : etm) (x0 : kElAt F0 w0),
                 TmShape rho t k Sy F0 w0 x0 -> TmInv rho t k Sy F0 w0 x0 with
  | 0 => fun _ _ _ H => inr H
  | S _ => fun _ _ _ H => H
  end F w x.

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

Ltac dc_ty c := cbn [TyD TmInv TmShape TyVal]; exists c; split;
  [ idtac | apply IsVal_self ].

Ltac dc1 := intros rho w Ew; dc_ty (natFam 0); exact (ity_nat rho w Ew).
Ltac dc2 := intros rho w Ew; dc_ty (propFam 0); exact (ity_prop rho w Ew).
Ltac dc3 := intros rho m w Ew; dc_ty (univFam m); exact (ity_univ rho m w Ew).
Ltac dc4 := intros rho p wp xp Dp IHp; dc_ty (prfF 0 xp);
  exact (ity_prf rho p wp xp Dp).
Ltac dc5 := intros rho A B k wA FA B0 wB FB redB isoB gPi Ew DA IHA DB IHB;
  dc_ty (piFam k wA B0 FA wB FB redB isoB gPi);
  exact (ity_pi rho A B k wA FA B0 wB FB redB isoB gPi Ew DA DB).
Ltac dc6 := intros rho A B k wA FA B0 wB FB redB isoB gSig Ew DA IHA DB IHB;
  dc_ty (sigFam k wA B0 FA wB FB redB isoB gSig);
  exact (ity_sig rho A B k wA FA B0 wB FB redB isoB gSig Ew DA DB).
Ltac dc7 := intros rho A k w F D IH;
  cbn [TyD TmInv TmShape UpShape TyVal];
  exists (famLiftK F); split; [exact (ity_up rho A k w F D) | apply IsVal_self].
Ltac dc8 := intros rho A k w v nf Dv IHv; unfold TyD in IHv |- *;
  eapply TmInv_resp; [apply kEqC_sym; apply famEl_elFam_rel | exact IHv].
(* ity_conv: the two families are isomorphic, so their codes are equal in the
   universe (uEq_of through uf_coh) and the decoder's branch travels by
   TmInv_resp. *)
Ltac dc8c := intros rho A k w F F' P D IH;
  unfold TyD in *;
  apply (TmInv_resp rho A (S k) (euniv k) (univFam k) w (famEl F) (famEl F'));
  [ apply uEq_of;
    [ exact (uf_ty F)
    | intros v h pf v' h' pf';
      eapply iso_trans; [apply uf_coh |];
      eapply iso_trans; [exact P | apply uf_coh] ]
  | exact IH ].

Ltac dc9 := intros rho A k w F D IH; exact IH.
Ltac dc10 := intros rho k Sy F w x; apply inShape;
  cbn [TmShape VarShape ext]; apply EntryRel_refl.
Ltac dc11 := intros rho en i k Sy F w x D IH; apply inShape;
  cbn [TmShape VarShape]; exists x; split; [exact D | apply kEqC_self].
Ltac dc12 := intros rho; apply inShape; cbn [TmShape ZeroVal]; apply IsVal_self.
Ltac dc13 := intros rho n wn x D IH; apply inShape; cbn [TmShape SuccVal];
  exists wn, x; split; [exact D | apply IsVal_self].
Ltac dc14 := intros rho A B t k wA FA B0 wB FB redB isoB gPi w x wt xt Ew Ep
    DA IHA DB IHB Dt IHt Hbeh;
  apply inShape; cbn [TmShape LamVal];
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, w, x, wt, xt;
  split;
  [ split;
    [ split; [split; [split; [exact Ep | exact DA] | exact DB] | exact Dt]
    | exact Hbeh]
  | apply IsVal_self ].
Ltac dc15 := intros rho A B f a k wA FA B0 wB FB redB isoB gPi wf xf wa xa Ep
    DA IHA DB IHB Df IHf Da IHa;
  apply inShape; cbn [TmShape AppVal];
  exists wA, FA, B0, wB, FB, redB, isoB, gPi, wf, xf, wa, xa;
  split;
  [ split;
    [ split; [split; [split; [exact Ep | exact DA] | exact DB] | exact Df]
    | exact Da]
  | apply IsVal_self ].
Ltac dc16 := intros rho A B t a k wA FA B0 wB FB redB isoB gSig wt xt wa xa g Ep
    DA IHA DB IHB Dt IHt Da IHa;
  apply inShape; cbn [TmShape PairVal];
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wt, xt, wa, xa, g;
  split;
  [ split;
    [ split; [split; [split; [exact Ep | exact DA] | exact DB] | exact Dt]
    | exact Da]
  | apply IsVal_self ].
Ltac dc17 := intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
    DA IHA DB IHB Dp IHp;
  apply inShape; cbn [TmShape FstVal];
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp;
  split;
  [ split; [split; [split; [exact Ep | exact DA] | exact DB] | exact Dp]
  | apply IsVal_self].
Ltac dc18 := intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
    DA IHA DB IHB Dp IHp;
  apply inShape; cbn [TmShape SndVal];
  exists wA, FA, B0, wB, FB, redB, isoB, gSig, wp, xp;
  split;
  [ split; [split; [split; [exact Ep | exact DA] | exact DB] | exact Dp]
  | apply IsVal_self].
Ltac dc19 := intros rho C z s n k SC FC isoC S0 wz xz ws xs redS wn xn
    ES DC IHC Dz IHz Ds IHs Dn IHn;
  apply inShape; cbn [TmShape RecVal];
  exists SC, FC, isoC, S0, wz, xz, ws, xs, redS, wn, xn;
  split;
  [ split;
    [ split; [split; [split; [exact ES | exact DC] | exact Dz] | exact Ds]
    | exact Dn]
  | apply IsVal_self ].
Ltac dc20 := intros rho w g Ew; apply inShape; cbn [TmShape FalseVal];
  exists g; apply IsVal_self.
Ltac dc21 := intros rho A p k wA FA wp xp w g Ew DA IHA Dp IHp;
  apply inShape; cbn [TmShape AllVal];
  exists k, wA, FA, wp, xp, w, g;
  split; [split; [exact DA | exact Dp] | apply IsVal_self].
Ltac dc22 := intros rho t p wp xp h w g Ew Dp IHp; cbn [TmInv]; left;
  apply prf_total.
Ltac dc23 := intros rho A t k Sy F w x DA IHA D IH; apply inShape;
  cbn [TmShape UpTmVal];
  exists Sy, F, x;
  split; [split; [exact DA | exact D] | apply IsVal_self].
Ltac dc24 := intros rho t k Sy F Sy' F' w x P D IH;
  exact (TmInv_conv rho t k Sy Sy' F F' P w x IH).

Lemma itm_inv : forall rho t k Sy (F : kUFam k Sy) w (x : kElAt F w),
  ITm rho t k Sy F w x -> TmInv rho t k Sy F w x.
Proof.
  apply (ITm_mut (fun rho A k w F _ => TyD rho A k w F)
                 (fun rho t k Sy F w x _ => TmInv rho t k Sy F w x));
    [ dc1 | dc2 | dc3 | dc4 | dc5 | dc6 | dc7 | dc8 | dc8c
    | dc9 | dc10 | dc11 | dc12 | dc13 | dc14 | dc15 | dc16 | dc17 | dc18
    | dc19 | dc20 | dc21 | dc22 | dc23 | dc24 ].
Qed.

Lemma ity_dec : forall rho A k w (F : kUFam k w), ITy rho A k w F -> TyD rho A k w F.
Proof.
  apply (ITy_mut (fun rho A k w F _ => TyD rho A k w F)
                 (fun rho t k Sy F w x _ => TmInv rho t k Sy F w x));
    [ dc1 | dc2 | dc3 | dc4 | dc5 | dc6 | dc7 | dc8 | dc8c
    | dc9 | dc10 | dc11 | dc12 | dc13 | dc14 | dc15 | dc16 | dc17 | dc18
    | dc19 | dc20 | dc21 | dc22 | dc23 | dc24 ].
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
(* genuinely different environments (natrec interprets its motive under  *)
(* an entry that depends on the reading).                               *)
(*                                                                    *)
(* Positive levels only.  At level 0 nothing is unique: layer 1's Prf     *)
(* clause relates every realiser (Rel_prf_intro), so i_proof reads any    *)
(* subject whatever as a proof.  Writing the level as a successor is what *)
(* keeps the decoder reduced and makes that restriction free.            *)
(* ------------------------------------------------------------------ *)

Fixpoint lvls (rho : Env) : list nat :=
  match rho with
  | nil => nil
  | en :: r => en_k en :: lvls r
  end.

Lemma lvls_ext rho {k S0} (F : kUFam k S0) w (x : kElAt F w) :
  lvls (ext rho F w x) = k :: lvls rho.
Proof. reflexivity. Qed.

(* Variables: an induction on the INDEX, which the induction on the term
   cannot supply -- var_tm i is not a subterm of var_tm (S i). *)
Lemma var_lvl : forall i rho rho', lvls rho = lvls rho' ->
  forall j Sy (F : kUFam (S j) Sy) w (x : kElAt F w),
    ITm rho (var_tm i) (S j) Sy F w x ->
  forall j' Sy' (F' : kUFam (S j') Sy') w' (x' : kElAt F' w'),
    ITm rho' (var_tm i) (S j') Sy' F' w' x' ->
  j = j'.
Proof.
  induction i as [| i IH]; intros rho rho' HL j Sy F w x D j' Sy' F' w' x' D';
    pose proof (itm_inv rho _ _ _ _ _ _ D) as E;
    pose proof (itm_inv rho' _ _ _ _ _ _ D') as E';
    destruct rho as [| en rho0]; destruct rho' as [| en' rho0'];
    cbn [TmInv TmShape VarShape lvls] in E, E', HL;
    try (solve [destruct E]); try (solve [destruct E']);
    injection HL as Hk HL0.
  - pose proof (EntryRel_k _ _ E) as Ee; pose proof (EntryRel_k _ _ E') as Ee'.
    cbn [en_k] in Ee, Ee'.
    injection (eq_trans Ee (eq_trans Hk (eq_sym Ee'))) as Ej; exact Ej.
  - destruct E as [x0 [D0 _]]; destruct E' as [x0' [D0' _]].
    exact (IH rho0 rho0' HL0 j Sy F w x0 D0 j' Sy' F' w' x0' D0').
Qed.

Ltac lvl_shapes D1 D2 :=
  pose proof (itm_inv _ _ _ _ _ _ _ D1) as E;
  pose proof (itm_inv _ _ _ _ _ _ _ D2) as E';
  cbn [TmInv TmShape VarShape TyVal UpTmVal UpShape ZeroVal SuccVal FalseVal
       AllVal LamVal AppVal PairVal FstVal SndVal RecVal NoVal] in E, E'.

(* An induction on the TERM, with the decoder standing in for inversion at each
   shape.  Only five shapes recurse: the three that read the level off a
   subterm's own derivation (app, pair, fst/snd), lam and natrec, which read it
   off a type's, and the formers pi and sig_, which read it off their domain.
   Everything else either fixes the level outright or has no derivation at a
   positive level at all. *)
Lemma itm_lvl : forall t rho rho', lvls rho = lvls rho' ->
  forall j Sy (F : kUFam (S j) Sy) w (x : kElAt F w), ITm rho t (S j) Sy F w x ->
  forall j' Sy' (F' : kUFam (S j') Sy') w' (x' : kElAt F' w'),
    ITm rho' t (S j') Sy' F' w' x' ->
  j = j'.
Proof.
  induction t as
    [ i | A IHA B IHB t1 IHt1 | A IHA t1 IHt1
    | A IHA B IHB f IHf a IHa | f IHf a IHa
    | A IHA B IHB t1 IHt1 a IHa | A IHA B IHB p IHp | A IHA B IHB p IHp
    | A IHA B IHB | A IHA B IHB | |
    | n IHn | C IHC z IHz s IHs n IHn | m | Au IHAu t1 IHt1
    | A IHA t1 IHt1 | | p IHp
    | A IHA p IHp | | T IHT e IHe | A IHA t1 IHt1 a IHa | A IHA a IHa
    | A IHA B IHB t1 IHt1 a IHa e IHe b IHb ];
    intros rho rho' HL j Sy F w x D j' Sy' F' w' x' D'.
  - (* var_tm *) exact (var_lvl i rho rho' HL j Sy F w x D j' Sy' F' w' x' D').
  - (* lam *) lvl_shapes D D'.
    destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi
      [wv [xv [wt [xt [[[[[Ep DA] DB] Dt] Hb] Hv]]]]]]]]]]]]].
    destruct E' as [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gPi2
      [wv2 [xv2 [wt2 [xt2 [[[[[Ep2 DA2] DB2] Dt2] Hb2] Hv2]]]]]]]]]]]]].
    assert (Eq := IHA rho rho' HL _ _ _ _ _ (i_ty _ _ _ _ _ DA)
                      _ _ _ _ _ (i_ty _ _ _ _ _ DA2)).
    injection Eq as Eq; exact Eq.
  - (* plam *) lvl_shapes D D'; destruct E.
  - (* app *) lvl_shapes D D'.
    destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi
      [wf [xf [wa [xa [[[[[Ep DA] DB] Df] Da] Hv]]]]]]]]]]]]].
    destruct E' as [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gPi2
      [wf2 [xf2 [wa2 [xa2 [[[[[Ep2 DA2] DB2] Df2] Da2] Hv2]]]]]]]]]]]]].
    exact (IHf rho rho' HL _ _ _ _ _ Df _ _ _ _ _ Df2).
  - (* papp *) lvl_shapes D D'; destruct E.
  - (* pair *) lvl_shapes D D'.
    destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig
      [wt [xt [wa [xa [g [[[[[Ep DA] DB] Dt] Da] Hv]]]]]]]]]]]]]].
    destruct E' as [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gSig2
      [wt2 [xt2 [wa2 [xa2 [g2 [[[[[Ep2 DA2] DB2] Dt2] Da2] Hv2]]]]]]]]]]]]]].
    exact (IHt1 rho rho' HL _ _ _ _ _ Dt _ _ _ _ _ Dt2).
  - (* fst *) lvl_shapes D D'.
    destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
    destruct E' as [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gSig2
      [wp2 [xp2 [[[[Ep2 DA2] DB2] Dp2] Hv2]]]]]]]]]]].
    exact (IHp rho rho' HL _ _ _ _ _ Dp _ _ _ _ _ Dp2).
  - (* snd *) lvl_shapes D D'.
    destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
    destruct E' as [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gSig2
      [wp2 [xp2 [[[[Ep2 DA2] DB2] Dp2] Hv2]]]]]]]]]]].
    exact (IHp rho rho' HL _ _ _ _ _ Dp _ _ _ _ _ Dp2).
  - (* pi *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    destruct (ity_pi_inv rho (pi A B) j w F0 D0) as
      [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hty] Hiso]]]]]]]]].
    destruct (ity_pi_inv rho' (pi A B) j' w' F2 D2) as
      [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gPi2 [[[DA2 DB2] Hty2] Hiso2]]]]]]]]].
    exact (IHA rho rho' HL _ _ _ _ _ (i_ty _ _ _ _ _ DA)
                _ _ _ _ _ (i_ty _ _ _ _ _ DA2)).
  - (* sig_ *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    destruct (ity_sig_inv rho (sig_ A B) j w F0 D0) as
      [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hty] Hiso]]]]]]]]].
    destruct (ity_sig_inv rho' (sig_ A B) j' w' F2 D2) as
      [wA2 [FA2 [B2 [wB2 [FB2 [redB2 [isoB2 [gSig2 [[[DA2 DB2] Hty2] Hiso2]]]]]]]]].
    exact (IHA rho rho' HL _ _ _ _ _ (i_ty _ _ _ _ _ DA)
                _ _ _ _ _ (i_ty _ _ _ _ _ DA2)).
  - (* nat_ *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    pose proof (ity_lvl_dec rho nat_ j w F0 D0) as Ej;
      pose proof (ity_lvl_dec rho' nat_ j' w' F2 D2) as Ej';
      cbn [LvlDec] in Ej, Ej'; exact (eq_trans Ej (eq_sym Ej')).
  - (* zero *) lvl_shapes D D'; destruct E.
  - (* succ *) lvl_shapes D D'; destruct E.
  - (* natrec *) lvl_shapes D D'.
    destruct E as [SC [FC [isoC [S0 [wz [xz [ws [xs [redS [wn [xn
      [[[[[ES DC] Dz] Ds] Dn] Hv]]]]]]]]]]]].
    destruct E' as [SC2 [FC2 [isoC2 [S2 [wz2 [xz2 [ws2 [xs2 [redS2 [wn2 [xn2
      [[[[[ES2 DC2] Dz2] Ds2] Dn2] Hv2]]]]]]]]]]]].
    assert (Eq := IHC (ext rho (natFam 0) ezero (natE 0 NatAt_zero))
                      (ext rho' (natFam 0) ezero (natE 0 NatAt_zero))
                      (f_equal (cons 0) HL) _ _ _ _ _
                      (i_ty _ _ _ _ _ (DC ezero (natE 0 NatAt_zero)))
                      _ _ _ _ _ (i_ty _ _ _ _ _ (DC2 ezero (natE 0 NatAt_zero)))).
    injection Eq as Eq; exact Eq.
  - (* univ *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    pose proof (ity_lvl_dec rho (univ m) j w F0 D0) as Ej;
      pose proof (ity_lvl_dec rho' (univ m) j' w' F2 D2) as Ej';
      cbn [LvlDec] in Ej, Ej'; exact (eq_trans Ej (eq_sym Ej')).
  - (* up: the TYPE lift, whose level the annotation fixes *)
    destruct Au; lvl_shapes D D'; try (solve [destruct E]).
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    pose proof (ity_lvl_dec rho (up (univ n) t1) j w F0 D0) as Ej;
      pose proof (ity_lvl_dec rho' (up (univ n) t1) j' w' F2 D2) as Ej';
      cbn [LvlDec] in Ej, Ej'; exact (eq_trans Ej (eq_sym Ej')).
  - (* uptm: the TERM lift, whose level is one above the recorded type's *)
    lvl_shapes D D'.
    destruct E as [Sy1 [F1 [x1 [[DA1 Dt1] Hv]]]].
    destruct E' as [Sy2 [F2 [x2 [[DA2 Dt2] Hv2]]]].
    exact (IHA rho rho' HL _ _ _ _ _ (i_ty _ _ _ _ _ DA1)
               _ _ _ _ _ (i_ty _ _ _ _ _ DA2)).
  - (* prop *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    pose proof (ity_lvl_dec rho prop j w F0 D0) as Ej;
      pose proof (ity_lvl_dec rho' prop j' w' F2 D2) as Ej';
      cbn [LvlDec] in Ej, Ej'; exact (eq_trans Ej (eq_sym Ej')).
  - (* prf *) lvl_shapes D D'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F2 [D2 Hv2]].
    pose proof (ity_lvl_dec rho (prf p) j w F0 D0) as Ej;
      pose proof (ity_lvl_dec rho' (prf p) j' w' F2 D2) as Ej';
      cbn [LvlDec] in Ej, Ej'; exact (eq_trans Ej (eq_sym Ej')).
  - (* all *) lvl_shapes D D'; destruct E.
  - (* false_ *) lvl_shapes D D'; destruct E.
  - (* absurd *) lvl_shapes D D'; destruct E.
  - (* eqty *) lvl_shapes D D'; destruct E.
  - (* refl *) lvl_shapes D D'; destruct E.
  - (* transp *) lvl_shapes D D'; destruct E.
Qed.

(* And the form the fundamental lemma uses: two readings of one type in
   level-matching environments are at the same level. *)
Lemma ity_lvl rho rho' (HL : lvls rho = lvls rho') A k w (F : kUFam k w)
  k' w' (F' : kUFam k' w') :
  ITy rho A k w F -> ITy rho' A k' w' F' -> k = k'.
Proof.
  intros D D'.
  assert (Eq := itm_lvl A rho rho' HL _ _ _ _ _ (i_ty rho A k w F D)
                        _ _ _ _ _ (i_ty rho' A k' w' F' D')).
  exact Eq.
Qed.

(* ------------------------------------------------------------------ *)
(* FUNCTIONALITY ON TERMS.                                            *)
(*                                                                    *)
(* Each clause compares its own value with whatever the decoder returns *)
(* for the second derivation.  Every branch of the decoder ends in       *)
(* IsVal, so the comparison always factors the same way: relate the two  *)
(* clauses' canonical values, then absorb the transport.  That is        *)
(* kRel_of_IsVal, and it is the only bookkeeping any clause needs.       *)
(* ------------------------------------------------------------------ *)

Lemma kRel_of_IsVal {k Sy Sy' Syc} (F : kUFam k Sy) (F' : kUFam k Sy')
  (Fc : kUFam k Syc) w (x : kElAt F w) w' (x' : kElAt F' w')
  wc (xc : kElAt Fc wc) :
  IsVal F' w' x' Fc wc xc -> kRel F Fc w x wc xc -> kRel F F' w x w' x'.
Proof.
  intros [P' H'] Hrel.
  eapply kRel_trans; [exact Hrel |].
  eapply kRel_trans;
    [ apply kRel_sym; apply (proj1 (kRel_same Fc _ _ _ _)); exact H' |].
  apply kRel_sym; apply hetC_to.
Qed.

(* ------------------------------------------------------------------ *)
(* A universe is not a type at its own level.  Layer 1 says so -- the   *)
(* universe clause of LR carries m < n -- and it is what rules out the  *)
(* readings of a term that the decoder cannot rule out by shape: an     *)
(* element of a universe at level k whose family sits at level k, and    *)
(* the term-lift reading of a subject whose type-lift reading is         *)
(* isomorphic to a universe.                                            *)
(* ------------------------------------------------------------------ *)

Lemma eqty_univ_lt k T m : eqty k T T -> eval T (euniv m) -> m < k.
Proof.
  intros [P HP] He; exact (proj1 (LR_inv_univ _ _ _ _ _ _ HP He)).
Qed.

Lemma eqty_univ_eval n T m : eqty n (euniv m) T -> eval T (euniv m).
Proof.
  intros [P HP].
  exact (proj1 (proj2 (LR_inv_univ _ _ _ _ _ _ HP
                         (eval_whnf _ (whnf_univ m))))).
Qed.

Lemma kUFam_univ_absurd k Sy (F : kUFam k Sy) : tyeq Sy (euniv k) -> False.
Proof.
  intros Hty.
  assert (He : eval Sy (euniv k))
    by (destruct (tyeq_sym _ _ Hty) as [n Hn]; exact (eqty_univ_eval n Sy k Hn)).
  exact (Nat.lt_irrefl k (eqty_univ_lt k Sy k (uf_ty F) He)).
Qed.

(* An element of a universe IS a family.  For a subject that is not a type
   former this is ity_of after i_conv; for one that is, the decoder's TyVal
   branch already carries the ITy derivation.  The term-lift reading of an
   `up` is the one case that has to be ruled out, and the universe's own level
   constraint does it. *)
Lemma itm_univ_ty rho A k Sy (F : kUFam (S k) Sy) w (x : kElAt F w)
  (P : iso (kAt F) (kAt (univFam k))) (D : ITm rho A (S k) Sy F w x) :
  { F0 : kUFam k w & (ITy rho A k w F0 *
    kEqAt (univFam k) w (ctoK (kAt F) (kAt (univFam k)) P w x) w (famEl F0))%type }.
Proof.
  destruct A as
    [ i | A1 B1 t1 | A1 t1 | A1 B1 f a | f a | A1 B1 t1 a | A1 B1 q | A1 B1 q
    | A1 B1 | A1 B1 | |
    | n | C z s n | m | Au t1 | A1 t1 | | q | A1 p1 | | T e | A1 t1 a | A1 a
    | A1 B1 t1 a e b ];
    try (exists (elFam (ctoK (kAt F) (kAt (univFam k)) P w x)); split;
         [ apply ity_of;
           [ exact I
           | exact (i_conv rho _ (S k) Sy F (euniv k) (univFam k) w x P D) ]
         | apply kEqC_sym; apply famEl_elFam_rel ]).
  all: pose proof (itm_inv _ _ _ _ _ _ _ D) as E;
       try (cbn [TmInv TmShape TyVal] in E;
            destruct E as [F0 [D0 [Q HQ]]];
            exists F0; split;
            [ exact D0 | eapply kEqC_trans; [apply ctoK_irr | exact HQ] ]).
  (* only the lift is left *)
  destruct Au; cbn [TmInv TmShape UpShape TyVal] in E;
    try (solve [destruct E]).
  destruct E as [F0 [D0 [Q HQ]]].
  exists F0; split; [exact D0 | eapply kEqC_trans; [apply ctoK_irr | exact HQ]].
Qed.

(* ---- the clauses that are pure bookkeeping ---- *)

(* Proof terms.  A Prf-family relates all of its elements, so nothing about the
   subject is needed: the layer-1 relatedness of the two realisers, which FTm
   carries, is the whole argument. *)
Lemma fun_proof rho t wp (xp : kElAt (propFam 0) wp) (h : propVal xp)
  w (g : Good (eprf wp) w) :
  FTm rho t 0 (eprf wp) (prfF 0 xp) w (prfElem w h g).
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  exact (kRel_of_total (prfF 0 xp) F' Piso
           (TotalFam_iso (prfF 0 xp) F' Piso (prf_total 0 wp xp)) w _ w' x' Hrel).
Qed.

(* Conversion of the type: compose the transport with the hypothesis. *)
Lemma fun_conv rho t k Sy (F : kUFam k Sy) Sy' (F' : kUFam k Sy')
  (P : iso (kAt F) (kAt F')) w (x : kElAt F w) (IH : FTm rho t k Sy F w x) :
  FTm rho t k Sy' F' w (ctoK (kAt F) (kAt F') P w x).
Proof.
  intros rho2 Sy2 F2 w2 x2 HR Piso Hrel D2.
  eapply kRel_trans; [apply kRel_sym; apply hetC_to |].
  exact (IH rho2 Sy2 F2 w2 x2 HR
           (iso_trans (kAt F) (kAt F') (kAt F2) P Piso) Hrel D2).
Qed.

(* Variables.  This is what EntryRel's package formulation was for: the two
   entries are related to the same entry of the second environment, and
   composing that is EntryRel_trans, which the old inductive could not
   support. *)
Lemma fun_var0 rho k Sy (F : kUFam k Sy) w (x : kElAt F w) :
  FTm (ext rho F w x) (var_tm 0) k Sy F w x.
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E.
  destruct rho' as [| en' rho0']; [cbn [ext EnvRel] in HR; destruct HR |].
  cbn [ext EnvRel] in HR; destruct HR as [_ Hen].
  destruct k as [| k0]; cbn [TmInv TmShape VarShape] in E.
  - destruct E as [HT | E].
    + exact (kRel_of_total F F' Piso HT w x w' x' Hrel).
    + eapply EntryRel_at; eapply EntryRel_trans;
        [exact Hen | apply EntryRel_sym; exact E].
  - eapply EntryRel_at; eapply EntryRel_trans;
      [exact Hen | apply EntryRel_sym; exact E].
Qed.

Lemma fun_varS rho en i k Sy (F : kUFam k Sy) w (x : kElAt F w)
  (IH : FTm rho (var_tm i) k Sy F w x) :
  FTm (en :: rho) (var_tm (S i)) k Sy F w x.
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E.
  destruct rho' as [| en' rho0']; [cbn [EnvRel] in HR; destruct HR |].
  cbn [EnvRel] in HR; destruct HR as [HR0 _].
  destruct k as [| k0]; cbn [TmInv TmShape VarShape] in E.
  - destruct E as [HT | [x0 [D0 HE]]].
    + exact (kRel_of_total F F' Piso HT w x w' x' Hrel).
    + eapply hetC_eq_r;
        [exact (IH rho0' Sy' F' w' x0 HR0 Piso Hrel D0)
        | apply kEqC_sym; exact HE].
  - destruct E as [x0 [D0 HE]].
    eapply hetC_eq_r;
      [exact (IH rho0' Sy' F' w' x0 HR0 Piso Hrel D0)
      | apply kEqC_sym; exact HE].
Qed.

Lemma fun_zero rho : FTm rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero).
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E; cbn [TmInv TmShape ZeroVal] in E.
  destruct E as [HT | Hv].
  - exact (kRel_of_total (natFam 0) F' Piso HT ezero _ w' x' Hrel).
  - eapply kRel_of_IsVal; [exact Hv | apply kRel_refl].
Qed.

(* A type, read as an element of the universe above it.  This is where
   functionality on types enters functionality on terms: the second
   derivation's value is a family (itm_univ_ty), the two families are
   isomorphic by the hypothesis, and the universe's own equality IS that
   isomorphism. *)
Lemma fun_ty rho A k w (F : kUFam k w) (IH : FTy rho A k w F) :
  FTm rho A (S k) (euniv k) (univFam k) w (famEl F).
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose (P' := iso_sym (kAt (univFam k)) (kAt F') Piso).
  destruct (itm_univ_ty rho' A k Sy' F' w' x' P' D') as [F0' [D0' HE]].
  assert (Hty : eqty k w w').
  { apply (Rel_univ_elim (euniv k) k w w' (eval_whnf _ (whnf_univ k))).
    apply (Rel_tyeq Sy' (euniv k) w w');
      [ apply tyeq_sym; exact (iso_ty (univFam k) F' Piso) | exact Hrel ]. }
  assert (Hiso : iso (kAt F) (kAt F0'))
    by exact (IH rho' w' F0' HR (ex_intro _ k Hty) D0').
  eapply kRel_of_IsVal; [exists P'; exact HE |].
  apply (proj1 (kRel_same (univFam k) _ _ _ _)).
  apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
  eapply iso_trans; [apply uf_coh |].
  eapply iso_trans; [exact Hiso | apply uf_coh].
Qed.

Lemma fun_false rho (g : Good eprop efalse) :
  FTm rho false_ 0 eprop (propFam 0) efalse (propElem efalse False g).
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E; cbn [TmInv TmShape FalseVal] in E.
  destruct E as [HT | [g' Hv]].
  - exact (kRel_of_total (propFam 0) F' Piso HT efalse _ w' x' Hrel).
  - eapply kRel_of_IsVal; [exact Hv |].
    apply (proj1 (kRel_same (propFam 0) _ _ _ _)).
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

Lemma fun_succ rho n wn (x : kElAt (natFam 0) wn)
  (IH : FTm rho n 0 enat (natFam 0) wn x) :
  FTm rho (succ n) 0 enat (natFam 0) (esucc wn) (natSucc x).
Proof.
  intros rho' Sy' F' w' x' HR Piso Hrel D'.
  pose proof (itm_inv _ _ _ _ _ _ _ D') as E; cbn [TmInv TmShape SuccVal] in E.
  destruct E as [HT | [wn' [xn' [Dn' Hv]]]].
  - exact (kRel_of_total (natFam 0) F' Piso HT (esucc wn) _ w' x' Hrel).
  - (* the second realiser is a successor too, so layer 1 peels *)
    assert (Hs : Rel enat (esucc wn) (esucc wn')).
    { destruct Hv as [Q HQ].
      eapply Rel_trans;
        [ apply (Rel_tyeq Sy' enat (esucc wn) w');
            [ apply tyeq_sym; exact (iso_ty (natFam 0) F' Piso) | exact Hrel ]
        | exact (proj2 (proj1 (natEq_iff _ _) HQ)) ]. }
    assert (Hn : Rel enat wn wn')
      by (apply Rel_nat_intro;
          [ apply gt_nat | apply ev_nat
          | apply (NatPer_succ_inv (esucc wn) (esucc wn') wn wn' eq_refl eq_refl);
            exact (Rel_nat_elim enat (esucc wn) (esucc wn') ev_nat Hs) ]).
    pose proof (IH rho' enat (natFam 0) wn' xn' HR (iso_self (natFam 0)) Hn Dn') as Hx.
    eapply kRel_of_IsVal; [exact Hv |].
    apply (proj1 (kRel_same (natFam 0) _ _ _ _)).
    apply natEq_iff; split;
      [ unfold natSucc; rewrite !natIdx_natE;
        exact (f_equal S
                 (proj1 (proj1 (natEq_iff _ _)
                           (proj2 (kRel_same (natFam 0) _ _ _ _) Hx))))
      | exact Hs ].
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
(* substitutions.  Without this lemma there would be no way to know     *)
(* that the realiser in hand is the one layer 1 is talking about.       *)
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
  - (* ity_prf *) intros rho p wp xp Dp IHp; exact (f_equal eprf IHp).
  - (* ity_pi *) intros rho A B k wA FA B0 wB FB redB isoB gPi Ew DA IHA DB IHB;
      exact Ew.
  - (* ity_sig *) intros rho A B k wA FA B0 wB FB redB isoB gSig Ew DA IHA DB IHB;
      exact Ew.
  - (* ity_up *) intros rho A k w F D IH; exact IH.
  - (* ity_of *) intros rho A k w v nf Dv IHv; exact IHv.
  - (* ity_conv *) intros rho A k w F F' P D IH; exact IH.
  - (* i_ty *) intros rho A k w F D IH; exact IH.
  - (* i_var0 *) reflexivity.
  - (* i_varS *) intros rho en i k Sy F w x D IH; exact IH.
  - (* i_zero *) reflexivity.
  - (* i_succ *) intros rho n wn x D IH; exact (f_equal esucc IH).
  - (* i_lam *) intros rho A B t k wA FA B0 wB FB redB isoB gPi w x wt xt Ew Ep
      DA IHA DB IHB Dt IHt Hbeh; exact Ew.
  - (* i_app *) intros rho A B f a k wA FA B0 wB FB redB isoB gPi wf xf wa xa Ep
      DA IHA DB IHB Df IHf Da IHa; exact (f_equal2 eapp IHf IHa).
  - (* i_pair *) intros rho A B t a k wA FA B0 wB FB redB isoB gSig wt xt wa xa g Ep
      DA IHA DB IHB Dt IHt Da IHa; exact (f_equal2 epair IHt IHa).
  - (* i_fst *) intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
      DA IHA DB IHB Dp IHp; exact (f_equal efst IHp).
  - (* i_snd *) intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
      DA IHA DB IHB Dp IHp; exact (f_equal esnd IHp).
  - (* i_natrec *) intros rho C z s n k SC FC isoC S0 wz xz ws xs redS wn xn
      ES DC IHC Dz IHz Ds IHs Dn IHn.
    rewrite IHz, IHn, ES; reflexivity.
  - (* i_false *) reflexivity.
  - (* i_all *) intros rho A p k wA FA wp xp w g Ew DA IHA Dp IHp; exact Ew.
  - (* i_proof *) intros rho t p wp xp h w g Ew Dp IHp; exact Ew.
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
