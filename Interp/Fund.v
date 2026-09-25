From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules Typing.Subst.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels Codes.Lift Codes.LiftIso.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Lift
  Interp.PiFam Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Def Interp.Inv Interp.Ctx Interp.Subst Interp.Fun.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.
Open Scope subst_scope.

(* Theorem 9.2, the layer-2 fundamental lemma.  Three things about the shape
   of the statement are forced, and each is worth spelling out, because none
   of them is what one would write down first.

   1.  THE TYPE'S INTERPRETATION IS AN INPUT, NOT AN OUTPUT.  Every rule of
   the redundant style carries the formation judgement of every type it
   mentions, so a term's type always comes with its own derivation, and its
   family is available from that sibling premise.  Taking it as an input is
   what makes the conversion case work: there the conclusion's type is a
   DIFFERENT type from the premise's, and a statement that produced the type's
   family would have to produce two unrelated ones and then reconcile them,
   which is functionality of the interpretation -- a theorem we do not have and
   do not need.

   2.  THE TYPE PART IS CONDITIONED ON AN ISOMORPHISM TO THE UNIVERSE FAMILY,
   not on the type index being syntactically `univ m`.  A term whose type is
   merely CONVERTIBLE to a universe is still a type, and the isomorphism
   travels along the conversion while the syntax does not.  Note the order of
   the binders: m is bound before the level S m appears, so no cast is needed
   anywhere -- `iso` relates codes at one level, and writing the level as
   `S m` is what keeps that constraint solvable.

   3.  THE CONVERSION CLAUSE OF THE INTERPRETATION IS WHAT MAKES 1 POSSIBLE.
   With the type's family an input, the conversion case has to move a value
   from the family of the premise's type to the family of the conclusion's,
   and `i_conv` (Interp/Def.v) is exactly that move.  It is also what makes
   the type part uniform at every subject that is not a type former: compose
   `i_conv` with `ity_of` and the type part is three lines, the same three
   lines, in every such case. *)

(* ------------------------------------------------------------------ *)
(* Related environments, and the three semantic judgements.           *)
(* ------------------------------------------------------------------ *)

(* Two environments fitting G and related, TOGETHER with the layer-1
   relatedness of the substitutions they induce.  The layer-1 part is not
   derivable from the other three -- Interp/Ctx.v derives it by induction on
   `wfc G`, which the fundamental lemma does not have at hand -- so it travels
   with them.  Extending the bundle under a binder needs exactly the layer-1
   relatedness of the new realisers, and that is what kRel_rel supplies. *)
Definition EnvRelOf (G : ctx) (rho rho' : Env) : Prop :=
  EnvOf G rho /\ EnvOf G rho' /\ EnvRel rho rho' /\ SubstRel G (rsub rho) (rsub rho').

Lemma EnvRelOf_nil : EnvRelOf nil nil nil.
Proof. repeat split; exact I. Qed.

Lemma EnvRelOf_ext G rho rho' (A : tm) k
  (FA : kUFam k (ers rho A)) (FA' : kUFam k (ers rho' A)) u x u' x' :
  EnvRelOf G rho rho' -> kRel FA FA' u x u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros [HO [HO' [HR HS]]] Hrel; split; [| split; [| split]].
  - apply EnvOf_ext; exact HO.
  - apply EnvOf_ext; exact HO'.
  - apply EnvRel_ext; [exact HR | exact Hrel].
  - apply SubstRel_cons; [exact HS |].
    apply Rel_sym; apply (kRel_rel FA' FA u' x' u x); apply kRel_sym; exact Hrel.
Qed.

Definition SemTm (G : ctx) (t A : tm) : Type :=
  forall k rho rho' (HE : EnvRelOf G rho rho')
    (F : kUFam k (ers rho A)) (F' : kUFam k (ers rho' A))
    (DA : ITy rho A k (ers rho A) F) (DA' : ITy rho' A k (ers rho' A) F')
    (IA : iso (kAt F) (kAt F')),
    { x : kElAt F (ers rho t) &
    { x' : kElAt F' (ers rho' t) &
      (ITm rho t k (ers rho A) F (ers rho t) x *
       ITm rho' t k (ers rho' A) F' (ers rho' t) x' *
       kRel F F' (ers rho t) x (ers rho' t) x')%type } }.

Definition SemTy (G : ctx) (t A : tm) : Type :=
  forall m rho rho' (HE : EnvRelOf G rho rho')
    (F : kUFam (S m) (ers rho A)) (F' : kUFam (S m) (ers rho' A))
    (DA : ITy rho A (S m) (ers rho A) F) (DA' : ITy rho' A (S m) (ers rho' A) F')
    (IA : iso (kAt F) (kAt F'))
    (P : iso (kAt F) (kAt (univFam m))),
    { FT : kUFam m (ers rho t) &
    { FT' : kUFam m (ers rho' t) &
      (ITy rho t m (ers rho t) FT * ITy rho' t m (ers rho' t) FT' *
       iso (kAt FT) (kAt FT'))%type } }.

Definition SemJ (G : ctx) (t A : tm) : Type := (SemTm G t A * SemTy G t A)%type.

(* Conversion, in BOTH orders, exactly as layer 1 states it and for the same
   reason: SubstRel is not symmetric (moving the relation from one entry's
   realiser to the other's is layer 1's type clause at the context type), so
   the pair of environments is fixed throughout and both directions have to be
   carried explicitly. *)
Definition SemC (G : ctx) (t t' A : tm) : Type :=
  forall k rho rho' (HE : EnvRelOf G rho rho')
    (F : kUFam k (ers rho A)) (F' : kUFam k (ers rho' A))
    (DA : ITy rho A k (ers rho A) F) (DA' : ITy rho' A k (ers rho' A) F')
    (IA : iso (kAt F) (kAt F')),
    { x : kElAt F (ers rho t) &
    { x' : kElAt F' (ers rho' t') &
    { y : kElAt F (ers rho t') &
    { y' : kElAt F' (ers rho' t) &
      (ITm rho t k (ers rho A) F (ers rho t) x *
       ITm rho' t' k (ers rho' A) F' (ers rho' t') x' *
       kRel F F' (ers rho t) x (ers rho' t') x' *
       ITm rho t' k (ers rho A) F (ers rho t') y *
       ITm rho' t k (ers rho' A) F' (ers rho' t) y' *
       kRel F F' (ers rho t') y (ers rho' t) y')%type } } } }.

(* The realisers of the closed formers are closed, so erasure in an
   environment leaves them alone -- and it does so definitionally, which is
   what lets `ity_univ` and friends be applied with `eq_refl`. *)
Lemma ers_univ rho m : ers rho (univ m) = euniv m.
Proof. reflexivity. Qed.

Lemma ers_nat rho : ers rho nat_ = enat.
Proof. reflexivity. Qed.

Lemma ers_prop rho : ers rho prop = eprop.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The two bridges every case uses.                                   *)
(* ------------------------------------------------------------------ *)

(* The type part, uniformly, at every subject that is NOT a type former:
   convert the value into the universe with i_conv and read it off as a family
   with ity_of.  The two families are isomorphic because the two values are
   related, and the universe's equality IS the isomorphism of the families it
   decodes to (Interp/Univ.v's uEq_iso).  This one lemma discharges the type
   part in every case except the seven formers and the conversion rule. *)
Lemma sem_ty_of (G : ctx) (t A : tm) (H : notFormer t) : SemTm G t A -> SemTy G t A.
Proof.
  intros Stm m rho rho' HE F F' DA DA' IA P.
  destruct (Stm (S m) rho rho' HE F F' DA DA' IA) as [x [x' [[Dx Dx'] Hrel]]].
  pose (P' := iso_trans (kAt F') (kAt F) (kAt (univFam m)) (iso_sym _ _ IA) P).
  exists (elFam (ctoK (kAt F) (kAt (univFam m)) P (ers rho t) x)).
  exists (elFam (ctoK (kAt F') (kAt (univFam m)) P' (ers rho' t) x')).
  split; [split |].
  - apply (ity_of rho t m (ers rho t) _ H).
    exact (i_conv rho t (S m) (ers rho A) F (euniv m) (univFam m) (ers rho t) x P Dx).
  - apply (ity_of rho' t m (ers rho' t) _ H).
    exact (i_conv rho' t (S m) (ers rho' A) F' (euniv m) (univFam m) (ers rho' t) x' P' Dx').
  - assert (Hu : kEqAt (univFam m) (ers rho t)
                   (ctoK (kAt F) (kAt (univFam m)) P (ers rho t) x)
                   (ers rho' t)
                   (ctoK (kAt F') (kAt (univFam m)) P' (ers rho' t) x')).
    { apply (proj2 (kRel_same (univFam m) _ _ _ _)).
      eapply hetC_trans; [apply hetC_sym; apply hetC_to |].
      eapply hetC_trans; [exact Hrel | apply hetC_to]. }
    apply (uEq_iso _ _ Hu).
Qed.

(* A type's own interpretation, from its formation judgement: instantiate the
   type part at the universe family itself, where the isomorphism is the
   identity.  This is how every rule reads the families of the types it
   mentions. *)
Lemma semJ_univ (G : ctx) (A : tm) (k : nat) :
  SemJ G A (univ k) ->
  forall rho rho' (HE : EnvRelOf G rho rho'),
    { FA : kUFam k (ers rho A) &
    { FA' : kUFam k (ers rho' A) &
      (ITy rho A k (ers rho A) FA * ITy rho' A k (ers rho' A) FA' *
       iso (kAt FA) (kAt FA'))%type } }.
Proof.
  intros [_ Sty] rho rho' HE.
  exact (Sty k rho rho' HE (univFam k) (univFam k)
           (ity_univ rho k (euniv k) eq_refl) (ity_univ rho' k (euniv k) eq_refl)
           (iso_self (univFam k)) (iso_self (univFam k))).
Qed.

(* And the term part at a universe type, where the family is the universe's
   own and the relatedness is the universe's equality. *)
Lemma semTm_univ (G : ctx) (A : tm) (k : nat) :
  SemTm G A (univ k) ->
  forall rho rho' (HE : EnvRelOf G rho rho'),
    { v : kElAt (univFam k) (ers rho A) &
    { v' : kElAt (univFam k) (ers rho' A) &
      (ITm rho A (S k) (euniv k) (univFam k) (ers rho A) v *
       ITm rho' A (S k) (euniv k) (univFam k) (ers rho' A) v' *
       kEqAt (univFam k) (ers rho A) v (ers rho' A) v')%type } }.
Proof.
  intros Stm rho rho' HE.
  destruct (Stm (S k) rho rho' HE (univFam k) (univFam k)
              (ity_univ rho k (euniv k) eq_refl) (ity_univ rho' k (euniv k) eq_refl)
              (iso_self (univFam k))) as [v [v' [[Dv Dv'] Hrel]]].
  exists v, v'; split; [split; [exact Dv | exact Dv'] |].
  apply (proj2 (kRel_same (univFam k) _ _ _ _)); exact Hrel.
Qed.

(* The layer-1 equality of a type's two realisers, which is what the universe's
   own equality asks for and what nothing at layer 2 can supply. *)
Lemma sem_lty (G : ctx) (A : tm) (k : nat) (D : ty G A (univ k)) :
  forall rho rho', EnvRelOf G rho rho' -> eqty k (ers rho A) (ers rho' A).
Proof.
  intros rho rho' [_ [_ [_ HS]]].
  exact (fundamental_U G A k D (rsub rho) (rsub rho') HS).
Qed.

(* ------------------------------------------------------------------ *)
(* The type formers, once and for all.                                *)
(*                                                                    *)
(* Every rule whose subject is a type former has the same shape: build *)
(* the family (that is the rule's real content), read it as an element *)
(* of the universe with i_ty, and push it into whatever family the     *)
(* statement was handed with i_conv.  Only the first step differs from *)
(* rule to rule, so it is the only thing sem_former asks for.          *)
(* ------------------------------------------------------------------ *)

Lemma sem_former (G : ctx) (t : tm) (j : nat)
  (Lty : forall rho rho', EnvRelOf G rho rho' -> eqty j (ers rho t) (ers rho' t))
  (mk : forall rho rho' (HE : EnvRelOf G rho rho'),
        { FT : kUFam j (ers rho t) &
        { FT' : kUFam j (ers rho' t) &
          (ITy rho t j (ers rho t) FT * ITy rho' t j (ers rho' t) FT' *
           iso (kAt FT) (kAt FT'))%type } }) :
  SemJ G t (univ j).
Proof.
  split.
  - (* the term part *)
    intros k rho rho' HE F F' DA DA' IA.
    pose proof (ity_univ_lvl rho (univ j) k (ers rho (univ j)) F DA) as El;
      cbn [UnivLvl] in El; subst k.
    pose proof (ity_univ_iso rho (univ j) (S j) (ers rho (univ j)) F DA) as Q;
      cbn [UnivIso] in Q.
    destruct (mk rho rho' HE) as [FT [FT' [[DT DT'] IT]]].
    pose (Q' := iso_trans (kAt F') (kAt F) (kAt (univFam j)) (iso_sym _ _ IA) Q).
    exists (ctoK (kAt (univFam j)) (kAt F) (iso_sym _ _ Q) (ers rho t) (famEl FT)).
    exists (ctoK (kAt (univFam j)) (kAt F') (iso_sym _ _ Q') (ers rho' t) (famEl FT')).
    split; [split |].
    + exact (i_conv rho t (S j) (euniv j) (univFam j) (ers rho (univ j)) F (ers rho t)
               (famEl FT) (iso_sym _ _ Q) (i_ty rho t j (ers rho t) FT DT)).
    + exact (i_conv rho' t (S j) (euniv j) (univFam j) (ers rho' (univ j)) F' (ers rho' t)
               (famEl FT') (iso_sym _ _ Q') (i_ty rho' t j (ers rho' t) FT' DT')).
    + eapply hetC_trans; [apply hetC_sym; apply hetC_to |].
      eapply hetC_trans; [| apply hetC_to].
      apply (proj1 (kRel_same (univFam j) _ _ _ _)).
      apply uEq_of.
      * apply Lty; exact HE.
      * intros v h pf v' h' pf'.
        eapply iso_trans; [apply uf_coh |].
        eapply iso_trans; [exact IT | apply uf_coh].
  - (* the type part: the level is forced, and then mk IS the answer *)
    intros m rho rho' HE F F' DA DA' IA P.
    pose proof (ity_univ_lvl rho (univ j) (S m) (ers rho (univ j)) F DA) as El;
      cbn [UnivLvl] in El; injection El as El1; destruct El1.
    exact (mk rho rho' HE).
Qed.

(* ------------------------------------------------------------------ *)
(* The closed formers: nothing to build, so sem_former does it all.   *)
(* ------------------------------------------------------------------ *)

Lemma sem_nat (G : ctx) (W : wfc G) : SemJ G nat_ (univ 0).
Proof.
  apply (sem_former G nat_ 0).
  - exact (sem_lty G nat_ 0 (t_nat G W)).
  - intros rho rho' HE.
    exists (natFam 0), (natFam 0); split; [split | apply iso_self].
    + exact (ity_nat rho (ers rho nat_) eq_refl).
    + exact (ity_nat rho' (ers rho' nat_) eq_refl).
Qed.

Lemma sem_prop (G : ctx) (W : wfc G) : SemJ G prop (univ 0).
Proof.
  apply (sem_former G prop 0).
  - exact (sem_lty G prop 0 (t_prop G W)).
  - intros rho rho' HE.
    exists (propFam 0), (propFam 0); split; [split | apply iso_self].
    + exact (ity_prop rho (ers rho prop) eq_refl).
    + exact (ity_prop rho' (ers rho' prop) eq_refl).
Qed.

Lemma sem_univ (G : ctx) (W : wfc G) (k : nat) : SemJ G (univ k) (univ (S k)).
Proof.
  apply (sem_former G (univ k) (S k)).
  - exact (sem_lty G (univ k) (S k) (t_univ G k W)).
  - intros rho rho' HE.
    exists (univFam k), (univFam k); split; [split | apply iso_self].
    + exact (ity_univ rho k (ers rho (univ k)) eq_refl).
    + exact (ity_univ rho' k (ers rho' (univ k)) eq_refl).
Qed.

(* ------------------------------------------------------------------ *)
(* FUNCTIONALITY, PROVED INSIDE 9.2.                                  *)
(*                                                                    *)
(* Not as a standalone theorem about raw derivations, because one side  *)
(* condition is missing there: FTy needs `tyeq w w'` -- that the two    *)
(* erasures of one type are equal TYPES -- and only layer 1 proves it.  *)
(* It threads downward through the type formers (eqty_pi_dom and        *)
(* friends), which is why the eight FTy clause lemmas in Interp/Fun.v    *)
(* are provable untyped, but it does NOT thread through a term          *)
(* elimination: at `app A B f a` the conclusion's realiser is wB wa xa,  *)
(* and the domain's tyeq cannot be recovered from it.  Under the typing  *)
(* derivation it comes from fundamental_U applied to the formation       *)
(* premises that the redundant style already carries.                    *)
(*                                                                    *)
(* The statement does not mention the type, which is what makes the      *)
(* conversion rule's case its own induction hypothesis.  The realisers    *)
(* stay free: ers_of_ITm pins them to the erasures anyway.               *)
(* ------------------------------------------------------------------ *)

Definition FunTm (G : ctx) (t : tm) : Prop :=
  forall rho rho' (HE : EnvRelOf G rho rho')
    k Sy (F : kUFam k Sy) w (x : kElAt F w) (D : ITm rho t k Sy F w x)
    Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w') (D' : ITm rho' t k Sy' F' w' x'),
    iso (kAt F) (kAt F') -> Rel Sy' w w' -> kRel F F' w x w' x'.

(* Functionality on TYPES is the same statement one level up: a type is a term
   of the universe, and the universe's own equality IS the isomorphism of the
   families it decodes to. *)
Lemma FunTy_of_FunTm (G : ctx) (A : tm) (H : FunTm G A) :
  forall rho rho' (HE : EnvRelOf G rho rho')
    k w (F : kUFam k w) w' (F' : kUFam k w'),
    ITy rho A k w F -> ITy rho' A k w' F' -> eqty k w w' ->
    iso (kAt F) (kAt F').
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
                (iso_self (univFam k)) Hrel) as Hr.
  pose proof (uEq_iso (famEl F) (famEl F')
                (proj2 (kRel_same (univFam k) _ _ _ _) Hr)) as Hi.
  rewrite !elFam_famEl in Hi.
  exact (Hi w (kAcc F) (evalAg_refl w) w' (kAcc F') (evalAg_refl w')).
Qed.

(* ---- t_var.  Both derivations read the same entry of their own
     environment, and EnvRel relates those two entries: composing the three is
     EntryRel_trans, which the package formulation of EntryRel supports.  The
     induction is on the INDEX, which the induction on the typing derivation
     does not supply. ---- *)
Lemma funtm_var : forall i (G : ctx), FunTm G (var_tm i).
Proof.
  intros i G rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  destruct HE as [_ [_ [HR _]]].
  revert rho rho' HR x x' D D'; induction i as [| i IH];
    intros rho rho' HR x x' D D';
    pose proof (itm_inv _ _ _ _ _ _ _ D) as E;
    pose proof (itm_inv _ _ _ _ _ _ _ D') as E';
    destruct k as [| k0]; cbn [TmInv] in E, E'.
  - destruct E' as [HT' | E'];
      [ exact (kRel_of_total F F' Piso HT' w x w' x' Hrel) |].
    destruct E as [HT | E];
      [ exact (kRel_of_total F F' Piso (TotalFam_iso F F' Piso HT) w x w' x' Hrel) |].
    cbn [TmShape VarShape] in E, E'.
    destruct rho as [| en rho0]; [destruct E |].
    destruct rho' as [| en' rho0']; [destruct E' |].
    cbn [EnvRel] in HR; destruct HR as [_ Hen].
    eapply EntryRel_at.
    eapply EntryRel_trans; [exact E |].
    eapply EntryRel_trans; [exact Hen | apply EntryRel_sym; exact E'].
  - cbn [TmShape VarShape] in E, E'.
    destruct rho as [| en rho0]; [destruct E |].
    destruct rho' as [| en' rho0']; [destruct E' |].
    cbn [EnvRel] in HR; destruct HR as [_ Hen].
    eapply EntryRel_at.
    eapply EntryRel_trans; [exact E |].
    eapply EntryRel_trans; [exact Hen | apply EntryRel_sym; exact E'].
  - destruct E' as [HT' | E'];
      [ exact (kRel_of_total F F' Piso HT' w x w' x' Hrel) |].
    destruct E as [HT | E];
      [ exact (kRel_of_total F F' Piso (TotalFam_iso F F' Piso HT) w x w' x' Hrel) |].
    cbn [TmShape VarShape] in E, E'.
    destruct rho as [| en rho0]; [destruct E |].
    destruct rho' as [| en' rho0']; [destruct E' |].
    cbn [EnvRel] in HR; destruct HR as [HR0 _].
    destruct E as [x0 [D0 HE]]; destruct E' as [x0' [D0' HE']].
    eapply hetC_eq_l; [exact HE |].
    eapply hetC_eq_r;
      [ exact (IH rho0 rho0' HR0 x0 x0' D0 D0') | apply kEqC_sym; exact HE' ].
  - cbn [TmShape VarShape] in E, E'.
    destruct rho as [| en rho0]; [destruct E |].
    destruct rho' as [| en' rho0']; [destruct E' |].
    cbn [EnvRel] in HR; destruct HR as [HR0 _].
    destruct E as [x0 [D0 HE]]; destruct E' as [x0' [D0' HE']].
    eapply hetC_eq_l; [exact HE |].
    eapply hetC_eq_r;
      [ exact (IH rho0 rho0' HR0 x0 x0' D0 D0') | apply kEqC_sym; exact HE' ].
Qed.

(* Both derivations are arbitrary here, so both get decoded and both IsVals
   have to be absorbed -- one on each side of the relation between the two
   clauses' canonical values.  That is all any case's plumbing amounts to. *)
Lemma kRel_of_IsVal_l {k Sy Syc} (F : kUFam k Sy) (Fc : kUFam k Syc)
  w (x : kElAt F w) wc (xc : kElAt Fc wc) :
  IsVal F w x Fc wc xc -> kRel F Fc w x wc xc.
Proof. intros [P HP]; eapply hetC_eq_r; [apply hetC_to | exact HP]. Qed.

Lemma kRel_of_IsVal2 {k Sy Sy' Syc Syc'} (F : kUFam k Sy) (F' : kUFam k Sy')
  (Fc : kUFam k Syc) (Fc' : kUFam k Syc')
  w (x : kElAt F w) w' (x' : kElAt F' w')
  wc (xc : kElAt Fc wc) wc' (xc' : kElAt Fc' wc') :
  IsVal F w x Fc wc xc -> IsVal F' w' x' Fc' wc' xc' ->
  kRel Fc Fc' wc xc wc' xc' -> kRel F F' w x w' x'.
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

Ltac funtm_proofs F F' Piso w x w' x' Hrel :=
  match goal with
  | E' : (TotalFam _ + _)%type |- _ =>
      destruct E' as [HT' | E'];
      [ exact (kRel_of_total F F' Piso HT' w x w' x' Hrel) |];
      match goal with
      | E : (TotalFam _ + _)%type |- _ =>
          destruct E as [HT | E];
          [ exact (kRel_of_total F F' Piso (TotalFam_iso F F' Piso HT) w x w' x' Hrel) |]
      end
  end.

Lemma funtm_zero (G : ctx) : FunTm G zero.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv TmShape ZeroVal] in E, E'; [| destruct E].
  funtm_proofs F F' Piso w x w' x' Hrel.
  eapply kRel_of_IsVal2; [exact E | exact E' | apply kRel_refl].
Qed.

Lemma funtm_false (G : ctx) : FunTm G false_.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv TmShape FalseVal] in E, E'; [| destruct E].
  funtm_proofs F F' Piso w x w' x' Hrel.
  destruct E as [g Hv]; destruct E' as [g' Hv'].
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (proj1 (kRel_same (propFam 0) _ _ _ _)).
  apply propEq_iff; split; [split; exact (fun h => h) | exact g].
Qed.

(* ---- the type formers, once.  At such a subject the decoder's branch IS
     TyVal, so both readings hand over an ITy derivation and the universe's own
     equality turns their isomorphism into the relation asked for.  Each former
     then only has to say why its two readings agree, which is what its
     inversion lemma in Interp/Inv.v is for. ---- *)
Lemma funtm_former (G : ctx) (t : tm)
  (Hsh : forall rho k Sy (F : kUFam k Sy) w (x : kElAt F w),
           TmShape rho t k Sy F w x -> TyVal rho t k Sy F w x)
  (H : forall rho rho' k w (F : kUFam k w) w' (F' : kUFam k w'),
         EnvRelOf G rho rho' -> ITy rho t k w F -> ITy rho' t k w' F' ->
         eqty k w w' /\ iso (kAt F) (kAt F')) :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv] in E, E'.
  - funtm_proofs F F' Piso w x w' x' Hrel.
    apply Hsh in E; cbn [TyVal] in E; destruct E.
  - apply Hsh in E; apply Hsh in E'; cbn [TyVal] in E, E'.
    destruct E as [F0 [D0 Hv]]; destruct E' as [F0' [D0' Hv']].
    destruct (H rho rho' k0 w F0 w' F0' HE D0 D0') as [Hty Hi].
    eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
    apply (proj1 (kRel_same (univFam k0) _ _ _ _)).
    apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
    eapply iso_trans; [apply uf_coh |].
    eapply iso_trans; [exact Hi | apply uf_coh].
Qed.

Lemma funtm_nat (G : ctx) : FunTm G nat_.
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  split; [exact (uf_ty F) |].
  eapply iso_trans;
    [ exact (ity_nat_inv rho nat_ k (ers rho nat_) F D)
    | apply iso_sym; exact (ity_nat_inv rho' nat_ k (ers rho' nat_) F' D') ].
Qed.

Lemma funtm_prop (G : ctx) : FunTm G prop.
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  split; [exact (uf_ty F) |].
  eapply iso_trans;
    [ exact (ity_prop_inv rho prop k (ers rho prop) F D)
    | apply iso_sym; exact (ity_prop_inv rho' prop k (ers rho' prop) F' D') ].
Qed.

Lemma funtm_univ (G : ctx) (m : nat) : FunTm G (univ m).
Proof.
  apply funtm_former; [intros rho k Sy F w x H; exact H |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  pose proof (ity_univ_lvl rho (univ m) k (ers rho (univ m)) F D) as El;
    cbn [UnivLvl] in El; subst k.
  split; [exact (uf_ty F) |].
  pose proof (ity_univ_iso rho (univ m) (S m) (ers rho (univ m)) F D) as Q;
    cbn [UnivIso] in Q.
  pose proof (ity_univ_iso rho' (univ m) (S m) (ers rho' (univ m)) F' D') as Q';
    cbn [UnivIso] in Q'.
  eapply iso_trans; [exact Q | apply iso_sym; exact Q'].
Qed.

Lemma funtm_succ (G : ctx) (n : tm) (IHn : FunTm G n) : FunTm G (succ n).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv TmShape SuccVal] in E, E'; [| destruct E].
  funtm_proofs F F' Piso w x w' x' Hrel.
  destruct E as [wn [xn [Dn Hv]]]; destruct E' as [wn' [xn' [Dn' Hv']]].
  assert (Hs : Rel enat (esucc wn) (esucc wn')).
  { destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
    eapply Rel_trans;
      [ apply Rel_sym; exact (proj2 (proj1 (natEq_iff _ _) HQ)) |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy' enat w w' (iso_ty F' (natFam 0) Q') Hrel)
      | exact (proj2 (proj1 (natEq_iff _ _) HQ')) ]. }
  assert (Hn : Rel enat wn wn')
    by (apply Rel_nat_intro;
        [ apply gt_nat | apply ev_nat
        | apply (NatPer_succ_inv (esucc wn) (esucc wn') wn wn' eq_refl eq_refl);
          exact (Rel_nat_elim enat (esucc wn) (esucc wn') ev_nat Hs) ]).
  pose proof (IHn rho rho' HE 0 enat (natFam 0) wn xn Dn enat (natFam 0) wn' xn' Dn'
                (iso_self (natFam 0)) Hn) as Hx.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (proj1 (kRel_same (natFam 0) _ _ _ _)).
  apply natEq_iff; split;
    [ unfold natSucc; rewrite !natIdx_natE;
      exact (f_equal S
               (proj1 (proj1 (natEq_iff _ _)
                         (proj2 (kRel_same (natFam 0) _ _ _ _) Hx))))
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
         iso (kAt F) (kAt F')) :
  FunTm G t.
Proof.
  apply funtm_former; [exact Hsh |].
  intros rho rho' k w F w' F' HE D D'.
  split; [| exact (H rho rho' k w F w' F' HE D D')].
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  exact (eqty_at_lvl k _ _ (uf_ty F) (uf_ty F') (Lt rho rho' HE)).
Qed.

Lemma funtm_prf (G : ctx) (p : tm) (Lp : LTy G (prf p)) (IHp : FunTm G p) :
  FunTm G (prf p).
Proof.
  apply (funtm_former_l G (prf p));
    [intros rho k Sy F w x H; exact H | exact Lp |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ity_lvl_dec rho (prf p) k w F D) as El; cbn [LvlDec] in El; subst k.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  pose proof (Lp rho rho' HE) as Hty.
  destruct (ity_prf_inv rho (prf p) 0 (ers rho (prf p)) F D) as [wp [xp [Dp Hiso]]].
  destruct (ity_prf_inv rho' (prf p) 0 (ers rho' (prf p)) F' D') as [wp' [xp' [Dp' Hiso']]].
  assert (Ep : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ep' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  subst wp wp'.
  assert (Hpr : PR (ers rho p) (ers rho' p)).
  { destruct Hty as [n Hn].
    exact (eqty_prf_inv n _ _ _ _ Hn (ev_prf_self _) (ev_prf_self _)). }
  assert (Hrp : Rel eprop (ers rho p) (ers rho' p))
    by (apply Rel_prop_intro;
        [ exact good_ty_prop | apply eval_whnf, whnf_prop | exact Hpr ]).
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply prfFam_iso; [exact Hty |].
  exact (proj1 (proj1 (propEq_iff xp xp')
                  (proj2 (kRel_same (propFam 0) _ _ _ _)
                     (IHp rho rho' HE 0 eprop (propFam 0) _ xp Dp
                          eprop (propFam 0) _ xp' Dp'
                          (iso_self (propFam 0)) Hrp)))).
Qed.

(* The universe lift.  The realiser is untouched, so nothing moves on the
   layer-1 side; the families move by famLiftK_iso. *)
Lemma funtm_up (G : ctx) (A : tm) (j : nat)
  (LA : LTy G A) (IHA : FunTm G A) : FunTm G (up (univ (S j)) A).
Proof.
  apply (funtm_former_l G (up (univ (S j)) A));
    [intros rho k Sy F w x H; exact H
    | intros rho rho' HE; exact (LA rho rho' HE) |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ity_lvl_dec rho (up (univ (S j)) A) k w F D) as El;
    cbn [LvlDec] in El; subst k.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_up_inv rho (up (univ (S j)) A) (S j) _ F D)
    as [F1 [[Ej DA] Hi]].
  destruct (ity_up_inv rho' (up (univ (S j)) A) (S j) _ F' D')
    as [F1' [[Ej' DA'] Hi']].
  eapply iso_trans; [exact Hi |].
  eapply iso_trans; [| apply iso_sym; exact Hi'].
  apply famLiftK_iso.
  exact (FunTy_of_FunTm G A IHA rho rho' HE j _ F1 _ F1' DA DA'
           (eqty_at_lvl j _ _ (uf_ty F1) (uf_ty F1') (LA rho rho' HE))).
Qed.

(* ------------------------------------------------------------------ *)
(* Pi and Sigma.  The codomain is interpreted in an environment EXTENDED *)
(* by the domain's family, and the two derivations decompose the type    *)
(* with different domain families, so the codomain's induction           *)
(* hypothesis is used at (A :: G) with the two extended environments     *)
(* related by EnvRelOf_ext.                                              *)
(* ------------------------------------------------------------------ *)

Lemma funtm_pi (G : ctx) (A B : tm)
  (Lpi : LTy G (pi A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) : FunTm G (pi A B).
Proof.
  apply (funtm_former_l G (pi A B));
    [intros rho k Sy F w x H; exact H | exact Lpi |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_pi_inv rho (pi A B) k _ F D)
    as [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hw] Hiso]]]]]]]]].
  destruct (ity_pi_inv rho' (pi A B) k _ F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply piFam_iso.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact (Lpi rho rho' HE) | exact Hw'].
  - exact (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA'
             (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  - intros u x u' x' Hrel.
    pose proof (EnvRelOf_ext G rho rho' A k FA FA' u x u' x' HE Hrel) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' x') as DBx'.
    assert (EB : wB u x = ers (ext rho FA u x) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB' : wB' u' x' = ers (ext rho' FA' u' x') B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    assert (Htyb : tyeq (wB u x) (wB' u' x'))
      by (rewrite EB, EB'; exact (LB _ _ HEx)).
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx k _ (FB u x) _ (FB' u' x')
             DBx DBx'
             (eqty_at_lvl k _ _ (uf_ty (FB u x)) (uf_ty (FB' u' x')) Htyb)).
Qed.

Lemma funtm_sig (G : ctx) (A B : tm)
  (Lsig : LTy G (sig_ A B)) (LA : LTy G A) (LB : LTy (A :: G) B)
  (IHA : FunTm G A) (IHB : FunTm (A :: G) B) : FunTm G (sig_ A B).
Proof.
  apply (funtm_former_l G (sig_ A B));
    [intros rho k Sy F w x H; exact H | exact Lsig |].
  intros rho rho' k w F w' F' HE D D'.
  pose proof (ers_of_ITy _ _ _ _ _ D) as Ew;
    pose proof (ers_of_ITy _ _ _ _ _ D') as Ew'; subst w w'.
  destruct (ity_sig_inv rho (sig_ A B) k _ F D)
    as [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hw] Hiso]]]]]]]]].
  destruct (ity_sig_inv rho' (sig_ A B) k _ F' D')
    as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  eapply iso_trans; [exact Hiso |].
  eapply iso_trans; [| apply iso_sym; exact Hiso'].
  apply sigFam_iso.
  - eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
    eapply tyeq_trans; [exact (Lsig rho rho' HE) | exact Hw'].
  - exact (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA'
             (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  - intros u x u' x' Hrel.
    pose proof (EnvRelOf_ext G rho rho' A k FA FA' u x u' x' HE Hrel) as HEx.
    pose proof (DB u x) as DBx; pose proof (DB' u' x') as DBx'.
    assert (EB : wB u x = ers (ext rho FA u x) B)
      by exact (ers_of_ITy _ _ _ _ _ DBx).
    assert (EB' : wB' u' x' = ers (ext rho' FA' u' x') B)
      by exact (ers_of_ITy _ _ _ _ _ DBx').
    assert (Htyb : tyeq (wB u x) (wB' u' x'))
      by (rewrite EB, EB'; exact (LB _ _ HEx)).
    exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx k _ (FB u x) _ (FB' u' x')
             DBx DBx'
             (eqty_at_lvl k _ _ (uf_ty (FB u x)) (uf_ty (FB' u' x')) Htyb)).
Qed.

(* ------------------------------------------------------------------ *)
(* The layer-1 side conditions, as they come out of the layer-1        *)
(* fundamental theorem: EnvRelOf carries a SubstRel, which is exactly  *)
(* what SEl consumes.                                                  *)
(* ------------------------------------------------------------------ *)

Definition LTm (G : ctx) (t A : tm) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> Rel (ers rho A) (ers rho t) (ers rho' t).

Lemma LTm_of_ty G t A (d : ty G t A) : LTm G t A.
Proof. intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_ty G t A d _ _ HS). Qed.

Lemma LTy_of_ty G A k (d : ty G A (univ k)) : LTy G A.
Proof.
  intros rho rho' [_ [_ [_ HS]]]; exists k; exact (fundamental_U G A k d _ _ HS).
Qed.

(* Related environments have the same levels, so ity_lvl applies to two
   derivations taken in them.  This is what pins the DOMAIN's level in the
   impredicative forall, where the subject does not mention it. *)
Lemma lvls_of_EnvRel : forall rho rho', EnvRel rho rho' -> lvls rho = lvls rho'.
Proof.
  induction rho as [| en r IH]; intros [| en' r'] H; cbn in H |- *;
    try (solve [destruct H]); [reflexivity |].
  destruct H as [HR HE]; f_equal;
    [exact (EntryRel_k _ _ HE) | exact (IH r' HR)].
Qed.

Lemma lvls_of_EnvRelOf G rho rho' : EnvRelOf G rho rho' -> lvls rho = lvls rho'.
Proof. intros [_ [_ [HR _]]]; exact (lvls_of_EnvRel rho rho' HR). Qed.

(* Impredicative forall: a TERM of prop, so the value is a proposition and
   functionality is an iff.  The domain's level is existential in the
   decoder, and the two readings agree on it by ity_lvl. *)
Lemma funtm_all (G : ctx) (A p : tm)
  (LA : LTy G A) (Lp : LTm (A :: G) p prop)
  (IHA : FunTm G A) (IHp : FunTm (A :: G) p) : FunTm G (all A p).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv TmShape AllVal] in E, E'; [| destruct E].
  funtm_proofs F F' Piso w x w' x' Hrel.
  destruct E as [kA [wA [FA [wp [xp [wv [g [[DA Dp] Hv]]]]]]]].
  destruct E' as [kA' [wA' [FA' [wp' [xp' [wv' [g' [[DA' Dp'] Hv']]]]]]]].
  pose proof (lvls_of_EnvRelOf G rho rho' HE) as HL.
  pose proof (ity_lvl rho rho' HL A kA wA FA kA' wA' FA' DA DA') as Ek; subst kA'.
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  assert (PA : iso (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE kA _ FA _ FA' DA DA'
                (eqty_at_lvl kA _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  (* one direction of the iff, stated for an arbitrary related pair of
     arguments, so that both directions are instances of it *)
  assert (Key : forall u (y : kElAt FA u) u2 (y2 : kElAt FA' u2),
             kRel FA FA' u y u2 y2 -> (propVal (xp u y) <-> propVal (xp' u2 y2))).
  { intros u y u2 y2 Hy.
    pose proof (EnvRelOf_ext G rho rho' A kA FA FA' u y u2 y2 HE Hy) as HEx.
    assert (Ew : wp u y = ers (ext rho FA u y) p)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp u y)).
    assert (Ew' : wp' u2 y2 = ers (ext rho' FA' u2 y2) p)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp' u2 y2)).
    assert (Hr : Rel eprop (wp u y) (wp' u2 y2))
      by (rewrite Ew, Ew'; exact (Lp _ _ HEx)).
    exact (proj1 (proj1 (propEq_iff (xp u y) (xp' u2 y2))
                    (proj2 (kRel_same (propFam 0) _ _ _ _)
                       (IHp _ _ HEx 0 eprop (propFam 0) _ (xp u y) (Dp u y)
                            eprop (propFam 0) _ (xp' u2 y2) (Dp' u2 y2)
                            (iso_self (propFam 0)) Hr)))). }
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hw : Rel eprop w wv)
    by exact (proj2 (proj1 (propEq_iff _ _) HQ)).
  assert (Hw' : Rel eprop w' wv')
    by exact (proj2 (proj1 (propEq_iff _ _) HQ')).
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  apply (proj1 (kRel_same (propFam 0) _ _ _ _)).
  apply propEq_iff; split.
  - cbn [propVal propElem proj1_sig Datatypes.fst]; split.
    + intros H u2 y2.
      exact (proj1 (Key u2 (moveTo FA' FA (iso_sym _ _ PA) u2 y2 u2 (reds_refl u2))
                         u2 y2
                     (kRel_sym _ _ _ _ _ _
                        (moveTo_rel FA' FA (iso_sym _ _ PA) u2 y2 u2
                           (reds_refl u2))))
               (H u2 _)).
    + intros H u y.
      exact (proj2 (Key u y u (moveTo FA FA' PA u y u (reds_refl u))
                     (moveTo_rel FA FA' PA u y u (reds_refl u)))
               (H u _)).
  - eapply Rel_trans; [apply Rel_sym; exact Hw |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy' eprop w w' (iso_ty F' (propFam 0) Q') Hrel)
      | exact Hw' ].
Qed.

(* ------------------------------------------------------------------ *)
(* Proof terms.  The interpretation has ONE clause for them (i_proof),  *)
(* so their decoder branch is empty and every reading is the universal   *)
(* one, which is functional by proof irrelevance.  This covers plam,     *)
(* papp and absurd at once -- t_all_intro, t_all_elim and t_absurd.      *)
(* ------------------------------------------------------------------ *)

Lemma funtm_noval (G : ctx) (t : tm)
  (Hsh : forall rho k Sy (F : kUFam k Sy) w (x : kElAt F w),
           TmShape rho t k Sy F w x -> False) :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv] in E, E'.
  - funtm_proofs F F' Piso w x w' x' Hrel.
    destruct (Hsh _ _ _ _ _ _ E).
  - destruct (Hsh _ _ _ _ _ _ E).
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
(* The term lift.  Two readings of `uptm A t` lift the value along two   *)
(* DIFFERENT families, so relating them needs the naturality of the      *)
(* lift against the transport (Codes/LiftIso.v, liftEl_to): the lift of  *)
(* a transported element is the transport of the lifted one.             *)
(* ------------------------------------------------------------------ *)

Lemma kRel_lift {k u u'} (F : kUFam k u) (F' : kUFam k u') w x w' x' :
  kRel F F' w x w' x' ->
  kRel (famLiftK F) (famLiftK F') w (elLift F w x) w' (elLift F' w' x').
Proof.
  intros [P HP].
  eapply hetC_eq_r; [| apply elLift_eq; exact HP].
  eapply hetC_trans;
    [ apply hetC_sym;
      exact (hetC_to (uf_c (famLiftK F) u (kAcc F) (evalAg_refl u))
               (kAt (famLiftK F))
               (uf_coh (famLiftK F) u (kAcc F) (evalAg_refl u) u
                  (kAcc (famLiftK F)) (evalAg_refl u))
               w (liftEl k (rk u (kAcc F)) (kAt F) w x)) |].
  eapply hetC_trans;
    [ exists (liftIso k (rk u (kAcc F)) (rk u' (kAcc F')) (kAt F) (kAt F') P);
      apply liftEl_to |].
  exact (hetC_to (uf_c (famLiftK F') u' (kAcc F') (evalAg_refl u'))
           (kAt (famLiftK F'))
           (uf_coh (famLiftK F') u' (kAcc F') (evalAg_refl u') u'
              (kAcc (famLiftK F')) (evalAg_refl u'))
           w (liftEl k (rk u' (kAcc F')) (kAt F') w
                (ctoK (kAt F) (kAt F') P w x))).
Qed.

Lemma funtm_uptm (G : ctx) (A t : tm) (LA : LTy G A)
  (IHA : FunTm G A) (IHt : FunTm G t) : FunTm G (uptm A t).
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv TmShape UpTmVal] in E, E';
    [ funtm_proofs F F' Piso w x w' x' Hrel; destruct E |].
  destruct E as [Sy1 [F1 [x1 [[DA D1] Hv]]]].
  destruct E' as [Sy1' [F1' [x1' [[DA' D1'] Hv']]]].
  assert (E1 : Sy1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (E1' : Sy1' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst Sy1 Sy1'.
  assert (PA : iso (kAt F1) (kAt F1'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE k0 _ F1 _ F1' DA DA'
                (eqty_at_lvl k0 _ _ (uf_ty F1) (uf_ty F1') (LA rho rho' HE))).
  assert (Hr : Rel (ers rho' A) w w')
    by exact (Rel_tyeq Sy' (ers rho' A) w w'
                (iso_ty F' (famLiftK F1') (projT1 Hv')) Hrel).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply kRel_lift.
  exact (IHt rho rho' HE k0 _ F1 w x1 D1 _ F1' w' x1' D1' PA Hr).
Qed.

(* ------------------------------------------------------------------ *)
(* The eliminators and the two introductions at Pi and Sigma.          *)
(*                                                                    *)
(* None of these subjects pins its level, so the i_proof reading has to *)
(* be discharged at level 0 and the same argument then run at every     *)
(* level.  funtm_shape does that once and for all: its hypothesis is    *)
(* the decoder's branch against the decoder's branch, which is what     *)
(* every case below actually proves.                                   *)
(* ------------------------------------------------------------------ *)

Lemma funtm_shape (G : ctx) (t : tm)
  (H : forall rho rho' k Sy (F : kUFam k Sy) w (x : kElAt F w)
              Sy' (F' : kUFam k Sy') w' (x' : kElAt F' w'),
         EnvRelOf G rho rho' ->
         TmShape rho t k Sy F w x -> TmShape rho' t k Sy' F' w' x' ->
         iso (kAt F) (kAt F') -> Rel Sy' w w' -> kRel F F' w x w' x') :
  FunTm G t.
Proof.
  intros rho rho' HE k Sy F w x D Sy' F' w' x' D' Piso Hrel.
  funtm_start D D'.
  destruct k as [| k0]; cbn [TmInv] in E, E'.
  - funtm_proofs F F' Piso w x w' x' Hrel.
    exact (H rho rho' 0 Sy F w x Sy' F' w' x' HE E E' Piso Hrel).
  - exact (H rho rho' (S k0) Sy F w x Sy' F' w' x' HE E E' Piso Hrel).
Qed.

(* The first projection.  The pin on the subject's Sigma-realiser (Interp/Def.v)
   is what makes this work: it rebuilds the interpretation of `sig_ A B` with
   ity_sig, so the two readings' Sigma-families are isomorphic by
   FunTy_of_FunTm, and the subject's layer-1 relatedness transfers to the
   second reading's realiser.  Then sigFst_to moves the transport across the
   projection and sigFst_eq closes the homogeneous half. *)
Lemma funtm_fst (G : ctx) (A B p : tm)
  (Lsig : LTy G (sig_ A B)) (IHsig : FunTm G (sig_ A B))
  (Lp : LTm G p (sig_ A B)) (IHp : FunTm G p) : FunTm G (fst A B p).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape FstVal] in E, E'.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig
    [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig'
    [wp' [xp' [[[[Ep' DA'] DB'] Dp'] Hv']]]]]]]]]]].
  assert (Hty : tyeq (esig wA B0) (esig wA' B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  pose proof (ity_sig rho A B k wA FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho' A B k wA' FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  assert (Psig : iso (kAt (sigFam k wA B0 FA wB FB redB isoB gSig))
                     (kAt (sigFam k wA' B0' FA' wB' FB' redB' isoB' gSig')))
    by exact (FunTy_of_FunTm G (sig_ A B) IHsig rho rho' HE k _ _ _ _ Dsig Dsig'
                (eqty_at_lvl k _ _ gSig gSig' Hty)).
  assert (Ewp : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ewp' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  assert (Hrp : Rel (esig wA' B0') wp wp').
  { rewrite Ewp, Ewp'.
    apply (Rel_tyeq (ers rho (sig_ A B)) (esig wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  pose proof (IHp rho rho' HE k (esig wA B0) _ wp xp Dp
                (esig wA' B0') _ wp' xp' Dp' Psig Hrp) as Hx.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (sigFst_to k wA B0 FA wB FB redB isoB gSig
               wA' B0' FA' wB' FB' redB' isoB' gSig' Psig wp xp) |].
  apply (proj1 (kRel_same FA' _ _ _ _)).
  apply (sigFst_eq k wA' B0' FA' wB' FB' redB' isoB' gSig').
  exact (kRel_at _ _ Psig wp xp wp' xp' Hx).
Qed.

(* The second projection.  Same shape, with sigSnd_to for the transport and
   sigSnd_eq -- which is already heterogeneous, the codomain instance moving
   with the first component -- for the homogeneous half.  No induction
   hypothesis for B is needed: sigSnd_eq carries the codomain iso itself. *)
Lemma funtm_snd (G : ctx) (A B p : tm)
  (Lsig : LTy G (sig_ A B)) (IHsig : FunTm G (sig_ A B))
  (Lp : LTm G p (sig_ A B)) (IHp : FunTm G p) : FunTm G (snd A B p).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape SndVal] in E, E'.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig
    [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig'
    [wp' [xp' [[[[Ep' DA'] DB'] Dp'] Hv']]]]]]]]]]].
  assert (Hty : tyeq (esig wA B0) (esig wA' B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  pose proof (ity_sig rho A B k wA FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho' A B k wA' FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  assert (Psig : iso (kAt (sigFam k wA B0 FA wB FB redB isoB gSig))
                     (kAt (sigFam k wA' B0' FA' wB' FB' redB' isoB' gSig')))
    by exact (FunTy_of_FunTm G (sig_ A B) IHsig rho rho' HE k _ _ _ _ Dsig Dsig'
                (eqty_at_lvl k _ _ gSig gSig' Hty)).
  assert (Ewp : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ewp' : wp' = ers rho' p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  assert (Hrp : Rel (esig wA' B0') wp wp').
  { rewrite Ewp, Ewp'.
    apply (Rel_tyeq (ers rho (sig_ A B)) (esig wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  pose proof (IHp rho rho' HE k (esig wA B0) _ wp xp Dp
                (esig wA' B0') _ wp' xp' Dp' Psig Hrp) as Hx.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (sigSnd_to k wA B0 FA wB FB redB isoB gSig
               wA' B0' FA' wB' FB' redB' isoB' gSig' Psig wp xp) |].
  apply (sigSnd_eq k wA' B0' FA' wB' FB' redB' isoB' gSig').
  exact (kRel_at _ _ Psig wp xp wp' xp' Hx).
Qed.

(* Application.  Two legs: piApp_to moves both transports -- the function's
   along the Pi-families' iso, the argument's along the domains' -- across the
   application, and piApp_eq closes the rest inside the second reading's
   codomain.  The argument's iso is NOT read off the Pi-families' one: it comes
   from the annotation A, which t_app carries a derivation for. *)
Lemma funtm_app (G : ctx) (A B f a : tm)
  (LA : LTy G A) (IHA : FunTm G A)
  (Lpi : LTy G (pi A B)) (IHpi : FunTm G (pi A B))
  (Lf : LTm G f (pi A B)) (IHf : FunTm G f)
  (La : LTm G a A) (IHa : FunTm G a) : FunTm G (app A B f a).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape AppVal] in E, E'.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi [wf [xf [wa [xa [[[[[Ep DA] DB] Df] Da] Hv]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [wf' [xf' [wa' [xa' [[[[[Ep' DA'] DB'] Df'] Da'] Hv']]]]]]]]]]]]].
  assert (Hty : tyeq (epi wA B0) (epi wA' B0'))
    by (rewrite Ep, Ep'; exact (Lpi rho rho' HE)).
  pose proof (ity_pi rho A B k wA FA B0 wB FB redB isoB gPi Ep DA DB) as Dpi.
  pose proof (ity_pi rho' A B k wA' FA' B0' wB' FB' redB' isoB' gPi' Ep' DA' DB')
    as Dpi'.
  assert (Ppi : iso (kAt (piFam k wA B0 FA wB FB redB isoB gPi))
                    (kAt (piFam k wA' B0' FA' wB' FB' redB' isoB' gPi')))
    by exact (FunTy_of_FunTm G (pi A B) IHpi rho rho' HE k _ _ _ _ Dpi Dpi'
                (eqty_at_lvl k _ _ gPi gPi' Hty)).
  (* the domain, from the annotation *)
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (QA : iso (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA'
                (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA')
                   (eq_rect_r (fun z => tyeq z _) (eq_rect_r (fun z => tyeq _ z)
                      (LA rho rho' HE) EA') EA))).
  (* the function and the argument *)
  assert (Ewf : wf = ers rho f) by exact (ers_of_ITm _ _ _ _ _ _ _ Df).
  assert (Ewf' : wf' = ers rho' f) by exact (ers_of_ITm _ _ _ _ _ _ _ Df').
  assert (Hrf : Rel (epi wA' B0') wf wf').
  { rewrite Ewf, Ewf'.
    apply (Rel_tyeq (ers rho (pi A B)) (epi wA' B0'));
      [ rewrite <- Ep; exact Hty | exact (Lf rho rho' HE) ]. }
  assert (Ewa : wa = ers rho a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho' a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  assert (Hra : Rel wA' wa wa').
  { rewrite Ewa, Ewa', EA'.
    apply (Rel_tyeq (ers rho A) (ers rho' A));
      [ exact (LA rho rho' HE) | exact (La rho rho' HE) ]. }
  pose proof (IHf rho rho' HE k (epi wA B0) _ wf xf Df
                (epi wA' B0') _ wf' xf' Df' Ppi Hrf) as Hxf.
  pose proof (IHa rho rho' HE k wA FA wa xa Da wA' FA' wa' xa' Da' QA Hra) as Hxa.
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (piApp_to k wA B0 FA wB FB redB isoB gPi
               wA' B0' FA' wB' FB' redB' isoB' gPi' Ppi QA wf xf
               (proj2 (kRel_same _ _ _ _ _) (kRel_refl _ wf xf)) wa xa) |].
  apply (piApp_eq k wA' B0' FA' wB' FB' redB' isoB' gPi');
    [ exact (kRel_at _ _ Ppi wf xf wf' xf' Hxf)
    | exact (kRel_at _ _ QA wa xa wa' xa' Hxa) ].
Qed.

(* ------------------------------------------------------------------ *)
(* The pair.  There is no `sigPair_to` -- the transport of a pair is not  *)
(* stated componentwise anywhere -- so the two readings are compared      *)
(* through SURJECTIVE PAIRING instead: inside the second reading's        *)
(* family, the transported pair IS the pair of its projections, and the   *)
(* projections are handled by sigFst_to/sigSnd_to exactly as at fst and   *)
(* snd.  sigPair_surj asks for two layer-1 facts about the reconstructed   *)
(* pair, which sig_eta_rel supplies.                                      *)
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

Lemma funtm_pair (G : ctx) (A B t a : tm)
  (LA : LTy G A) (IHA : FunTm G A)
  (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  (Lsig : LTy G (sig_ A B)) (IHsig : FunTm G (sig_ A B))
  (Lp : LTm G (pair A B t a) (sig_ A B))
  (Lt : LTm G t A) (IHt : FunTm G t)
  (La : LTm G a (B [t..])) (IHa : FunTm G a) : FunTm G (pair A B t a).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape PairVal] in E, E'.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig [wt [xt [wa [xa [g
    [[[[[Ep DA] DB] Dt] Da] Hv]]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [wt' [xt' [wa' [xa' [g'
    [[[[[Ep' DA'] DB'] Dt'] Da'] Hv']]]]]]]]]]]]]].
  (* every realiser is the erasure it should be *)
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (Ewt : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt).
  assert (Ewt' : wt' = ers rho' t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt').
  assert (Ewa : wa = ers rho a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho' a) by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  subst wA wA' wt wt' wa wa'.
  (* the Sigma-families, through the pin *)
  assert (Hty : tyeq (esig (ers rho A) B0) (esig (ers rho' A) B0'))
    by (rewrite Ep, Ep'; exact (Lsig rho rho' HE)).
  pose proof (ity_sig rho A B k _ FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho' A B k _ FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  assert (Psig : iso (kAt (sigFam k (ers rho A) B0 FA wB FB redB isoB gSig))
                     (kAt (sigFam k (ers rho' A) B0' FA' wB' FB' redB' isoB' gSig')))
    by exact (FunTy_of_FunTm G (sig_ A B) IHsig rho rho' HE k _ _ _ _ Dsig Dsig'
                (eqty_at_lvl k _ _ gSig gSig' Hty)).
  (* the first component *)
  assert (QA : iso (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA'
                (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  assert (Hrt : Rel (ers rho' A) (ers rho t) (ers rho' t))
    by (apply (Rel_tyeq (ers rho A) (ers rho' A));
        [ exact (LA rho rho' HE) | exact (Lt rho rho' HE) ]).
  assert (A3 : kRel FA FA' (ers rho t) xt (ers rho' t) xt')
    by exact (IHt rho rho' HE k _ FA _ xt Dt _ FA' _ xt' Dt' QA Hrt).
  (* the second component, in the extended environments *)
  pose proof (EnvRelOf_ext G rho rho' A k FA FA' _ xt _ xt' HE A3) as HEx.
  assert (EB : wB (ers rho t) xt = ers (ext rho FA (ers rho t) xt) B)
    by exact (ers_of_ITy _ _ _ _ _ (DB _ xt)).
  assert (EB' : wB' (ers rho' t) xt' = ers (ext rho' FA' (ers rho' t) xt') B)
    by exact (ers_of_ITy _ _ _ _ _ (DB' _ xt')).
  assert (Htb : tyeq (wB (ers rho t) xt) (wB' (ers rho' t) xt'))
    by (rewrite EB, EB'; exact (LB _ _ HEx)).
  assert (QB : iso (kAt (FB (ers rho t) xt)) (kAt (FB' (ers rho' t) xt')))
    by exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx k _ (FB _ xt) _ (FB' _ xt')
                (DB _ xt) (DB' _ xt')
                (eqty_at_lvl k _ _ (uf_ty (FB _ xt)) (uf_ty (FB' _ xt')) Htb)).
  assert (Hra : Rel (wB' (ers rho' t) xt') (ers rho a) (ers rho' a)).
  { apply (Rel_tyeq (wB (ers rho t) xt) (wB' (ers rho' t) xt')); [exact Htb |].
    rewrite EB, <- (ers_sub1 rho B t FA xt); exact (La rho rho' HE). }
  assert (B3 : kRel (FB (ers rho t) xt) (FB' (ers rho' t) xt')
                 (ers rho a) xa (ers rho' a) xa')
    by exact (IHa rho rho' HE k _ (FB _ xt) _ xa Da _ (FB' _ xt') _ xa' Da' QB Hra).
  (* the layer-1 facts about the reconstructed pair *)
  assert (Hrp : Rel (esig (ers rho' A) B0')
                  (epair (ers rho t) (ers rho a)) (epair (ers rho' t) (ers rho' a))).
  { apply (Rel_tyeq (ers rho (sig_ A B)) (esig (ers rho' A) B0'));
      [ rewrite <- Ep; exact Hty | exact (Lp rho rho' HE) ]. }
  assert (gT' : Good_ty (esig (ers rho' A) B0')) by (exists k; exact gSig').
  assert (Hsame : Rel (esig (ers rho' A) B0')
                    (epair (ers rho t) (ers rho a)) (epair (ers rho t) (ers rho a)))
    by (eapply Rel_trans; [exact Hrp | apply Rel_sym; exact Hrp]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hsame) as gr.
  assert (g2 : Good (esig (ers rho' A) B0')
                 (epair (efst (epair (ers rho t) (ers rho a)))
                        (esnd (epair (ers rho t) (ers rho a)))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hrp) as Hc.
  (* and the comparison itself *)
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  exists Psig.
  eapply kEqAt_trans;
    [ apply kEqAt_sym;
      exact (sigPair_surj k _ B0' FA' wB' FB' redB' isoB' gSig' _
               (ctoK _ _ Psig _ (sigPair k _ B0 FA wB FB redB isoB gSig _ _ xt xa g))
               g2 gr) |].
  apply (sigPair_eq k _ B0' FA' wB' FB' redB' isoB' gSig'); [exact Hc | |].
  - (* the first components *)
    apply (proj2 (kRel_same FA' _ _ _ _)).
    eapply kRel_trans;
      [ apply kRel_sym;
        apply (sigFst_to k _ B0 FA wB FB redB isoB gSig
                 _ B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same FA _ _ _ _));
        apply (sigFst_pair k _ B0 FA wB FB redB isoB gSig)
      | exact A3 ].
  - (* the second components *)
    eapply kRel_trans;
      [ apply kRel_sym;
        apply (sigSnd_to k _ B0 FA wB FB redB isoB gSig
                 _ B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
    eapply kRel_trans;
      [ apply (sigSnd_pair k _ B0 FA wB FB redB isoB gSig) | exact B3 ].
Qed.

(* ------------------------------------------------------------------ *)
(* EXTENSIONALITY AT PI.                                               *)
(*                                                                    *)
(* piApp_eq (Interp/PiEl.v) is the elimination: related functions send   *)
(* related arguments to related values.  This is its converse, which is  *)
(* what a lambda needs -- i_lam pins its value only by its behaviour, so  *)
(* nothing but pointwise agreement is available to compare two readings.  *)
(*                                                                    *)
(* It belongs next to piApp_eq, but Interp/PiEl.v sits upstream of        *)
(* Interp/SigEl.v, which takes ~500s to compile, so it lives here.        *)
(*                                                                    *)
(* The proof is piApp_eq's read backwards: the goal's two conjuncts are    *)
(* the pointwise hypothesis at the argument after its round trip through   *)
(* the domain code (pApp_het), and the round trip itself is absorbed by     *)
(* the function's own self-equality (which every element of a decoding      *)
(* carries).                                                              *)
(* ------------------------------------------------------------------ *)

Lemma piEq_of (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (epi A0 B0) (epi A0 B0))
  u (x : kElAt (piFam k A0 B0 FA SB FB redB isoB gPi) u)
  u' (x' : kElAt (piFam k A0 B0 FA SB FB redB isoB gPi) u') :
  Rel (epi A0 B0) u u' ->
  (forall v (y : kElAt FA v) v' (y' : kElAt FA v'), kEqAt FA v y v' y' ->
     kRel (FB v y) (FB v' y')
          (eapp u v) (piApp k A0 B0 FA SB FB redB isoB gPi u x v y)
          (eapp u' v') (piApp k A0 B0 FA SB FB redB isoB gPi u' x' v' y')) ->
  kEqAt (piFam k A0 B0 FA SB FB redB isoB gPi) u x u' x'.
Proof.
  revert x x'; unfold piApp, kElAt, kEqAt, kAt, uf_at, kAcc.
  generalize (uf_acc (piFam k A0 B0 FA SB FB redB isoB gPi)) as h.
  intros h; destruct h as [fT]; intros x x' Hrel H.
  set (pf := evalAg_refl (epi A0 B0)).
  split; [| exact Hrel].
  intros v1 z1 v1' z1' r r'.
  (* the two arguments, read as elements of the domain FAMILY *)
  set (y1 := pxc k A0 B0 FA (epi A0 B0) fT pf v1 z1).
  set (y1' := pxc k A0 B0 FA (epi A0 B0) fT pf v1' z1').
  assert (Hy : kEqAt FA v1 y1 v1' y1') by (apply famTo_eq; exact r).
  (* each side: the raw code-level application is the family-level one, up to
     the argument's round trip, which the function's self-equality absorbs *)
  assert (Hside : forall w1 (t1 : kElS (placeDom k (epi A0 B0) A0 B0 fT
                                         (pEv A0 B0 (epi A0 B0) fT pf)
                                         (pcA k A0 B0 FA (epi A0 B0) fT pf)) w1)
                    uu (xx : kElC (pcode k A0 B0 FA SB FB redB isoB
                                     (epi A0 B0) fT pf) uu),
             hetC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf w1 t1)
                  (kAt (FB w1 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)))
                  (eapp uu w1) (Datatypes.fst (proj1_sig xx) w1 t1)
                  (eapp uu w1) (pApp k A0 B0 FA SB FB redB isoB
                                  (epi A0 B0) fT pf uu xx w1
                                  (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1))).
  { intros w1 t1 uu xx.
    set (zz := famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf) (evalAg_refl A0) w1
                 (pxc k A0 B0 FA (epi A0 B0) fT pf w1 t1)).
    assert (q : kEqC (pcA k A0 B0 FA (epi A0 B0) fT pf) w1 zz w1 t1)
      by (apply (famFrom_famTo FA A0 (pAcc A0 B0 (epi A0 B0) fT pf)
                   (evalAg_refl A0))).
    assert (q' : kEqC (pcA k A0 B0 FA (epi A0 B0) fT pf) w1 t1 w1 zz)
      by (apply kEqC_sym; exact q).
    eapply hetC_trans; [| apply (pApp_het k A0 B0 FA SB FB redB isoB)].
    exists (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf w1 zz w1 t1 q).
    apply kEqC_sym.
    exact (proj1 (proj1 (proj2_sig xx) w1 zz w1 t1 q q')). }
  assert (Hmain : hetC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1 z1)
                       (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf v1' z1')
                       (eapp u v1) (Datatypes.fst (proj1_sig x) v1 z1)
                       (eapp u' v1') (Datatypes.fst (proj1_sig x') v1' z1')).
  { eapply hetC_trans; [apply Hside |].
    eapply hetC_trans; [exact (H v1 y1 v1' y1' Hy) |].
    apply hetC_sym; apply Hside. }
  split.
  - apply kEqC_sym.
    apply (hetC_at _ _ (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf
                          v1 z1 v1' z1' r)).
    apply hetC_sym; exact Hmain.
  - apply kEqC_sym.
    apply (hetC_at _ _ (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf
                          v1' z1' v1 z1 r')).
    exact Hmain.
Qed.

(* The lambda.  Its value is pinned only by its behaviour, so the two readings
   are compared pointwise (piEq_of), and at each argument the chain is: move
   the argument back to the first reading's domain (moveTo), read both
   behaviours, and use the body's induction hypothesis in the extended
   environments.  piApp_to carries the two transports across the application
   and piApp_eq re-seats the argument. *)
Lemma funtm_lam (G : ctx) (A B t : tm)
  (LA : LTy G A) (IHA : FunTm G A)
  (LB : LTy (A :: G) B) (IHB : FunTm (A :: G) B)
  (Lpi : LTy G (pi A B)) (IHpi : FunTm G (pi A B))
  (Lt : LTm (A :: G) t B) (IHt : FunTm (A :: G) t) : FunTm G (lam A B t).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape LamVal] in E, E'.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi [wv [xv [wt [xt
    [[[[[Ep DA] DB] Dt] Hb] Hv]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [wv' [xv' [wt' [xt'
    [[[[[Ep' DA'] DB'] Dt'] Hb'] Hv']]]]]]]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho' A) by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  (* the two Pi-families, through the pin *)
  assert (Hty : tyeq (epi (ers rho A) B0) (epi (ers rho' A) B0'))
    by (rewrite Ep, Ep'; exact (Lpi rho rho' HE)).
  pose proof (ity_pi rho A B k _ FA B0 wB FB redB isoB gPi Ep DA DB) as Dpi.
  pose proof (ity_pi rho' A B k _ FA' B0' wB' FB' redB' isoB' gPi' Ep' DA' DB')
    as Dpi'.
  assert (Ppi : iso (kAt (piFam k (ers rho A) B0 FA wB FB redB isoB gPi))
                    (kAt (piFam k (ers rho' A) B0' FA' wB' FB' redB' isoB' gPi')))
    by exact (FunTy_of_FunTm G (pi A B) IHpi rho rho' HE k _ _ _ _ Dpi Dpi'
                (eqty_at_lvl k _ _ gPi gPi' Hty)).
  assert (QA : iso (kAt FA) (kAt FA'))
    by exact (FunTy_of_FunTm G A IHA rho rho' HE k _ FA _ FA' DA DA'
                (eqty_at_lvl k _ _ (uf_ty FA) (uf_ty FA') (LA rho rho' HE))).
  (* the two values' realisers are layer-1 related: each is related to its
     reading's own realiser by the value equation, and those two by Hrel *)
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hrv : Rel (epi (ers rho' A) B0') wv wv').
  { eapply Rel_trans;
      [ apply Rel_sym;
        exact (Rel_tyeq _ _ _ _ Hty
                 (kRel_rel _ _ _ _ _ _ (proj1 (kRel_same _ _ _ _ _) HQ))) |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy' (epi (ers rho' A) B0') w w'
                 (iso_ty F' (piFam k (ers rho' A) B0' FA' wB' FB' redB' isoB' gPi')
                    Q') Hrel)
      | exact (kRel_rel _ _ _ _ _ _ (proj1 (kRel_same _ _ _ _ _) HQ')) ]. }
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  exists Ppi.
  apply (piEq_of k _ B0' FA' wB' FB' redB' isoB' gPi'); [exact Hrv |].
  intros v y v' y' Hyy.
  (* the argument, pulled back to the first reading's domain *)
  set (y0 := moveTo FA' FA (iso_sym _ _ QA) v y v (reds_refl v)).
  assert (Hy0 : kRel FA FA' v y0 v y)
    by (apply kRel_sym; apply (moveTo_rel FA' FA (iso_sym _ _ QA) v y v (reds_refl v))).
  assert (Hy0' : kRel FA FA' v y0 v' y').
  { eapply kRel_trans; [exact Hy0 |].
    apply (proj1 (kRel_same FA' _ _ _ _)); exact Hyy. }
  (* the body, in the two extended environments *)
  pose proof (EnvRelOf_ext G rho rho' A k FA FA' v y0 v' y' HE Hy0') as HEx.
  assert (EB : wB v y0 = ers (ext rho FA v y0) B)
    by exact (ers_of_ITy _ _ _ _ _ (DB v y0)).
  assert (EB' : wB' v' y' = ers (ext rho' FA' v' y') B)
    by exact (ers_of_ITy _ _ _ _ _ (DB' v' y')).
  assert (Htb : tyeq (wB v y0) (wB' v' y'))
    by (rewrite EB, EB'; exact (LB _ _ HEx)).
  assert (QB : iso (kAt (FB v y0)) (kAt (FB' v' y')))
    by exact (FunTy_of_FunTm (A :: G) B IHB _ _ HEx k _ (FB v y0) _ (FB' v' y')
                (DB v y0) (DB' v' y')
                (eqty_at_lvl k _ _ (uf_ty (FB v y0)) (uf_ty (FB' v' y')) Htb)).
  assert (EBt : wt v y0 = ers (ext rho FA v y0) t)
    by exact (ers_of_ITm _ _ _ _ _ _ _ (Dt v y0)).
  assert (EBt' : wt' v' y' = ers (ext rho' FA' v' y') t)
    by exact (ers_of_ITm _ _ _ _ _ _ _ (Dt' v' y')).
  assert (Hrb : Rel (wB' v' y') (wt v y0) (wt' v' y')).
  { rewrite EB', EBt, EBt'.
    apply (Rel_tyeq (ers (ext rho FA v y0) B) (ers (ext rho' FA' v' y') B));
      [ exact (LB _ _ HEx) | exact (Lt _ _ HEx) ]. }
  pose proof (IHt _ _ HEx k _ (FB v y0) _ (xt v y0) (Dt v y0)
                _ (FB' v' y') _ (xt' v' y') (Dt' v' y') QB Hrb) as Hbody.
  (* and the five legs *)
  eapply kRel_trans;
    [ apply kRel_sym;
      apply (piApp_eq k _ B0' FA' wB' FB' redB' isoB' gPi' wv
               (ctoK _ _ Ppi wv xv) wv (ctoK _ _ Ppi wv xv) v
               (ctoK _ _ QA v y0) v y);
      [ apply (proj2 (kRel_same _ _ _ _ _)); apply kRel_refl
      | exact (kRel_at _ _ QA v y0 v y Hy0) ] |].
  eapply kRel_trans;
    [ apply kRel_sym;
      apply (piApp_to k _ B0 FA wB FB redB isoB gPi
               _ B0' FA' wB' FB' redB' isoB' gPi' Ppi QA wv xv
               (proj2 (kRel_same _ _ _ _ _) (kRel_refl _ wv xv)) v y0) |].
  eapply kRel_trans;
    [ apply (proj1 (kRel_same (FB v y0) _ _ _ _)); exact (Hb v y0) |].
  eapply kRel_trans; [ exact Hbody |].
  apply (proj1 (kRel_same (FB' v' y') _ _ _ _)).
  apply kEqAt_sym; exact (Hb' v' y').
Qed.

(* ------------------------------------------------------------------ *)
(* natrec.  Three small pieces first: an extension lemma that takes the *)
(* realiser equations rather than demanding them up front, the successor *)
(* congruence for semantic naturals, and semrec_rel re-stated in terms of *)
(* ELEMENTS of the nat-family rather than of an index and a witness --     *)
(* destructing the element is what lets the two indices be identified.     *)
(* ------------------------------------------------------------------ *)

Lemma EnvRelOf_ext' G rho rho' (A : tm) k S S'
  (FA : kUFam k S) (FA' : kUFam k S') u x u' x' :
  EnvRelOf G rho rho' -> S = ers rho A -> S' = ers rho' A ->
  kRel FA FA' u x u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros HE E E' Hr; subst S S'; apply EnvRelOf_ext; [exact HE | exact Hr].
Qed.

Lemma natSucc_eq {k m m'} (x : kElAt (natFam k) m) (x' : kElAt (natFam k) m') :
  kEqAt (natFam k) m x m' x' ->
  kEqAt (natFam k) (esucc m) (natSucc x) (esucc m') (natSucc x').
Proof.
  intros H; destruct (proj1 (natEq_iff x x') H) as [Ej _].
  apply natEq_iff; split; [exact (f_equal S Ej) |].
  assert (e2 : NatAt (S (natIdx x')) (esucc m))
    by (rewrite <- Ej; exact (NatAt_succ _ _ (natSpec x))).
  apply Rel_nat_intro; [apply gt_nat | apply ev_nat |].
  exact (NatAt_NatPer _ _ _ e2 (NatAt_succ _ _ (natSpec x'))).
Qed.

Lemma semrec_rel_el (k : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam 0) m), kUFam k (SC m))
  (isoC : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
            iso (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  (SC' : etm -> etm) (FC' : forall m (x : kElAt (natFam 0) m), kUFam k (SC' m))
  (isoC' : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
             iso (kAt (FC' m x)) (kAt (FC' m' x')))
  (zr' sr' : etm) (xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) zr')
  (step' : forall m x w (y : kElAt (FC' m x) w),
             kElAt (FC' (esucc m) (natSucc x)) (eapp (eapp sr' m) w))
  (Hz : kRel (FC ezero (natE 0 NatAt_zero)) (FC' ezero (natE 0 NatAt_zero))
          zr xz zr' xz')
  (Hstep : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
             forall w y w' y', kRel (FC m x) (FC' m' x') w y w' y' ->
             kRel (FC (esucc m) (natSucc x)) (FC' (esucc m') (natSucc x'))
                  (eapp (eapp sr m) w) (step m x w y)
                  (eapp (eapp sr' m') w') (step' m' x' w' y'))
  m (x : kElAt (natFam 0) m) m' (x' : kElAt (natFam 0) m')
  (Hx : kEqAt (natFam 0) m x m' x') :
  kRel (FC m (natE (natIdx x) (natSpec x))) (FC' m' (natE (natIdx x') (natSpec x')))
       (enatrec zr sr m) (semrec k 0 SC FC isoC zr sr xz step (natIdx x) m (natSpec x))
       (enatrec zr' sr' m')
       (semrec k 0 SC' FC' isoC' zr' sr' xz' step' (natIdx x') m' (natSpec x')).
Proof.
  destruct (proj1 (natEq_iff x x') Hx) as [Ej _]; clear Hx.
  revert Ej; destruct x as [[[j e] gd] pp]; destruct x' as [[[j' e'] gd'] pp'];
    cbn [natIdx natSpec proj1_sig Datatypes.fst projT1 projT2];
    intros Ej; subst j'.
  exact (semrec_rel k 0 SC FC isoC zr sr xz step SC' FC' isoC' zr' sr' xz' step'
           Hz Hstep j m e m' e').
Qed.

(* natrec itself.  semrec_rel does the recursion; what has to be supplied is
   the two base values' relatedness, the step's (which is the body's induction
   hypothesis in the DOUBLY extended environment, the step term carrying its
   own two binders), and the fact that the two scrutinees have the same index.
   The motive's families are related at every related pair of naturals, which
   is IHC in the singly extended environment. *)
Lemma funtm_natrec (G : ctx) (C z s n : tm)
  (LC : LTy (nat_ :: G) C) (IHC : FunTm (nat_ :: G) C)
  (Lz : LTm G z (C [zero..])) (IHz : FunTm G z)
  (Ls : LTm (C :: nat_ :: G) s (nrec_succ C)) (IHs : FunTm (C :: nat_ :: G) s)
  (Ln : LTm G n nat_) (IHn : FunTm G n) : FunTm G (natrec C z s n).
Proof.
  apply funtm_shape.
  intros rho rho' k Sy F w x Sy' F' w' x' HE E E' Piso Hrel.
  cbn [TmShape RecVal] in E, E'.
  destruct E as [SC [FC [isoC [S0 [wz [xz [ws [xs [redS [wn [xn [[[[[ES DC] Dz] Ds] Dn] Hv]]]]]]]]]]]].
  destruct E' as [SC' [FC' [isoC' [S0' [wz' [xz' [ws' [xs' [redS' [wn' [xn' [[[[[ES' DC'] Dz'] Ds'] Dn'] Hv']]]]]]]]]]]].
  (* the motive: related environments and related families at related naturals *)
  assert (HEm : forall m (xm : kElAt (natFam 0) m) m' (xm' : kElAt (natFam 0) m'),
             kEqAt (natFam 0) m xm m' xm' ->
             EnvRelOf (nat_ :: G) (ext rho (natFam 0) m xm)
                                  (ext rho' (natFam 0) m' xm')).
  { intros m xm m' xm' Hm.
    apply (EnvRelOf_ext' G rho rho' nat_ 0 enat enat);
      [ exact HE | reflexivity | reflexivity
      | apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm ]. }
  assert (HCm : forall m (xm : kElAt (natFam 0) m) m' (xm' : kElAt (natFam 0) m'),
             kEqAt (natFam 0) m xm m' xm' ->
             iso (kAt (FC m xm)) (kAt (FC' m' xm'))).
  { intros m xm m' xm' Hm.
    assert (ECm : SC m = ers (ext rho (natFam 0) m xm) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC m xm)).
    assert (ECm' : SC' m' = ers (ext rho' (natFam 0) m' xm') C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' m' xm')).
    assert (Htc : tyeq (SC m) (SC' m'))
      by (rewrite ECm, ECm'; exact (LC _ _ (HEm m xm m' xm' Hm))).
    exact (FunTy_of_FunTm (nat_ :: G) C IHC _ _ (HEm m xm m' xm' Hm) k
             _ (FC m xm) _ (FC' m' xm') (DC m xm) (DC' m' xm')
             (eqty_at_lvl k _ _ (uf_ty (FC m xm)) (uf_ty (FC' m' xm')) Htc)). }
  (* the scrutinee *)
  assert (Ewn : wn = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn).
  assert (Ewn' : wn' = ers rho' n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn').
  assert (Hrn : Rel enat wn wn') by (rewrite Ewn, Ewn'; exact (Ln rho rho' HE)).
  assert (Hxn : kEqAt (natFam 0) wn xn wn' xn')
    by (apply (proj2 (kRel_same (natFam 0) _ _ _ _));
        exact (IHn rho rho' HE 0 enat (natFam 0) wn xn Dn
                 enat (natFam 0) wn' xn' Dn' (iso_self (natFam 0)) Hrn)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (semrec_rel_el k SC FC isoC wz S0 xz _ SC' FC' isoC' wz' S0' xz' _);
    [ | | exact Hxn ].
  - (* the base value *)
    assert (Hz0 : kEqAt (natFam 0) ezero (natE 0 NatAt_zero)
                    ezero (natE 0 NatAt_zero))
      by apply (natE_eq 0 NatAt_zero NatAt_zero).
    assert (EC0 : SC ezero = ers (ext rho (natFam 0) ezero (natE 0 NatAt_zero)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC ezero (natE 0 NatAt_zero))).
    assert (EC0' : SC' ezero
                   = ers (ext rho' (natFam 0) ezero (natE 0 NatAt_zero)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' ezero (natE 0 NatAt_zero))).
    assert (Htc0 : tyeq (SC ezero) (SC' ezero))
      by (rewrite EC0, EC0'; exact (LC _ _ (HEm _ _ _ _ Hz0))).
    assert (Ewz : wz = ers rho z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz).
    assert (Ewz' : wz' = ers rho' z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz').
    assert (Esub : ers rho (C [zero..]) = SC ezero).
    { rewrite EC0; exact (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero)). }
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
    assert (ECm : SC m = ers (ext rho (natFam 0) m xm) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC m xm)).
    assert (ECm' : SC' m' = ers (ext rho' (natFam 0) m' xm') C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' m' xm')).
    pose proof (EnvRelOf_ext' (nat_ :: G) (ext rho (natFam 0) m xm)
                  (ext rho' (natFam 0) m' xm') C k _ _ (FC m xm) (FC' m' xm')
                  w0 y0 w0' y0' (HEm m xm m' xm' Hm) ECm ECm' Hy) as HEs.
    assert (Hsucc : kEqAt (natFam 0) (esucc m) (natSucc xm) (esucc m') (natSucc xm'))
      by (apply natSucc_eq; exact Hm).
    assert (ECs : SC (esucc m)
                  = ers (ext rho (natFam 0) (esucc m) (natSucc xm)) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC (esucc m) (natSucc xm))).
    assert (ECs' : SC' (esucc m')
                   = ers (ext rho' (natFam 0) (esucc m') (natSucc xm')) C)
      by exact (ers_of_ITy _ _ _ _ _ (DC' (esucc m') (natSucc xm'))).
    assert (Htcs : tyeq (SC (esucc m)) (SC' (esucc m')))
      by (rewrite ECs, ECs'; exact (LC _ _ (HEm _ _ _ _ Hsucc))).
    assert (Ews : ws m xm w0 y0
                  = ers (ext (ext rho (natFam 0) m xm) (FC m xm) w0 y0) s)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds m xm w0 y0)).
    assert (Ews' : ws' m' xm' w0' y0'
                   = ers (ext (ext rho' (natFam 0) m' xm') (FC' m' xm') w0' y0') s)
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds' m' xm' w0' y0')).
    assert (Esub2 : ers (ext (ext rho (natFam 0) m xm) (FC m xm) w0 y0) (nrec_succ C)
                    = SC (esucc m)).
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
(* FUNCTIONALITY OF THE INTERPRETATION OF TERMS.                       *)
(*                                                                    *)
(* The cases above are stated per term former, with the layer-1 side     *)
(* conditions as hypotheses; here they are assembled by induction on the *)
(* typing derivation, which is what discharges those hypotheses --       *)
(* LTy_of_ty and LTm_of_ty are the layer-1 fundamental theorem, and every *)
(* rule carries derivations for exactly the types the corresponding case   *)
(* needs.  That is what the full Church annotations bought.               *)
(*                                                                    *)
(* t_conv needs nothing: FunTm quantifies over ALL readings of the        *)
(* subject, and i_conv produces one of them.                             *)
(* ------------------------------------------------------------------ *)

Theorem funtm (G : ctx) (t A : tm) (d : ty G t A) : FunTm G t.
Proof.
  revert G t A d.
  apply (ty_mind (fun _ => True) (fun G t A => FunTm G t) (fun _ _ _ _ => True));
    try (intros; exact I).
  - (* t_var *) intros G i A W IHW Hl; apply funtm_var.
  - (* t_conv *) intros G t A B k dt IHt dA IHA dB IHB c IHc; exact IHt.
  - (* t_univ *) intros G k W IHW; apply funtm_univ.
  - (* t_up *) intros G A k dA IHA.
    apply funtm_up; [exact (LTy_of_ty G A k dA) | exact IHA].
  - (* t_up_tm *) intros G A t k dA IHA dt IHt.
    apply funtm_uptm; [exact (LTy_of_ty G A k dA) | exact IHA | exact IHt].
  - (* t_pi *) intros G A B k dA IHA dB IHB.
    apply (funtm_pi G A B);
      [ exact (LTy_of_ty G (pi A B) k (t_pi G A B k dA dB))
      | exact (LTy_of_ty G A k dA) | exact (LTy_of_ty (A :: G) B k dB)
      | exact IHA | exact IHB ].
  - (* t_lam *) intros G A B t k dA IHA dB IHB dt IHt.
    pose proof (LTy_of_ty G A k dA) as LA.
    pose proof (LTy_of_ty (A :: G) B k dB) as LB.
    pose proof (LTy_of_ty G (pi A B) k (t_pi G A B k dA dB)) as Lpi.
    apply (funtm_lam G A B t);
      [ exact LA | exact IHA | exact LB | exact IHB | exact Lpi
      | exact (funtm_pi G A B Lpi LA LB IHA IHB)
      | exact (LTm_of_ty (A :: G) t B dt) | exact IHt ].
  - (* t_app *) intros G A B f u k dA IHA dB IHB df IHf du IHu.
    pose proof (LTy_of_ty G A k dA) as LA.
    pose proof (LTy_of_ty (A :: G) B k dB) as LB.
    pose proof (LTy_of_ty G (pi A B) k (t_pi G A B k dA dB)) as Lpi.
    apply (funtm_app G A B f u);
      [ exact LA | exact IHA | exact Lpi
      | exact (funtm_pi G A B Lpi LA LB IHA IHB)
      | exact (LTm_of_ty G f (pi A B) df) | exact IHf
      | exact (LTm_of_ty G u A du) | exact IHu ].
  - (* t_sig *) intros G A B k dA IHA dB IHB.
    apply (funtm_sig G A B);
      [ exact (LTy_of_ty G (sig_ A B) k (t_sig G A B k dA dB))
      | exact (LTy_of_ty G A k dA) | exact (LTy_of_ty (A :: G) B k dB)
      | exact IHA | exact IHB ].
  - (* t_pair *) intros G A B t u k dA IHA dB IHB dt IHt du IHu.
    pose proof (LTy_of_ty G A k dA) as LA.
    pose proof (LTy_of_ty (A :: G) B k dB) as LB.
    pose proof (LTy_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as Lsig.
    apply (funtm_pair G A B t u);
      [ exact LA | exact IHA | exact LB | exact IHB | exact Lsig
      | exact (funtm_sig G A B Lsig LA LB IHA IHB)
      | exact (LTm_of_ty G (pair A B t u) (sig_ A B)
                 (t_pair G A B t u k dA dB dt du))
      | exact (LTm_of_ty G t A dt) | exact IHt
      | exact (LTm_of_ty G u (B [t..]) du) | exact IHu ].
  - (* t_fst *) intros G A B p k dA IHA dB IHB dp IHp.
    pose proof (LTy_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as Lsig.
    apply (funtm_fst G A B p);
      [ exact Lsig
      | exact (funtm_sig G A B Lsig (LTy_of_ty G A k dA)
                 (LTy_of_ty (A :: G) B k dB) IHA IHB)
      | exact (LTm_of_ty G p (sig_ A B) dp) | exact IHp ].
  - (* t_snd *) intros G A B p k dA IHA dB IHB dp IHp.
    pose proof (LTy_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as Lsig.
    apply (funtm_snd G A B p);
      [ exact Lsig
      | exact (funtm_sig G A B Lsig (LTy_of_ty G A k dA)
                 (LTy_of_ty (A :: G) B k dB) IHA IHB)
      | exact (LTm_of_ty G p (sig_ A B) dp) | exact IHp ].
  - (* t_nat *) intros G W IHW; apply funtm_nat.
  - (* t_zero *) intros G W IHW; apply funtm_zero.
  - (* t_succ *) intros G n dn IHn; apply funtm_succ; exact IHn.
  - (* t_natrec *) intros G C z s n k dC IHC dz IHz ds IHs dn IHn.
    apply (funtm_natrec G C z s n);
      [ exact (LTy_of_ty (nat_ :: G) C k dC) | exact IHC
      | exact (LTm_of_ty G z (C [zero..]) dz) | exact IHz
      | exact (LTm_of_ty (C :: nat_ :: G) s (nrec_succ C) ds) | exact IHs
      | exact (LTm_of_ty G n nat_ dn) | exact IHn ].
  - (* t_prop *) intros G W IHW; apply funtm_prop.
  - (* t_prf *) intros G p dp IHp.
    apply funtm_prf;
      [ exact (LTy_of_ty G (prf p) 0 (t_prf G p dp)) | exact IHp ].
  - (* t_all *) intros G A p k dA IHA dp IHp.
    apply (funtm_all G A p);
      [ exact (LTy_of_ty G A k dA) | exact (LTm_of_ty (A :: G) p prop dp)
      | exact IHA | exact IHp ].
  - (* t_all_intro *) intros G A p t k dA IHA dp IHp dt IHt; apply funtm_plam.
  - (* t_all_elim *) intros G A p f u k dA IHA dp IHp df IHf du IHu;
      apply funtm_papp.
  - (* t_false *) intros G W IHW; apply funtm_false.
  - (* t_absurd *) intros G T e k dT IHT de IHe; apply funtm_absurd.
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
(* the typing motive is IEq G t t A and the conversion motive IEq G t u A. *)
(*                                                                    *)
(* Everything below is Type-valued: the Pi and Sigma cases have to        *)
(* produce a FUNCTION assigning a codomain family to every argument, so    *)
(* a Prop-valued (`inhabited`) formulation would need choice.  That is     *)
(* also why the induction is assembled by applying the two Type-sorted     *)
(* schemes to the same case lemmas rather than through a Combined Scheme.  *)
(* ================================================================== *)

(* An environment that carries the interpretation of every context type.
   EnvOf records only the realisers; the variable case needs the families to
   be interpretations of the context types, because that is what makes the
   entry's family isomorphic to the one the statement is handed. *)
Fixpoint EnvITy (G : ctx) (rho : Env) : Type :=
  match G, rho with
  | nil, nil => unit
  | A :: G0, en :: rho0 =>
      (EnvITy G0 rho0 *
       { F0 : kUFam (en_k en) (ers rho0 A) &
         (ITy rho0 A (en_k en) (ers rho0 A) F0 *
          iso (kAt (en_F en)) (kAt F0))%type })%type
  | _, _ => Empty_set
  end.

Lemma EnvOf_of_EnvITy : forall G rho, EnvITy G rho -> EnvOf G rho.
Proof.
  induction G as [| A G0 IH]; intros [| en rho0] H; cbn in H |- *;
    try (exact I); try (solve [destruct H]).
  destruct H as [H0 [F0 [D0 P0]]]; split;
    [exact (IH rho0 H0) | exact (iso_ty (en_F en) F0 P0)].
Qed.

Definition EnvITy_ext G rho (A : tm) k (FA : kUFam k (ers rho A))
  (DA : ITy rho A k (ers rho A) FA) u x (H : EnvITy G rho)
  : EnvITy (A :: G) (ext rho FA u x) :=
  (H, existT _ FA (DA, iso_self FA)).

(* the same, for a family that only happens to be ISOMORPHIC to an
   interpretation of the context type: what a conversion of that type gives *)
Definition EnvITy_ext_iso G rho (A : tm) k S (FS : kUFam k S)
  (F0 : kUFam k (ers rho A)) (D0 : ITy rho A k (ers rho A) F0)
  (P : iso (kAt FS) (kAt F0)) u x (H : EnvITy G rho)
  : EnvITy (A :: G) (ext rho FS u x) :=
  (H, existT _ F0 (D0, P)).

Lemma EnvRelOf_selfE G rho (W : wfc G) (H : EnvITy G rho) : EnvRelOf G rho rho.
Proof.
  pose proof (EnvOf_of_EnvITy G rho H) as HO.
  split; [exact HO | split; [exact HO | split; [apply EnvRel_refl |]]].
  exact (EnvOf_SubstRel G W rho rho HO HO (EnvRel_refl rho)).
Qed.

(* Extension of a related pair of environments by families whose realisers are
   only layer-1 equal to the context type's -- the conversion-closed form. *)
Lemma EnvRelOf_ext_ty G rho rho' (A : tm) k S S'
  (FA : kUFam k S) (FA' : kUFam k S') u x u' x' :
  EnvRelOf G rho rho' -> tyeq S (ers rho A) -> tyeq S' (ers rho' A) ->
  kRel FA FA' u x u' x' ->
  EnvRelOf (A :: G) (ext rho FA u x) (ext rho' FA' u' x').
Proof.
  intros [HO [HO' [HR HS]]] Hty Hty' Hrel; split; [| split; [| split]].
  - apply (EnvOf_ext_ty G rho A k S FA u x HO Hty).
  - apply (EnvOf_ext_ty G rho' A k S' FA' u' x' HO' Hty').
  - apply EnvRel_ext; [exact HR | exact Hrel].
  - apply SubstRel_cons; [exact HS |].
    destruct Hty as [n Hn].
    eapply Rel_cast; [exact Hn |].
    apply Rel_sym; apply (kRel_rel FA' FA u' x' u x); apply kRel_sym; exact Hrel.
Qed.

(* The layer-1 side condition AT A FIXED LEVEL.  LTy loses the level to an
   existential, which is enough for a tyeq but not for the `eqty k` a Pi- or
   Sigma-family carries as its own goodness field. *)
Definition LTyK (G : ctx) (A : tm) (k : nat) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> eqty k (ers rho A) (ers rho' A).

Lemma LTyK_of_ty G A k (d : ty G A (univ k)) : LTyK G A k.
Proof. intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_U G A k d _ _ HS). Qed.

(* Two interpretations of one well-typed type in one environment are
   isomorphic.  This is functionality on the diagonal, where the layer-1 side
   condition is free (uf_ty), and it is what lets a case build its value at
   the family it constructs and then move it to the family it was handed. *)
Lemma ity_same_iso G A (HA : FunTm G A) rho (W : wfc G) (H : EnvITy G rho)
  k (F F0 : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D0 : ITy rho A k (ers rho A) F0) :
  iso (kAt F) (kAt F0).
Proof.
  exact (FunTy_of_FunTm G A HA rho rho
           (EnvRelOf_selfE G rho W H) k _ F _ F0 D D0 (uf_ty F)).
Qed.

(* The typing derivation of a type is only ever used to call funtm, whose
   conclusion is a Prop -- so it may be supplied wrapped, which is what the
   variable case needs: `lookup` is Prop-valued and cannot be eliminated into
   Type. *)
Lemma FunTm_of_inh G A : inhabited { k : nat & ty G A (univ k) } -> FunTm G A.
Proof. intros [[k d]]; exact (funtm G A (univ k) d). Qed.

Lemma FunTm_of_ty G A k (d : ty G A (univ k)) : FunTm G A.
Proof. exact (funtm G A (univ k) d). Qed.

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
    kEqAt F (ers rho t) x (ers rho u) y.

Definition ISem (G : ctx) (t u A : tm) : Type :=
  (ITot G t A * ITot G u A * IRel G t u A)%type.

Lemma kEqAt_refl {k u} (F : kUFam k u) w (x : kElAt F w) : kEqAt F w x w x.
Proof. exact (proj2 (kRel_same F w x w x) (kRel_refl F w x)). Qed.

(* Relatedness on the diagonal is functionality. *)
Lemma IRel_self G t A (d : ty G t A) (W : wfc G) : IRel G t t A.
Proof.
  intros rho Hrho k F DA x y Dx Dy.
  apply (proj2 (kRel_same F _ _ _ _)).
  refine (funtm G t A d rho rho (EnvRelOf_selfE G rho W Hrho) k _ F _ x Dx _ F _ y Dy
            (iso_self F) _).
  exact (LTm_of_ty G t A d rho rho (EnvRelOf_selfE G rho W Hrho)).
Qed.

(* Moving a value to another interpretation of the same type. *)
Lemma itot_move G (t A : tm) (HA : FunTm G A) (W : wfc G)
  rho (Hrho : EnvITy G rho) k (F F0 : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D0 : ITy rho A k (ers rho A) F0)
  x (Dx : ITm rho t k (ers rho A) F0 (ers rho t) x) :
  { y : kElAt F (ers rho t) & ITm rho t k (ers rho A) F (ers rho t) y }.
Proof.
  pose proof (ity_same_iso G A HA rho W Hrho k F0 F D0 D) as P.
  exists (ctoK (kAt F0) (kAt F) P (ers rho t) x).
  exact (i_conv rho t k (ers rho A) F0 (ers rho A) F (ers rho t) x P Dx).
Qed.

(* ---- the constants.  Each is its canonical family's code, read as an
     element of the universe, moved to whatever interpretation of that
     universe the statement was handed. ---- *)

Lemma itot_univ G (W : wfc G) m : ITot G (univ m) (univ (S m)).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (univ (S m)) k (ers rho (univ (S m))) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G (univ m) (univ (S m)) (FunTm_of_ty G (univ (S m)) (S (S m)) (t_univ G (S m) W)) W rho Hrho
            (S (S m)) F (univFam (S m)) DA
            (ity_univ rho (S m) (ers rho (univ (S m))) eq_refl) _ _).
  exact (i_ty rho (univ m) (S m) (euniv m) (univFam m)
           (ity_univ rho m (ers rho (univ m)) eq_refl)).
Qed.

Lemma itot_nat G (W : wfc G) : ITot G nat_ (univ 0).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (univ 0) k (ers rho (univ 0)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G nat_ (univ 0) (FunTm_of_ty G (univ 0) 1 (t_univ G 0 W)) W rho Hrho 1 F (univFam 0) DA
            (ity_univ rho 0 (ers rho (univ 0)) eq_refl) _ _).
  exact (i_ty rho nat_ 0 enat (natFam 0) (ity_nat rho (ers rho nat_) eq_refl)).
Qed.

Lemma itot_prop G (W : wfc G) : ITot G prop (univ 0).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (univ 0) k (ers rho (univ 0)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G prop (univ 0) (FunTm_of_ty G (univ 0) 1 (t_univ G 0 W)) W rho Hrho 1 F (univFam 0) DA
            (ity_univ rho 0 (ers rho (univ 0)) eq_refl) _ _).
  exact (i_ty rho prop 0 eprop (propFam 0) (ity_prop rho (ers rho prop) eq_refl)).
Qed.

Lemma itot_zero G (W : wfc G) : ITot G zero nat_.
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho nat_ k (ers rho nat_) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G zero nat_ (FunTm_of_ty G nat_ 0 (t_nat G W)) W rho Hrho 0 F (natFam 0) DA
            (ity_nat rho (ers rho nat_) eq_refl) _ (i_zero rho)).
Qed.

Lemma itot_succ G (W : wfc G) (n : tm) (IHn : ITot G n nat_) : ITot G (succ n) nat_.
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho nat_ k (ers rho nat_) F DA) as El;
    cbn [LvlDec] in El; subst k.
  destruct (IHn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl)) as [xn Dn].
  refine (itot_move G (succ n) nat_ (FunTm_of_ty G nat_ 0 (t_nat G W)) W rho Hrho 0 F (natFam 0) DA
            (ity_nat rho (ers rho nat_) eq_refl) _
            (i_succ rho n (ers rho n) xn Dn)).
Qed.

Lemma itot_false G (W : wfc G) : ITot G false_ prop.
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho prop k (ers rho prop) F DA) as El;
    cbn [LvlDec] in El; subst k.
  refine (itot_move G false_ prop (FunTm_of_ty G prop 0 (t_prop G W)) W rho Hrho 0 F (propFam 0) DA
            (ity_prop rho (ers rho prop) eq_refl) _ _).
  refine (i_false rho (ers rho false_) _ eq_refl).
  apply Rel_prop_intro;
    [ exact good_ty_prop | apply eval_whnf, whnf_prop
    | apply PR_false; apply ev_false ].
Qed.

(* ---- variables.  The value is the environment entry's own, and the entry's
     family is an interpretation of the context type (which is what EnvITy
     records), so it is isomorphic to whichever interpretation the statement
     was handed.  The recursion is on the INDEX: `lookup` is Prop-valued and
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
    destruct D as [FB0 [DB0 Piso]].
    exists (B ⟨↑⟩), k0.
    rewrite (ers_shift_en (Build_Entry k0 S0 F0 u0 x0) rho0 B).
    exists FB0; split; [split |].
    + apply lookup_O.
    + exact (weaken1_ITy rho0 B k0 (ers rho0 B) FB0
               (Build_Entry k0 S0 F0 u0 x0) DB0).
    + exists (ctoK (kAt F0) (kAt FB0) Piso u0 x0).
      exact (i_conv (ext rho0 F0 u0 x0) (var_tm 0) k0 S0 F0 (ers rho0 B) FB0
               u0 x0 Piso (i_var0 rho0 k0 S0 F0 u0 x0)).
  - destruct H as [H0 D]; cbn in Hlt.
    destruct (IH G0 rho0 H0 ltac:(lia)) as [A [k0 [F0 [[Hl DA] [x Dx]]]]].
    exists (A ⟨↑⟩), k0.
    rewrite (ers_shift_en en rho0 A).
    exists F0; split; [split |].
    + apply lookup_S; exact Hl.
    + exact (weaken1_ITy rho0 A k0 (ers rho0 A) F0 en DA).
    + exists x; exact (i_varS rho0 en i k0 (ers rho0 A) F0 (ers rho0 (var_tm i)) x Dx).
Qed.

Lemma itot_var G i A (W : wfc G) (Hl : lookup i G A) : ITot G (var_tm i) A.
Proof.
  intros rho Hrho k F DA.
  destruct (env_var i G rho Hrho (lookup_len i G A Hl))
    as [A' [k0 [F0 [[Hl' DA'] [x Dx]]]]].
  pose proof (lookup_fun i G A A' Hl Hl') as E; subst A'.
  (* the two readings of A agree on the level *)
  pose proof (ity_lvl rho rho eq_refl A k0 (ers rho A) F0 k (ers rho A) F DA' DA) as Ek.
  subst k0.
  exact (itot_move G (var_tm i) A (FunTm_of_inh G A (lookup_ty i G A Hl W)) W rho Hrho
           k F F0 DA DA' x Dx).
Qed.

(* At a type, totality gives an interpretation of it: a term of a universe IS
   a family (itm_univ_ty). *)
Definition ITyT (G : ctx) (A : tm) (k : nat) : Type :=
  forall rho (H : EnvITy G rho),
    { F : kUFam k (ers rho A) & ITy rho A k (ers rho A) F }.

Lemma ityT_of_ITot G A k (H : ITot G A (univ k)) : ITyT G A k.
Proof.
  intros rho Hrho.
  destruct (H rho Hrho (S k) (univFam k) (ity_univ rho k (ers rho (univ k)) eq_refl))
    as [x Dx].
  destruct (itm_univ_ty rho A k (euniv k) (univFam k) (ers rho A) x
              (iso_self (univFam k)) Dx) as [F0 [D0 _]].
  exists F0; exact D0.
Qed.

(* and a CONVERSION of types gives the isomorphism of any two of their
   interpretations. *)
Lemma iso_of_IRel G A B k (W : wfc G)
  (HA : ITot G A (univ k)) (HB : ITot G B (univ k)) (HR : IRel G A B (univ k))
  (fA : FunTm G A) (fB : FunTm G B)
  rho (Hrho : EnvITy G rho)
  (FA : kUFam k (ers rho A)) (DA : ITy rho A k (ers rho A) FA)
  (FB : kUFam k (ers rho B)) (DB : ITy rho B k (ers rho B) FB) :
  iso (kAt FA) (kAt FB).
Proof.
  destruct (HA rho Hrho (S k) (univFam k) (ity_univ rho k (ers rho (univ k)) eq_refl))
    as [x Dx].
  destruct (HB rho Hrho (S k) (univFam k) (ity_univ rho k (ers rho (univ k)) eq_refl))
    as [y Dy].
  pose proof (HR rho Hrho (S k) (univFam k)
                (ity_univ rho k (ers rho (univ k)) eq_refl) x y Dx Dy) as Heq.
  destruct (itm_univ_ty rho A k (euniv k) (univFam k) (ers rho A) x
              (iso_self (univFam k)) Dx) as [F1 [D1 H1]].
  destruct (itm_univ_ty rho B k (euniv k) (univFam k) (ers rho B) y
              (iso_self (univFam k)) Dy) as [F2 [D2 H2]].
  assert (Hfe : kEqAt (univFam k) (ers rho A) (famEl F1) (ers rho B) (famEl F2)).
  { eapply kEqAt_trans; [apply kEqAt_sym; exact H1 |].
    eapply kEqAt_trans; [| exact H2].
    apply ctoK_eq; exact Heq. }
  pose proof (uEq_iso (famEl F1) (famEl F2) Hfe) as Hi.
  rewrite !elFam_famEl in Hi.
  eapply iso_trans; [ exact (ity_same_iso G A fA rho W Hrho k FA F1 DA D1) |].
  eapply iso_trans;
    [ exact (Hi (ers rho A) (kAcc F1) (evalAg_refl _)
               (ers rho B) (kAcc F2) (evalAg_refl _)) |].
  exact (ity_same_iso G B fB rho W Hrho k F2 FB D2 DB).
Qed.

(* ---- conversion of the type ---- *)
Lemma itot_conv G t A B k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty G B (univ k))
  (IHt : ITot G t A) (IHA : ITot G A (univ k)) (IHB : ITot G B (univ k))
  (IHc : IRel G A B (univ k)) : ITot G t B.
Proof.
  intros rho Hrho k' F DB'.
  destruct (ityT_of_ITot G B k IHB rho Hrho) as [FB DB].
  pose proof (ity_lvl rho rho eq_refl B k (ers rho B) FB k' (ers rho B) F DB DB')
    as Ek; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DA].
  destruct (IHt rho Hrho k FA DA) as [x Dx].
  pose proof (iso_of_IRel G A B k W IHA IHB IHc
                (FunTm_of_ty G A k dA) (FunTm_of_ty G B k dB) rho Hrho FA DA F DB')
    as P.
  exists (ctoK (kAt FA) (kAt F) P (ers rho t) x).
  exact (i_conv rho t k (ers rho A) FA (ers rho B) F (ers rho t) x P Dx).
Qed.

(* ---- Prf ---- *)
Lemma itot_prf G p (W : wfc G) (dp : ty G p prop) (IHp : ITot G p prop) :
  ITot G (prf p) (univ 0).
Proof.
  intros rho Hrho k F DA.
  pose proof (ity_lvl_dec rho (univ 0) k (ers rho (univ 0)) F DA) as El;
    cbn [LvlDec] in El; subst k.
  destruct (IHp rho Hrho 0 (propFam 0) (ity_prop rho (ers rho prop) eq_refl)) as [xp Dp].
  refine (itot_move G (prf p) (univ 0) (FunTm_of_ty G (univ 0) 1 (t_univ G 0 W)) W
            rho Hrho 1 F (univFam 0) DA (ity_univ rho 0 (ers rho (univ 0)) eq_refl) _ _).
  exact (i_ty rho (prf p) 0 (eprf (ers rho p)) (prfF 0 xp)
           (ity_prf rho p (ers rho p) xp Dp)).
Qed.

(* ---- the type lift ---- *)
Lemma itot_up G A k (W : wfc G) (dA : ty G A (univ k)) (IHA : ITot G A (univ k)) :
  ITot G (up (univ (S k)) A) (univ (S k)).
Proof.
  intros rho Hrho k' F DA'.
  pose proof (ity_lvl_dec rho (univ (S k)) k' (ers rho (univ (S k))) F DA') as El;
    cbn [LvlDec] in El; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  refine (itot_move G (up (univ (S k)) A) (univ (S k))
            (FunTm_of_ty G (univ (S k)) (S (S k)) (t_univ G (S k) W)) W rho Hrho
            (S (S k)) F (univFam (S k)) DA'
            (ity_univ rho (S k) (ers rho (univ (S k))) eq_refl) _ _).
  exact (i_ty rho (up (univ (S k)) A) (S k) (ers rho A) (famLiftK FA)
           (ity_up rho A k (ers rho A) FA DFA)).
Qed.

(* ---- the term lift ---- *)
Lemma itot_uptm G A t k (W : wfc G) (dA : ty G A (univ k)) (dt : ty G t A)
  (IHA : ITot G A (univ k)) (IHt : ITot G t A) :
  ITot G (uptm A t) (up (univ (S k)) A).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (up (univ (S k)) A) k' (ers rho (up (univ (S k)) A)) F DU)
    as El; cbn [LvlDec] in El; subst k'.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  destruct (IHt rho Hrho k FA DFA) as [x Dx].
  refine (itot_move G (uptm A t) (up (univ (S k)) A)
            (FunTm_of_ty G (up (univ (S k)) A) (S k) (t_up G A k dA)) W rho Hrho
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

Lemma itot_absurd G T e (IHe : ITot G e (prf false_)) : ITot G (absurd T e) T.
Proof.
  intros rho Hrho k' F DT.
  pose proof (i_false rho (ers rho false_) good_false eq_refl) as Df.
  pose proof (ity_prf rho false_ efalse (propElem efalse False good_false) Df) as DP.
  destruct (IHe rho Hrho 0 (prfF 0 (propElem efalse False good_false)) DP) as [x _].
  destruct (prfVal x).
Qed.

(* ---- the impredicative forall.  The value is the proposition
     "for every element of the domain, the body holds", which is exactly what
     i_all records; the builder is shared with the forall-introduction, whose
     truth-component has to be that very proposition, not one merely
     equivalent to it. ---- *)
Lemma build_all G A p k (W : wfc G) (dA : ty G A (univ k)) (dp : ty (A :: G) p prop)
  (IHA : ITot G A (univ k)) (IHp : ITot (A :: G) p prop)
  rho (Hrho : EnvITy G rho) :
  { FA : kUFam k (ers rho A) &
  { xp : forall u (y : kElAt FA u), kElAt (propFam 0) (ers (ext rho FA u y) p) &
    (ITy rho A k (ers rho A) FA *
     (forall u y, ITm (ext rho FA u y) p 0 eprop (propFam 0)
                    (ers (ext rho FA u y) p) (xp u y)))%type } }.
Proof.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  exists FA.
  refine (existT _ (fun u y =>
            projT1 (IHp (ext rho FA u y) (EnvITy_ext G rho A k FA DFA u y Hrho)
                      0 (propFam 0)
                      (ity_prop (ext rho FA u y) (ers (ext rho FA u y) prop) eq_refl)))
            _).
  split; [exact DFA |].
  intros u y.
  exact (projT2 (IHp (ext rho FA u y) (EnvITy_ext G rho A k FA DFA u y Hrho)
                   0 (propFam 0)
                   (ity_prop (ext rho FA u y) (ers (ext rho FA u y) prop) eq_refl))).
Qed.

Lemma itot_all G A p k (W : wfc G) (dA : ty G A (univ k)) (dp : ty (A :: G) p prop)
  (IHA : ITot G A (univ k)) (IHp : ITot (A :: G) p prop) : ITot G (all A p) prop.
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho prop k' (ers rho prop) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p k W dA dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all A p)))
    by exact (LTm_of_ty G (all A p) prop (t_all G A p k dA dp) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  refine (itot_move G (all A p) prop (FunTm_of_ty G prop 0 (t_prop G W)) W rho Hrho
            0 F (propFam 0) DP (ity_prop rho (ers rho prop) eq_refl) _ _).
  exact (i_all rho A p k (ers rho A) FA (fun u y => ers (ext rho FA u y) p) xp
           (ers rho (all A p)) g eq_refl DFA Dp).
Qed.

(* ---- forall-introduction.  plam has no clause of its own: i_proof gives a
     value to ANY subject at a Prf type, provided the proposition is TRUE, and
     the truth is the body's value at every argument. ---- *)
Lemma itot_plam G A p t k (W : wfc G) (dA : ty G A (univ k)) (dp : ty (A :: G) p prop)
  (dt : ty (A :: G) t (prf p))
  (IHA : ITot G A (univ k)) (IHp : ITot (A :: G) p prop) (IHt : ITot (A :: G) t (prf p)) :
  ITot G (plam A t) (prf (all A p)).
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho (prf (all A p)) k' (ers rho (prf (all A p))) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p k W dA dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all A p)))
    by exact (LTm_of_ty G (all A p) prop (t_all G A p k dA dp) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  pose proof (i_all rho A p k (ers rho A) FA (fun u y => ers (ext rho FA u y) p) xp
                (ers rho (all A p)) g eq_refl DFA Dp) as DAll.
  (* the proposition is true: the body has a value at every argument *)
  assert (h : forall u (y : kElAt FA u), propVal (xp u y)).
  { intros u y.
    refine (prfVal (projT1 (IHt (ext rho FA u y) (EnvITy_ext G rho A k FA DFA u y Hrho)
                              0 (prfF 0 (xp u y)) _))).
    exact (ity_prf (ext rho FA u y) p (ers (ext rho FA u y) p) (xp u y) (Dp u y)). }
  assert (gp : Good (eprf (ers rho (all A p))) (ers rho (plam A t)))
    by exact (LTm_of_ty G (plam A t) (prf (all A p))
                (t_all_intro G A p t k dA dp dt) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  refine (itot_move G (plam A t) (prf (all A p))
            (FunTm_of_ty G (prf (all A p)) 0 (t_prf G (all A p) (t_all G A p k dA dp)))
            W rho Hrho 0 F
            (prfF 0 (propElem (ers rho (all A p))
                       (forall u (y : kElAt FA u), propVal (xp u y)) g))
            DP (ity_prf rho (all A p) (ers rho (all A p)) _ DAll) _ _).
  exact (i_proof rho (plam A t) (all A p) (ers rho (all A p))
           (propElem (ers rho (all A p))
              (forall u (y : kElAt FA u), propVal (xp u y)) g)
           h (ers rho (plam A t)) gp eq_refl DAll).
Qed.

(* ---- Pi and Sigma.  The two share all their data -- domain family,
     codomain family at every argument, and the codomain's coherence -- so it
     is built once; only the realiser's head and the reduction of the erased
     codomain differ. ---- *)

Lemma reds_beta_sub sigma (s : etm) u :
  reds (eapp (elam (subst_etm (up_etm_etm sigma) s)) u) (subst_etm (scons u sigma) s).
Proof.
  eapply reds_step; [apply red_beta |].
  replace (subst_etm (scons u sigma) s)
    with (subst_etm (u..) (subst_etm (up_etm_etm sigma) s)) by (asimpl; reflexivity).
  apply reds_refl.
Qed.

Lemma build_fam_data G A B k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  rho (Hrho : EnvITy G rho) :
  { FA : kUFam k (ers rho A) &
  { FB : forall u (x : kElAt FA u), kUFam k (ers (ext rho FA u x) B) &
    (ITy rho A k (ers rho A) FA *
     (forall u x, ITy (ext rho FA u x) B k (ers (ext rho FA u x) B) (FB u x)) *
     (forall u x u' x', kEqAt FA u x u' x' ->
        iso (kAt (FB u' x')) (kAt (FB u x))))%type } }.
Proof.
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA DFA].
  exists FA.
  pose (FB := fun u (x : kElAt FA u) =>
                projT1 (ityT_of_ITot (A :: G) B k IHB (ext rho FA u x)
                          (EnvITy_ext G rho A k FA DFA u x Hrho))).
  assert (DB : forall u x, ITy (ext rho FA u x) B k (ers (ext rho FA u x) B) (FB u x))
    by (intros u x;
        exact (projT2 (ityT_of_ITot (A :: G) B k IHB (ext rho FA u x)
                         (EnvITy_ext G rho A k FA DFA u x Hrho)))).
  exists FB; split; [split; [exact DFA | exact DB] |].
  intros u x u' x' Hxx.
  assert (HEx : EnvRelOf (A :: G) (ext rho FA u' x') (ext rho FA u x)).
  { apply (EnvRelOf_ext G rho rho A k FA FA u' x' u x (EnvRelOf_selfE G rho W Hrho)).
    apply (proj1 (kRel_same FA _ _ _ _)); apply kEqAt_sym; exact Hxx. }
  exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (univ k) dB)
           (ext rho FA u' x') (ext rho FA u x) HEx k _ (FB u' x') _ (FB u x)
           (DB u' x') (DB u x) (LTyK_of_ty (A :: G) B k dB _ _ HEx)).
Qed.

Lemma build_pi G A B k (W : wfc G) (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k)) : ITyT G (pi A B) k.
Proof.
  intros rho Hrho.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  refine (existT _ (piFam k (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B)))
                     FA (fun u x => ers (ext rho FA u x) B) FB
                     (fun u x => reds_beta_sub (rsub rho) (er B) u) isoB
                     (LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho
                        (EnvRelOf_selfE G rho W Hrho))) _).
  exact (ity_pi rho A B k (ers rho A) FA
           (elam (subst_etm (up_etm_etm (rsub rho)) (er B)))
           (fun u x => ers (ext rho FA u x) B) FB
           (fun u x => reds_beta_sub (rsub rho) (er B) u) isoB
           (LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho
              (EnvRelOf_selfE G rho W Hrho))
           eq_refl DFA DB).
Qed.

Lemma build_sig G A B k (W : wfc G) (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k)) : ITyT G (sig_ A B) k.
Proof.
  intros rho Hrho.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  refine (existT _ (sigFam k (ers rho A) (elam (subst_etm (up_etm_etm (rsub rho)) (er B)))
                     FA (fun u x => ers (ext rho FA u x) B) FB
                     (fun u x => reds_beta_sub (rsub rho) (er B) u) isoB
                     (LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                        (EnvRelOf_selfE G rho W Hrho))) _).
  exact (ity_sig rho A B k (ers rho A) FA
           (elam (subst_etm (up_etm_etm (rsub rho)) (er B)))
           (fun u x => ers (ext rho FA u x) B) FB
           (fun u x => reds_beta_sub (rsub rho) (er B) u) isoB
           (LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
              (EnvRelOf_selfE G rho W Hrho))
           eq_refl DFA DB).
Qed.

Lemma itot_pi G A B k (W : wfc G) (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k)) : ITot G (pi A B) (univ k).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (univ k) k' (ers rho (univ k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_pi G A B k W dA dB IHA IHB rho Hrho) as [FP DP].
  refine (itot_move G (pi A B) (univ k)
            (FunTm_of_ty G (univ k) (S k) (t_univ G k W)) W rho Hrho
            (S k) F (univFam k) DU (ity_univ rho k (ers rho (univ k)) eq_refl) _ _).
  exact (i_ty rho (pi A B) k (ers rho (pi A B)) FP DP).
Qed.

Lemma itot_sig G A B k (W : wfc G) (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k)) : ITot G (sig_ A B) (univ k).
Proof.
  intros rho Hrho k' F DU.
  pose proof (ity_lvl_dec rho (univ k) k' (ers rho (univ k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_sig G A B k W dA dB IHA IHB rho Hrho) as [FP DP].
  refine (itot_move G (sig_ A B) (univ k)
            (FunTm_of_ty G (univ k) (S k) (t_univ G k W)) W rho Hrho
            (S k) F (univFam k) DU (ity_univ rho k (ers rho (univ k)) eq_refl) _ _).
  exact (i_ty rho (sig_ A B) k (ers rho (sig_ A B)) FP DP).
Qed.

(* ---- the first projection.  Its type is the annotation A, so no
     substitution is involved: the value is sigFst of the subject's value at
     the Sigma-family built from the two type premises. ---- *)
Lemma itot_fst G A B p k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) : ITot G (fst A B p) A.
Proof.
  intros rho Hrho k' F DA'.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose proof (ity_lvl rho rho eq_refl A k (ers rho A) FA k' (ers rho A) F DFA DA')
    as Ek; subst k'.
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u (x : kElAt FA u) => reds_beta_sub (rsub rho) (er B) u).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                  (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u x => ers (ext rho FA u x) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 FA (fun u x => ers (ext rho FA u x) B) FB
                 redB isoB gSig) Dsig) as [xp Dp].
  refine (itot_move G (fst A B p) A (FunTm_of_ty G A k dA) W rho Hrho k F FA DA' DFA
            _ _).
  exact (i_fst rho A B p k (ers rho A) FA B0 (fun u x => ers (ext rho FA u x) B) FB
           redB isoB gSig (ers rho p) xp eq_refl DFA DB Dp).
Qed.

(* ================================================================== *)
(* The substitution lemma's side condition, discharged.                *)
(*                                                                    *)
(* SubUniv asks that every image of the substitution which is a term of *)
(* a universe be a FAMILY -- at the family its value names, `elFam v`.   *)
(* For an image that is a variable this is ity_of; for the substituted    *)
(* term itself ity_of applies only when it is not a type former, and       *)
(* itm_univ_ty gives a family that is merely ISOMORPHIC to the one asked    *)
(* for.  ity_conv (Interp/Def.v) closes that gap, and with it the           *)
(* condition holds for every term, so the substitution lemma is usable      *)
(* where the fundamental lemma needs it: at t_app, t_pair, t_snd,           *)
(* t_natrec and t_all_elim, whose conclusion types are substitution          *)
(* instances.                                                               *)
(* ================================================================== *)

Lemma subUniv_all rho a : SubUniv rho a.
Proof.
  intros delta i k' w' v' D.
  destruct (itm_univ_ty (delta ++ rho) (upn (length delta) (a..) i) k' (euniv k')
              (univFam k') w' v' (iso_self (univFam k')) D) as [F0 [D0 HE]].
  assert (HE2 : kEqAt (univFam k') w' v' w' (famEl F0)).
  { eapply kEqAt_trans; [apply kEqAt_sym; apply ctoK_self | exact HE]. }
  pose proof (uEq_iso v' (famEl F0) HE2) as Hi.
  rewrite elFam_famEl in Hi.
  refine (ity_conv _ _ _ _ F0 (elFam v') _ D0).
  apply iso_sym.
  exact (Hi w' (kAcc (elFam v')) (evalAg_refl _) w' (kAcc F0) (evalAg_refl _)).
Qed.

(* The forms the fundamental lemma uses. *)
Corollary isubst_ITm (rho : Env) (b : tm) k' Sy' (FA : kUFam k' Sy') (ub : etm)
  (xb : kElAt FA ub) (Hub : ub = ers rho b)
  (Db : ITm rho b k' Sy' FA ub xb)
  t k Sy (F : kUFam k Sy) w (x : kElAt F w) :
  ITm (Build_Entry k' Sy' FA ub xb :: rho) t k Sy F w x ->
  ITm rho (t [b..]) k Sy F w x.
Proof.
  exact (subst1_ITm rho b k' Sy' FA ub xb Hub Db (subUniv_all rho b) t k Sy F w x).
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

(* ---- application.  The conclusion type is a substitution instance, which is
     what the two fixes were for: ty_subst1 (Typing/Subst.v) makes it a well
     typed type, so functionality applies to it, and isubst_ITy -- whose side
     condition ity_conv discharged -- turns the codomain's interpretation in
     the extended environment into one of `B [u..]` in rho. ---- *)
Lemma itot_app G A B f u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df : ty G f (pi A B)) (du : ty G u A)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHf : ITot G f (pi A B)) (IHu : ITot G u A) :
  ITot G (app A B f u) (B [u..]).
Proof.
  intros rho Hrho k' F DBu.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gPi := LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho
                 (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_pi rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                eq_refl DFA DB) as Dpi.
  destruct (IHf rho Hrho k
              (piFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gPi) Dpi) as [xf Df].
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  (* the codomain instance interprets B [u..] in rho, at a realiser that is
     equal -- not convertible -- to ers rho (B [u..]) *)
  pose proof (isubst_ITy rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                B k (ers (ext rho FA (ers rho u) xu) B) (FB (ers rho u) xu)
                (DB (ers rho u) xu)) as DBsub.
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  pose proof (ITy_cast rho (B [u..]) k _ _ E (FB (ers rho u) xu) DBsub) as DBc.
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (univ k) u dB du) as [d].
    exact (FunTm_of_ty G (B [u..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [u..]) k (ers rho (B [u..]))
                (famCast E (FB (ers rho u) xu)) k' (ers rho (B [u..])) F DBc DBu)
    as Ek; subst k'.
  refine (itot_move G (app A B f u) (B [u..]) Hfun W rho Hrho k F
            (famCast E (FB (ers rho u) xu)) DBu DBc _ _).
  refine (ITm_cast rho (app A B f u) k _ _ E (FB (ers rho u) xu) _ _ _).
  exact (i_app rho A B f u k (ers rho A) FA B0
           (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
           (ers rho f) xf (ers rho u) xu eq_refl DFA DB Df Du).
Qed.

(* The other direction of the cast: a value living in a cast family is a value
   in the original one. *)
Lemma ITm_uncast rho t k w w' (E : w = w') (F : kUFam k w) v
  (y : kElAt (famCast E F) v) :
  ITm rho t k w' (famCast E F) v y -> { x : kElAt F v & ITm rho t k w F v x }.
Proof. destruct E; intros D; exists y; exact D. Qed.

(* ---- the pair.  Its type is the annotation, so only the SECOND component's
     type is a substitution instance: its interpretation is the codomain
     instance at the first component's value, cast to the realiser of
     `B [t..]`. ---- *)
Lemma itot_pair G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ITot G (pair A B t u) (sig_ A B).
Proof.
  intros rho Hrho k' F Dsg.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                  (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHt rho Hrho k FA DFA) as [xt Dt].
  (* the second component, at the codomain instance the first one picks *)
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t k (ers rho A) FA (ers rho t) xt eq_refl Dt
                B k (ers (ext rho FA (ers rho t) xt) B) (FB (ers rho t) xt)
                (DB (ers rho t) xt)) as DBsub.
  destruct (IHu rho Hrho k (famCast E (FB (ers rho t) xt))
              (ITy_cast rho (B [t..]) k _ _ E (FB (ers rho t) xt) DBsub))
    as [xu' Du'].
  destruct (ITm_uncast rho u k _ _ E (FB (ers rho t) xt) _ _ Du') as [xu Du].
  assert (g : Good (esig (ers rho A) B0)
                (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair A B t u) (sig_ A B)
                (t_pair G A B t u k dA dB dt du) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_lvl rho rho eq_refl (sig_ A B) k (ers rho (sig_ A B))
                (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                   redB isoB gSig) k' (ers rho (sig_ A B)) F Dsig Dsg) as Ek;
    subst k'.
  refine (itot_move G (pair A B t u) (sig_ A B)
            (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) W rho Hrho k F
            (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
               redB isoB gSig) Dsg Dsig _ _).
  exact (i_pair rho A B t u k (ers rho A) FA B0
           (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
           (ers rho t) xt (ers rho u) xu g eq_refl DFA DB Dt Du).
Qed.

(* ---- the second projection.  Its type is a substitution instance whose
     substituted term is the FIRST projection, so the codomain instance is
     taken at that projection's own value. ---- *)
Lemma itot_snd G A B p k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) : ITot G (snd A B p) (B [(fst A B p)..]).
Proof.
  intros rho Hrho k' F DBs.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                  (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gSig) Dsig) as [xp Dp].
  pose proof (i_fst rho A B p k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  assert (E : ers (ext rho FA (efst (ers rho p))
                     (sigFst k (ers rho A) B0 FA
                        (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                        (ers rho p) xp)) B
              = ers rho (B [(fst A B p)..]))
    by exact (eq_sym (ers_sub1 rho B (fst A B p) FA _)).
  pose proof (isubst_ITy rho (fst A B p) k (ers rho A) FA (efst (ers rho p)) _
                eq_refl Dfst B k _ _
                (DB (efst (ers rho p))
                   (sigFst k (ers rho A) B0 FA
                      (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                      (ers rho p) xp))) as DBsub.
  pose proof (ITy_cast rho (B [(fst A B p)..]) k _ _ E _ DBsub) as DBc.
  assert (Hfun : FunTm G (B [(fst A B p)..])).
  { destruct (ty_subst1 G A B (univ k) (fst A B p) dB
                (t_fst G A B p k dA dB dp)) as [d].
    exact (FunTm_of_ty G (B [(fst A B p)..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [(fst A B p)..]) k (ers rho (B [(fst A B p)..]))
                (famCast E _) k' (ers rho (B [(fst A B p)..])) F DBc DBs) as Ek;
    subst k'.
  refine (itot_move G (snd A B p) (B [(fst A B p)..]) Hfun W rho Hrho k F
            (famCast E _) DBs DBc _ _).
  refine (ITm_cast rho (snd A B p) k _ _ E _ _ _ _).
  exact (i_snd rho A B p k (ers rho A) FA B0
           (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
           (ers rho p) xp eq_refl DFA DB Dp).
Qed.

(* ---- forall-elimination.  papp has no clause of its own either: the value is
     i_proof's, and the truth it carries is the function's truth instantiated at
     the argument's value.  The proposition itself travels by isubst_ITm. ---- *)
Lemma itot_papp G A p f u k (W : wfc G) (dA : ty G A (univ k))
  (dp : ty (A :: G) p prop) (df : ty G f (prf (all A p))) (du : ty G u A)
  (IHA : ITot G A (univ k)) (IHp : ITot (A :: G) p prop)
  (IHf : ITot G f (prf (all A p))) (IHu : ITot G u A) :
  ITot G (papp f u) (prf (p [u..])).
Proof.
  intros rho Hrho k' F DP.
  pose proof (ity_lvl_dec rho (prf (p [u..])) k' (ers rho (prf (p [u..]))) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  destruct (build_all G A p k W dA dp IHA IHp rho Hrho) as [FA [xp [DFA Dp]]].
  assert (g : Good eprop (ers rho (all A p)))
    by exact (LTm_of_ty G (all A p) prop (t_all G A p k dA dp) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  pose proof (i_all rho A p k (ers rho A) FA (fun u0 y => ers (ext rho FA u0 y) p) xp
                (ers rho (all A p)) g eq_refl DFA Dp) as DAll.
  (* the function's value carries the truth of the universally quantified body *)
  destruct (IHf rho Hrho 0
              (prfF 0 (propElem (ers rho (all A p))
                         (forall u0 (y : kElAt FA u0), propVal (xp u0 y)) g))
              (ity_prf rho (all A p) (ers rho (all A p)) _ DAll)) as [xf _].
  pose proof (prfVal xf) as htruth.
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  (* the substituted proposition, and its value *)
  pose proof (isubst_ITm rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                p 0 eprop (propFam 0) (ers (ext rho FA (ers rho u) xu) p)
                (xp (ers rho u) xu) (Dp (ers rho u) xu)) as Dpu.
  assert (E : eprf (ers (ext rho FA (ers rho u) xu) p) = eprf (ers rho (p [u..])))
    by exact (f_equal eprf (eq_sym (ers_sub1 rho p u FA xu))).
  assert (gp : Good (eprf (ers (ext rho FA (ers rho u) xu) p)) (ers rho (papp f u))).
  { rewrite E.
    exact (LTm_of_ty G (papp f u) (prf (p [u..]))
             (t_all_elim G A p f u k dA dp df du) rho rho
             (EnvRelOf_selfE G rho W Hrho)). }
  pose proof (i_proof rho (papp f u) (p [u..])
                (ers (ext rho FA (ers rho u) xu) p) (xp (ers rho u) xu)
                (htruth (ers rho u) xu) (ers rho (papp f u)) gp eq_refl Dpu) as Dpapp.
  pose proof (ITy_cast rho (prf (p [u..])) 0 _ _ E _
                (ity_prf rho (p [u..]) (ers (ext rho FA (ers rho u) xu) p)
                   (xp (ers rho u) xu) Dpu)) as DPc.
  assert (Hfun : FunTm G (prf (p [u..]))).
  { destruct (ty_subst1 G A p prop u dp du) as [d].
    exact (FunTm_of_ty G (prf (p [u..])) 0 (t_prf G (p [u..]) d)). }
  refine (itot_move G (papp f u) (prf (p [u..])) Hfun W rho Hrho 0 F
            (famCast E _) DP DPc _ _).
  exact (ITm_cast rho (papp f u) 0 _ _ E _ _ _ Dpapp).
Qed.

(* ---- natrec.  The one case whose step term lives two entries deep, and whose
     TYPE `nrec_succ C` is therefore not a single substitution instance of the
     motive.  It is a composite of the three operations Interp/Subst.v does
     provide: weaken C in the tail, replace its nat variable by its own
     successor, weaken at the front. ---- *)

Lemma nrec_succ_as (C : tm) :
  nrec_succ C = ((C ⟨upRen_tm_tm shift⟩) [(succ (var_tm 0))..]) ⟨↑⟩.
Proof. unfold nrec_succ; asimpl; reflexivity. Qed.

Lemma ity_nrec_succ rho (C : tm) k m (x : kElAt (natFam 0) m)
  (FCs : kUFam k (ers (ext rho (natFam 0) (esucc m) (natSucc x)) C))
  (DCs : ITy (ext rho (natFam 0) (esucc m) (natSucc x)) C k
           (ers (ext rho (natFam 0) (esucc m) (natSucc x)) C) FCs)
  kc Sc (FCm : kUFam kc Sc) w (y : kElAt FCm w) :
  ITy (ext (ext rho (natFam 0) m x) FCm w y) (nrec_succ C) k
      (ers (ext rho (natFam 0) (esucc m) (natSucc x)) C) FCs.
Proof.
  rewrite nrec_succ_as.
  apply (weaken1_ITy (ext rho (natFam 0) m x)
           ((C ⟨upRen_tm_tm shift⟩) [(succ (var_tm 0))..]) k _ FCs
           (Build_Entry kc Sc FCm w y)).
  refine (subst_ITy (ext rho (natFam 0) m x) (succ (var_tm 0))
            (Build_Entry 0 enat (natFam 0) (esucc m) (natSucc x)) eq_refl
            (i_succ (ext rho (natFam 0) m x) (var_tm 0) m x
               (i_var0 rho 0 enat (natFam 0) m x))
            (subUniv_all (ext rho (natFam 0) m x) (succ (var_tm 0)))
            _ (C ⟨upRen_tm_tm shift⟩) k _ FCs _ nil eq_refl).
  exact (weaken_ITy (ext rho (natFam 0) (esucc m) (natSucc x)) C k _ FCs DCs
           (Build_Entry 0 enat (natFam 0) (esucc m) (natSucc x) :: nil) rho
           (Build_Entry 0 enat (natFam 0) m x) eq_refl).
Qed.

Lemma itot_natrec G C z s n k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C)) (dn : ty G n nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHz : ITot G z (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C)) (IHn : ITot G n nat_) :
  ITot G (natrec C z s n) (C [n..]).
Proof.
  intros rho Hrho k' F DCn.
  pose (SC := fun m : etm => subst_etm (scons m (rsub rho)) (er C)).
  assert (HEm : forall m (x : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x)).
  { intros m x.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam 0) m) =>
                projT1 (ityT_of_ITot (nat_ :: G) C k IHC
                          (ext rho (natFam 0) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam 0) m x) C k (SC m) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ :: G) C k IHC
                         (ext rho (natFam 0) m x) (HEm m x)))).
  assert (isoC : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
             iso (kAt (FC m x)) (kAt (FC m' x'))).
  { intros m x m' x' Hm.
    assert (HEx : EnvRelOf (nat_ :: G) (ext rho (natFam 0) m x)
                    (ext rho (natFam 0) m' x')).
    { apply (EnvRelOf_ext G rho rho nat_ 0 (natFam 0) (natFam 0) m x m' x'
               (EnvRelOf_selfE G rho W Hrho)).
      apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm. }
    exact (FunTy_of_FunTm (nat_ :: G) C (funtm (nat_ :: G) C (univ k) dC)
             _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
             (LTyK_of_ty (nat_ :: G) C k dC _ _ HEx)). }
  (* the base value *)
  assert (E0 : SC ezero = ers rho (C [zero..]))
    by exact (eq_sym (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
                eq_refl (i_zero rho) C k (SC ezero) (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [zero..]) k _ _ E0 _ DCz)) as [xz' Dz'].
  destruct (ITm_uncast rho z k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dz')
    as [xz Dz].
  (* the step value, at every predecessor and recursive result *)
  assert (Hstep : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w),
             { xs : kElAt (FC (esucc m) (natSucc x))
                      (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) &
               ITm (ext (ext rho (natFam 0) m x) (FC m x) w y) s k
                   (SC (esucc m)) (FC (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) xs }).
  { intros m x w y.
    pose proof (ity_nrec_succ rho C k m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k (SC m) (FC m x) w y) as DS.
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam 0) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs (ext (ext rho (natFam 0) m x) (FC m x) w y)
                (EnvITy_ext (nat_ :: G) (ext rho (natFam 0) m x) C k (FC m x)
                   (DC m x) w y (HEm m x))
                k (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [xs' Ds'].
    destruct (ITm_uncast _ s k _ _ Es (FC (esucc m) (natSucc x)) _ _ Ds')
      as [xs Ds].
    exists xs; exact Ds. }
  pose (ws := fun m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w) =>
                ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s).
  pose (xs := fun m x w y => projT1 (Hstep m x w y)).
  assert (Ds : forall m x w y,
             ITm (ext (ext rho (natFam 0) m x) (FC m x) w y) s k
                 (SC (esucc m)) (FC (esucc m) (natSucc x)) (ws m x w y)
                 (xs m x w y))
    by (intros m x w y; exact (projT2 (Hstep m x w y))).
  pose (redS := fun m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w) =>
                  reds_lam2_app (er s) (rsub rho) m w).
  (* the scrutinee *)
  destruct (IHn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl))
    as [xn Dn].
  pose proof (i_natrec rho C z s n k SC FC isoC (ers rho (stepWrap s))
                (ers rho z) xz ws xs redS (ers rho n) xn
                eq_refl DC Dz Ds Dn) as Dnr.
  (* the conclusion type *)
  assert (En : SC (ers rho n) = ers rho (C [n..]))
    by exact (eq_sym (ers_sub1 rho C n (natFam 0) xn)).
  pose proof (isubst_ITy rho n 0 enat (natFam 0) (ers rho n) xn eq_refl Dn
                C k (SC (ers rho n)) (FC (ers rho n) xn)
                (DC (ers rho n) xn)) as DCsub.
  pose proof (ITy_cast rho (C [n..]) k _ _ En _ DCsub) as DCc.
  assert (Hfun : FunTm G (C [n..])).
  { destruct (ty_subst1 G nat_ C (univ k) n dC dn) as [d].
    exact (FunTm_of_ty G (C [n..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (C [n..]) k (ers rho (C [n..]))
                (famCast En (FC (ers rho n) xn)) k' (ers rho (C [n..])) F
                DCc DCn) as Ek; subst k'.
  refine (itot_move G (natrec C z s n) (C [n..]) Hfun W rho Hrho k F
            (famCast En (FC (ers rho n) xn)) DCn DCc _ _).
  refine (ITm_cast rho (natrec C z s n) k _ _ En (FC (ers rho n) xn) _ _ _).
  (* the recursor's value, moved to the motive instance at the scrutinee's
     own value: the two nat-values agree (natEq_self) *)
  exact (i_conv rho (natrec C z s n) k (SC (ers rho n))
           (FC (ers rho n) (natE (natIdx xn) (natSpec xn)))
           (SC (ers rho n)) (FC (ers rho n) xn) _ _
           (isoC (ers rho n) (natE (natIdx xn) (natSpec xn)) (ers rho n) xn
              (natEq_self _ _)) Dnr).
Qed.

(* ================================================================== *)
(* INTRODUCTION AT PI.                                                 *)
(*                                                                    *)
(* piApp (Interp/PiEl.v) eliminates; piEq_of above compares two         *)
(* elements; this BUILDS one, from a family of codomain values together  *)
(* with the beta step of its realiser.  It is what i_lam's behaviour     *)
(* premise needs, and hence the only thing the lambda case of 9.2 was    *)
(* missing.  It belongs beside piApp in Interp/PiEl.v, which is upstream *)
(* of the ~500s Interp/SigEl.v, so it lives here.                       *)
(* ================================================================== *)

Lemma piEl_of (k : nat) (A0 B0 : etm) (FA : kUFam k A0)
  (SB : forall u, kElAt FA u -> etm)
  (FB : forall u (x : kElAt FA u), kUFam k (SB u x))
  (redB : forall u x, reds (eapp B0 u) (SB u x))
  (isoB : forall u x u' x', kEqAt FA u x u' x' -> iso (kAt (FB u' x')) (kAt (FB u x)))
  (gPi : eqty k (epi A0 B0) (epi A0 B0))
  (w : etm) (gw : Good (epi A0 B0) w)
  (wt : forall u, kElAt FA u -> etm)
  (xt : forall u (y : kElAt FA u), kElAt (FB u y) (wt u y))
  (redw : forall u y, reds (eapp w u) (wt u y))
  (Hfun : forall u y u' y', kEqAt FA u y u' y' ->
            kRel (FB u y) (FB u' y') (wt u y) (xt u y) (wt u' y') (xt u' y')) :
  { x : kElAt (piFam k A0 B0 FA SB FB redB isoB gPi) w &
    forall u y, kEqAt (FB u y) (eapp w u)
                  (piApp k A0 B0 FA SB FB redB isoB gPi w x u y) (wt u y) (xt u y) }.
Proof.
  unfold piApp, kElAt, kAt, uf_at, kAcc.
  generalize (uf_acc (piFam k A0 B0 FA SB FB redB isoB gPi)) as h.
  intros h; destruct h as [fT].
  set (pf := evalAg_refl (epi A0 B0)).
  (* the function: at a code-level argument, read the argument as an element of
     the domain FAMILY (pxc), take the body's value there, expand its realiser
     to `eapp w u` and move it into the codomain code's own instance *)
  pose (f := (fun u' (z : kElS (placeDom k (epi A0 B0) A0 B0 fT
                                  (pEv A0 B0 (epi A0 B0) fT pf)
                                  (pcA k A0 B0 FA (epi A0 B0) fT pf)) u') =>
                famFrom (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z)) _ _ _
                  (eapp w u')
                  (famExp (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))
                     (eapp w u') (wt u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))
                     (redw u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))
                     (xt u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))))
             : forall u' (z : kElS (placeDom k (epi A0 B0) A0 B0 fT
                                      (pEv A0 B0 (epi A0 B0) fT pf)
                                      (pcA k A0 B0 FA (epi A0 B0) fT pf)) u'),
                 kElC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
                   (eapp w u')).
  (* each value is heterogeneously the body's own value *)
  assert (Hf : forall u' z,
             hetC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u' z)
                  (kAt (FB u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z)))
                  (eapp w u') (f u' z)
                  (wt u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))
                  (xt u' (pxc k A0 B0 FA (epi A0 B0) fT pf u' z))).
  { intros u' z.
    eapply hetC_eq_r; [apply hetC_sym; apply hetC_to | apply famExp_rel]. }
  (* and two of them at related arguments are related *)
  assert (Hmain : forall u1 z1 u1' z1',
             kEqC (pcA k A0 B0 FA (epi A0 B0) fT pf) u1 z1 u1' z1' ->
             hetC (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u1 z1)
                  (pcB k A0 B0 FA SB FB redB (epi A0 B0) fT pf u1' z1')
                  (eapp w u1) (f u1 z1) (eapp w u1') (f u1' z1')).
  { intros u1 z1 u1' z1' r.
    eapply hetC_trans; [exact (Hf u1 z1) |].
    eapply hetC_trans;
      [ exact (Hfun u1 _ u1' _ (famTo_eq FA A0 (pAcc A0 B0 (epi A0 B0) fT pf)
                                  (evalAg_refl A0) u1 z1 u1' z1' r)) |].
    apply hetC_sym; exact (Hf u1' z1'). }
  unshelve refine (existT _ (exist _ (f, gw) _) _).
  - (* the element's own equality *)
    cbn [uf_c piFam]; unfold pcode, mkCode, buildPi, mkPi; cbn [eqEl projT2].
    split; [| exact gw].
    intros u1 z1 u1' z1' r r'; split.
    + apply kEqC_sym.
      apply (hetC_at _ _ (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf
                            u1 z1 u1' z1' r)).
      apply hetC_sym; exact (Hmain u1 z1 u1' z1' r).
    + apply kEqC_sym.
      apply (hetC_at _ _ (pisoB k A0 B0 FA SB FB redB isoB (epi A0 B0) fT pf
                            u1' z1' u1 z1 r')).
      exact (Hmain u1 z1 u1' z1' r).
  - (* the behaviour *)
    intros u y.
    apply (proj2 (kRel_same (FB u y) _ _ _ _)).
    eapply hetC_trans; [apply hetC_sym; apply (pApp_het k A0 B0 FA SB FB redB isoB) |].
    eapply hetC_trans; [exact (Hf u _) |].
    exact (Hfun u _ u y (famTo_famFrom FA A0 (pAcc A0 B0 (epi A0 B0) fT pf)
                           (evalAg_refl A0) u y)).
Qed.

(* ---- the lambda.  Its value is built from the body's values by piEl_of, and
     the behaviour equation piEl_of returns is exactly i_lam's last premise.
     The body's functionality -- which piEl_of needs to see that the value is
     self-related -- is funtm at the two extended environments. ---- *)
Lemma itot_lam G A B t k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty (A :: G) t B)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot (A :: G) t B) : ITot G (lam A B t) (pi A B).
Proof.
  intros rho Hrho k' F Dpi'.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gPi := LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho
                 (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_pi rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                eq_refl DFA DB) as Dpi.
  (* the body's value at every argument *)
  pose (xt := fun u0 (y : kElAt FA u0) =>
                projT1 (IHt (ext rho FA u0 y)
                          (EnvITy_ext G rho A k FA DFA u0 y Hrho)
                          k (FB u0 y) (DB u0 y))).
  assert (Dt : forall u0 y, ITm (ext rho FA u0 y) t k (ers (ext rho FA u0 y) B)
                              (FB u0 y) (ers (ext rho FA u0 y) t) (xt u0 y))
    by (intros u0 y;
        exact (projT2 (IHt (ext rho FA u0 y)
                         (EnvITy_ext G rho A k FA DFA u0 y Hrho)
                         k (FB u0 y) (DB u0 y)))).
  (* the body is functional across the two extended environments *)
  assert (Hfun : forall u0 y u0' y', kEqAt FA u0 y u0' y' ->
             kRel (FB u0 y) (FB u0' y')
                  (ers (ext rho FA u0 y) t) (xt u0 y)
                  (ers (ext rho FA u0' y') t) (xt u0' y')).
  { intros u0 y u0' y' Hyy.
    assert (HEx : EnvRelOf (A :: G) (ext rho FA u0 y) (ext rho FA u0' y')).
    { apply (EnvRelOf_ext G rho rho A k FA FA u0 y u0' y'
               (EnvRelOf_selfE G rho W Hrho)).
      apply (proj1 (kRel_same FA _ _ _ _)); exact Hyy. }
    refine (funtm (A :: G) t B dt _ _ HEx k _ (FB u0 y) _ (xt u0 y) (Dt u0 y)
              _ (FB u0' y') _ (xt u0' y') (Dt u0' y')
              (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (univ k) dB) _ _ HEx
                 k _ (FB u0 y) _ (FB u0' y') (DB u0 y) (DB u0' y')
                 (LTyK_of_ty (A :: G) B k dB _ _ HEx)) _).
    apply (Rel_tyeq (ers (ext rho FA u0 y) B) (ers (ext rho FA u0' y') B));
      [ exact (LTy_of_ty (A :: G) B k dB _ _ HEx)
      | exact (LTm_of_ty (A :: G) t B dt _ _ HEx) ]. }
  (* the lambda's own realiser is good, and beta-reduces to the body's *)
  assert (gw : Good (epi (ers rho A) B0) (ers rho (lam A B t)))
    by exact (LTm_of_ty G (lam A B t) (pi A B) (t_lam G A B t k dA dB dt) rho rho
                (EnvRelOf_selfE G rho W Hrho)).
  destruct (piEl_of k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
              redB isoB gPi (ers rho (lam A B t)) gw
              (fun u0 y => ers (ext rho FA u0 y) t) xt
              (fun u0 y => reds_beta_sub (rsub rho) (er t) u0) Hfun)
    as [x Hbeh].
  pose proof (ity_lvl rho rho eq_refl (pi A B) k (ers rho (pi A B))
                (piFam k (ers rho A) B0 FA (fun u0 x0 => ers (ext rho FA u0 x0) B) FB
                   redB isoB gPi) k' (ers rho (pi A B)) F Dpi Dpi') as Ek;
    subst k'.
  refine (itot_move G (lam A B t) (pi A B)
            (FunTm_of_ty G (pi A B) k (t_pi G A B k dA dB)) W rho Hrho k F
            (piFam k (ers rho A) B0 FA (fun u0 x0 => ers (ext rho FA u0 x0) B) FB
               redB isoB gPi) Dpi' Dpi _ _).
  exact (i_lam rho A B t k (ers rho A) FA B0
           (fun u0 x0 => ers (ext rho FA u0 x0) B) FB redB isoB gPi
           (ers rho (lam A B t)) x (fun u0 y => ers (ext rho FA u0 y) t) xt
           eq_refl eq_refl DFA DB Dt Hbeh).
Qed.

(* ================================================================== *)
(* THE CONVERSION CASES.                                               *)
(*                                                                    *)
(* For `cv G t u A` the statement is ISem: totality for both sides and   *)
(* their relatedness.  The congruences follow the corresponding typing    *)
(* case with two terms in place of one; the computation rules are the      *)
(* element laws of Interp/PiEl.v, Interp/SigEl.v and Interp/Rec.v.        *)
(* ================================================================== *)

(* Transport is injective on the equality, which is what a conversion of the
   TYPE needs: the values live at the new type's family and have to be compared
   at the old one's. *)
Lemma kEqAt_of_ctoK {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : iso (kAt F) (kAt F')) w x w' x' :
  kEqAt F' w (ctoK (kAt F) (kAt F') P w x) w' (ctoK (kAt F) (kAt F') P w' x') ->
  kEqAt F w x w' x'.
Proof.
  intros H.
  eapply kEqC_trans; [apply kEqC_sym; apply (ctoK_pull (kAt F) (kAt F') P) |].
  eapply kEqC_trans; [| apply (ctoK_pull (kAt F) (kAt F') P)].
  apply cpullK_eq; exact H.
Qed.

Lemma IRel_self' G t A (d : ty G t A) : IRel G t t A.
Proof. destruct (ty_wfc G t A d) as [W]; exact (IRel_self G t A d W). Qed.

(* ---- the equivalence and the conversion of the type ---- *)

Lemma isem_refl G t A (d : ty G t A) (IHd : ITot G t A) : ISem G t t A.
Proof. exact (IHd, IHd, IRel_self' G t A d). Qed.

Lemma isem_sym G t u A (H : ISem G t u A) : ISem G u t A.
Proof.
  destruct H as [[Ht Hu] HR]; split; [split; [exact Hu | exact Ht] |].
  intros rho Hrho k F DA x y Dx Dy.
  apply kEqAt_sym; exact (HR rho Hrho k F DA y x Dy Dx).
Qed.

Lemma isem_trans G t u v A (H1 : ISem G t u A) (H2 : ISem G u v A) : ISem G t v A.
Proof.
  destruct H1 as [[Ht Hu] HR1]; destruct H2 as [[Hu' Hv] HR2].
  split; [split; [exact Ht | exact Hv] |].
  intros rho Hrho k F DA x y Dx Dy.
  destruct (Hu rho Hrho k F DA) as [z Dz].
  eapply kEqAt_trans;
    [ exact (HR1 rho Hrho k F DA x z Dx Dz)
    | exact (HR2 rho Hrho k F DA z y Dz Dy) ].
Qed.

Lemma isem_conv G t u A B k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty G B (univ k))
  (H : ISem G t u A) (IHA : ITot G A (univ k)) (IHB : ITot G B (univ k))
  (IHc : IRel G A B (univ k)) : ISem G t u B.
Proof.
  destruct H as [[Ht Hu] HR].
  split; [split |].
  - exact (itot_conv G t A B k W dA dB Ht IHA IHB IHc).
  - exact (itot_conv G u A B k W dA dB Hu IHA IHB IHc).
  - intros rho Hrho k' F DB' x y Dx Dy.
    destruct (ityT_of_ITot G B k IHB rho Hrho) as [FB0 DB0].
    pose proof (ity_lvl rho rho eq_refl B k (ers rho B) FB0 k' (ers rho B) F
                  DB0 DB') as Ek; subst k'.
    destruct (ityT_of_ITot G A k IHA rho Hrho) as [FA0 DA0].
    pose proof (iso_of_IRel G A B k W IHA IHB IHc
                  (FunTm_of_ty G A k dA) (FunTm_of_ty G B k dB)
                  rho Hrho FA0 DA0 F DB') as P.
    apply (kEqAt_of_ctoK F FA0 (iso_sym _ _ P)).
    apply (HR rho Hrho k FA0 DA0);
      [ exact (i_conv rho t k (ers rho B) F (ers rho A) FA0 (ers rho t) x
                 (iso_sym _ _ P) Dx)
      | exact (i_conv rho u k (ers rho B) F (ers rho A) FA0 (ers rho u) y
                 (iso_sym _ _ P) Dy) ].
Qed.

(* ---- proof irrelevance: a Prf-family relates all of its elements, and at
     layer 1 all realisers of a Prf type are related. ---- *)
Lemma isem_prf_irr G p e e' (de : ty G e (prf p)) (de' : ty G e' (prf p))
  (IHe : ITot G e (prf p)) (IHe' : ITot G e' (prf p)) : ISem G e e' (prf p).
Proof.
  split; [split; [exact IHe | exact IHe'] |].
  intros rho Hrho k F DP x y Dx Dy.
  pose proof (ity_lvl_dec rho (prf p) k (ers rho (prf p)) F DP) as El;
    cbn [LvlDec] in El; subst k.
  destruct (ity_prf_inv rho (prf p) 0 (ers rho (prf p)) F DP)
    as [wp [xp [Dp Hiso]]].
  pose proof (TotalFam_iso (prfF 0 xp) F (iso_sym _ _ Hiso)
                (prf_total 0 wp xp)) as HT.
  apply HT.
  apply (Rel_prf_intro (ers rho (prf p)) (ers rho p));
    [ exists 0; exact (uf_ty F) | apply eval_whnf, whnf_prf ].
Qed.

(* The layer-1 side condition for a conversion, as fundamental_cv gives it. *)
Definition LCv (G : ctx) (t u A : tm) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> Rel (ers rho A) (ers rho t) (ers rho' u).

Lemma LCv_of_cv G t u A (c : cv G t u A) : LCv G t u A.
Proof.
  intros rho rho' [_ [_ [_ HS]]].
  exact (proj1 (fundamental_cv G t u A c _ _ HS)).
Qed.

(* ---- a congruence at a UNIVERSE: the two values are codes, so what has to be
     shown is that the two families are isomorphic and their realisers layer-1
     equal -- which is the universe's own equality (uEq_of). ---- *)
Lemma isem_former_cv G (t u : tm) (k : nat) (W : wfc G)
  (Htot : ITot G t (univ k)) (Hutot : ITot G u (univ k))
  (Hsht : forall rho k' Sy (F : kUFam k' Sy) w (x : kElAt F w),
            TmShape rho t k' Sy F w x -> TyVal rho t k' Sy F w x)
  (Hshu : forall rho k' Sy (F : kUFam k' Sy) w (x : kElAt F w),
            TmShape rho u k' Sy F w x -> TyVal rho u k' Sy F w x)
  (Hfam : forall rho (Hrho : EnvITy G rho) F1 F2,
            ITy rho t k (ers rho t) F1 -> ITy rho u k (ers rho u) F2 ->
            (eqty k (ers rho t) (ers rho u) * iso (kAt F1) (kAt F2))%type)
  (Lc : LCv G t u (univ k)) : ISem G t u (univ k).
Proof.
  split; [split; [exact Htot | exact Hutot] |].
  intros rho Hrho k' F DU x y Dx Dy.
  pose proof (ity_lvl_dec rho (univ k) k' (ers rho (univ k)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (itm_inv rho t (S k) (ers rho (univ k)) F (ers rho t) x Dx) as E.
  pose proof (itm_inv rho u (S k) (ers rho (univ k)) F (ers rho u) y Dy) as E'.
  cbn [TmInv] in E, E'.
  apply Hsht in E; apply Hshu in E'; cbn [TyVal] in E, E'.
  destruct E as [F1 [D1 Hv]]; destruct E' as [F2 [D2 Hv']].
  destruct (Hfam rho Hrho F1 F2 D1 D2) as [Hty Hi].
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (proj1 (kRel_same (univFam k) _ _ _ _)).
  apply uEq_of; [exact Hty | intros v h pf v' h' pf'].
  eapply iso_trans; [apply uf_coh |].
  eapply iso_trans; [exact Hi | apply uf_coh].
Qed.

(* The isomorphism a conversion of types gives, at interpretations SUPPLIED by
   the caller: simpler than iso_of_IRel, which has to build them. *)
Lemma iso_of_IRel_at G t u k (HR : IRel G t u (univ k))
  rho (Hrho : EnvITy G rho)
  (F1 : kUFam k (ers rho t)) (D1 : ITy rho t k (ers rho t) F1)
  (F2 : kUFam k (ers rho u)) (D2 : ITy rho u k (ers rho u) F2) :
  iso (kAt F1) (kAt F2).
Proof.
  pose proof (HR rho Hrho (S k) (univFam k)
                (ity_univ rho k (ers rho (univ k)) eq_refl)
                (famEl F1) (famEl F2)
                (i_ty rho t k (ers rho t) F1 D1)
                (i_ty rho u k (ers rho u) F2 D2)) as Heq.
  pose proof (uEq_iso (famEl F1) (famEl F2) Heq) as Hi.
  rewrite !elFam_famEl in Hi.
  exact (Hi (ers rho t) (kAcc F1) (evalAg_refl _)
            (ers rho u) (kAcc F2) (evalAg_refl _)).
Qed.

(* the same with the realisers left general: an inversion hands back a family
   at a realiser that is only PROVABLY the erasure. *)
Lemma iso_of_IRel_at' G t u k (HR : IRel G t u (univ k))
  rho (Hrho : EnvITy G rho)
  w1 (F1 : kUFam k w1) (D1 : ITy rho t k w1 F1)
  w2 (F2 : kUFam k w2) (D2 : ITy rho u k w2 F2) :
  iso (kAt F1) (kAt F2).
Proof.
  assert (E1 : w1 = ers rho t) by exact (ers_of_ITy _ _ _ _ _ D1).
  assert (E2 : w2 = ers rho u) by exact (ers_of_ITy _ _ _ _ _ D2).
  subst w1 w2.
  exact (iso_of_IRel_at G t u k HR rho Hrho F1 D1 F2 D2).
Qed.

(* the layer-1 equality of two convertible TYPES, at their level *)
Definition LCvK (G : ctx) (A A' : tm) (k : nat) : Prop :=
  forall rho rho', EnvRelOf G rho rho' -> eqty k (ers rho A) (ers rho' A').

Lemma LCvK_of_cv G A A' k (c : cv G A A' (univ k)) : LCvK G A A' k.
Proof.
  intros rho rho' [_ [_ [_ HS]]]; exact (fundamental_cv_U G A A' k c _ _ HS).
Qed.

(* ---- the congruences at Pi and Sigma.  The codomains are compared in two
     steps: first B against B' in the SAME environment (the conversion's own
     induction hypothesis), then B' against itself across the two environments
     extended by the isomorphic domains (functionality).  The second step is
     what needed EnvOf to be closed under conversion. ---- *)

Lemma isem_pi G A A' B B' k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (dA' : ty G A' (univ k)) (dB' : ty (A' :: G) B' (univ k))
  (cA : cv G A A' (univ k)) (cB : cv (A :: G) B B' (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHA' : ITot G A' (univ k)) (IHB' : ITot (A' :: G) B' (univ k))
  (IHcA : IRel G A A' (univ k)) (IHcB : IRel (A :: G) B B' (univ k)) :
  ISem G (pi A B) (pi A' B') (univ k).
Proof.
  apply (isem_former_cv G (pi A B) (pi A' B') k W
           (itot_pi G A B k W dA dB IHA IHB)
           (itot_pi G A' B' k W dA' dB' IHA' IHB')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H));
    [| exact (LCv_of_cv G (pi A B) (pi A' B') (univ k)
                (c_pi G A A' B B' k dA dB dA' dB' cA cB)) ].
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  assert (HtyA : tyeq (ers rho A) (ers rho A'))
    by (exists k; exact (LCvK_of_cv G A A' k cA rho rho HEself)).
  split.
  - exact (LCvK_of_cv G (pi A B) (pi A' B') k
             (c_pi G A A' B B' k dA dB dA' dB' cA cB) rho rho HEself).
  - (* decompose both Pi-families *)
    destruct (ity_pi_inv rho (pi A B) k (ers rho (pi A B)) F1 D1)
      as [wA [FA [B0 [wB [FB [redB [isoB [gPi [[[DA DB] Hw] Hiso]]]]]]]]].
    destruct (ity_pi_inv rho (pi A' B') k (ers rho (pi A' B')) F2 D2)
      as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
    assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
    assert (EA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
    subst wA wA'.
    eapply iso_trans; [exact Hiso |].
    eapply iso_trans; [| apply iso_sym; exact Hiso'].
    (* the domains *)
    assert (QA : iso (kAt FA) (kAt FA'))
      by exact (iso_of_IRel_at' G A A' k IHcA rho Hrho _ FA DA _ FA' DA').
    apply piFam_iso.
    + eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
      eapply tyeq_trans;
        [ exists k; exact (LCvK_of_cv G (pi A B) (pi A' B') k
                             (c_pi G A A' B B' k dA dB dA' dB' cA cB) rho rho HEself)
        | exact Hw' ].
    + exact QA.
    + (* the codomains *)
      intros u x u' x' Hxx.
      (* B' interpreted in the A-extended environment *)
      pose proof (EnvITy_ext G rho A k FA DA u x Hrho) as HExA.
      pose proof (EnvITy_ext_iso G rho A' k (ers rho A) FA FA' DA' QA u x Hrho)
        as HExA'.
      destruct (ityT_of_ITot (A' :: G) B' k IHB' (ext rho FA u x) HExA')
        as [FBm DBm].
      eapply iso_trans;
        [ exact (iso_of_IRel_at' (A :: G) B B' k IHcB (ext rho FA u x) HExA
                   _ (FB u x) (DB u x) _ FBm DBm) |].
      (* and B' across the two environments *)
      assert (HEr : EnvRelOf (A' :: G) (ext rho FA u x) (ext rho FA' u' x')).
      { apply (EnvRelOf_ext_ty G rho rho A' k (ers rho A) (ers rho A')
                 FA FA' u x u' x' HEself HtyA);
          [ exists k; exact (uf_ty FA') | exact Hxx ]. }
      assert (Eb' : wB' u' x' = ers (ext rho FA' u' x') B')
        by exact (ers_of_ITy _ _ _ _ _ (DB' u' x')).
      refine (FunTy_of_FunTm (A' :: G) B' (funtm (A' :: G) B' (univ k) dB')
                _ _ HEr k _ FBm _ (FB' u' x') DBm (DB' u' x') _).
      rewrite Eb'; exact (LTyK_of_ty (A' :: G) B' k dB' _ _ HEr).
Qed.

Lemma isem_sig G A A' B B' k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (dA' : ty G A' (univ k)) (dB' : ty (A' :: G) B' (univ k))
  (cA : cv G A A' (univ k)) (cB : cv (A :: G) B B' (univ k))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHA' : ITot G A' (univ k)) (IHB' : ITot (A' :: G) B' (univ k))
  (IHcA : IRel G A A' (univ k)) (IHcB : IRel (A :: G) B B' (univ k)) :
  ISem G (sig_ A B) (sig_ A' B') (univ k).
Proof.
  apply (isem_former_cv G (sig_ A B) (sig_ A' B') k W
           (itot_sig G A B k W dA dB IHA IHB)
           (itot_sig G A' B' k W dA' dB' IHA' IHB')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H));
    [| exact (LCv_of_cv G (sig_ A B) (sig_ A' B') (univ k)
                (c_sig G A A' B B' k dA dB dA' dB' cA cB)) ].
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  assert (HtyA : tyeq (ers rho A) (ers rho A'))
    by (exists k; exact (LCvK_of_cv G A A' k cA rho rho HEself)).
  split.
  - exact (LCvK_of_cv G (sig_ A B) (sig_ A' B') k
             (c_sig G A A' B B' k dA dB dA' dB' cA cB) rho rho HEself).
  - (* decompose both Pi-families *)
    destruct (ity_sig_inv rho (sig_ A B) k (ers rho (sig_ A B)) F1 D1)
      as [wA [FA [B0 [wB [FB [redB [isoB [gSig [[[DA DB] Hw] Hiso]]]]]]]]].
    destruct (ity_sig_inv rho (sig_ A' B') k (ers rho (sig_ A' B')) F2 D2)
      as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [[[DA' DB'] Hw'] Hiso']]]]]]]]].
    assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
    assert (EA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
    subst wA wA'.
    eapply iso_trans; [exact Hiso |].
    eapply iso_trans; [| apply iso_sym; exact Hiso'].
    (* the domains *)
    assert (QA : iso (kAt FA) (kAt FA'))
      by exact (iso_of_IRel_at' G A A' k IHcA rho Hrho _ FA DA _ FA' DA').
    apply sigFam_iso.
    + eapply tyeq_trans; [apply tyeq_sym; exact Hw |].
      eapply tyeq_trans;
        [ exists k; exact (LCvK_of_cv G (sig_ A B) (sig_ A' B') k
                             (c_sig G A A' B B' k dA dB dA' dB' cA cB) rho rho HEself)
        | exact Hw' ].
    + exact QA.
    + (* the codomains *)
      intros u x u' x' Hxx.
      (* B' interpreted in the A-extended environment *)
      pose proof (EnvITy_ext G rho A k FA DA u x Hrho) as HExA.
      pose proof (EnvITy_ext_iso G rho A' k (ers rho A) FA FA' DA' QA u x Hrho)
        as HExA'.
      destruct (ityT_of_ITot (A' :: G) B' k IHB' (ext rho FA u x) HExA')
        as [FBm DBm].
      eapply iso_trans;
        [ exact (iso_of_IRel_at' (A :: G) B B' k IHcB (ext rho FA u x) HExA
                   _ (FB u x) (DB u x) _ FBm DBm) |].
      (* and B' across the two environments *)
      assert (HEr : EnvRelOf (A' :: G) (ext rho FA u x) (ext rho FA' u' x')).
      { apply (EnvRelOf_ext_ty G rho rho A' k (ers rho A) (ers rho A')
                 FA FA' u x u' x' HEself HtyA);
          [ exists k; exact (uf_ty FA') | exact Hxx ]. }
      assert (Eb' : wB' u' x' = ers (ext rho FA' u' x') B')
        by exact (ers_of_ITy _ _ _ _ _ (DB' u' x')).
      refine (FunTy_of_FunTm (A' :: G) B' (funtm (A' :: G) B' (univ k) dB')
                _ _ HEr k _ FBm _ (FB' u' x') DBm (DB' u' x') _).
      rewrite Eb'; exact (LTyK_of_ty (A' :: G) B' k dB' _ _ HEr).
Qed.

(* A conversion's relatedness across two DIFFERENT interpretations of the type:
   what a term congruence needs of its subterms, since the two readings'
   inversions produce their own families. *)
Lemma kRel_of_IRel G (t u A : tm) (HR : IRel G t u A) (fA : FunTm G A) (W : wfc G)
  rho (Hrho : EnvITy G rho) k (F F' : kUFam k (ers rho A))
  (D : ITy rho A k (ers rho A) F) (D' : ITy rho A k (ers rho A) F')
  x y (Dx : ITm rho t k (ers rho A) F (ers rho t) x)
      (Dy : ITm rho u k (ers rho A) F' (ers rho u) y) :
  kRel F F' (ers rho t) x (ers rho u) y.
Proof.
  pose proof (ity_same_iso G A fA rho W Hrho k F F' D D') as P.
  exists P.
  eapply kEqC_trans;
    [ apply (ctoK_eq (kAt F) (kAt F') P);
      exact (HR rho Hrho k F D x
               (ctoK (kAt F') (kAt F) (iso_sym _ _ P) (ers rho u) y) Dx
               (i_conv rho u k (ers rho A) F' (ers rho A) F (ers rho u) y
                  (iso_sym _ _ P) Dy)) |].
  (* moving y back and forth is the identity *)
  eapply kEqC_trans;
    [ apply (ctoK_eq (kAt F) (kAt F') P);
      apply (ctoK_sym (kAt F) (kAt F') P (iso_sym _ _ P)) |].
  apply (cpullK_to (kAt F) (kAt F') P).
Qed.

(* ---- the lift, Prf and the successor ---- *)

Lemma isem_up G A A' k (W : wfc G)
  (dA : ty G A (univ k)) (dA' : ty G A' (univ k)) (cA : cv G A A' (univ k))
  (IHA : ITot G A (univ k)) (IHA' : ITot G A' (univ k))
  (IHcA : IRel G A A' (univ k)) :
  ISem G (up (univ (S k)) A) (up (univ (S k)) A') (univ (S k)).
Proof.
  apply (isem_former_cv G (up (univ (S k)) A) (up (univ (S k)) A') (S k) W
           (itot_up G A k W dA IHA) (itot_up G A' k W dA' IHA')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H));
    [| exact (LCv_of_cv G _ _ _ (c_up G A A' k dA dA' cA)) ].
  intros rho Hrho F1 F2 D1 D2.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  split.
  - apply (eqty_cumul k (S k)); [apply Nat.le_succ_diag_r |].
    exact (LCvK_of_cv G A A' k cA rho rho HEself).
  - destruct (ity_up_inv rho (up (univ (S k)) A) (S k) _ F1 D1)
      as [F1a [[Ej DA] Hi1]].
    destruct (ity_up_inv rho (up (univ (S k)) A') (S k) _ F2 D2)
      as [F2a [[Ej' DA'] Hi2]].
    eapply iso_trans; [exact Hi1 |].
    eapply iso_trans; [| apply iso_sym; exact Hi2].
    apply famLiftK_iso.
    exact (iso_of_IRel_at' G A A' k IHcA rho Hrho _ F1a DA _ F2a DA').
Qed.

Lemma isem_prf G p p' (W : wfc G) (dp : ty G p prop) (dp' : ty G p' prop)
  (cp : cv G p p' prop) (IHp : ITot G p prop) (IHp' : ITot G p' prop)
  (IHc : IRel G p p' prop) : ISem G (prf p) (prf p') (univ 0).
Proof.
  apply (isem_former_cv G (prf p) (prf p') 0 W
           (itot_prf G p W dp IHp) (itot_prf G p' W dp' IHp')
           (fun rho k' Sy F w x H => H) (fun rho k' Sy F w x H => H));
    [| exact (LCv_of_cv G _ _ _ (c_prf G p p' dp dp' cp)) ].
  intros rho Hrho F1 F2 D1 D2.
  destruct (ity_prf_inv rho (prf p) 0 _ F1 D1) as [wp [xp [Dp Hi1]]].
  destruct (ity_prf_inv rho (prf p') 0 _ F2 D2) as [wp' [xp' [Dp' Hi2]]].
  assert (Ep : wp = ers rho p) by exact (ers_of_ITm _ _ _ _ _ _ _ Dp).
  assert (Ep' : wp' = ers rho p') by exact (ers_of_ITm _ _ _ _ _ _ _ Dp').
  subst wp wp'.
  pose proof (IHc rho Hrho 0 (propFam 0) (ity_prop rho (ers rho prop) eq_refl)
                xp xp' Dp Dp') as Hxx.
  destruct (proj1 (propEq_iff xp xp') Hxx) as [Hiff Hrelp].
  assert (Hpr : PR (ers rho p) (ers rho p'))
    by exact (Rel_prop_elim eprop _ _ (eval_whnf _ whnf_prop) Hrelp).
  split.
  - exact (eqty_prf 0 (ers rho (prf p)) (ers rho (prf p')) (ers rho p) (ers rho p')
             (eval_whnf _ (whnf_prf _)) (eval_whnf _ (whnf_prf _)) Hpr).
  - eapply iso_trans; [exact Hi1 |].
    eapply iso_trans; [| apply iso_sym; exact Hi2].
    apply prfFam_iso;
      [ exists 0;
        exact (eqty_prf 0 (eprf (ers rho p)) (eprf (ers rho p'))
                 (ers rho p) (ers rho p')
                 (eval_whnf _ (whnf_prf _)) (eval_whnf _ (whnf_prf _)) Hpr)
      | exact Hiff ].
Qed.

Lemma isem_succ G n n' (W : wfc G) (dn : ty G n nat_) (dn' : ty G n' nat_)
  (cn : cv G n n' nat_) (IHn : ITot G n nat_) (IHn' : ITot G n' nat_)
  (IHc : IRel G n n' nat_) : ISem G (succ n) (succ n') nat_.
Proof.
  split; [split; [exact (itot_succ G W n IHn) | exact (itot_succ G W n' IHn')] |].
  intros rho Hrho k F DN x y Dx Dy.
  pose proof (ity_lvl_dec rho nat_ k (ers rho nat_) F DN) as El;
    cbn [LvlDec] in El; subst k.
  pose proof (LCv_of_cv G (succ n) (succ n') nat_ (c_succ G n n' dn dn' cn) rho rho
                (EnvRelOf_selfE G rho W Hrho)) as Hrel.
  pose proof (itm_inv rho (succ n) 0 (ers rho nat_) F (ers rho (succ n)) x Dx) as E.
  pose proof (itm_inv rho (succ n') 0 (ers rho nat_) F (ers rho (succ n')) y Dy) as E'.
  cbn [TmInv TmShape SuccVal] in E, E'.
  destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
  destruct E as [wn [xn [Dn Hv]]]; destruct E' as [wn' [xn' [Dn' Hv']]].
  assert (Ewn : wn = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn).
  assert (Ewn' : wn' = ers rho n') by exact (ers_of_ITm _ _ _ _ _ _ _ Dn').
  subst wn wn'.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply (proj1 (kRel_same (natFam 0) _ _ _ _)).
  apply natSucc_eq.
  exact (IHc rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl) xn xn' Dn Dn').
Qed.

(* ---- the term lift and the first projection ---- *)

Lemma isem_uptm G A t t' k (W : wfc G) (dA : ty G A (univ k))
  (dt : ty G t A) (dt' : ty G t' A) (ct : cv G t t' A)
  (IHA : ITot G A (univ k)) (IHt : ITot G t A) (IHt' : ITot G t' A)
  (IHc : IRel G t t' A) : ISem G (uptm A t) (uptm A t') (up (univ (S k)) A).
Proof.
  split; [split; [exact (itot_uptm G A t k W dA dt IHA IHt)
                 | exact (itot_uptm G A t' k W dA dt' IHA IHt')] |].
  intros rho Hrho k' F DU x y Dx Dy.
  pose proof (ity_lvl_dec rho (up (univ (S k)) A) k'
                (ers rho (up (univ (S k)) A)) F DU) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (itm_inv rho (uptm A t) (S k) (ers rho (up (univ (S k)) A)) F
                (ers rho (uptm A t)) x Dx) as E.
  pose proof (itm_inv rho (uptm A t') (S k) (ers rho (up (univ (S k)) A)) F
                (ers rho (uptm A t')) y Dy) as E'.
  cbn [TmInv TmShape UpTmVal] in E, E'.
  destruct E as [Sy1 [F1 [x1 [[DA1 D1] Hv]]]].
  destruct E' as [Sy1' [F1' [x1' [[DA1' D1'] Hv']]]].
  assert (E1 : Sy1 = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA1).
  assert (E1' : Sy1' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA1').
  subst Sy1 Sy1'.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  apply kRel_lift.
  exact (kRel_of_IRel G t t' A IHc (FunTm_of_ty G A k dA) W rho Hrho k F1 F1'
           DA1 DA1' x1 x1' D1 D1').
Qed.

(* the realiser-general forms: an inversion hands back families at realisers
   that are only provably the erasures *)
Lemma ity_same_iso' G A (HA : FunTm G A) rho (W : wfc G) (H : EnvITy G rho)
  k w (F : kUFam k w) w' (F0 : kUFam k w')
  (D : ITy rho A k w F) (D0 : ITy rho A k w' F0) : iso (kAt F) (kAt F0).
Proof.
  assert (E : w = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D).
  assert (E' : w' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D0).
  subst w w'.
  exact (ity_same_iso G A HA rho W H k F F0 D D0).
Qed.

Lemma kRel_of_IRel' G (t u A : tm) (HR : IRel G t u A) (fA : FunTm G A) (W : wfc G)
  rho (Hrho : EnvITy G rho) k w (F : kUFam k w) w' (F' : kUFam k w')
  (D : ITy rho A k w F) (D' : ITy rho A k w' F')
  wt (x : kElAt F wt) wu (y : kElAt F' wu)
  (Dx : ITm rho t k w F wt x) (Dy : ITm rho u k w' F' wu y) :
  kRel F F' wt x wu y.
Proof.
  assert (E : w = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D).
  assert (E' : w' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ D').
  subst w w'.
  assert (Et : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dx).
  assert (Eu : wu = ers rho u) by exact (ers_of_ITm _ _ _ _ _ _ _ Dy).
  subst wt wu.
  exact (kRel_of_IRel G t u A HR fA W rho Hrho k F F' D D' x y Dx Dy).
Qed.

(* ---- the first projection ---- *)
Lemma isem_fst_core G A B p p' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (IHc : IRel G p p' (sig_ A B))
  rho (Hrho : EnvITy G rho) k' (F : kUFam k' (ers rho A)) x y
  (E : FstVal rho A B p k' (ers rho A) F (ers rho (fst A B p)) x)
  (E' : FstVal rho A B p' k' (ers rho A) F (ers rho (fst A B p')) y) :
  kEqAt F (ers rho (fst A B p)) x (ers rho (fst A B p')) y.
Proof.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig
    [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig'
    [wp' [xp' [[[[Ep' DA'] DB'] Dp'] Hv']]]]]]]]]]].
  pose proof (ity_sig rho A B k' wA FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho A B k' wA' FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  pose proof (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as fS.
  pose proof (ity_same_iso' G (sig_ A B) fS rho W Hrho k' _ _ _ _ Dsig Dsig') as Psig.
  pose proof (kRel_of_IRel' G p p' (sig_ A B) IHc fS W rho Hrho k' _ _ _ _
                Dsig Dsig' _ xp _ xp' Dp Dp') as Hxx.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (sigFst_to k' wA B0 FA wB FB redB isoB gSig
               wA' B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
  apply (proj1 (kRel_same FA' _ _ _ _)).
  apply (sigFst_eq k' wA' B0' FA' wB' FB' redB' isoB' gSig').
  exact (kRel_at _ _ Psig _ xp _ xp' Hxx).
Qed.

Lemma isem_fst G A B p p' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B)) (dp' : ty G p' (sig_ A B))
  (cp : cv G p p' (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) (IHp' : ITot G p' (sig_ A B))
  (IHc : IRel G p p' (sig_ A B)) : ISem G (fst A B p) (fst A B p') A.
Proof.
  split;
    [split; [exact (itot_fst G A B p k W dA dB dp IHA IHB IHp)
            | exact (itot_fst G A B p' k W dA dB dp' IHA IHB IHp')] |].
  intros rho Hrho k' F DA' x y Dx Dy.
  pose proof (itm_inv rho (fst A B p) k' (ers rho A) F
                (ers rho (fst A B p)) x Dx) as E.
  pose proof (itm_inv rho (fst A B p') k' (ers rho A) F
                (ers rho (fst A B p')) y Dy) as E'.
  destruct k' as [| k0]; cbn [TmInv TmShape FstVal] in E, E'.
  - pose proof (LCv_of_cv G (fst A B p) (fst A B p') A
                  (c_fst G A B p p' k dA dB dp dp' cp) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hrel.
    destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
    exact (isem_fst_core G A B p p' k W dA dB IHc rho Hrho 0 F x y E E').
  - exact (isem_fst_core G A B p p' k W dA dB IHc rho Hrho (S k0) F x y E E').
Qed.

(* ---- the second projection ---- *)
Lemma isem_snd_core G A B p p' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (IHc : IRel G p p' (sig_ A B))
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : SndVal rho A B p k' Sy F (ers rho (snd A B p)) x)
  (E' : SndVal rho A B p' k' Sy F (ers rho (snd A B p')) y) :
  kEqAt F (ers rho (snd A B p)) x (ers rho (snd A B p')) y.
Proof.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig
    [wp [xp [[[[Ep DA] DB] Dp] Hv]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig'
    [wp' [xp' [[[[Ep' DA'] DB'] Dp'] Hv']]]]]]]]]]].
  pose proof (ity_sig rho A B k' wA FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho A B k' wA' FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  pose proof (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as fS.
  pose proof (ity_same_iso' G (sig_ A B) fS rho W Hrho k' _ _ _ _ Dsig Dsig') as Psig.
  pose proof (kRel_of_IRel' G p p' (sig_ A B) IHc fS W rho Hrho k' _ _ _ _
                Dsig Dsig' _ xp _ xp' Dp Dp') as Hxx.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (sigSnd_to k' wA B0 FA wB FB redB isoB gSig
               wA' B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
  apply (sigSnd_eq k' wA' B0' FA' wB' FB' redB' isoB' gSig').
  exact (kRel_at _ _ Psig _ xp _ xp' Hxx).
Qed.


(* The second projection of the RIGHT-hand subject, at the type the rule's
   conclusion mentions -- which is the one built from the LEFT subject.  The
   two codomain families differ, at the two first projections; they are
   isomorphic because those projections are related (build_fam_data's isoB),
   and that isomorphism is where the value travels. *)
Lemma itot_snd' G A B p p' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B)) (dp' : ty G p' (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) (IHp' : ITot G p' (sig_ A B))
  (IHc : IRel G p p' (sig_ A B)) : ITot G (snd A B p') (B [(fst A B p)..]).
Proof.
  intros rho Hrho k' F DBs.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                  (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gSig) Dsig) as [xp Dp].
  destruct (IHp' rho Hrho k
              (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gSig) Dsig) as [xp' Dp'].
  pose proof (IHc rho Hrho k
                (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                   redB isoB gSig) Dsig xp xp' Dp Dp') as Hpp.
  pose proof (sigFst_eq k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
                FB redB isoB gSig (ers rho p) xp (ers rho p') xp' Hpp) as Hfst.
  pose proof (isoB (efst (ers rho p))
                (sigFst k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
                   FB redB isoB gSig (ers rho p) xp)
                (efst (ers rho p'))
                (sigFst k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
                   FB redB isoB gSig (ers rho p') xp') Hfst) as Pfam.
  pose proof (i_snd rho A B p' k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                (ers rho p') xp' eq_refl DFA DB Dp') as Dsnd'.
  pose proof (i_conv rho (snd A B p') k _ _ _ _ _ _ Pfam Dsnd') as Dsnd.
  (* the type of the conclusion, and its family *)
  pose proof (i_fst rho A B p k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  assert (E : ers (ext rho FA (efst (ers rho p))
                     (sigFst k (ers rho A) B0 FA
                        (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                        (ers rho p) xp)) B
              = ers rho (B [(fst A B p)..]))
    by exact (eq_sym (ers_sub1 rho B (fst A B p) FA _)).
  pose proof (isubst_ITy rho (fst A B p) k (ers rho A) FA (efst (ers rho p)) _
                eq_refl Dfst B k _ _
                (DB (efst (ers rho p))
                   (sigFst k (ers rho A) B0 FA
                      (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                      (ers rho p) xp))) as DBsub.
  pose proof (ITy_cast rho (B [(fst A B p)..]) k _ _ E _ DBsub) as DBc.
  assert (Hfun : FunTm G (B [(fst A B p)..])).
  { destruct (ty_subst1 G A B (univ k) (fst A B p) dB
                (t_fst G A B p k dA dB dp)) as [d].
    exact (FunTm_of_ty G (B [(fst A B p)..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [(fst A B p)..]) k
                (ers rho (B [(fst A B p)..])) (famCast E _) k'
                (ers rho (B [(fst A B p)..])) F DBc DBs) as Ek; subst k'.
  refine (itot_move G (snd A B p') (B [(fst A B p)..]) Hfun W rho Hrho k F
            (famCast E _) DBs DBc _ _).
  refine (ITm_cast rho (snd A B p') k _ _ E _ _ _ _).
  exact Dsnd.
Qed.

Lemma isem_snd G A B p p' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B)) (dp' : ty G p' (sig_ A B))
  (cp : cv G p p' (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) (IHp' : ITot G p' (sig_ A B))
  (IHc : IRel G p p' (sig_ A B)) :
  ISem G (snd A B p) (snd A B p') (B [(fst A B p)..]).
Proof.
  split;
    [split; [exact (itot_snd G A B p k W dA dB dp IHA IHB IHp)
            | exact (itot_snd' G A B p p' k W dA dB dp dp' IHA IHB IHp IHp' IHc)] |].
  intros rho Hrho k' F DBs x y Dx Dy.
  pose proof (itm_inv rho (snd A B p) k' (ers rho (B [(fst A B p)..])) F
                (ers rho (snd A B p)) x Dx) as E.
  pose proof (itm_inv rho (snd A B p') k' (ers rho (B [(fst A B p)..])) F
                (ers rho (snd A B p')) y Dy) as E'.
  destruct k' as [| k0]; cbn [TmInv] in E, E'.
  - pose proof (LCv_of_cv G (snd A B p) (snd A B p') (B [(fst A B p)..])
                  (c_snd G A B p p' k dA dB dp dp' cp) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hrel.
    destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
    exact (isem_snd_core G A B p p' k W dA dB IHc rho Hrho 0 _ F x y E E').
  - exact (isem_snd_core G A B p p' k W dA dB IHc rho Hrho (S k0) _ F x y E E').
Qed.

(* ---- application ---- *)

(* the right-hand subject at the LEFT-hand type, as for the second
   projection: the codomain instances at the two arguments are isomorphic
   because the arguments are related. *)
Lemma itot_app' G A B f' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df' : ty G f' (pi A B)) (du : ty G u A)
  (du' : ty G u' A)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHf' : ITot G f' (pi A B)) (IHu : ITot G u A) (IHu' : ITot G u' A)
  (IHcu : IRel G u u' A) : ITot G (app A B f' u') (B [u..]).
Proof.
  intros rho Hrho k' F DBu.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gPi := LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho
                 (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_pi rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                eq_refl DFA DB) as Dpi.
  destruct (IHf' rho Hrho k
              (piFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gPi) Dpi) as [xf Df].
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  destruct (IHu' rho Hrho k FA DFA) as [xu' Du'].
  pose proof (IHcu rho Hrho k FA DFA xu xu' Du Du') as Huu.
  pose proof (isoB (ers rho u) xu (ers rho u') xu' Huu) as Pfam.
  pose proof (i_app rho A B f' u' k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                (ers rho f') xf (ers rho u') xu' eq_refl DFA DB Df Du') as Dap'.
  pose proof (i_conv rho (app A B f' u') k _ _ _ _ _ _ Pfam Dap') as Dap.
  (* the type of the conclusion *)
  pose proof (isubst_ITy rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                B k (ers (ext rho FA (ers rho u) xu) B) (FB (ers rho u) xu)
                (DB (ers rho u) xu)) as DBsub.
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  pose proof (ITy_cast rho (B [u..]) k _ _ E (FB (ers rho u) xu) DBsub) as DBc.
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (univ k) u dB du) as [d].
    exact (FunTm_of_ty G (B [u..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [u..]) k (ers rho (B [u..]))
                (famCast E (FB (ers rho u) xu)) k' (ers rho (B [u..])) F DBc DBu)
    as Ek; subst k'.
  refine (itot_move G (app A B f' u') (B [u..]) Hfun W rho Hrho k F
            (famCast E (FB (ers rho u) xu)) DBu DBc _ _).
  refine (ITm_cast rho (app A B f' u') k _ _ E (FB (ers rho u) xu) _ _ _).
  exact Dap.
Qed.

Lemma isem_app_core G A B f f' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k))
  (IHcf : IRel G f f' (pi A B)) (IHcu : IRel G u u' A)
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : AppVal rho A B f u k' Sy F (ers rho (app A B f u)) x)
  (E' : AppVal rho A B f' u' k' Sy F (ers rho (app A B f' u')) y) :
  kEqAt F (ers rho (app A B f u)) x (ers rho (app A B f' u')) y.
Proof.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi
    [wf [xf [wa [xa [[[[[Ep DA] DB] Df] Da] Hv]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi'
    [wf' [xf' [wa' [xa' [[[[[Ep' DA'] DB'] Df'] Da'] Hv']]]]]]]]]]]]].
  pose proof (ity_pi rho A B k' wA FA B0 wB FB redB isoB gPi Ep DA DB) as Dpi.
  pose proof (ity_pi rho A B k' wA' FA' B0' wB' FB' redB' isoB' gPi' Ep' DA' DB')
    as Dpi'.
  pose proof (FunTm_of_ty G (pi A B) k (t_pi G A B k dA dB)) as fPi.
  pose proof (ity_same_iso' G (pi A B) fPi rho W Hrho k' _ _ _ _ Dpi Dpi') as Ppi.
  pose proof (ity_same_iso' G A (FunTm_of_ty G A k dA)
                rho W Hrho k' _ FA _ FA' DA DA') as QA.
  pose proof (kRel_of_IRel' G f f' (pi A B) IHcf fPi W rho Hrho k' _ _ _ _
                Dpi Dpi' _ xf _ xf' Df Df') as Hxf.
  pose proof (kRel_of_IRel' G u u' A IHcu
                (FunTm_of_ty G A k dA) W rho Hrho k'
                _ FA _ FA' DA DA' _ xa _ xa' Da Da') as Hxa.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  eapply kRel_trans;
    [ apply (piApp_to k' wA B0 FA wB FB redB isoB gPi
               wA' B0' FA' wB' FB' redB' isoB' gPi' Ppi QA wf xf
               (proj2 (kRel_same _ _ _ _ _) (kRel_refl _ wf xf)) wa xa) |].
  apply (piApp_eq k' wA' B0' FA' wB' FB' redB' isoB' gPi');
    [ exact (kRel_at _ _ Ppi wf xf wf' xf' Hxf)
    | exact (kRel_at _ _ QA wa xa wa' xa' Hxa) ].
Qed.

Lemma isem_app G A B f f' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df : ty G f (pi A B)) (df' : ty G f' (pi A B))
  (cf : cv G f f' (pi A B)) (du : ty G u A) (du' : ty G u' A) (cu : cv G u u' A)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHf : ITot G f (pi A B)) (IHf' : ITot G f' (pi A B))
  (IHcf : IRel G f f' (pi A B))
  (IHu : ITot G u A) (IHu' : ITot G u' A) (IHcu : IRel G u u' A) :
  ISem G (app A B f u) (app A B f' u') (B [u..]).
Proof.
  split;
    [split; [exact (itot_app G A B f u k W dA dB df du IHA IHB IHf IHu)
            | exact (itot_app' G A B f' u u' k W dA dB df' du du'
                       IHA IHB IHf' IHu IHu' IHcu)] |].
  intros rho Hrho k' F DBu x y Dx Dy.
  pose proof (itm_inv rho (app A B f u) k' (ers rho (B [u..])) F
                (ers rho (app A B f u)) x Dx) as E.
  pose proof (itm_inv rho (app A B f' u') k' (ers rho (B [u..])) F
                (ers rho (app A B f' u')) y Dy) as E'.
  destruct k' as [| k0]; cbn [TmInv] in E, E'.
  - pose proof (LCv_of_cv G (app A B f u) (app A B f' u') (B [u..])
                  (c_app G A B f f' u u' k dA dB df df' cf du du' cu) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hrel.
    destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
    exact (isem_app_core G A B f f' u u' k W dA dB IHcf IHcu rho Hrho 0 _ F x y E E').
  - exact (isem_app_core G A B f f' u u' k W dA dB IHcf IHcu rho Hrho (S k0) _ F x y
             E E').
Qed.

(* ---- the pair ---- *)

(* The right-hand pair.  Its second component is typed at `B [t..]`, the
   LEFT-hand instance -- the rule is stated that way on purpose -- so the
   value has to be moved to the codomain instance at t', along the
   isomorphism the relatedness of t and t' provides.  Its layer-1 goodness is
   read off the conversion the rule concludes. *)
Lemma itot_pair' G A B t t' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (dt' : ty G t' A)
  (ct : cv G t t' A) (du : ty G u (B [t..])) (du' : ty G u' (B [t..]))
  (cu : cv G u u' (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHt' : ITot G t' A) (IHu' : ITot G u' (B [t..]))
  (IHct : IRel G t t' A) : ITot G (pair A B t' u') (sig_ A B).
Proof.
  intros rho Hrho k' F Dsg.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                  (EnvRelOf_selfE G rho W Hrho)).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHt rho Hrho k FA DFA) as [xt Dt].
  destruct (IHt' rho Hrho k FA DFA) as [xt' Dt'].
  pose proof (IHct rho Hrho k FA DFA xt xt' Dt Dt') as Htt.
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t k (ers rho A) FA (ers rho t) xt eq_refl Dt
                B k _ (FB (ers rho t) xt) (DB (ers rho t) xt)) as DBsub.
  destruct (IHu' rho Hrho k (famCast E (FB (ers rho t) xt))
              (ITy_cast rho (B [t..]) k _ _ E _ DBsub)) as [y0 Dy0].
  destruct (ITm_uncast rho u' k _ _ E (FB (ers rho t) xt) _ _ Dy0) as [ya Dya].
  pose proof (isoB (ers rho t') xt' (ers rho t) xt (kEqAt_sym FA _ _ _ _ Htt))
    as Pfam.
  pose proof (i_conv rho u' k _ _ _ _ _ _ Pfam Dya) as Dya'.
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t') (ers rho u'))).
  { pose proof (LCv_of_cv G (pair A B t u) (pair A B t' u') (sig_ A B)
                  (c_pair G A B t t' u u' k dA dB dt dt' ct du du' cu) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hpr.
    eapply Rel_trans; [apply Rel_sym; exact Hpr | exact Hpr]. }
  pose proof (ity_lvl rho rho eq_refl (sig_ A B) k (ers rho (sig_ A B))
                (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                   redB isoB gSig) k' (ers rho (sig_ A B)) F Dsig Dsg) as Ek;
    subst k'.
  refine (itot_move G (pair A B t' u') (sig_ A B)
            (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) W rho Hrho k F
            (sigFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
               redB isoB gSig) Dsg Dsig _ _).
  exact (i_pair rho A B t' u' k (ers rho A) FA B0
           (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gSig
           (ers rho t') xt' (ers rho u') _ g eq_refl DFA DB Dt' Dya').
Qed.

Lemma isem_pair_core G A B t t' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (dt' : ty G t' A)
  (ct : cv G t t' A) (du : ty G u (B [t..])) (du' : ty G u' (B [t..]))
  (cu : cv G u u' (B [t..]))
  (IHct : IRel G t t' A) (IHcu : IRel G u u' (B [t..]))
  (IHu' : ITot G u' (B [t..]))
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : PairVal rho A B t u k' Sy F (ers rho (pair A B t u)) x)
  (E' : PairVal rho A B t' u' k' Sy F (ers rho (pair A B t' u')) y) :
  kEqAt F (ers rho (pair A B t u)) x (ers rho (pair A B t' u')) y.
Proof.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gSig [wt [xt [wa [xa [g
    [[[[[Ep DA] DB] Dt] Da] Hv]]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gSig' [wt' [xt' [wa' [xa' [g'
    [[[[[Ep' DA'] DB'] Dt'] Da'] Hv']]]]]]]]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA').
  assert (Ewt : wt = ers rho t) by exact (ers_of_ITm _ _ _ _ _ _ _ Dt).
  assert (Ewt' : wt' = ers rho t') by exact (ers_of_ITm _ _ _ _ _ _ _ Dt').
  assert (Ewa : wa = ers rho u) by exact (ers_of_ITm _ _ _ _ _ _ _ Da).
  assert (Ewa' : wa' = ers rho u') by exact (ers_of_ITm _ _ _ _ _ _ _ Da').
  subst wA wA' wt wt' wa wa'.
  pose proof (ity_sig rho A B k' _ FA B0 wB FB redB isoB gSig Ep DA DB) as Dsig.
  pose proof (ity_sig rho A B k' _ FA' B0' wB' FB' redB' isoB' gSig' Ep' DA' DB')
    as Dsig'.
  pose proof (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) as fS.
  pose proof (ity_same_iso' G (sig_ A B) fS rho W Hrho k' _ _ _ _ Dsig Dsig')
    as Psig.
  pose proof (ity_same_iso' G A (FunTm_of_ty G A k dA) rho W Hrho k' _ FA _ FA'
                DA DA') as QA.
  pose proof (kRel_of_IRel' G t t' A IHct (FunTm_of_ty G A k dA) W rho Hrho k'
                _ FA _ FA' DA DA' _ xt _ xt' Dt Dt') as A3.
  (* the second components, in the two extended environments *)
  pose proof (EnvRelOf_ext G rho rho A k' FA FA' _ xt _ xt'
                (EnvRelOf_selfE G rho W Hrho) A3) as HEx.
  assert (EB : wB (ers rho t) xt = ers (ext rho FA (ers rho t) xt) B)
    by exact (ers_of_ITy _ _ _ _ _ (DB _ xt)).
  assert (EB' : wB' (ers rho t') xt' = ers (ext rho FA' (ers rho t') xt') B)
    by exact (ers_of_ITy _ _ _ _ _ (DB' _ xt')).
  assert (Htb : tyeq (wB (ers rho t) xt) (wB' (ers rho t') xt'))
    by (rewrite EB, EB'; exact (LTy_of_ty (A :: G) B k dB _ _ HEx)).
  assert (QB : iso (kAt (FB (ers rho t) xt)) (kAt (FB' (ers rho t') xt')))
    by exact (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (univ k) dB) _ _ HEx k'
                _ (FB _ xt) _ (FB' _ xt') (DB _ xt) (DB' _ xt')
                (eqty_at_lvl k' _ _ (uf_ty (FB _ xt)) (uf_ty (FB' _ xt')) Htb)).
  (* u and u' are related at the UNPRIMED codomain instance, and u' travels
     from there to the primed one by its own functionality *)
  pose proof (isubst_ITy rho t k' _ FA (ers rho t) xt eq_refl Dt
                B k' _ (FB _ xt) (DB _ xt)) as D1.
  assert (Eb : wB (ers rho t) xt = ers rho (B [t..]))
    by (rewrite EB; exact (eq_sym (ers_sub1 rho B t FA xt))).
  destruct (IHu' rho Hrho k' (famCast Eb (FB _ xt))
              (ITy_cast rho (B [t..]) k' _ _ Eb _ D1)) as [y0 Dy0].
  destruct (ITm_uncast rho u' k' _ _ Eb (FB _ xt) _ _ Dy0) as [ya Dya].
  assert (fBt : FunTm G (B [t..])).
  { destruct (ty_subst1 G A B (univ k) t dB dt) as [d].
    exact (FunTm_of_ty G (B [t..]) k d). }
  pose proof (kRel_of_IRel' G u u' (B [t..]) IHcu fBt W rho Hrho k'
                _ (FB _ xt) _ (FB _ xt) D1 D1 _ xa _ ya Da Dya) as Hb1.
  assert (Hru' : Rel (wB' (ers rho t') xt') (ers rho u') (ers rho u')).
  { apply (Rel_tyeq (wB (ers rho t) xt) (wB' (ers rho t') xt')); [exact Htb |].
    rewrite Eb.
    exact (LTm_of_ty G u' (B [t..]) du' rho rho
             (EnvRelOf_selfE G rho W Hrho)). }
  pose proof (funtm G u' (B [t..]) du' rho rho (EnvRelOf_selfE G rho W Hrho) k'
                _ (FB _ xt) _ ya Dya _ (FB' _ xt') _ xa' Da' QB Hru') as Hb2.
  assert (B3 : kRel (FB (ers rho t) xt) (FB' (ers rho t') xt')
                 (ers rho u) xa (ers rho u') xa')
    by (eapply kRel_trans; [exact Hb1 | exact Hb2]).
  (* the layer-1 facts about the two pairs *)
  assert (Hty : tyeq (esig (ers rho A) B0) (esig (ers rho A) B0'))
    by (rewrite Ep, Ep';
        exact (LTy_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho
                 (EnvRelOf_selfE G rho W Hrho))).
  assert (Hrp : Rel (esig (ers rho A) B0')
                  (epair (ers rho t) (ers rho u)) (epair (ers rho t') (ers rho u'))).
  { apply (Rel_tyeq (ers rho (sig_ A B)) (esig (ers rho A) B0'));
      [ rewrite <- Ep; exact Hty
      | exact (LCv_of_cv G (pair A B t u) (pair A B t' u') (sig_ A B)
                 (c_pair G A B t t' u u' k dA dB dt dt' ct du du' cu) rho rho
                 (EnvRelOf_selfE G rho W Hrho)) ]. }
  assert (gT' : Good_ty (esig (ers rho A) B0')) by (exists k'; exact gSig').
  assert (Hsame : Rel (esig (ers rho A) B0')
                    (epair (ers rho t) (ers rho u)) (epair (ers rho t) (ers rho u)))
    by (eapply Rel_trans; [exact Hrp | apply Rel_sym; exact Hrp]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hsame) as gr.
  assert (g2 : Good (esig (ers rho A) B0')
                 (epair (efst (epair (ers rho t) (ers rho u)))
                        (esnd (epair (ers rho t) (ers rho u)))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (sig_eta_rel _ _ _ _ _ gT' (ev_sig _ _) Hrp) as Hc.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exact Hv | exact Hv' |].
  exists Psig.
  eapply kEqAt_trans;
    [ apply kEqAt_sym;
      exact (sigPair_surj k' _ B0' FA' wB' FB' redB' isoB' gSig' _
               (ctoK _ _ Psig _ (sigPair k' _ B0 FA wB FB redB isoB gSig _ _ xt xa g))
               g2 gr) |].
  apply (sigPair_eq k' _ B0' FA' wB' FB' redB' isoB' gSig'); [exact Hc | |].
  - apply (proj2 (kRel_same FA' _ _ _ _)).
    eapply kRel_trans;
      [ apply kRel_sym;
        apply (sigFst_to k' _ B0 FA wB FB redB isoB gSig
                 _ B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same FA _ _ _ _));
        apply (sigFst_pair k' _ B0 FA wB FB redB isoB gSig)
      | exact A3 ].
  - eapply kRel_trans;
      [ apply kRel_sym;
        apply (sigSnd_to k' _ B0 FA wB FB redB isoB gSig
                 _ B0' FA' wB' FB' redB' isoB' gSig' Psig) |].
    eapply kRel_trans;
      [ apply (sigSnd_pair k' _ B0 FA wB FB redB isoB gSig) | exact B3 ].
Qed.

Lemma isem_pair G A B t t' u u' k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (dt' : ty G t' A)
  (ct : cv G t t' A) (du : ty G u (B [t..])) (du' : ty G u' (B [t..]))
  (cu : cv G u u' (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHt' : ITot G t' A) (IHct : IRel G t t' A)
  (IHu : ITot G u (B [t..])) (IHu' : ITot G u' (B [t..]))
  (IHcu : IRel G u u' (B [t..])) :
  ISem G (pair A B t u) (pair A B t' u') (sig_ A B).
Proof.
  split;
    [split; [exact (itot_pair G A B t u k W dA dB dt du IHA IHB IHt IHu)
            | exact (itot_pair' G A B t t' u u' k W dA dB dt dt' ct du du' cu
                       IHA IHB IHt IHt' IHu' IHct)] |].
  intros rho Hrho k' F Dsg x y Dx Dy.
  pose proof (itm_inv rho (pair A B t u) k' (ers rho (sig_ A B)) F
                (ers rho (pair A B t u)) x Dx) as E.
  pose proof (itm_inv rho (pair A B t' u') k' (ers rho (sig_ A B)) F
                (ers rho (pair A B t' u')) y Dy) as E'.
  destruct k' as [| k0]; cbn [TmInv] in E, E'.
  - pose proof (LCv_of_cv G (pair A B t u) (pair A B t' u') (sig_ A B)
                  (c_pair G A B t t' u u' k dA dB dt dt' ct du du' cu) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hrel.
    destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
    exact (isem_pair_core G A B t t' u u' k W dA dB dt dt' ct du du' cu
             IHct IHcu IHu' rho Hrho 0 _ F x y E E').
  - exact (isem_pair_core G A B t t' u u' k W dA dB dt dt' ct du du' cu
             IHct IHcu IHu' rho Hrho (S k0) _ F x y E E').
Qed.

(* ---- the universal quantifier.  Its type is `prop`, so the two values are
     propositions and what has to be shown is that they are logically
     equivalent: the two directions are the same statement about a related
     pair of arguments, once each way, and the bodies are compared in the two
     steps isem_pi uses for the codomains. ---- *)
Lemma isem_all G A A' p p' k (W : wfc G) (dA : ty G A (univ k))
  (dp : ty (A :: G) p prop) (dA' : ty G A' (univ k)) (dp' : ty (A' :: G) p' prop)
  (cA : cv G A A' (univ k)) (cp : cv (A :: G) p p' prop)
  (IHA : ITot G A (univ k)) (IHp : ITot (A :: G) p prop)
  (IHA' : ITot G A' (univ k)) (IHp' : ITot (A' :: G) p' prop)
  (IHcA : IRel G A A' (univ k)) (IHcp : IRel (A :: G) p p' prop) :
  ISem G (all A p) (all A' p') prop.
Proof.
  pose proof (w_cons G A k W dA) as WA.
  split;
    [split; [exact (itot_all G A p k W dA dp IHA IHp)
            | exact (itot_all G A' p' k W dA' dp' IHA' IHp')] |].
  intros rho Hrho k' F DP x y Dx Dy.
  pose proof (ity_lvl_dec rho prop k' (ers rho prop) F DP) as El;
    cbn [LvlDec] in El; subst k'.
  pose proof (LCv_of_cv G (all A p) (all A' p') prop
                (c_all G A A' p p' k dA dp dA' dp' cA cp) rho rho
                (EnvRelOf_selfE G rho W Hrho)) as Hrel.
  pose proof (itm_inv rho (all A p) 0 (ers rho prop) F (ers rho (all A p)) x Dx)
    as E.
  pose proof (itm_inv rho (all A' p') 0 (ers rho prop) F (ers rho (all A' p')) y Dy)
    as E'.
  cbn [TmInv] in E, E'.
  destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
  destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
  cbn [TmShape AllVal] in E, E'.
  destruct E as [kA [wA [FA [wp [xp [wv [g [[DA Dp] Hv]]]]]]]].
  destruct E' as [kA' [wA' [FA' [wp' [xp' [wv' [g' [[DA' Dp'] Hv']]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  (* both domains are interpreted at the level their typing gives *)
  destruct (ityT_of_ITot G A k IHA rho Hrho) as [FAc DAc].
  pose proof (ity_lvl rho rho eq_refl A k (ers rho A) FAc kA (ers rho A) FA DAc DA)
    as EkA; subst kA.
  destruct (ityT_of_ITot G A' k IHA' rho Hrho) as [FAc' DAc'].
  pose proof (ity_lvl rho rho eq_refl A' k (ers rho A') FAc' kA' (ers rho A') FA'
                DAc' DA') as EkA'; subst kA'.
  assert (QA : iso (kAt FA) (kAt FA'))
    by exact (iso_of_IRel_at' G A A' k IHcA rho Hrho _ FA DA _ FA' DA').
  assert (HtyA : tyeq (ers rho A) (ers rho A'))
    by (exists k; exact (LCvK_of_cv G A A' k cA rho rho
                           (EnvRelOf_selfE G rho W Hrho))).
  (* one direction of the equivalence, for an arbitrary related pair *)
  assert (Key : forall u (z : kElAt FA u) u2 (z2 : kElAt FA' u2),
             kRel FA FA' u z u2 z2 -> (propVal (xp u z) <-> propVal (xp' u2 z2))).
  { intros u z u2 z2 Hz.
    pose proof (EnvITy_ext G rho A k FA DA u z Hrho) as HExA.
    pose proof (EnvITy_ext_iso G rho A' k (ers rho A) FA FA' DA' QA u z Hrho)
      as HExA'.
    destruct (IHp' (ext rho FA u z) HExA' 0 (propFam 0)
                (ity_prop (ext rho FA u z) (ers (ext rho FA u z) prop) eq_refl))
      as [w0 Dw0].
    pose proof (kRel_of_IRel' (A :: G) p p' prop IHcp
                  (FunTm_of_ty (A :: G) prop 0 (t_prop (A :: G) WA)) WA
                  (ext rho FA u z) HExA 0 eprop (propFam 0) eprop (propFam 0)
                  (ity_prop _ _ eq_refl) (ity_prop _ _ eq_refl)
                  _ (xp u z) _ w0 (Dp u z) Dw0) as H1.
    assert (HEr : EnvRelOf (A' :: G) (ext rho FA u z) (ext rho FA' u2 z2)).
    { apply (EnvRelOf_ext_ty G rho rho A' k (ers rho A) (ers rho A')
               FA FA' u z u2 z2 (EnvRelOf_selfE G rho W Hrho) HtyA);
        [ exists k; exact (uf_ty FA') | exact Hz ]. }
    assert (Ew' : wp' u2 z2 = ers (ext rho FA' u2 z2) p')
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dp' u2 z2)).
    assert (Hr2 : Rel eprop (ers (ext rho FA u z) p') (wp' u2 z2))
      by (rewrite Ew'; exact (LTm_of_ty (A' :: G) p' prop dp' _ _ HEr)).
    pose proof (funtm (A' :: G) p' prop dp' _ _ HEr 0 eprop (propFam 0) _ w0 Dw0
                  eprop (propFam 0) _ (xp' u2 z2) (Dp' u2 z2)
                  (iso_self (propFam 0)) Hr2) as H2.
    exact (proj1 (proj1 (propEq_iff (xp u z) (xp' u2 z2))
                    (proj2 (kRel_same (propFam 0) _ _ _ _)
                       (kRel_trans _ _ _ _ _ _ _ _ _ H1 H2)))). }
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hw : Rel eprop (ers rho (all A p)) wv)
    by exact (proj2 (proj1 (propEq_iff _ _) HQ)).
  assert (Hw' : Rel eprop (ers rho (all A' p')) wv')
    by exact (proj2 (proj1 (propEq_iff _ _) HQ')).
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  apply (proj1 (kRel_same (propFam 0) _ _ _ _)).
  apply propEq_iff; split.
  - cbn [propVal propElem proj1_sig Datatypes.fst]; split.
    + intros H u2 z2.
      exact (proj1 (Key u2 (moveTo FA' FA (iso_sym _ _ QA) u2 z2 u2 (reds_refl u2))
                        u2 z2
                     (kRel_sym _ _ _ _ _ _
                        (moveTo_rel FA' FA (iso_sym _ _ QA) u2 z2 u2
                           (reds_refl u2))))
               (H u2 _)).
    + intros H u z.
      exact (proj2 (Key u z u (moveTo FA FA' QA u z u (reds_refl u))
                     (moveTo_rel FA FA' QA u z u (reds_refl u)))
               (H u _)).
  - eapply Rel_trans; [apply Rel_sym; exact Hw |].
    eapply Rel_trans; [exact Hrel | exact Hw'].
Qed.

(* ---- the lambda.  The right-hand subject is typed at `pi A' B'` and the
     rule concludes at `pi A B`, so its totality is the conversion of the two
     -- which is the Pi-congruence, symmetrised.  The bodies are compared in
     the same two steps as the codomains: t against t' in the A-extended
     environment, then t' against itself across the two extensions. ---- *)
Lemma isem_lam_core G A A' B B' t t' k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (dA' : ty G A' (univ k)) (dB' : ty (A' :: G) B' (univ k))
  (cA : cv G A A' (univ k)) (cB : cv (A :: G) B B' (univ k))
  (dt : ty (A :: G) t B) (dt' : ty (A' :: G) t' B') (ct : cv (A :: G) t t' B)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHA' : ITot G A' (univ k)) (IHB' : ITot (A' :: G) B' (univ k))
  (IHcA : IRel G A A' (univ k)) (IHcB : IRel (A :: G) B B' (univ k))
  (IHt2 : ITot (A :: G) t' B) (IHct : IRel (A :: G) t t' B)
  (IHcPi : IRel G (pi A B) (pi A' B') (univ k))
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : LamVal rho A B t k' Sy F (ers rho (lam A B t)) x)
  (E' : LamVal rho A' B' t' k' Sy F (ers rho (lam A' B' t')) y)
  (Hrel : Rel Sy (ers rho (lam A B t)) (ers rho (lam A' B' t'))) :
  kEqAt F (ers rho (lam A B t)) x (ers rho (lam A' B' t')) y.
Proof.
  pose proof (w_cons G A k W dA) as WA.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct E as [wA [FA [B0 [wB [FB [redB [isoB [gPi [wv [xv [wt [xt
    [[[[[Ep DA] DB] Dt] Hb] Hv]]]]]]]]]]]]].
  destruct E' as [wA' [FA' [B0' [wB' [FB' [redB' [isoB' [gPi' [wv' [xv' [wt' [xt'
    [[[[[Ep' DA'] DB'] Dt'] Hb'] Hv']]]]]]]]]]]]].
  assert (EA : wA = ers rho A) by exact (ers_of_ITy _ _ _ _ _ DA).
  assert (EA' : wA' = ers rho A') by exact (ers_of_ITy _ _ _ _ _ DA').
  subst wA wA'.
  pose proof (ity_pi rho A B k' _ FA B0 wB FB redB isoB gPi Ep DA DB) as Dpi.
  pose proof (ity_pi rho A' B' k' _ FA' B0' wB' FB' redB' isoB' gPi' Ep' DA' DB')
    as Dpi'.
  (* the shape's level is the typing's *)
  destruct (ityT_of_ITot G (pi A B) k (itot_pi G A B k W dA dB IHA IHB) rho Hrho)
    as [Fpic Dpic].
  pose proof (ity_lvl rho rho eq_refl (pi A B) k _ Fpic k' _ _ Dpic Dpi) as Ek;
    subst k'.
  assert (Ppi : iso (kAt (piFam k (ers rho A) B0 FA wB FB redB isoB gPi))
                    (kAt (piFam k (ers rho A') B0' FA' wB' FB' redB' isoB' gPi')))
    by exact (iso_of_IRel_at' G (pi A B) (pi A' B') k IHcPi rho Hrho _ _ Dpi _ _ Dpi').
  assert (QA : iso (kAt FA) (kAt FA'))
    by exact (iso_of_IRel_at' G A A' k IHcA rho Hrho _ FA DA _ FA' DA').
  assert (HtyA : tyeq (ers rho A) (ers rho A'))
    by (exists k; exact (LCvK_of_cv G A A' k cA rho rho HEself)).
  assert (Hty : tyeq (epi (ers rho A) B0) (epi (ers rho A') B0'))
    by (rewrite Ep, Ep'; exists k;
        exact (LCvK_of_cv G (pi A B) (pi A' B') k
                 (c_pi G A A' B B' k dA dB dA' dB' cA cB) rho rho HEself)).
  destruct Hv as [Q HQ]; destruct Hv' as [Q' HQ'].
  assert (Hrv : Rel (epi (ers rho A') B0') wv wv').
  { eapply Rel_trans;
      [ apply Rel_sym;
        exact (Rel_tyeq _ _ _ _ Hty
                 (kRel_rel _ _ _ _ _ _ (proj1 (kRel_same _ _ _ _ _) HQ))) |].
    eapply Rel_trans;
      [ exact (Rel_tyeq Sy (epi (ers rho A') B0') _ _
                 (iso_ty F (piFam k (ers rho A') B0' FA' wB' FB' redB' isoB' gPi')
                    Q') Hrel)
      | exact (kRel_rel _ _ _ _ _ _ (proj1 (kRel_same _ _ _ _ _) HQ')) ]. }
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_of_IsVal2; [exists Q; exact HQ | exists Q'; exact HQ' |].
  exists Ppi.
  apply (piEq_of k _ B0' FA' wB' FB' redB' isoB' gPi'); [exact Hrv |].
  intros v y1 v' y1' Hyy.
  set (y0 := moveTo FA' FA (iso_sym _ _ QA) v y1 v (reds_refl v)).
  assert (Hy0 : kRel FA FA' v y0 v y1)
    by (apply kRel_sym;
        apply (moveTo_rel FA' FA (iso_sym _ _ QA) v y1 v (reds_refl v))).
  assert (Hy0' : kRel FA FA' v y0 v' y1').
  { eapply kRel_trans; [exact Hy0 |].
    apply (proj1 (kRel_same FA' _ _ _ _)); exact Hyy. }
  pose proof (EnvITy_ext G rho A k FA DA v y0 Hrho) as HExA.
  pose proof (EnvITy_ext_iso G rho A' k (ers rho A) FA FA' DA' QA v y0 Hrho)
    as HExA'.
  assert (HEr : EnvRelOf (A' :: G) (ext rho FA v y0) (ext rho FA' v' y1')).
  { apply (EnvRelOf_ext_ty G rho rho A' k (ers rho A) (ers rho A')
             FA FA' v y0 v' y1' HEself HtyA);
      [ exists k; exact (uf_ty FA') | exact Hy0' ]. }
  (* the codomains *)
  destruct (ityT_of_ITot (A' :: G) B' k IHB' (ext rho FA v y0) HExA') as [FBm DBm].
  assert (Eb' : wB' v' y1' = ers (ext rho FA' v' y1') B')
    by exact (ers_of_ITy _ _ _ _ _ (DB' v' y1')).
  assert (QB : iso (kAt (FB v y0)) (kAt (FB' v' y1'))).
  { eapply iso_trans;
      [ exact (iso_of_IRel_at' (A :: G) B B' k IHcB (ext rho FA v y0) HExA
                 _ (FB v y0) (DB v y0) _ FBm DBm) |].
    refine (FunTy_of_FunTm (A' :: G) B' (funtm (A' :: G) B' (univ k) dB')
              _ _ HEr k _ FBm _ (FB' v' y1') DBm (DB' v' y1') _).
    rewrite Eb'; exact (LTyK_of_ty (A' :: G) B' k dB' _ _ HEr). }
  (* the bodies *)
  assert (EB : wB v y0 = ers (ext rho FA v y0) B)
    by exact (ers_of_ITy _ _ _ _ _ (DB v y0)).
  destruct (IHt2 (ext rho FA v y0) HExA k (famCast EB (FB v y0))
              (ITy_cast (ext rho FA v y0) B k _ _ EB _ (DB v y0))) as [z0 Dz0].
  destruct (ITm_uncast (ext rho FA v y0) t' k _ _ EB (FB v y0) _ _ Dz0) as [z Dz].
  pose proof (kRel_of_IRel' (A :: G) t t' B IHct (FunTm_of_ty (A :: G) B k dB) WA
                (ext rho FA v y0) HExA k _ (FB v y0) _ (FB v y0)
                (DB v y0) (DB v y0) _ (xt v y0) _ z (Dt v y0) Dz) as Hb1.
  assert (Hrb : Rel (wB' v' y1') (ers (ext rho FA v y0) t') (wt' v' y1')).
  { assert (Et' : wt' v' y1' = ers (ext rho FA' v' y1') t')
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Dt' v' y1')).
    rewrite Eb', Et'.
    apply (Rel_tyeq (ers (ext rho FA v y0) B') (ers (ext rho FA' v' y1') B'));
      [ exact (LTy_of_ty (A' :: G) B' k dB' _ _ HEr)
      | exact (LTm_of_ty (A' :: G) t' B' dt' _ _ HEr) ]. }
  pose proof (funtm (A' :: G) t' B' dt' _ _ HEr k _ (FB v y0) _ z Dz
                _ (FB' v' y1') _ (xt' v' y1') (Dt' v' y1') QB Hrb) as Hb2.
  assert (Hbody : kRel (FB v y0) (FB' v' y1')
                    (wt v y0) (xt v y0) (wt' v' y1') (xt' v' y1'))
    by (eapply kRel_trans; [exact Hb1 | exact Hb2]).
  (* and the five legs *)
  eapply kRel_trans;
    [ apply kRel_sym;
      apply (piApp_eq k _ B0' FA' wB' FB' redB' isoB' gPi' wv
               (ctoK _ _ Ppi wv xv) wv (ctoK _ _ Ppi wv xv) v
               (ctoK _ _ QA v y0) v y1);
      [ apply (proj2 (kRel_same _ _ _ _ _)); apply kRel_refl
      | exact (kRel_at _ _ QA v y0 v y1 Hy0) ] |].
  eapply kRel_trans;
    [ apply kRel_sym;
      apply (piApp_to k _ B0 FA wB FB redB isoB gPi
               _ B0' FA' wB' FB' redB' isoB' gPi' Ppi QA wv xv
               (proj2 (kRel_same _ _ _ _ _) (kRel_refl _ wv xv)) v y0) |].
  eapply kRel_trans;
    [ apply (proj1 (kRel_same (FB v y0) _ _ _ _)); exact (Hb v y0) |].
  eapply kRel_trans; [ exact Hbody |].
  apply (proj1 (kRel_same (FB' v' y1') _ _ _ _)).
  apply kEqAt_sym; exact (Hb' v' y1').
Qed.

Lemma isem_lam G A A' B B' t t' k (W : wfc G)
  (dA : ty G A (univ k)) (dB : ty (A :: G) B (univ k))
  (dA' : ty G A' (univ k)) (dB' : ty (A' :: G) B' (univ k))
  (cA : cv G A A' (univ k)) (cB : cv (A :: G) B B' (univ k))
  (dt : ty (A :: G) t B) (dt' : ty (A' :: G) t' B') (ct : cv (A :: G) t t' B)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHA' : ITot G A' (univ k)) (IHB' : ITot (A' :: G) B' (univ k))
  (IHcA : IRel G A A' (univ k)) (IHcB : IRel (A :: G) B B' (univ k))
  (IHt : ITot (A :: G) t B) (IHt2 : ITot (A :: G) t' B)
  (IHt' : ITot (A' :: G) t' B') (IHct : IRel (A :: G) t t' B) :
  ISem G (lam A B t) (lam A' B' t') (pi A B).
Proof.
  pose proof (isem_pi G A A' B B' k W dA dB dA' dB' cA cB
                IHA IHB IHA' IHB' IHcA IHcB) as Hpi.
  split.
  - split; [exact (itot_lam G A B t k W dA dB dt IHA IHB IHt) |].
    exact (itot_conv G (lam A' B' t') (pi A' B') (pi A B) k W
             (t_pi G A' B' k dA' dB') (t_pi G A B k dA dB)
             (itot_lam G A' B' t' k W dA' dB' dt' IHA' IHB' IHt')
             (itot_pi G A' B' k W dA' dB' IHA' IHB')
             (itot_pi G A B k W dA dB IHA IHB)
             (Datatypes.snd (isem_sym G (pi A B) (pi A' B') (univ k) Hpi))).
  - intros rho Hrho k' F Dpi0 x y Dx Dy.
    pose proof (LCv_of_cv G (lam A B t) (lam A' B' t') (pi A B)
                  (c_lam G A A' B B' t t' k dA dB dA' dB' cA cB dt dt' ct) rho rho
                  (EnvRelOf_selfE G rho W Hrho)) as Hrel.
    pose proof (itm_inv rho (lam A B t) k' (ers rho (pi A B)) F
                  (ers rho (lam A B t)) x Dx) as E.
    pose proof (itm_inv rho (lam A' B' t') k' (ers rho (pi A B)) F
                  (ers rho (lam A' B' t')) y Dy) as E'.
    destruct k' as [| k0]; cbn [TmInv] in E, E'.
    + destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
      destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
      exact (isem_lam_core G A A' B B' t t' k W dA dB dA' dB' cA cB dt dt' ct
               IHA IHB IHA' IHB' IHcA IHcB IHt2 IHct (Datatypes.snd Hpi)
               rho Hrho 0 _ F x y E E' Hrel).
    + exact (isem_lam_core G A A' B B' t t' k W dA dB dA' dB' cA cB dt dt' ct
               IHA IHB IHA' IHB' IHcA IHcB IHt2 IHct (Datatypes.snd Hpi)
               rho Hrho (S k0) _ F x y E E' Hrel).
Qed.

(* ---- the Sigma computation rules.  Each is proved by CONSTRUCTING the
     canonical value of both sides and comparing them with the family's own
     law (sigFst_pair, sigSnd_pair, sigPair_surj); the values the statement is
     handed are compared to the constructed ones by functionality, which is
     what funtm says about two readings of one term. ---- *)

Lemma isem_fst_beta G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ISem G (fst A B (pair A B t u)) t A.
Proof.
  pose proof (t_pair G A B t u k dA dB dt du) as dpair.
  split;
    [split; [exact (itot_fst G A B (pair A B t u) k W dA dB dpair IHA IHB
                      (itot_pair G A B t u k W dA dB dt du IHA IHB IHt IHu))
            | exact IHt] |].
  intros rho Hrho k' F DA0 x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (z : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho HEself).
  destruct (IHt rho Hrho k FA DFA) as [xt Dt].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t k (ers rho A) FA (ers rho t) xt eq_refl Dt
                B k _ (FB (ers rho t) xt) (DB (ers rho t) xt)) as DBsub.
  destruct (IHu rho Hrho k (famCast E (FB (ers rho t) xt))
              (ITy_cast rho (B [t..]) k _ _ E _ DBsub)) as [xu0 Du0].
  destruct (ITm_uncast rho u k _ _ E (FB (ers rho t) xt) _ _ Du0) as [xu Du].
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair A B t u) (sig_ A B) dpair rho rho HEself).
  pose proof (i_pair rho A B t u k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (ers rho t) xt (ers rho u) xu g eq_refl DFA DB Dt Du) as Dpair.
  pose proof (i_fst rho A B (pair A B t u) k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dfst.
  pose proof (ity_lvl rho rho eq_refl A k (ers rho A) FA k' (ers rho A) F DFA DA0)
    as Ek; subst k'.
  pose proof (ity_same_iso G A (FunTm_of_ty G A k dA) rho W Hrho k F FA DA0 DFA)
    as P.
  pose proof (funtm G (fst A B (pair A B t u)) A
                (t_fst G A B (pair A B t u) k dA dB dpair) rho rho HEself k
                (ers rho A) F _ x Dx (ers rho A) FA _ _ Dfst P
                (LTm_of_ty G (fst A B (pair A B t u)) A
                   (t_fst G A B (pair A B t u) k dA dB dpair) rho rho HEself))
    as H1.
  pose proof (funtm G t A dt rho rho HEself k (ers rho A) FA _ xt Dt
                (ers rho A) F _ y Dy (iso_sym _ _ P)
                (LTm_of_ty G t A dt rho rho HEself)) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans;
    [ apply (proj1 (kRel_same FA _ _ _ _));
      exact (sigFst_pair k (ers rho A) B0 FA
               (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
               (ers rho t) (ers rho u) xt xu g)
    | exact H2 ].
Qed.

Lemma itot_snd_beta G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ITot G (snd A B (pair A B t u)) (B [t..]).
Proof.
  pose proof (t_pair G A B t u k dA dB dt du) as dpair.
  intros rho Hrho k' F DBt.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (z : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho HEself).
  destruct (IHt rho Hrho k FA DFA) as [xt Dt].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t k (ers rho A) FA (ers rho t) xt eq_refl Dt
                B k _ (FB (ers rho t) xt) (DB (ers rho t) xt)) as DBsub.
  destruct (IHu rho Hrho k (famCast E (FB (ers rho t) xt))
              (ITy_cast rho (B [t..]) k _ _ E _ DBsub)) as [xu0 Du0].
  destruct (ITm_uncast rho u k _ _ E (FB (ers rho t) xt) _ _ Du0) as [xu Du].
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair A B t u) (sig_ A B) dpair rho rho HEself).
  pose proof (i_pair rho A B t u k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (ers rho t) xt (ers rho u) xu g eq_refl DFA DB Dt Du) as Dpair.
  pose proof (i_snd rho A B (pair A B t u) k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dsnd0.
  pose proof (isoB (ers rho t) xt _
                (sigFst k (ers rho A) B0 FA
                   (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                   (epair (ers rho t) (ers rho u))
                   (sigPair k (ers rho A) B0 FA
                      (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                      (ers rho t) (ers rho u) xt xu g))
                (kEqAt_sym FA _ _ _ _
                   (sigFst_pair k (ers rho A) B0 FA
                      (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                      (ers rho t) (ers rho u) xt xu g))) as Pfam.
  pose proof (i_conv rho (snd A B (pair A B t u)) k _ _ _ _ _ _ Pfam Dsnd0) as Dsnd.
  assert (Hfun : FunTm G (B [t..])).
  { destruct (ty_subst1 G A B (univ k) t dB dt) as [d].
    exact (FunTm_of_ty G (B [t..]) k d). }
  pose proof (ITy_cast rho (B [t..]) k _ _ E _ DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [t..]) k (ers rho (B [t..]))
                (famCast E (FB (ers rho t) xt)) k' (ers rho (B [t..])) F DBc DBt)
    as Ek; subst k'.
  refine (itot_move G (snd A B (pair A B t u)) (B [t..]) Hfun W rho Hrho k F
            (famCast E (FB (ers rho t) xt)) DBt DBc _ _).
  refine (ITm_cast rho (snd A B (pair A B t u)) k _ _ E (FB (ers rho t) xt) _ _ _).
  exact Dsnd.
Qed.

Lemma isem_snd_beta G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty G t A) (du : ty G u (B [t..]))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot G t A) (IHu : ITot G u (B [t..])) :
  ISem G (snd A B (pair A B t u)) u (B [t..]).
Proof.
  pose proof (t_pair G A B t u k dA dB dt du) as dpair.
  split;
    [split; [exact (itot_snd_beta G A B t u k W dA dB dt du IHA IHB IHt IHu)
            | exact IHu] |].
  intros rho Hrho k' F DBt x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (z : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho HEself).
  destruct (IHt rho Hrho k FA DFA) as [xt Dt].
  assert (E : ers (ext rho FA (ers rho t) xt) B = ers rho (B [t..]))
    by exact (eq_sym (ers_sub1 rho B t FA xt)).
  pose proof (isubst_ITy rho t k (ers rho A) FA (ers rho t) xt eq_refl Dt
                B k _ (FB (ers rho t) xt) (DB (ers rho t) xt)) as DBsub.
  destruct (IHu rho Hrho k (famCast E (FB (ers rho t) xt))
              (ITy_cast rho (B [t..]) k _ _ E _ DBsub)) as [xu0 Du0].
  destruct (ITm_uncast rho u k _ _ E (FB (ers rho t) xt) _ _ Du0) as [xu Du].
  assert (g : Good (esig (ers rho A) B0) (epair (ers rho t) (ers rho u)))
    by exact (LTm_of_ty G (pair A B t u) (sig_ A B) dpair rho rho HEself).
  pose proof (i_pair rho A B t u k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (ers rho t) xt (ers rho u) xu g eq_refl DFA DB Dt Du) as Dpair.
  pose proof (i_snd rho A B (pair A B t u) k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (epair (ers rho t) (ers rho u)) _ eq_refl DFA DB Dpair) as Dsnd0.
  (* the level and the isomorphism to the statement's family *)
  assert (Hfun : FunTm G (B [t..])).
  { destruct (ty_subst1 G A B (univ k) t dB dt) as [d].
    exact (FunTm_of_ty G (B [t..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [t..]) k _ (FB (ers rho t) xt) k'
                (ers rho (B [t..])) F DBsub DBt) as Ek; subst k'.
  pose proof (ity_same_iso' G (B [t..]) Hfun rho W Hrho k _ F _
                (FB (ers rho t) xt) DBt DBsub) as P.
  (* the canonical second projection lives at the codomain instance the FIRST
     projection picks, which is isomorphic to the one at t *)
  pose proof (isoB (ers rho t) xt _
                (sigFst k (ers rho A) B0 FA
                   (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                   (epair (ers rho t) (ers rho u))
                   (sigPair k (ers rho A) B0 FA
                      (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                      (ers rho t) (ers rho u) xt xu g))
                (kEqAt_sym FA _ _ _ _
                   (sigFst_pair k (ers rho A) B0 FA
                      (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                      (ers rho t) (ers rho u) xt xu g))) as Pfam.
  assert (Hgs : Rel (ers (ext rho FA (ers rho t) xt) B)
                  (ers rho (snd A B (pair A B t u))) (ers rho (snd A B (pair A B t u)))).
  { rewrite E.
    pose proof (LCv_of_cv G (snd A B (pair A B t u)) u (B [t..])
                  (c_snd_beta G A B t u k dA dB dt du) rho rho HEself) as Hc.
    eapply Rel_trans; [exact Hc | apply Rel_sym; exact Hc]. }
  pose proof (funtm G (snd A B (pair A B t u)) (B [(fst A B (pair A B t u))..])
                (t_snd G A B (pair A B t u) k dA dB dpair)
                rho rho HEself k _ F _ x Dx _ (FB (ers rho t) xt) _ _
                (i_conv rho (snd A B (pair A B t u)) k _ _ _ _ _ _ Pfam Dsnd0)
                P Hgs) as H1.
  assert (Hgu : Rel (ers rho (B [t..])) (ers rho u) (ers rho u))
    by exact (LTm_of_ty G u (B [t..]) du rho rho HEself).
  pose proof (funtm G u (B [t..]) du rho rho HEself k _ (FB (ers rho t) xt) _ xu Du
                _ F _ y Dy (iso_sym _ _ P) Hgu) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  (* the moved canonical value is the second component *)
  apply (proj1 (kRel_same (FB (ers rho t) xt) _ _ _ _)).
  exact (kRel_at _ _ Pfam _ _ _ _
           (sigSnd_pair k (ers rho A) B0 FA
              (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
              (ers rho t) (ers rho u) xt xu g)).
Qed.

(* ---- surjective pairing ---- *)
Lemma isem_surj G A B p k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dp : ty G p (sig_ A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHp : ITot G p (sig_ A B)) :
  ISem G (pair A B (fst A B p) (snd A B p)) p (sig_ A B).
Proof.
  pose proof (t_fst G A B p k dA dB dp) as dfst.
  pose proof (t_snd G A B p k dA dB dp) as dsnd.
  split;
    [split; [exact (itot_pair G A B (fst A B p) (snd A B p) k W dA dB dfst dsnd
                      IHA IHB (itot_fst G A B p k W dA dB dp IHA IHB IHp)
                      (itot_snd G A B p k W dA dB dp IHA IHB IHp))
            | exact IHp] |].
  intros rho Hrho k' F Dsg x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (z : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gSig := LTyK_of_ty G (sig_ A B) k (t_sig G A B k dA dB) rho rho HEself).
  pose proof (ity_sig rho A B k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                eq_refl DFA DB) as Dsig.
  destruct (IHp rho Hrho k
              (sigFam k (ers rho A) B0 FA (fun u0 z => ers (ext rho FA u0 z) B) FB
                 redB isoB gSig) Dsig) as [xp Dp].
  pose proof (i_fst rho A B p k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (ers rho p) xp eq_refl DFA DB Dp) as Dfst.
  pose proof (i_snd rho A B p k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (ers rho p) xp eq_refl DFA DB Dp) as Dsnd.
  assert (gT : Good_ty (esig (ers rho A) B0)) by (exists k; exact gSig).
  pose proof (LTm_of_ty G p (sig_ A B) dp rho rho HEself) as Hgp.
  pose proof (sig_eta_rel _ _ _ _ _ gT (ev_sig _ _) Hgp) as gr.
  assert (g2 : Good (esig (ers rho A) B0)
                 (epair (efst (ers rho p)) (esnd (ers rho p))))
    by (eapply Rel_trans; [exact gr | apply Rel_sym; exact gr]).
  pose proof (i_pair rho A B (fst A B p) (snd A B p) k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
                (efst (ers rho p)) _ (esnd (ers rho p)) _ g2 eq_refl DFA DB
                Dfst Dsnd) as Dpv.
  pose proof (ity_lvl rho rho eq_refl (sig_ A B) k (ers rho (sig_ A B)) _ k'
                (ers rho (sig_ A B)) F Dsig Dsg) as Ek; subst k'.
  pose proof (ity_same_iso G (sig_ A B)
                (FunTm_of_ty G (sig_ A B) k (t_sig G A B k dA dB)) rho W Hrho k
                F _ Dsg Dsig) as P.
  pose proof (funtm G (pair A B (fst A B p) (snd A B p)) (sig_ A B)
                (t_pair G A B (fst A B p) (snd A B p) k dA dB dfst dsnd)
                rho rho HEself k _ F _ x Dx _ _ _ _ Dpv P g2) as H1.
  pose proof (funtm G p (sig_ A B) dp rho rho HEself k _ _ _ xp Dp
                _ F _ y Dy (iso_sym _ _ P) Hgp) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  apply (proj1 (kRel_same _ _ _ _ _)).
  exact (sigPair_surj k (ers rho A) B0 FA
           (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gSig
           (ers rho p) xp g2 gr).
Qed.

(* ---- beta.  The right-hand side is a substitution instance, and its
     totality is the body's value in the extended environment, carried down by
     isubst_ITm. ---- *)
Lemma ITm_vcast rho t k w (F : kUFam k w) v v' (Ev : v = v') (x : kElAt F v) :
  ITm rho t k w F v x -> { y : kElAt F v' & ITm rho t k w F v' y }.
Proof. destruct Ev; intros D; exists x; exact D. Qed.

Lemma itot_subst1 G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty (A :: G) t B) (du : ty G u A)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot (A :: G) t B) (IHu : ITot G u A) : ITot G (t [u..]) (B [u..]).
Proof.
  intros rho Hrho k' F DBu.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  assert (Ev : ers (ext rho FA (ers rho u) xu) t = ers rho (t [u..]))
    by exact (eq_sym (ers_sub1 rho t u FA xu)).
  pose proof (isubst_ITy rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                B k _ (FB (ers rho u) xu) (DB (ers rho u) xu)) as DBsub.
  destruct (IHt (ext rho FA (ers rho u) xu)
              (EnvITy_ext G rho A k FA DFA (ers rho u) xu Hrho) k
              (FB (ers rho u) xu) (DB (ers rho u) xu)) as [z Dz].
  pose proof (isubst_ITm rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                t k _ (FB (ers rho u) xu) _ z Dz) as Dzs.
  destruct (ITm_vcast rho (t [u..]) k _ (FB (ers rho u) xu) _ _ Ev z Dzs)
    as [z' Dz'].
  assert (Hfun : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (univ k) u dB du) as [d].
    exact (FunTm_of_ty G (B [u..]) k d). }
  pose proof (ITy_cast rho (B [u..]) k _ _ E _ DBsub) as DBc.
  pose proof (ity_lvl rho rho eq_refl (B [u..]) k (ers rho (B [u..]))
                (famCast E (FB (ers rho u) xu)) k' (ers rho (B [u..])) F DBc DBu)
    as Ek; subst k'.
  refine (itot_move G (t [u..]) (B [u..]) Hfun W rho Hrho k F
            (famCast E (FB (ers rho u) xu)) DBu DBc _ _).
  refine (ITm_cast rho (t [u..]) k _ _ E (FB (ers rho u) xu) _ _ _).
  exact Dz'.
Qed.

Lemma isem_beta G A B t u k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (dt : ty (A :: G) t B) (du : ty G u A)
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHt : ITot (A :: G) t B) (IHu : ITot G u A) :
  ISem G (app A B (lam A B t) u) (t [u..]) (B [u..]).
Proof.
  pose proof (t_lam G A B t k dA dB dt) as dlam.
  split;
    [split; [exact (itot_app G A B (lam A B t) u k W dA dB dlam du IHA IHB
                      (itot_lam G A B t k W dA dB dt IHA IHB IHt) IHu)
            | exact (itot_subst1 G A B t u k W dA dB dt du IHA IHB IHt IHu)] |].
  intros rho Hrho k' F DBu x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (z : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gPi := LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho HEself).
  pose proof (ity_pi rho A B k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gPi
                eq_refl DFA DB) as Dpi.
  (* the body's values, and the lambda they make *)
  pose (xt := fun u0 (z : kElAt FA u0) =>
                projT1 (IHt (ext rho FA u0 z)
                          (EnvITy_ext G rho A k FA DFA u0 z Hrho) k (FB u0 z)
                          (DB u0 z))).
  assert (Dt : forall u0 z, ITm (ext rho FA u0 z) t k (ers (ext rho FA u0 z) B)
                              (FB u0 z) (ers (ext rho FA u0 z) t) (xt u0 z))
    by (intros u0 z;
        exact (projT2 (IHt (ext rho FA u0 z)
                         (EnvITy_ext G rho A k FA DFA u0 z Hrho) k (FB u0 z)
                         (DB u0 z)))).
  assert (Hfunb : forall u0 z u0' z', kEqAt FA u0 z u0' z' ->
             kRel (FB u0 z) (FB u0' z')
                  (ers (ext rho FA u0 z) t) (xt u0 z)
                  (ers (ext rho FA u0' z') t) (xt u0' z')).
  { intros u0 z u0' z' Hzz.
    assert (HEx : EnvRelOf (A :: G) (ext rho FA u0 z) (ext rho FA u0' z')).
    { apply (EnvRelOf_ext G rho rho A k FA FA u0 z u0' z' HEself).
      apply (proj1 (kRel_same FA _ _ _ _)); exact Hzz. }
    refine (funtm (A :: G) t B dt _ _ HEx k _ (FB u0 z) _ (xt u0 z) (Dt u0 z)
              _ (FB u0' z') _ (xt u0' z') (Dt u0' z')
              (FunTy_of_FunTm (A :: G) B (funtm (A :: G) B (univ k) dB) _ _ HEx
                 k _ (FB u0 z) _ (FB u0' z') (DB u0 z) (DB u0' z')
                 (LTyK_of_ty (A :: G) B k dB _ _ HEx)) _).
    apply (Rel_tyeq (ers (ext rho FA u0 z) B) (ers (ext rho FA u0' z') B));
      [ exact (LTy_of_ty (A :: G) B k dB _ _ HEx)
      | exact (LTm_of_ty (A :: G) t B dt _ _ HEx) ]. }
  assert (gw : Good (epi (ers rho A) B0) (ers rho (lam A B t)))
    by exact (LTm_of_ty G (lam A B t) (pi A B) dlam rho rho HEself).
  destruct (piEl_of k (ers rho A) B0 FA (fun u0 z => ers (ext rho FA u0 z) B) FB
              redB isoB gPi (ers rho (lam A B t)) gw
              (fun u0 z => ers (ext rho FA u0 z) t) xt
              (fun u0 z => reds_beta_sub (rsub rho) (er t) u0) Hfunb)
    as [xl Hbeh].
  pose proof (i_lam rho A B t k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gPi
                (ers rho (lam A B t)) xl (fun u0 z => ers (ext rho FA u0 z) t) xt
                eq_refl eq_refl DFA DB Dt Hbeh) as Dlam.
  destruct (IHu rho Hrho k FA DFA) as [xu Du].
  pose proof (i_app rho A B (lam A B t) u k (ers rho A) FA B0
                (fun u0 z => ers (ext rho FA u0 z) B) FB redB isoB gPi
                (ers rho (lam A B t)) xl (ers rho u) xu eq_refl DFA DB Dlam Du)
    as Dapp.
  (* the substituted body, in rho *)
  assert (E : ers (ext rho FA (ers rho u) xu) B = ers rho (B [u..]))
    by exact (eq_sym (ers_sub1 rho B u FA xu)).
  assert (Ev : ers (ext rho FA (ers rho u) xu) t = ers rho (t [u..]))
    by exact (eq_sym (ers_sub1 rho t u FA xu)).
  pose proof (isubst_ITy rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                B k _ (FB (ers rho u) xu) (DB (ers rho u) xu)) as DBsub.
  pose proof (isubst_ITm rho u k (ers rho A) FA (ers rho u) xu eq_refl Du
                t k _ (FB (ers rho u) xu) _ (xt (ers rho u) xu)
                (Dt (ers rho u) xu)) as Dzs.
  (* the level, and the isomorphism to the statement's family *)
  assert (ftu : FunTm G (t [u..])).
  { destruct (ty_subst1 G A t B u dt du) as [d].
    exact (funtm G (t [u..]) (B [u..]) d). }
  assert (fBu : FunTm G (B [u..])).
  { destruct (ty_subst1 G A B (univ k) u dB du) as [d].
    exact (FunTm_of_ty G (B [u..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (B [u..]) k _ (FB (ers rho u) xu) k'
                (ers rho (B [u..])) F DBsub DBu) as Ek; subst k'.
  pose proof (ity_same_iso' G (B [u..]) fBu rho W Hrho k _ F _
                (FB (ers rho u) xu) DBu DBsub) as P.
  assert (Hg1 : Rel (ers (ext rho FA (ers rho u) xu) B)
                  (ers rho (app A B (lam A B t) u))
                  (eapp (ers rho (lam A B t)) (ers rho u))).
  { rewrite E.
    exact (LTm_of_ty G (app A B (lam A B t) u) (B [u..])
             (t_app G A B (lam A B t) u k dA dB dlam du) rho rho HEself). }
  pose proof (funtm G (app A B (lam A B t) u) (B [u..])
                (t_app G A B (lam A B t) u k dA dB dlam du) rho rho HEself k
                _ F _ x Dx _ (FB (ers rho u) xu) _ _ Dapp P Hg1) as H1.
  assert (Hg2 : Rel (ers rho (B [u..])) (ers (ext rho FA (ers rho u) xu) t)
                  (ers rho (t [u..]))).
  { rewrite Ev.
    destruct (ty_subst1 G A t B u dt du) as [d].
    exact (LTm_of_ty G (t [u..]) (B [u..]) d rho rho HEself). }
  pose proof (ftu rho rho HEself k _ (FB (ers rho u) xu) _ (xt (ers rho u) xu) Dzs
                _ F _ y Dy (iso_sym _ _ P) Hg2) as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  apply (proj1 (kRel_same (FB (ers rho u) xu) _ _ _ _)).
  exact (Hbeh (ers rho u) xu).
Qed.

(* ---- the recursor.  The three rules share the data itot_natrec builds, so
     it is packaged once here. ---- *)
Lemma build_rec_data G C z s k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C))
  (IHC : ITot (nat_ :: G) C (univ k)) (IHz : ITot G z (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C))
  rho (Hrho : EnvITy G rho) :
  { FC : forall m (x : kElAt (natFam 0) m),
           kUFam k (subst_etm (scons m (rsub rho)) (er C)) &
  { isoC : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
             iso (kAt (FC m x)) (kAt (FC m' x')) &
  { xz : kElAt (FC ezero (natE 0 NatAt_zero)) (ers rho z) &
  { xs : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w),
           kElAt (FC (esucc m) (natSucc x))
             (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) &
    ((forall m x, ITy (ext rho (natFam 0) m x) C k
                    (subst_etm (scons m (rsub rho)) (er C)) (FC m x)) *
     ITm rho z k (subst_etm (scons ezero (rsub rho)) (er C))
         (FC ezero (natE 0 NatAt_zero)) (ers rho z) xz *
     (forall m x w y,
        ITm (ext (ext rho (natFam 0) m x) (FC m x) w y) s k
            (subst_etm (scons (esucc m) (rsub rho)) (er C))
            (FC (esucc m) (natSucc x))
            (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) (xs m x w y)) *
     (forall m x w y m' x' w' y', kEqAt (natFam 0) m x m' x' ->
        kRel (FC m x) (FC m' x') w y w' y' ->
        kRel (FC (esucc m) (natSucc x)) (FC (esucc m') (natSucc x'))
             (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) (xs m x w y)
             (ers (ext (ext rho (natFam 0) m' x') (FC m' x') w' y') s)
             (xs m' x' w' y')))%type
  } } } }.
Proof.
  pose (SC := fun m : etm => subst_etm (scons m (rsub rho)) (er C)).
  assert (HEm : forall m (x : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x)).
  { intros m x.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam 0) m) =>
                projT1 (ityT_of_ITot (nat_ :: G) C k IHC
                          (ext rho (natFam 0) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam 0) m x) C k (SC m) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ :: G) C k IHC
                         (ext rho (natFam 0) m x) (HEm m x)))).
  assert (isoC : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
             iso (kAt (FC m x)) (kAt (FC m' x'))).
  { intros m x m' x' Hm.
    assert (HEx : EnvRelOf (nat_ :: G) (ext rho (natFam 0) m x)
                    (ext rho (natFam 0) m' x')).
    { apply (EnvRelOf_ext G rho rho nat_ 0 (natFam 0) (natFam 0) m x m' x'
               (EnvRelOf_selfE G rho W Hrho)).
      apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm. }
    exact (FunTy_of_FunTm (nat_ :: G) C (funtm (nat_ :: G) C (univ k) dC)
             _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
             (LTyK_of_ty (nat_ :: G) C k dC _ _ HEx)). }
  assert (E0 : SC ezero = ers rho (C [zero..]))
    by exact (eq_sym (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
                eq_refl (i_zero rho) C k (SC ezero) (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [zero..]) k _ _ E0 _ DCz)) as [xz' Dz'].
  destruct (ITm_uncast rho z k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dz')
    as [xz Dz].
  assert (Hstep : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w),
             { xs : kElAt (FC (esucc m) (natSucc x))
                      (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) &
               ITm (ext (ext rho (natFam 0) m x) (FC m x) w y) s k
                   (SC (esucc m)) (FC (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s) xs }).
  { intros m x w y.
    pose proof (ity_nrec_succ rho C k m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k (SC m) (FC m x) w y) as DS.
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam 0) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs (ext (ext rho (natFam 0) m x) (FC m x) w y)
                (EnvITy_ext (nat_ :: G) (ext rho (natFam 0) m x) C k (FC m x)
                   (DC m x) w y (HEm m x))
                k (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [xs' Ds'].
    destruct (ITm_uncast _ s k _ _ Es (FC (esucc m) (natSucc x)) _ _ Ds')
      as [xs Ds].
    exists xs; exact Ds. }
  assert (Hfs : forall m x w y m' x' w' y', kEqAt (natFam 0) m x m' x' ->
             kRel (FC m x) (FC m' x') w y w' y' ->
             kRel (FC (esucc m) (natSucc x)) (FC (esucc m') (natSucc x'))
                  (ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s)
                  (projT1 (Hstep m x w y))
                  (ers (ext (ext rho (natFam 0) m' x') (FC m' x') w' y') s)
                  (projT1 (Hstep m' x' w' y'))).
  { intros m x w y m' x' w' y' Hm Hy.
    assert (HE0 : EnvRelOf (nat_ :: G) (ext rho (natFam 0) m x)
                    (ext rho (natFam 0) m' x')).
    { apply (EnvRelOf_ext G rho rho nat_ 0 (natFam 0) (natFam 0) m x m' x'
               (EnvRelOf_selfE G rho W Hrho)).
      apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm. }
    assert (HEr : EnvRelOf (C :: nat_ :: G)
                    (ext (ext rho (natFam 0) m x) (FC m x) w y)
                    (ext (ext rho (natFam 0) m' x') (FC m' x') w' y'))
      by exact (EnvRelOf_ext (nat_ :: G) (ext rho (natFam 0) m x)
                  (ext rho (natFam 0) m' x') C k (FC m x) (FC m' x') w y w' y'
                  HE0 Hy).
    assert (Q : iso (kAt (FC (esucc m) (natSucc x)))
                    (kAt (FC (esucc m') (natSucc x'))))
      by exact (isoC (esucc m) (natSucc x) (esucc m') (natSucc x')
                  (natSucc_eq x x' Hm)).
    assert (Es : SC (esucc m)
                 = ers (ext (ext rho (natFam 0) m x) (FC m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    refine (funtm (C :: nat_ :: G) s (nrec_succ C) ds _ _ HEr k
              _ (FC (esucc m) (natSucc x)) _ (projT1 (Hstep m x w y))
              (projT2 (Hstep m x w y))
              _ (FC (esucc m') (natSucc x')) _ (projT1 (Hstep m' x' w' y'))
              (projT2 (Hstep m' x' w' y')) Q _).
    apply (Rel_tyeq (ers (ext (ext rho (natFam 0) m x) (FC m x) w y)
                      (nrec_succ C)) (SC (esucc m'))).
    - rewrite <- Es; exact (iso_ty _ _ Q).
    - exact (LTm_of_ty (C :: nat_ :: G) s (nrec_succ C) ds _ _ HEr). }
  exists FC, isoC, xz, (fun m x w y => projT1 (Hstep m x w y)).
  split; [split; [split; [exact DC | exact Dz] |] |].
  - intros m x w y; exact (projT2 (Hstep m x w y)).
  - exact Hfs.
Qed.

Lemma isem_rec_zero G C z s k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C))
  (IHC : ITot (nat_ :: G) C (univ k)) (IHz : ITot G z (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C)) :
  ISem G (natrec C z s zero) z (C [zero..]).
Proof.
  split;
    [split; [exact (itot_natrec G C z s zero k W dC dz ds (t_zero G W)
                      IHC IHz IHs (itot_zero G W))
            | exact IHz] |].
  intros rho Hrho k' F DCz x y Dx Dy.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_rec_data G C z s k W dC dz ds IHC IHz IHs rho Hrho)
    as [FC [isoC [xz [xs [[[DC Dz] Ds] Hfs]]]]].
  pose proof (i_natrec rho C z s zero k
                (fun m => subst_etm (scons m (rsub rho)) (er C)) FC isoC
                (ers rho (stepWrap s)) (ers rho z) xz
                (fun m x w y => ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s)
                xs (fun m x w y => reds_lam2_app (er s) (rsub rho) m w)
                ezero (natE 0 NatAt_zero) eq_refl DC Dz Ds (i_zero rho)) as Dnr.
  assert (E0 : subst_etm (scons ezero (rsub rho)) (er C) = ers rho (C [zero..]))
    by exact (eq_sym (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
                eq_refl (i_zero rho) C k _ (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz0.
  assert (fCz : FunTm G (C [zero..])).
  { destruct (ty_subst1 G nat_ C (univ k) zero dC (t_zero G W)) as [d].
    exact (FunTm_of_ty G (C [zero..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (C [zero..]) k _
                (FC ezero (natE 0 NatAt_zero)) k' (ers rho (C [zero..])) F
                DCz0 DCz) as Ek; subst k'.
  pose proof (ity_same_iso' G (C [zero..]) fCz rho W Hrho k _ F _
                (FC ezero (natE 0 NatAt_zero)) DCz DCz0) as P.
  assert (Hg1 : Rel (subst_etm (scons ezero (rsub rho)) (er C))
                  (ers rho (natrec C z s zero))
                  (enatrec (ers rho z) (ers rho (stepWrap s)) ezero)).
  { rewrite E0.
    exact (LTm_of_ty G (natrec C z s zero) (C [zero..])
             (t_natrec G C z s zero k dC dz ds (t_zero G W)) rho rho HEself). }
  pose proof (funtm G (natrec C z s zero) (C [zero..])
                (t_natrec G C z s zero k dC dz ds (t_zero G W)) rho rho HEself k
                _ F _ x Dx _ (FC ezero (natE 0 NatAt_zero)) _ _ Dnr P Hg1) as H1.
  pose proof (funtm G z (C [zero..]) dz rho rho HEself k
                _ (FC ezero (natE 0 NatAt_zero)) _ xz Dz _ F _ y Dy
                (iso_sym _ _ P) (LTm_of_ty G z (C [zero..]) dz rho rho HEself))
    as H2.
  apply (proj2 (kRel_same F _ _ _ _)).
  eapply kRel_trans; [exact H1 |].
  eapply kRel_trans; [| exact H2].
  cbn [semrec].
  apply kRel_sym; apply moveTo_rel.
Qed.

(* The motive alone, which the congruence needs for both motives. *)
Lemma build_motive G C k (W : wfc G) (dC : ty (nat_ :: G) C (univ k))
  (IHC : ITot (nat_ :: G) C (univ k)) rho (Hrho : EnvITy G rho) :
  { FC : forall m (x : kElAt (natFam 0) m),
           kUFam k (subst_etm (scons m (rsub rho)) (er C)) &
    ((forall m x, ITy (ext rho (natFam 0) m x) C k
                    (subst_etm (scons m (rsub rho)) (er C)) (FC m x)) *
     (forall m x m' x', kEqAt (natFam 0) m x m' x' ->
        iso (kAt (FC m x)) (kAt (FC m' x'))))%type }.
Proof.
  assert (HEm : forall m (x : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x)).
  { intros m x.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x Hrho). }
  pose (FC := fun m (x : kElAt (natFam 0) m) =>
                projT1 (ityT_of_ITot (nat_ :: G) C k IHC
                          (ext rho (natFam 0) m x) (HEm m x))).
  assert (DC : forall m x, ITy (ext rho (natFam 0) m x) C k
                             (subst_etm (scons m (rsub rho)) (er C)) (FC m x))
    by (intros m x;
        exact (projT2 (ityT_of_ITot (nat_ :: G) C k IHC
                         (ext rho (natFam 0) m x) (HEm m x)))).
  exists FC; split; [exact DC |].
  intros m x m' x' Hm.
  assert (HEx : EnvRelOf (nat_ :: G) (ext rho (natFam 0) m x)
                  (ext rho (natFam 0) m' x')).
  { apply (EnvRelOf_ext G rho rho nat_ 0 (natFam 0) (natFam 0) m x m' x'
             (EnvRelOf_selfE G rho W Hrho)).
    apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm. }
  exact (FunTy_of_FunTm (nat_ :: G) C (funtm (nat_ :: G) C (univ k) dC)
           _ _ HEx k _ (FC m x) _ (FC m' x') (DC m x) (DC m' x')
           (LTyK_of_ty (nat_ :: G) C k dC _ _ HEx)).
Qed.

(* The step's type is well typed: a renaming, a substitution and a weakening of
   the motive's derivation. *)
Lemma ty_nrec_succ G C k (W : wfc G) (dC : ty (nat_ :: G) C (univ k)) :
  inhabited (ty (C :: nat_ :: G) (nrec_succ C) (univ k)).
Proof.
  pose proof (w_cons G nat_ 0 W (t_nat G W)) as W1.
  pose proof (w_cons (nat_ :: G) nat_ 0 W1 (t_nat (nat_ :: G) W1)) as W2.
  destruct (proj1 (proj2 renaming) (nat_ :: G) C (univ k) dC
              (nat_ :: nat_ :: G) (upRen_tm_tm shift)
              (ren_ok_up shift G (nat_ :: G) nat_ (ren_ok_shift G nat_))
              (inhabits W2)) as [d1].
  destruct (ty_subst1 (nat_ :: G) nat_ (C ⟨upRen_tm_tm shift⟩) (univ k)
              (succ (var_tm 0)) d1
              (t_succ (nat_ :: G) (var_tm 0)
                 (t_var (nat_ :: G) 0 nat_ W1 (lookup_O G nat_)))) as [d2].
  destruct (proj1 (proj2 renaming) (nat_ :: G) _ (univ k) d2
              (C :: nat_ :: G) shift (ren_ok_shift (nat_ :: G) C)
              (inhabits (w_cons (nat_ :: G) C k W1 dC))) as [d3].
  rewrite <- nrec_succ_as in d3.
  exact (inhabits d3).
Qed.

Lemma funtm_nrec_succ G C k (W : wfc G) (dC : ty (nat_ :: G) C (univ k)) :
  FunTm (C :: nat_ :: G) (nrec_succ C).
Proof.
  destruct (ty_nrec_succ G C k W dC) as [d].
  exact (FunTm_of_ty (C :: nat_ :: G) (nrec_succ C) k d).
Qed.

(* semrec_rel at two indices that are only PROVABLY equal, which is what the
   scrutinees' relatedness gives. *)
Lemma semrec_rel_idx (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (isoC : forall m x m' x', kEqAt (natFam k0) m x m' x' ->
            iso (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  (SC' : etm -> etm) (FC' : forall m (x : kElAt (natFam k0) m), kUFam k (SC' m))
  (isoC' : forall m x m' x', kEqAt (natFam k0) m x m' x' ->
             iso (kAt (FC' m x)) (kAt (FC' m' x')))
  (zr' sr' : etm) (xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) zr')
  (step' : forall m x w (y : kElAt (FC' m x) w),
             kElAt (FC' (esucc m) (natSucc x)) (eapp (eapp sr' m) w))
  (Hz : kRel (FC ezero (natE 0 NatAt_zero)) (FC' ezero (natE 0 NatAt_zero))
          zr xz zr' xz')
  (Hstep : forall m x m' x', kEqAt (natFam k0) m x m' x' ->
             forall w y w' y', kRel (FC m x) (FC' m' x') w y w' y' ->
             kRel (FC (esucc m) (natSucc x)) (FC' (esucc m') (natSucc x'))
                  (eapp (eapp sr m) w) (step m x w y)
                  (eapp (eapp sr' m') w') (step' m' x' w' y'))
  j m (e : NatAt j m) j' m' (e' : NatAt j' m') (Ej : j = j') :
  kRel (FC m (natE j e)) (FC' m' (natE j' e'))
       (enatrec zr sr m) (semrec k k0 SC FC isoC zr sr xz step j m e)
       (enatrec zr' sr' m') (semrec k k0 SC' FC' isoC' zr' sr' xz' step' j' m' e').
Proof.
  destruct Ej.
  exact (semrec_rel k k0 SC FC isoC zr sr xz step SC' FC' isoC' zr' sr' xz' step'
           Hz Hstep j m e m' e').
Qed.

(* The primed recursor's data: the motive is C', but the branches are typed at
   C's instances -- that is how the rule is stated -- so their values are the
   C-values moved along the motives' isomorphism. *)
Lemma build_rec_data' G C C' z' s' k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dC' : ty (nat_ :: G) C' (univ k))
  (dz' : ty G z' (C [zero..])) (ds' : ty (C :: nat_ :: G) s' (nrec_succ C))
  (IHC : ITot (nat_ :: G) C (univ k)) (IHC' : ITot (nat_ :: G) C' (univ k))
  (IHz' : ITot G z' (C [zero..])) (IHs' : ITot (C :: nat_ :: G) s' (nrec_succ C))
  (IHcC : IRel (nat_ :: G) C C' (univ k))
  rho (Hrho : EnvITy G rho) :
  { FC' : forall m (x : kElAt (natFam 0) m),
            kUFam k (subst_etm (scons m (rsub rho)) (er C')) &
  { isoC' : forall m x m' x', kEqAt (natFam 0) m x m' x' ->
              iso (kAt (FC' m x)) (kAt (FC' m' x')) &
  { xz' : kElAt (FC' ezero (natE 0 NatAt_zero)) (ers rho z') &
  { xs' : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC' m x) w),
            kElAt (FC' (esucc m) (natSucc x))
              (ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) s') &
    ((forall m x, ITy (ext rho (natFam 0) m x) C' k
                    (subst_etm (scons m (rsub rho)) (er C')) (FC' m x)) *
     ITm rho z' k (subst_etm (scons ezero (rsub rho)) (er C'))
         (FC' ezero (natE 0 NatAt_zero)) (ers rho z') xz' *
     (forall m x w y,
        ITm (ext (ext rho (natFam 0) m x) (FC' m x) w y) s' k
            (subst_etm (scons (esucc m) (rsub rho)) (er C'))
            (FC' (esucc m) (natSucc x))
            (ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) s') (xs' m x w y)))%type
  } } } }.
Proof.
  assert (HEm : forall m (x : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x)).
  { intros m x.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x Hrho). }
  destruct (build_motive G C k W dC IHC rho Hrho) as [FC [DC isoC]].
  destruct (build_motive G C' k W dC' IHC' rho Hrho) as [FC' [DC' isoC']].
  assert (PCC : forall m x, iso (kAt (FC m x)) (kAt (FC' m x))).
  { intros m x.
    exact (iso_of_IRel_at' (nat_ :: G) C C' k IHcC (ext rho (natFam 0) m x)
             (HEm m x) _ (FC m x) (DC m x) _ (FC' m x) (DC' m x)). }
  (* the base branch *)
  assert (E0 : subst_etm (scons ezero (rsub rho)) (er C) = ers rho (C [zero..]))
    by exact (eq_sym (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero))).
  pose proof (isubst_ITy rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
                eq_refl (i_zero rho) C k _ (FC ezero (natE 0 NatAt_zero))
                (DC ezero (natE 0 NatAt_zero))) as DCz.
  destruct (IHz' rho Hrho k (famCast E0 (FC ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [zero..]) k _ _ E0 _ DCz)) as [w0 Dw0].
  destruct (ITm_uncast rho z' k _ _ E0 (FC ezero (natE 0 NatAt_zero)) _ _ Dw0)
    as [xz0 Dz0].
  (* the step branch *)
  assert (Hstep : forall m (x : kElAt (natFam 0) m) w (y : kElAt (FC' m x) w),
             { v : kElAt (FC' (esucc m) (natSucc x))
                     (ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) s') &
               ITm (ext (ext rho (natFam 0) m x) (FC' m x) w y) s' k
                   (subst_etm (scons (esucc m) (rsub rho)) (er C'))
                   (FC' (esucc m) (natSucc x))
                   (ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) s') v }).
  { intros m x w y.
    pose proof (EnvITy_ext_iso (nat_ :: G) (ext rho (natFam 0) m x) C k _
                  (FC' m x) (FC m x) (DC m x) (iso_sym _ _ (PCC m x)) w y (HEm m x))
      as HE1.
    pose proof (ity_nrec_succ rho C k m x (FC (esucc m) (natSucc x))
                  (DC (esucc m) (natSucc x)) k _ (FC' m x) w y) as DS.
    assert (Es : subst_etm (scons (esucc m) (rsub rho)) (er C)
                 = ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) (nrec_succ C))
      by exact (eq_sym (er_nrec_succ C (rsub rho) m w)).
    destruct (IHs' (ext (ext rho (natFam 0) m x) (FC' m x) w y) HE1 k
                (famCast Es (FC (esucc m) (natSucc x)))
                (ITy_cast _ (nrec_succ C) k _ _ Es _ DS)) as [v0 Dv0].
    destruct (ITm_uncast _ s' k _ _ Es (FC (esucc m) (natSucc x)) _ _ Dv0)
      as [v1 Dv1].
    exists (ctoK _ _ (PCC (esucc m) (natSucc x)) _ v1).
    exact (i_conv _ s' k _ _ _ _ _ _ (PCC (esucc m) (natSucc x)) Dv1). }
  exists FC', isoC',
    (ctoK _ _ (PCC ezero (natE 0 NatAt_zero)) _ xz0),
    (fun m x w y => projT1 (Hstep m x w y)).
  split;
    [split; [exact DC'
            | exact (i_conv rho z' k _ _ _ _ _ _
                       (PCC ezero (natE 0 NatAt_zero)) Dz0)] |].
  intros m x w y; exact (projT2 (Hstep m x w y)).
Qed.

Lemma ITy_uncast rho A k w w' (E : w = w') (F : kUFam k w) :
  ITy rho A k w' (famCast E F) -> ITy rho A k w F.
Proof. destruct E; intros D; exact D. Qed.

Lemma iso_famCast {k w w'} (E : w = w') (F : kUFam k w) :
  iso (kAt F) (kAt (famCast E F)).
Proof. destruct E; apply iso_self. Qed.

(* ---- the recursor's congruence.  Both subjects are decoded; the two
     recursions are compared by semrec_rel, whose two hypotheses are the
     branches' relatedness -- each obtained in the two steps the conversion
     cases use: the induction hypothesis in one environment, then the
     right-hand branch's own functionality across the two. ---- *)
Lemma isem_natrec_core G C C' z z' s s' n n' k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dC' : ty (nat_ :: G) C' (univ k))
  (dz : ty G z (C [zero..])) (dz' : ty G z' (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C))
  (ds' : ty (C :: nat_ :: G) s' (nrec_succ C))
  (dn : ty G n nat_) (dn' : ty G n' nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHcC : IRel (nat_ :: G) C C' (univ k))
  (IHz' : ITot G z' (C [zero..])) (IHcz : IRel G z z' (C [zero..]))
  (IHs' : ITot (C :: nat_ :: G) s' (nrec_succ C))
  (IHcs : IRel (C :: nat_ :: G) s s' (nrec_succ C))
  (IHcn : IRel G n n' nat_)
  rho (Hrho : EnvITy G rho) k' Sy (F : kUFam k' Sy) x y
  (E : RecVal rho C z s n k' Sy F (ers rho (natrec C z s n)) x)
  (E' : RecVal rho C' z' s' n' k' Sy F (ers rho (natrec C' z' s' n')) y) :
  kEqAt F (ers rho (natrec C z s n)) x (ers rho (natrec C' z' s' n')) y.
Proof.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  pose proof (w_cons G nat_ 0 W (t_nat G W)) as W1.
  pose proof (w_cons (nat_ :: G) C k W1 dC) as WC.
  destruct E as [SC1 [FC1 [isoC1 [S01 [wz1 [xz1 [ws1 [xs1 [redS1 [wn1 [xn1
    [[[[[Ep1 DC1] Dz1] Ds1] Dn1] Hv1]]]]]]]]]]]].
  destruct E' as [SC2 [FC2 [isoC2 [S02 [wz2 [xz2 [ws2 [xs2 [redS2 [wn2 [xn2
    [[[[[Ep2 DC2] Dz2] Ds2] Dn2] Hv2]]]]]]]]]]]].
  assert (En1 : wn1 = ers rho n) by exact (ers_of_ITm _ _ _ _ _ _ _ Dn1).
  assert (En2 : wn2 = ers rho n') by exact (ers_of_ITm _ _ _ _ _ _ _ Dn2).
  assert (Ez1 : wz1 = ers rho z) by exact (ers_of_ITm _ _ _ _ _ _ _ Dz1).
  assert (Ez2 : wz2 = ers rho z') by exact (ers_of_ITm _ _ _ _ _ _ _ Dz2).
  subst wn1 wn2 wz1 wz2.
  assert (HEm : forall m (x0 : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x0)).
  { intros m x0.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x0 Hrho). }
  (* the shapes' level is the motive's *)
  destruct (build_motive G C k W dC IHC rho Hrho) as [FCc [DCc isoCc]].
  pose proof (IHcn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl)
                xn1 xn2 Dn1 Dn2) as Hnn.
  assert (Eidx : natIdx xn1 = natIdx xn2)
    by exact (proj1 (proj1 (natEq_iff xn1 xn2) Hnn)).
  pose proof (ity_lvl (ext rho (natFam 0) (ers rho n) xn1)
                (ext rho (natFam 0) (ers rho n) xn1) eq_refl C k _
                (FCc (ers rho n) xn1) k' _ (FC1 (ers rho n) xn1)
                (DCc (ers rho n) xn1) (DC1 (ers rho n) xn1)) as Ek; subst k'.
  (* the motives' instances are isomorphic *)
  assert (PCC : forall m x0, iso (kAt (FC1 m x0)) (kAt (FC2 m x0))).
  { intros m x0.
    exact (iso_of_IRel_at' (nat_ :: G) C C' k IHcC (ext rho (natFam 0) m x0)
             (HEm m x0) _ (FC1 m x0) (DC1 m x0) _ (FC2 m x0) (DC2 m x0)). }
  assert (EC1 : forall m (x0 : kElAt (natFam 0) m),
             SC1 m = ers (ext rho (natFam 0) m x0) C)
    by (intros m x0; exact (ers_of_ITy _ _ _ _ _ (DC1 m x0))).
  (* the base branches *)
  assert (E0 : SC1 ezero = ers rho (C [zero..])).
  { rewrite (EC1 ezero (natE 0 NatAt_zero)).
    exact (eq_sym (ers_sub1 rho C zero (natFam 0) (natE 0 NatAt_zero))). }
  pose proof (isubst_ITy rho zero 0 enat (natFam 0) ezero (natE 0 NatAt_zero)
                eq_refl (i_zero rho) C k _ (FC1 ezero (natE 0 NatAt_zero))
                (DC1 ezero (natE 0 NatAt_zero))) as DCz1.
  assert (fCz : FunTm G (C [zero..])).
  { destruct (ty_subst1 G nat_ C (univ k) zero dC (t_zero G W)) as [d].
    exact (FunTm_of_ty G (C [zero..]) k d). }
  destruct (IHz' rho Hrho k (famCast E0 (FC1 ezero (natE 0 NatAt_zero)))
              (ITy_cast rho (C [zero..]) k _ _ E0 _ DCz1)) as [w0 Dw0].
  destruct (ITm_uncast rho z' k _ _ E0 (FC1 ezero (natE 0 NatAt_zero)) _ _ Dw0)
    as [xz0 Dz0].
  assert (Hz : kRel (FC1 ezero (natE 0 NatAt_zero)) (FC2 ezero (natE 0 NatAt_zero))
                 (ers rho z) xz1 (ers rho z') xz2).
  { eapply kRel_trans;
      [ exact (kRel_of_IRel' G z z' (C [zero..]) IHcz fCz W rho Hrho k _ _ _ _
                 DCz1 DCz1 _ xz1 _ xz0 Dz1 Dz0) |].
    refine (funtm G z' (C [zero..]) dz' rho rho HEself k
              _ (FC1 ezero (natE 0 NatAt_zero)) _ xz0 Dz0
              _ (FC2 ezero (natE 0 NatAt_zero)) _ xz2 Dz2
              (PCC ezero (natE 0 NatAt_zero)) _).
    apply (Rel_tyeq (SC1 ezero) (SC2 ezero));
      [ exact (iso_ty (FC1 ezero (natE 0 NatAt_zero))
                 (FC2 ezero (natE 0 NatAt_zero)) (PCC ezero (natE 0 NatAt_zero)))
      | rewrite E0; exact (LTm_of_ty G z' (C [zero..]) dz' rho rho HEself) ]. }
  (* the step branches *)
  assert (fS : FunTm (C :: nat_ :: G) (nrec_succ C))
    by exact (funtm_nrec_succ G C k W dC).
  assert (Hst : forall m x0 m' x0', kEqAt (natFam 0) m x0 m' x0' ->
             forall w y0 w' y0', kRel (FC1 m x0) (FC2 m' x0') w y0 w' y0' ->
             kRel (FC1 (esucc m) (natSucc x0)) (FC2 (esucc m') (natSucc x0'))
                  (ws1 m x0 w y0) (xs1 m x0 w y0)
                  (ws2 m' x0' w' y0') (xs2 m' x0' w' y0')).
  { intros m x0 m' x0' Hm w y0 w' y0' Hy.
    (* the interpretation of the step's type in the unprimed environment *)
    pose proof (ITy_uncast _ (nrec_succ C) k _ _ (EC1 (esucc m) (natSucc x0))
                  (FC1 (esucc m) (natSucc x0))
                  (ity_nrec_succ rho C k m x0
                     (famCast (EC1 (esucc m) (natSucc x0))
                        (FC1 (esucc m) (natSucc x0)))
                     (ITy_cast _ C k _ _ (EC1 (esucc m) (natSucc x0)) _
                        (DC1 (esucc m) (natSucc x0)))
                     k _ (FC1 m x0) w y0)) as DS1.
    assert (Es1 : SC1 (esucc m)
                  = ers (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0)
                      (nrec_succ C))
      by exact (eq_trans (EC1 (esucc m) (natSucc x0))
                  (eq_sym (er_nrec_succ C (rsub rho) m w))).
    pose proof (EnvITy_ext_iso (nat_ :: G) (ext rho (natFam 0) m x0) C k _
                  (FC1 m x0) (famCast (EC1 m x0) (FC1 m x0))
                  (ITy_cast _ C k _ _ (EC1 m x0) _ (DC1 m x0))
                  (iso_famCast (EC1 m x0) (FC1 m x0)) w y0 (HEm m x0)) as HE1.
    destruct (IHs' (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0) HE1 k
                (famCast Es1 (FC1 (esucc m) (natSucc x0)))
                (ITy_cast _ (nrec_succ C) k _ _ Es1 _ DS1)) as [v0 Dv0].
    destruct (ITm_uncast _ s' k _ _ Es1 (FC1 (esucc m) (natSucc x0)) _ _ Dv0)
      as [v1 Dv1].
    (* s against s' in the unprimed environment *)
    pose proof (kRel_of_IRel' (C :: nat_ :: G) s s' (nrec_succ C) IHcs fS WC
                  (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0) HE1 k
                  _ (FC1 (esucc m) (natSucc x0)) _ (FC1 (esucc m) (natSucc x0))
                  DS1 DS1 _ (xs1 m x0 w y0) _ v1 (Ds1 m x0 w y0) Dv1) as Hb1.
    (* s' across the two environments *)
    assert (HE0 : EnvRelOf (nat_ :: G) (ext rho (natFam 0) m x0)
                    (ext rho (natFam 0) m' x0')).
    { apply (EnvRelOf_ext G rho rho nat_ 0 (natFam 0) (natFam 0) m x0 m' x0'
               HEself).
      apply (proj1 (kRel_same (natFam 0) _ _ _ _)); exact Hm. }
    assert (T1 : tyeq (SC1 m) (ers (ext rho (natFam 0) m x0) C)).
    { pose proof (uf_ty (FC1 m x0)) as U.
      rewrite (EC1 m x0) in U |- *; exists k; exact U. }
    assert (T2 : tyeq (SC2 m') (ers (ext rho (natFam 0) m' x0') C)).
    { rewrite <- (EC1 m' x0').
      apply tyeq_sym; exact (iso_ty (FC1 m' x0') (FC2 m' x0') (PCC m' x0')). }
    assert (HEr : EnvRelOf (C :: nat_ :: G)
                    (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0)
                    (ext (ext rho (natFam 0) m' x0') (FC2 m' x0') w' y0')).
    { apply (EnvRelOf_ext_ty (nat_ :: G) (ext rho (natFam 0) m x0)
               (ext rho (natFam 0) m' x0') C k (SC1 m) (SC2 m')
               (FC1 m x0) (FC2 m' x0') w y0 w' y0' HE0 T1 T2 Hy). }
    assert (Q : iso (kAt (FC1 (esucc m) (natSucc x0)))
                    (kAt (FC2 (esucc m') (natSucc x0')))).
    { eapply iso_trans; [exact (PCC (esucc m) (natSucc x0)) |].
      exact (isoC2 (esucc m) (natSucc x0) (esucc m') (natSucc x0')
               (natSucc_eq x0 x0' Hm)). }
    assert (Ew2 : ws2 m' x0' w' y0'
                  = ers (ext (ext rho (natFam 0) m' x0') (FC2 m' x0') w' y0') s')
      by exact (ers_of_ITm _ _ _ _ _ _ _ (Ds2 m' x0' w' y0')).
    assert (Hr : Rel (SC2 (esucc m'))
                   (ers (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0) s')
                   (ws2 m' x0' w' y0')).
    { rewrite Ew2.
      apply (Rel_tyeq (ers (ext (ext rho (natFam 0) m x0) (FC1 m x0) w y0)
                         (nrec_succ C)) (SC2 (esucc m'))).
      - rewrite <- Es1; exact (iso_ty _ _ Q).
      - exact (LTm_of_ty (C :: nat_ :: G) s' (nrec_succ C) ds' _ _ HEr). }
    pose proof (funtm (C :: nat_ :: G) s' (nrec_succ C) ds' _ _ HEr k
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
Lemma itot_natrec' G C C' z' s' n n' k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dC' : ty (nat_ :: G) C' (univ k))
  (dz' : ty G z' (C [zero..])) (ds' : ty (C :: nat_ :: G) s' (nrec_succ C))
  (dn : ty G n nat_) (dn' : ty G n' nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHC' : ITot (nat_ :: G) C' (univ k))
  (IHz' : ITot G z' (C [zero..])) (IHs' : ITot (C :: nat_ :: G) s' (nrec_succ C))
  (IHcC : IRel (nat_ :: G) C C' (univ k))
  (IHn : ITot G n nat_) (IHn' : ITot G n' nat_) (IHcn : IRel G n n' nat_) :
  ITot G (natrec C' z' s' n') (C [n..]).
Proof.
  intros rho Hrho k' F DCn.
  destruct (build_motive G C k W dC IHC rho Hrho) as [FC [DC isoC]].
  destruct (build_rec_data' G C C' z' s' k W dC dC' dz' ds' IHC IHC' IHz' IHs'
              IHcC rho Hrho) as [FC' [isoC' [xz' [xs' [[DC' Dz'] Ds']]]]].
  assert (HEm : forall m (x : kElAt (natFam 0) m),
             EnvITy (nat_ :: G) (ext rho (natFam 0) m x)).
  { intros m x.
    exact (EnvITy_ext G rho nat_ 0 (natFam 0)
             (ity_nat rho (ers rho nat_) eq_refl) m x Hrho). }
  assert (PCC : forall m x, iso (kAt (FC m x)) (kAt (FC' m x))).
  { intros m x.
    exact (iso_of_IRel_at' (nat_ :: G) C C' k IHcC (ext rho (natFam 0) m x)
             (HEm m x) _ (FC m x) (DC m x) _ (FC' m x) (DC' m x)). }
  destruct (IHn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl))
    as [xn Dn].
  destruct (IHn' rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl))
    as [xn' Dn'].
  pose proof (IHcn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl)
                xn xn' Dn Dn') as Hnn.
  pose proof (i_natrec rho C' z' s' n' k
                (fun m => subst_etm (scons m (rsub rho)) (er C')) FC' isoC'
                (ers rho (stepWrap s')) (ers rho z') xz'
                (fun m x w y => ers (ext (ext rho (natFam 0) m x) (FC' m x) w y) s')
                xs' (fun m x w y => reds_lam2_app (er s') (rsub rho) m w)
                (ers rho n') xn' eq_refl DC' Dz' Ds' Dn') as Dnr'.
  assert (Q : iso (kAt (FC' (ers rho n') (natE (natIdx xn') (natSpec xn'))))
                  (kAt (FC (ers rho n) xn))).
  { apply iso_sym.
    eapply iso_trans; [exact (PCC (ers rho n) xn) |].
    apply isoC'.
    eapply kEqAt_trans; [exact Hnn | apply natEq_self]. }
  pose proof (i_conv rho (natrec C' z' s' n') k _ _ _ _ _ _ Q Dnr') as Dnr.
  assert (En : subst_etm (scons (ers rho n) (rsub rho)) (er C)
               = ers rho (C [n..]))
    by exact (eq_sym (ers_sub1 rho C n (natFam 0) xn)).
  pose proof (isubst_ITy rho n 0 enat (natFam 0) (ers rho n) xn eq_refl Dn
                C k _ (FC (ers rho n) xn) (DC (ers rho n) xn)) as DCsub.
  pose proof (ITy_cast rho (C [n..]) k _ _ En _ DCsub) as DCc.
  assert (Hfun : FunTm G (C [n..])).
  { destruct (ty_subst1 G nat_ C (univ k) n dC dn) as [d].
    exact (FunTm_of_ty G (C [n..]) k d). }
  pose proof (ity_lvl rho rho eq_refl (C [n..]) k (ers rho (C [n..]))
                (famCast En (FC (ers rho n) xn)) k' (ers rho (C [n..])) F DCc DCn)
    as Ek; subst k'.
  refine (itot_move G (natrec C' z' s' n') (C [n..]) Hfun W rho Hrho k F
            (famCast En (FC (ers rho n) xn)) DCn DCc _ _).
  refine (ITm_cast rho (natrec C' z' s' n') k _ _ En (FC (ers rho n) xn) _ _ _).
  exact Dnr.
Qed.

Lemma isem_natrec G C C' z z' s s' n n' k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dC' : ty (nat_ :: G) C' (univ k))
  (cC : cv (nat_ :: G) C C' (univ k))
  (dz : ty G z (C [zero..])) (dz' : ty G z' (C [zero..]))
  (cz : cv G z z' (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C))
  (ds' : ty (C :: nat_ :: G) s' (nrec_succ C))
  (cs : cv (C :: nat_ :: G) s s' (nrec_succ C))
  (dn : ty G n nat_) (dn' : ty G n' nat_) (cn : cv G n n' nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHC' : ITot (nat_ :: G) C' (univ k))
  (IHcC : IRel (nat_ :: G) C C' (univ k))
  (IHz : ITot G z (C [zero..])) (IHz' : ITot G z' (C [zero..]))
  (IHcz : IRel G z z' (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C))
  (IHs' : ITot (C :: nat_ :: G) s' (nrec_succ C))
  (IHcs : IRel (C :: nat_ :: G) s s' (nrec_succ C))
  (IHn : ITot G n nat_) (IHn' : ITot G n' nat_) (IHcn : IRel G n n' nat_) :
  ISem G (natrec C z s n) (natrec C' z' s' n') (C [n..]).
Proof.
  split;
    [split; [exact (itot_natrec G C z s n k W dC dz ds dn IHC IHz IHs IHn)
            | exact (itot_natrec' G C C' z' s' n n' k W dC dC' dz' ds' dn dn'
                       IHC IHC' IHz' IHs' IHcC IHn IHn' IHcn)] |].
  intros rho Hrho k' F DCn x y Dx Dy.
  pose proof (LCv_of_cv G (natrec C z s n) (natrec C' z' s' n') (C [n..])
                (c_natrec G C C' z z' s s' n n' k dC dC' cC dz dz' cz ds ds' cs
                   dn dn' cn) rho rho (EnvRelOf_selfE G rho W Hrho)) as Hrel.
  pose proof (itm_inv rho (natrec C z s n) k' (ers rho (C [n..])) F
                (ers rho (natrec C z s n)) x Dx) as E.
  pose proof (itm_inv rho (natrec C' z' s' n') k' (ers rho (C [n..])) F
                (ers rho (natrec C' z' s' n')) y Dy) as E'.
  destruct k' as [| k0]; cbn [TmInv] in E, E'.
  - destruct E as [HT | E]; [exact (HT _ x _ y Hrel) |].
    destruct E' as [HT' | E']; [exact (HT' _ x _ y Hrel) |].
    exact (isem_natrec_core G C C' z z' s s' n n' k W dC dC' dz dz' ds ds' dn dn'
             IHC IHcC IHz' IHcz IHs' IHcs IHcn rho Hrho 0 _ F x y E E').
  - exact (isem_natrec_core G C C' z z' s s' n n' k W dC dC' dz dz' ds ds' dn dn'
             IHC IHcC IHz' IHcz IHs' IHcs IHcn rho Hrho (S k0) _ F x y E E').
Qed.

Lemma kRel_ctoK {k u u'} (F : kUFam k u) (F' : kUFam k u')
  (P : iso (kAt F) (kAt F')) w (x : kElAt F w) :
  kRel F F' w x w (ctoK (kAt F) (kAt F') P w x).
Proof. apply hetC_to. Qed.

(* Naming a derivation's value without spelling it out. *)
Lemma ITm_pack rho t k w (F : kUFam k w) v (x : kElAt F v) :
  ITm rho t k w F v x -> { y : kElAt F v & (ITm rho t k w F v y * (y = x))%type }.
Proof. intros D; exists x; split; [exact D | reflexivity]. Qed.

(* The step rule's right-hand side is a two-place substitution instance, so its
   typing needs the substitution it performs to be well typed. *)
Lemma sub_ok_rec_succ G C z s n k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C)) (dn : ty G n nat_) :
  sub_ok ((natrec C z s n) .: n ..) (C :: nat_ :: G) G.
Proof.
  intros i A Hl; inversion Hl; subst.
  - replace ((C ⟨↑⟩) [(natrec C z s n) .: n ..]) with (C [n..])
      by (asimpl; reflexivity).
    exact (inhabits (t_natrec G C z s n k dC dz ds dn)).
  - match goal with
    | H : lookup ?i0 (nat_ :: G) ?A0 |- _ => inversion H; subst
    end.
    + replace (((nat_ ⟨↑⟩) ⟨↑⟩) [(natrec C z s n) .: n ..]) with nat_
        by (asimpl; reflexivity).
      exact (inhabits dn).
    + match goal with
      | H : lookup ?i1 G ?A1 |- _ =>
          replace (((A1 ⟨↑⟩) ⟨↑⟩) [(natrec C z s n) .: n ..]) with A1
            by (asimpl; reflexivity);
          exact (inhabits (t_var G i1 A1 W H))
      end.
Qed.

Lemma ty_rec_succ_rhs G C z s n k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C)) (dn : ty G n nat_) :
  inhabited (ty G (s [(natrec C z s n) .: n ..]) (C [(succ n)..])).
Proof.
  destruct (proj1 (proj2 substitution) (C :: nat_ :: G) s (nrec_succ C) ds G
              ((natrec C z s n) .: n ..)
              (sub_ok_rec_succ G C z s n k W dC dz ds dn) (inhabits W)) as [d].
  replace ((nrec_succ C) [(natrec C z s n) .: n ..]) with (C [(succ n)..]) in d
    by (unfold nrec_succ; asimpl; reflexivity).
  exact (inhabits d).
Qed.

(* One unfolding of the recursor at a successor: the value is the step applied
   to the predecessor and the recursive result, up to the realiser's
   expansion. *)
Lemma semrec_succ_step (k k0 : nat)
  (SC : etm -> etm) (FC : forall m (x : kElAt (natFam k0) m), kUFam k (SC m))
  (isoC : forall m x m' x', kEqAt (natFam k0) m x m' x' ->
            iso (kAt (FC m x)) (kAt (FC m' x')))
  (zr sr : etm) (xz : kElAt (FC ezero (natE 0 NatAt_zero)) zr)
  (step : forall m x w (y : kElAt (FC m x) w),
            kElAt (FC (esucc m) (natSucc x)) (eapp (eapp sr m) w))
  j u (e : NatAt j u) :
  kRel (FC (esucc u) (natSucc (natE j e))) (FC (esucc u) (natSucc (natE j e)))
       (enatrec zr sr (esucc u))
       (semrec k k0 SC FC isoC zr sr xz step (S j) (esucc u) (NatAt_succ j u e))
       (eapp (eapp sr u) (enatrec zr sr u))
       (step u (natE j e) (enatrec zr sr u)
          (semrec k k0 SC FC isoC zr sr xz step j u e)).
Proof.
  cbn [semrec NatAt_pred NatAt_pred_at].
  apply kRel_sym; apply moveTo_rel.
Qed.

(* ---- the step rule ---- *)
Lemma rec_succ_data G C z s n k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C)) (dn : ty G n nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHz : ITot G z (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C)) (IHn : ITot G n nat_)
  rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam k S1 &
  { v1 : kElAt F1 (ers rho (natrec C z s (succ n))) &
  { w2 : etm & { v2 : kElAt F1 w2 &
    (ITy rho (C [(succ n)..]) k S1 F1 *
     ITm rho (natrec C z s (succ n)) k S1 F1
         (ers rho (natrec C z s (succ n))) v1 *
     ITm rho (s [(natrec C z s n) .: n ..]) k S1 F1 w2 v2 *
     kEqAt F1 (ers rho (natrec C z s (succ n))) v1 w2 v2)%type } } } } }.
Proof.
  destruct (build_rec_data G C z s k W dC dz ds IHC IHz IHs rho Hrho)
    as [FC [isoC [xz [xs [[[DC Dz] Ds] Hfs]]]]].
  destruct (IHn rho Hrho 0 (natFam 0) (ity_nat rho (ers rho nat_) eq_refl))
    as [xn Dn].
  pose (ws := fun m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w) =>
                ers (ext (ext rho (natFam 0) m x) (FC m x) w y) s).
  pose (redS := fun m (x : kElAt (natFam 0) m) w (y : kElAt (FC m x) w) =>
                  reds_lam2_app (er s) (rsub rho) m w).
  (* the recursive call, moved to the scrutinee's own value *)
  pose proof (i_natrec rho C z s n k (fun m => subst_etm (scons m (rsub rho)) (er C))
                FC isoC (ers rho (stepWrap s)) (ers rho z) xz ws xs redS
                (ers rho n) xn eq_refl DC Dz Ds Dn) as Dnr.
  pose proof (i_conv rho (natrec C z s n) k _ _ _ _ _ _
                (isoC (ers rho n) (natE (natIdx xn) (natSpec xn)) (ers rho n) xn
                   (natEq_self _ _)) Dnr) as Dyr.
  destruct (ITm_pack rho (natrec C z s n) k _ (FC (ers rho n) xn) _ _ Dyr)
    as [yrec [Dyrec Ey]].
  pose proof (Ds (ers rho n) xn (ers rho (natrec C z s n)) yrec) as Dstep.
  (* the two substitutions *)
  pose proof (subst_ITm rho n (Build_Entry 0 enat (natFam 0) (ers rho n) xn)
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
    by (cbn [upn]; asimpl; reflexivity).
  assert (D3 : ITm rho (s [(natrec C z s n) .: n ..]) k
                 (subst_etm (scons (esucc (ers rho n)) (rsub rho)) (er C))
                 (FC (esucc (ers rho n)) (natSucc xn))
                 (ers (ext (ext rho (natFam 0) (ers rho n) xn) (FC (ers rho n) xn)
                         (ers rho (natrec C z s n)) yrec) s)
                 (xs (ers rho n) xn (ers rho (natrec C z s n)) yrec))
    by (rewrite <- Esub; exact D2).
  (* the left-hand side *)
  pose proof (i_succ rho n (ers rho n) xn Dn) as Dsn.
  pose proof (i_natrec rho C z s (succ n) k
                (fun m => subst_etm (scons m (rsub rho)) (er C)) FC isoC
                (ers rho (stepWrap s)) (ers rho z) xz ws xs redS
                (esucc (ers rho n)) (natSucc xn) eq_refl DC Dz Ds Dsn) as Dlhs.
  destruct (ITm_pack rho (natrec C z s (succ n)) k _
              (FC (esucc (ers rho n)) (natSucc xn)) _ _ Dlhs) as [v1 [Dv1 Ev1]].
  exists (subst_etm (scons (esucc (ers rho n)) (rsub rho)) (er C)),
    (FC (esucc (ers rho n)) (natSucc xn)), v1,
    (ers (ext (ext rho (natFam 0) (ers rho n) xn) (FC (ers rho n) xn)
            (ers rho (natrec C z s n)) yrec) s),
    (xs (ers rho n) xn (ers rho (natrec C z s n)) yrec).
  split; [split; [split |] |].
  - exact (isubst_ITy rho (succ n) 0 enat (natFam 0) (esucc (ers rho n))
             (natSucc xn) eq_refl Dsn C k _
             (FC (esucc (ers rho n)) (natSucc xn))
             (DC (esucc (ers rho n)) (natSucc xn))).
  - exact Dv1.
  - exact D3.
  - rewrite Ev1.
    apply (proj2 (kRel_same _ _ _ _ _)).
    eapply kRel_trans;
      [ exact (semrec_succ_step k 0
                 (fun m => subst_etm (scons m (rsub rho)) (er C)) FC isoC
                 (ers rho z) (ers rho (stepWrap s)) xz
                 (fun m x w y =>
                    moveTo (FC (esucc m) (natSucc x)) (FC (esucc m) (natSucc x))
                      (iso_self (FC (esucc m) (natSucc x))) (ws m x w y)
                      (xs m x w y) (eapp (eapp (ers rho (stepWrap s)) m) w)
                      (redS m x w y))
                 (natIdx xn) (ers rho n) (natSpec xn)) |].
    eapply kRel_trans; [apply kRel_sym; apply moveTo_rel |].
    rewrite Ey.
    apply Hfs; [apply natEq_self | apply kRel_ctoK].
Qed.

Lemma isem_rec_succ G C z s n k (W : wfc G)
  (dC : ty (nat_ :: G) C (univ k)) (dz : ty G z (C [zero..]))
  (ds : ty (C :: nat_ :: G) s (nrec_succ C)) (dn : ty G n nat_)
  (IHC : ITot (nat_ :: G) C (univ k)) (IHz : ITot G z (C [zero..]))
  (IHs : ITot (C :: nat_ :: G) s (nrec_succ C)) (IHn : ITot G n nat_) :
  ISem G (natrec C z s (succ n)) (s [(natrec C z s n) .: n ..]) (C [(succ n)..]).
Proof.
  assert (fL : FunTm G (natrec C z s (succ n)))
    by exact (funtm G (natrec C z s (succ n)) (C [(succ n)..])
                (t_natrec G C z s (succ n) k dC dz ds (t_succ G n dn))).
  assert (fR : FunTm G (s [(natrec C z s n) .: n ..])).
  { destruct (ty_rec_succ_rhs G C z s n k W dC dz ds dn) as [d].
    exact (funtm G (s [(natrec C z s n) .: n ..]) (C [(succ n)..]) d). }
  assert (fT : FunTm G (C [(succ n)..])).
  { destruct (ty_subst1 G nat_ C (univ k) (succ n) dC (t_succ G n dn)) as [d].
    exact (FunTm_of_ty G (C [(succ n)..]) k d). }
  assert (gR : forall rho, EnvRelOf G rho rho ->
             Rel (ers rho (C [(succ n)..]))
               (ers rho (s [(natrec C z s n) .: n ..]))
               (ers rho (s [(natrec C z s n) .: n ..]))).
  { intros rho HE.
    destruct (ty_rec_succ_rhs G C z s n k W dC dz ds dn) as [d].
    exact (LTm_of_ty G (s [(natrec C z s n) .: n ..]) (C [(succ n)..]) d
             rho rho HE). }
  split.
  - split.
    + exact (itot_natrec G C z s (succ n) k W dC dz ds (t_succ G n dn)
               IHC IHz IHs (itot_succ G W n IHn)).
    + intros rho Hrho k' F DCn.
      destruct (rec_succ_data G C z s n k W dC dz ds dn IHC IHz IHs IHn rho Hrho)
        as [S1 [F1 [v1 [w2 [v2 [[[DT Dv1] Dv2] Hmid]]]]]].
      assert (ES1 : S1 = ers rho (C [(succ n)..]))
        by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      assert (E2 : w2 = ers rho (s [(natrec C z s n) .: n ..]))
        by exact (ers_of_ITm _ _ _ _ _ _ _ Dv2).
      subst w2.
      pose proof (ity_lvl rho rho eq_refl (C [(succ n)..]) k _ F1 k' _ F DT DCn)
        as Ek; subst k'.
      pose proof (ity_same_iso G (C [(succ n)..]) fT rho W Hrho k F1 F DT DCn)
        as P.
      exists (ctoK _ _ P _ v2).
      exact (i_conv rho (s [(natrec C z s n) .: n ..]) k _ F1 _ F _ v2 P Dv2).
  - intros rho Hrho k' F DCn x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
    destruct (rec_succ_data G C z s n k W dC dz ds dn IHC IHz IHs IHn rho Hrho)
      as [S1 [F1 [v1 [w2 [v2 [[[DT Dv1] Dv2] Hmid]]]]]].
    assert (ES1 : S1 = ers rho (C [(succ n)..]))
      by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    assert (E2 : w2 = ers rho (s [(natrec C z s n) .: n ..]))
      by exact (ers_of_ITm _ _ _ _ _ _ _ Dv2).
    subst w2.
    pose proof (ity_lvl rho rho eq_refl (C [(succ n)..]) k _ F1 k' _ F DT DCn)
      as Ek; subst k'.
    pose proof (ity_same_iso G (C [(succ n)..]) fT rho W Hrho k F F1 DCn DT) as P.
    pose proof (fL rho rho HEself k _ F _ x Dx _ F1 _ v1 Dv1 P
                  (LTm_of_ty G (natrec C z s (succ n)) (C [(succ n)..])
                     (t_natrec G C z s (succ n) k dC dz ds (t_succ G n dn))
                     rho rho HEself)) as H1.
    pose proof (fR rho rho HEself k _ F1 _ v2 Dv2 _ F _ y Dy (iso_sym _ _ P)
                  (gR rho HEself)) as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans; [apply (proj1 (kRel_same F1 _ _ _ _)); exact Hmid | exact H2].
Qed.

(* ---- eta.  The subject is a lambda whose body is an application of the
     WEAKENED function to the variable, so its data is the original Pi-data
     weakened (weaken_ITy / weaken1) and its value at every argument is the
     function's own application: piEl_of builds the lambda, and piEq_of
     compares it with the function. ---- *)
Lemma ty_eta_lam G A B f k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df : ty G f (pi A B)) :
  inhabited (ty G (lam A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))
               (pi A B)).
Proof.
  pose proof (w_cons G A k W dA) as WA.
  destruct (proj1 (proj2 renaming) G A (univ k) dA (A :: G) shift
              (ren_ok_shift G A) (inhabits WA)) as [dA1].
  destruct (proj1 (proj2 renaming) (A :: G) B (univ k) dB ((A ⟨↑⟩) :: A :: G)
              (upRen_tm_tm shift)
              (ren_ok_up shift G (A :: G) A (ren_ok_shift G A))
              (inhabits (w_cons (A :: G) (A ⟨↑⟩) k WA dA1))) as [dB1].
  destruct (proj1 (proj2 renaming) G f (pi A B) df (A :: G) shift
              (ren_ok_shift G A) (inhabits WA)) as [df1].
  pose proof (t_app (A :: G) (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0) k
                dA1 dB1 df1
                (t_var (A :: G) 0 (A ⟨↑⟩) WA (lookup_O G A))) as dap.
  replace ((B ⟨upRen_tm_tm shift⟩) [(var_tm 0)..]) with B in dap.
  2: { asimpl; symmetry; apply idSubst_tm; intros [| i]; reflexivity. }
  exact (inhabits (t_lam G A B _ k dA dB dap)).
Qed.

Lemma eta_value G A B f k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df : ty G f (pi A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHf : ITot G f (pi A B)) rho (Hrho : EnvITy G rho) :
  { S1 : etm & { F1 : kUFam k S1 &
  { xl : kElAt F1 (ers rho (lam A B
           (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) &
  { xf : kElAt F1 (ers rho f) &
    (ITy rho (pi A B) k S1 F1 *
     ITm rho (lam A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))
         k S1 F1 (ers rho (lam A B
           (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) xl *
     ITm rho f k S1 F1 (ers rho f) xf *
     kEqAt F1 (ers rho (lam A B
           (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) xl
           (ers rho f) xf)%type } } } }.
Proof.
  pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
  destruct (build_fam_data G A B k W dA dB IHA IHB rho Hrho)
    as [FA [FB [[DFA DB] isoB]]].
  pose (B0 := elam (subst_etm (up_etm_etm (rsub rho)) (er B))).
  pose (redB := fun u0 (x : kElAt FA u0) => reds_beta_sub (rsub rho) (er B) u0).
  pose (gPi := LTyK_of_ty G (pi A B) k (t_pi G A B k dA dB) rho rho HEself).
  pose proof (ity_pi rho A B k (ers rho A) FA B0
                (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                eq_refl DFA DB) as Dpi.
  destruct (IHf rho Hrho k
              (piFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
                 redB isoB gPi) Dpi) as [xf Df].
  (* the body's data, weakened *)
  assert (Ep : forall u (y : kElAt FA u),
             epi (ers rho A) B0
             = ers (ext rho FA u y) (pi (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩)))
    by (intros u y;
        exact (eq_sym (ers_shift_en (Build_Entry k (ers rho A) FA u y) rho
                         (pi A B)))).
  assert (DAw : forall u (y : kElAt FA u),
             ITy (ext rho FA u y) (A ⟨↑⟩) k (ers rho A) FA)
    by (intros u y;
        exact (weaken_ITy rho A k (ers rho A) FA DFA nil rho
                 (Build_Entry k (ers rho A) FA u y) eq_refl)).
  assert (DBw : forall u (y : kElAt FA u) u' (y' : kElAt FA u'),
             ITy (ext (ext rho FA u y) FA u' y') (B ⟨upRen_tm_tm shift⟩) k
                 (ers (ext rho FA u' y') B) (FB u' y'))
    by (intros u y u' y';
        exact (weaken_ITy (ext rho FA u' y') B k _ (FB u' y') (DB u' y')
                 (Build_Entry k (ers rho A) FA u' y' :: nil) rho
                 (Build_Entry k (ers rho A) FA u y) eq_refl)).
  assert (Dfw : forall u (y : kElAt FA u),
             ITm (ext rho FA u y) (f ⟨↑⟩) k (epi (ers rho A) B0)
                 (piFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
                    FB redB isoB gPi) (ers rho f) xf)
    by (intros u y;
        exact (weaken1 rho f k _ _ (ers rho f) xf
                 (Build_Entry k (ers rho A) FA u y) Df)).
  assert (Dbody : forall u (y : kElAt FA u),
             ITm (ext rho FA u y)
                 (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)) k
                 (ers (ext rho FA u y) B) (FB u y) (eapp (ers rho f) u)
                 (piApp k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
                    FB redB isoB gPi (ers rho f) xf u y))
    by (intros u y;
        exact (i_app (ext rho FA u y) (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩)
                 (var_tm 0) k (ers rho A) FA B0
                 (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                 (ers rho f) xf u y (Ep u y) (DAw u y) (DBw u y) (Dfw u y)
                 (i_var0 rho k (ers rho A) FA u y))).
  (* the lambda's realiser beta-reduces to the application's *)
  assert (Ebody : forall u (y : kElAt FA u),
             ers (ext rho FA u y)
               (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))
             = eapp (ers rho f) u)
    by (intros u y;
        exact (f_equal (fun z => eapp z u)
                 (ers_shift_en (Build_Entry k (ers rho A) FA u y) rho f))).
  assert (redw : forall u (y : kElAt FA u),
             reds (eapp (ers rho (lam A B
                     (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) u)
                  (eapp (ers rho f) u)).
  { intros u y.
    rewrite <- (Ebody u y).
    exact (reds_beta_sub (rsub rho)
             (er (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))) u). }
  assert (Hfun : forall u y u' y', kEqAt FA u y u' y' ->
             kRel (FB u y) (FB u' y')
                  (eapp (ers rho f) u)
                  (piApp k (ers rho A) B0 FA
                     (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                     (ers rho f) xf u y)
                  (eapp (ers rho f) u')
                  (piApp k (ers rho A) B0 FA
                     (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                     (ers rho f) xf u' y')).
  { intros u y u' y' Hyy.
    apply (piApp_eq k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B)
             FB redB isoB gPi);
      [ apply kEqAt_refl | exact Hyy ]. }
  assert (gw : Good (epi (ers rho A) B0)
                 (ers rho (lam A B
                    (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))))).
  { destruct (ty_eta_lam G A B f k W dA dB df) as [d].
    exact (LTm_of_ty G _ (pi A B) d rho rho HEself). }
  destruct (piEl_of k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
              redB isoB gPi
              (ers rho (lam A B
                 (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) gw
              (fun u y => eapp (ers rho f) u)
              (fun u y => piApp k (ers rho A) B0 FA
                            (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB gPi
                            (ers rho f) xf u y)
              redw Hfun) as [xl Hbeh].
  pose proof (i_lam rho A B
                (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)) k
                (ers rho A) FA B0 (fun u0 x => ers (ext rho FA u0 x) B) FB
                redB isoB gPi
                (ers rho (lam A B
                   (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))) xl
                (fun u y => eapp (ers rho f) u)
                (fun u y => piApp k (ers rho A) B0 FA
                              (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB
                              gPi (ers rho f) xf u y)
                eq_refl eq_refl DFA DB Dbody Hbeh) as Dl.
  exists (epi (ers rho A) B0),
    (piFam k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB redB isoB
       gPi), xl, xf.
  split; [split; [split; [exact Dpi | exact Dl] | exact Df] |].
  apply (piEq_of k (ers rho A) B0 FA (fun u0 x => ers (ext rho FA u0 x) B) FB
           redB isoB gPi).
  - exact (LCv_of_cv G _ f (pi A B) (c_eta G A B f k dA dB df) rho rho HEself).
  - intros v y v' y' Hyy.
    eapply kRel_trans;
      [ apply (proj1 (kRel_same (FB v y) _ _ _ _)); exact (Hbeh v y) |].
    exact (Hfun v y v' y' Hyy).
Qed.

Lemma isem_eta G A B f k (W : wfc G) (dA : ty G A (univ k))
  (dB : ty (A :: G) B (univ k)) (df : ty G f (pi A B))
  (IHA : ITot G A (univ k)) (IHB : ITot (A :: G) B (univ k))
  (IHf : ITot G f (pi A B)) :
  ISem G (lam A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))) f
    (pi A B).
Proof.
  assert (fL : FunTm G (lam A B
                 (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0)))).
  { destruct (ty_eta_lam G A B f k W dA dB df) as [d].
    exact (funtm G _ (pi A B) d). }
  assert (gL : forall rho, EnvRelOf G rho rho ->
             Rel (ers rho (pi A B))
               (ers rho (lam A B
                  (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))))
               (ers rho (lam A B
                  (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))))).
  { intros rho HE.
    destruct (ty_eta_lam G A B f k W dA dB df) as [d].
    exact (LTm_of_ty G _ (pi A B) d rho rho HE). }
  assert (fT : FunTm G (pi A B))
    by exact (FunTm_of_ty G (pi A B) k (t_pi G A B k dA dB)).
  split.
  - split.
    + intros rho Hrho k' F DPi.
      destruct (eta_value G A B f k W dA dB df IHA IHB IHf rho Hrho)
        as [S1 [F1 [xl [xf [[[DT Dl] Df] Hcv]]]]].
      assert (ES1 : S1 = ers rho (pi A B)) by exact (ers_of_ITy _ _ _ _ _ DT).
      subst S1.
      pose proof (ity_lvl rho rho eq_refl (pi A B) k _ F1 k' _ F DT DPi) as Ek;
        subst k'.
      pose proof (ity_same_iso G (pi A B) fT rho W Hrho k F1 F DT DPi) as P.
      exists (ctoK _ _ P _ xl).
      exact (i_conv rho _ k _ F1 _ F _ xl P Dl).
    + exact IHf.
  - intros rho Hrho k' F DPi x y Dx Dy.
    pose proof (EnvRelOf_selfE G rho W Hrho) as HEself.
    destruct (eta_value G A B f k W dA dB df IHA IHB IHf rho Hrho)
      as [S1 [F1 [xl [xf [[[DT Dl] Df] Hcv]]]]].
    assert (ES1 : S1 = ers rho (pi A B)) by exact (ers_of_ITy _ _ _ _ _ DT).
    subst S1.
    pose proof (ity_lvl rho rho eq_refl (pi A B) k _ F1 k' _ F DT DPi) as Ek;
      subst k'.
    pose proof (ity_same_iso G (pi A B) fT rho W Hrho k F F1 DPi DT) as P.
    pose proof (fL rho rho HEself k _ F _ x Dx _ F1 _ xl Dl P (gL rho HEself))
      as H1.
    pose proof (funtm G f (pi A B) df rho rho HEself k _ F1 _ xf Df _ F _ y Dy
                  (iso_sym _ _ P) (LTm_of_ty G f (pi A B) df rho rho HEself))
      as H2.
    apply (proj2 (kRel_same F _ _ _ _)).
    eapply kRel_trans; [exact H1 |].
    eapply kRel_trans;
      [ apply (proj1 (kRel_same F1 _ _ _ _)); exact Hcv | exact H2 ].
Qed.

(* ================================================================== *)
(* THEOREM 9.2: the induction.                                         *)
(*                                                                    *)
(* Everything is Type-valued, so the schemes are the Type-sorted ones   *)
(* and there is no Combined Scheme; the conversion judgement's scheme    *)
(* suffices, because c_refl turns a typing derivation into a conversion  *)
(* and ISem's first component is then the term's totality.              *)
(*                                                                    *)
(* The context's well-formedness travels in the motive: no rule but the  *)
(* structural ones carries a wfc premise, and every rule has at least    *)
(* one premise in the SAME context, so wfc G is read off that premise's  *)
(* own conclusion.                                                      *)
(* ================================================================== *)

Scheme wfc_rect2 := Induction for wfc Sort Type
  with ty_rect2 := Induction for ty Sort Type
  with cv_rect2 := Induction for cv Sort Type.

Theorem fund_cv : forall G t u A (c : cv G t u A), (wfc G * ISem G t u A)%type.
Proof.
  apply (cv_rect2 (fun G _ => wfc G)
           (fun G t A _ => (wfc G * ITot G t A)%type)
           (fun G t u A _ => (wfc G * ISem G t u A)%type)).
  (* ---- wfc ---- *)
  - exact w_nil.
  - intros G A k W IHW dA IHA; exact (w_cons G A k W dA).
  (* ---- ty ---- *)
  - intros G i A W IHW Hl; exact (W, itot_var G i A W Hl).
  - intros G t A B k dt [W IHt] dA [_ IHA] dB [_ IHB] cAB [_ [[_ _] Hc]];
      exact (W, itot_conv G t A B k W dA dB IHt IHA IHB Hc).
  - intros G k W IHW; exact (W, itot_univ G W k).
  - intros G A k dA [W IHA]; exact (W, itot_up G A k W dA IHA).
  - intros G A t k dA [W IHA] dt [_ IHt];
      exact (W, itot_uptm G A t k W dA dt IHA IHt).
  - intros G A B k dA [W IHA] dB [_ IHB];
      exact (W, itot_pi G A B k W dA dB IHA IHB).
  - intros G A B t k dA [W IHA] dB [_ IHB] dt [_ IHt];
      exact (W, itot_lam G A B t k W dA dB dt IHA IHB IHt).
  - intros G A B f u k dA [W IHA] dB [_ IHB] df [_ IHf] du [_ IHu];
      exact (W, itot_app G A B f u k W dA dB df du IHA IHB IHf IHu).
  - intros G A B k dA [W IHA] dB [_ IHB];
      exact (W, itot_sig G A B k W dA dB IHA IHB).
  - intros G A B t u k dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, itot_pair G A B t u k W dA dB dt du IHA IHB IHt IHu).
  - intros G A B p k dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, itot_fst G A B p k W dA dB dp IHA IHB IHp).
  - intros G A B p k dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, itot_snd G A B p k W dA dB dp IHA IHB IHp).
  - intros G W IHW; exact (W, itot_nat G W).
  - intros G W IHW; exact (W, itot_zero G W).
  - intros G n dn [W IHn]; exact (W, itot_succ G W n IHn).
  - intros G C z s n k dC [_ IHC] dz [W IHz] ds [_ IHs] dn [_ IHn];
      exact (W, itot_natrec G C z s n k W dC dz ds dn IHC IHz IHs IHn).
  - intros G W IHW; exact (W, itot_prop G W).
  - intros G p dp [W IHp]; exact (W, itot_prf G p W dp IHp).
  - intros G A p k dA [W IHA] dp [_ IHp];
      exact (W, itot_all G A p k W dA dp IHA IHp).
  - intros G A p t k dA [W IHA] dp [_ IHp] dt [_ IHt];
      exact (W, itot_plam G A p t k W dA dp dt IHA IHp IHt).
  - intros G A p f u k dA [W IHA] dp [_ IHp] df [_ IHf] du [_ IHu];
      exact (W, itot_papp G A p f u k W dA dp df du IHA IHp IHf IHu).
  - intros G W IHW; exact (W, itot_false G W).
  - intros G T e k dT [W IHT] de [_ IHe]; exact (W, itot_absurd G T e IHe).
  (* ---- cv ---- *)
  - intros G t A d [W IHd]; exact (W, isem_refl G t A d IHd).
  - intros G t u A c [W IHc]; exact (W, isem_sym G t u A IHc).
  - intros G t u v A c1 [W IH1] c2 [_ IH2];
      exact (W, isem_trans G t u v A IH1 IH2).
  - intros G t u A B k c [W IHc] dA [_ IHA] dB [_ IHB] cAB [_ [[_ _] Hc]];
      exact (W, isem_conv G t u A B k W dA dB IHc IHA IHB Hc).
  - intros G p e e' dp [W IHp] de [_ IHe] de' [_ IHe'];
      exact (W, isem_prf_irr G p e e' de de' IHe IHe').
  - intros G A A' k dA [W IHA] dA' [_ IHA'] cA [_ [[_ _] HcA]];
      exact (W, isem_up G A A' k W dA dA' cA IHA IHA' HcA).
  - intros G A t t' k dA [W IHA] dt [_ IHt] dt' [_ IHt'] ct [_ [[_ _] Hct]];
      exact (W, isem_uptm G A t t' k W dA dt dt' ct IHA IHt IHt' Hct).
  - intros G A A' B B' k dA [W IHA] dB [_ IHB] dA' [_ IHA'] dB' [_ IHB']
      cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]];
      exact (W, isem_pi G A A' B B' k W dA dB dA' dB' cA cB
               IHA IHB IHA' IHB' HcA HcB).
  - intros G A A' B B' t t' k dA [W IHA] dB [_ IHB] dA' [_ IHA'] dB' [_ IHB']
      cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]] dt [_ IHt] dt' [_ IHt']
      ct [_ [[_ IHt2] Hct]];
      exact (W, isem_lam G A A' B B' t t' k W dA dB dA' dB' cA cB dt dt' ct
               IHA IHB IHA' IHB' HcA HcB IHt IHt2 IHt' Hct).
  - intros G A B f f' u u' k dA [W IHA] dB [_ IHB] df [_ IHf] df' [_ IHf']
      cf [_ [[_ _] Hcf]] du [_ IHu] du' [_ IHu'] cu [_ [[_ _] Hcu]];
      exact (W, isem_app G A B f f' u u' k W dA dB df df' cf du du' cu
               IHA IHB IHf IHf' Hcf IHu IHu' Hcu).
  - intros G A B t u k dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_beta G A B t u k W dA dB dt du IHA IHB IHt IHu).
  - intros G A B f k dA [W IHA] dB [_ IHB] df [_ IHf];
      exact (W, isem_eta G A B f k W dA dB df IHA IHB IHf).
  - intros G A A' B B' k dA [W IHA] dB [_ IHB] dA' [_ IHA'] dB' [_ IHB']
      cA [_ [[_ _] HcA]] cB [_ [[_ _] HcB]];
      exact (W, isem_sig G A A' B B' k W dA dB dA' dB' cA cB
               IHA IHB IHA' IHB' HcA HcB).
  - intros G A B t t' u u' k dA [W IHA] dB [_ IHB] dt [_ IHt] dt' [_ IHt']
      ct [_ [[_ _] Hct]] du [_ IHu] du' [_ IHu'] cu [_ [[_ _] Hcu]];
      exact (W, isem_pair G A B t t' u u' k W dA dB dt dt' ct du du' cu
               IHA IHB IHt IHt' Hct IHu IHu' Hcu).
  - intros G A B p p' k dA [W IHA] dB [_ IHB] dp [_ IHp] dp' [_ IHp']
      cp [_ [[_ _] Hcp]];
      exact (W, isem_fst G A B p p' k W dA dB dp dp' cp IHA IHB IHp IHp' Hcp).
  - intros G A B p p' k dA [W IHA] dB [_ IHB] dp [_ IHp] dp' [_ IHp']
      cp [_ [[_ _] Hcp]];
      exact (W, isem_snd G A B p p' k W dA dB dp dp' cp IHA IHB IHp IHp' Hcp).
  - intros G A B t u k dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_fst_beta G A B t u k W dA dB dt du IHA IHB IHt IHu).
  - intros G A B t u k dA [W IHA] dB [_ IHB] dt [_ IHt] du [_ IHu];
      exact (W, isem_snd_beta G A B t u k W dA dB dt du IHA IHB IHt IHu).
  - intros G A B p k dA [W IHA] dB [_ IHB] dp [_ IHp];
      exact (W, isem_surj G A B p k W dA dB dp IHA IHB IHp).
  - intros G n n' dn [W IHn] dn' [_ IHn'] cn [_ [[_ _] Hcn]];
      exact (W, isem_succ G n n' W dn dn' cn IHn IHn' Hcn).
  - intros G C C' z z' s s' n n' k dC [_ IHC] dC' [_ IHC'] cC [_ [[_ _] HcC]]
      dz [W IHz] dz' [_ IHz'] cz [_ [[_ _] Hcz]] ds [_ IHs] ds' [_ IHs']
      cs [_ [[_ _] Hcs]] dn [_ IHn] dn' [_ IHn'] cn [_ [[_ _] Hcn]];
      exact (W, isem_natrec G C C' z z' s s' n n' k W dC dC' cC dz dz' cz
               ds ds' cs dn dn' cn IHC IHC' HcC IHz IHz' Hcz IHs IHs' Hcs
               IHn IHn' Hcn).
  - intros G C z s k dC [_ IHC] dz [W IHz] ds [_ IHs];
      exact (W, isem_rec_zero G C z s k W dC dz ds IHC IHz IHs).
  - intros G C z s n k dC [_ IHC] dz [W IHz] ds [_ IHs] dn [_ IHn];
      exact (W, isem_rec_succ G C z s n k W dC dz ds dn IHC IHz IHs IHn).
  - intros G p p' dp [W IHp] dp' [_ IHp'] cp [_ [[_ _] Hcp]];
      exact (W, isem_prf G p p' W dp dp' cp IHp IHp' Hcp).
  - intros G A A' p p' k dA [W IHA] dp [_ IHp] dA' [_ IHA'] dp' [_ IHp']
      cA [_ [[_ _] HcA]] cp2 [_ [[_ _] Hcp]];
      exact (W, isem_all G A A' p p' k W dA dp dA' dp' cA cp2
               IHA IHp IHA' IHp' HcA Hcp).
Qed.

(* Totality, by reflexivity of conversion. *)
Theorem fund_tot G t A (d : ty G t A) : (wfc G * ITot G t A)%type.
Proof.
  destruct (fund_cv G t t A (c_refl G t A d)) as [W [[Ht _] _]].
  exact (W, Ht).
Qed.
