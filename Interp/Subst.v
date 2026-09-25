From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.SigFam Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.SigEl
  Interp.Rec Interp.Lift Interp.Def Interp.Inv Interp.Ctx.
From Stdlib Require Import Arith Lia List.

Import UnscopedNotations.
Open Scope list_scope.
Open Scope subst_scope.

(* Blueprint Lemma 9.1: semantic substitution.

   Substituting a term for a variable IS extending the environment by that
   term's value.  The lemma is stated under a prefix of extra entries, because
   the induction goes under binders: `delta` is what the binders added, and the
   syntactic substitution is correspondingly `a..` pushed under |delta| ups.

   Entries are self-contained -- an Entry carries its own family and realiser,
   with no reference to the environment it sits in -- so `delta ++ rho` and
   `delta ++ ext rho FA _ xa` are both environments without any adjustment.
   That is what keeps this lemma about substitutions and not about environments.

   Since the realisers are free indices of ITy and ITm (see Interp/Def.v),
   NEITHER weakening NOR substitution touches a realiser, a family or a value:
   they change the environment and the term, and rewrite the one equation that
   pins the realiser to the erasure.  That is the whole content of the
   free-realiser form -- with the realiser computed, each of these lemmas would
   have had to transport the family, and every component indexed by it. *)

(* ------------------------------------------------------------------ *)
(* Renaming: inserting an entry at depth |delta|.                     *)
(* ------------------------------------------------------------------ *)

Fixpoint upn (n : nat) (sigma : nat -> tm) : nat -> tm :=
  match n with
  | 0 => sigma
  | S n0 => up_tm_tm (upn n0 sigma)
  end.

Fixpoint upnr (n : nat) (xi : nat -> nat) : nat -> nat :=
  match n with
  | 0 => xi
  | S n0 => upRen_tm_tm (upnr n0 xi)
  end.

Lemma rsub_upnr (rho : Env) (d : Entry) :
  forall (delta : list Entry) i,
    rsub (delta ++ d :: rho) (upnr (length delta) shift i) = rsub (delta ++ rho) i.
Proof.
  induction delta as [| e delta IH]; intros i; cbn; [reflexivity |].
  destruct i as [| j]; cbn; [reflexivity | apply IH].
Qed.

Lemma ers_upnr (rho : Env) (d : Entry) (delta : list Entry) (t : tm) :
  ers (delta ++ d :: rho) (t ⟨upnr (length delta) shift⟩) = ers (delta ++ rho) t.
Proof.
  unfold ers; rewrite er_ren, renSubst_etm.
  apply ext_etm; intros i; apply (rsub_upnr rho d delta i).
Qed.

(* And the same for a substitution at depth |delta|. *)
Lemma rsub_upn (rho : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho a) :
  forall (delta : list Entry) i,
    subst_etm (rsub (delta ++ rho)) (er (upn (length delta) (a..) i))
    = rsub (delta ++ en :: rho) i.
Proof.
  induction delta as [| d delta IH]; intros i; cbn.
  - destruct i as [| j]; cbn; [exact (eq_sym Hua) | reflexivity].
  - destruct i as [| j]; cbn; [reflexivity |].
    unfold funcomp; rewrite er_ren, sub_shift.
    rewrite (ext_etm (funcomp (scons (en_u d) (rsub (delta ++ rho))) shift)
               (rsub (delta ++ rho)) (fun y => eq_refl)).
    apply IH.
Qed.

Lemma ers_upn (rho : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho a)
  (delta : list Entry) (t : tm) :
  ers (delta ++ rho) (t [upn (length delta) (a..)])
  = ers (delta ++ en :: rho) t.
Proof.
  unfold ers; rewrite er_subst, substSubst_etm.
  apply ext_etm; intros i; apply (rsub_upn rho a en Hua delta i).
Qed.

(* ------------------------------------------------------------------ *)
(* Weakening.  The family, the realiser and the value are UNCHANGED;   *)
(* only the environment, the term and the pinning equation move.       *)
(* ------------------------------------------------------------------ *)

Definition WTy (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  forall delta rho0 d, rho = delta ++ rho0 ->
    ITy (delta ++ d :: rho0) (A ⟨upnr (length delta) shift⟩) k w F.

Definition WTm (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy) (w : etm)
  (x : kElAt F w) : Type :=
  forall delta rho0 d, rho = delta ++ rho0 ->
    ITm (delta ++ d :: rho0) (t ⟨upnr (length delta) shift⟩) k Sy F w x.

Scheme ITy_mut := Induction for ITy Sort Type
  with ITm_mut := Induction for ITm Sort Type.

(* The pin, moved: the realiser is unchanged, so only the equation that ties it
   to the erasure has to travel, and ers_upnr is exactly that travel. *)
Ltac pin_for t0 :=
  subst;
  first
    [ reflexivity
    | match goal with
      | |- ?w = ers (?delta ++ ?d :: ?rho0) _ =>
          first
            [ match goal with
              | H : w = ers (delta ++ rho0) t0 |- _ =>
                  exact (eq_trans H (eq_sym (ers_upnr rho0 d delta t0)))
              end
            | exact (eq_sym (ers_upnr rho0 d delta t0)) ]
      end ].

Ltac wc1 := unfold WTy, WTm; (* ity_nat *) intros rho w Ew delta rho0 d E;
      apply (ity_nat _ w); pin_for nat_.

Ltac wc2 := unfold WTy, WTm; (* ity_prop *) intros rho w Ew delta rho0 d E;
      apply (ity_prop _ w); pin_for prop.

Ltac wc3 := unfold WTy, WTm; (* ity_univ *) intros rho m w Ew delta rho0 d E;
      apply (ity_univ _ _ w); pin_for (univ m).

Ltac wc4 := unfold WTy, WTm; (* ity_prf *) intros rho p wp xp Dp IHp delta rho0 d E;
      apply ity_prf; apply IHp; exact E.

Ltac wc5 := unfold WTy, WTm; (* ity_pi *) intros rho A B k wA FA B0 wB FB redB isoB gPi Ew DA IHA DB IHB
      delta rho0 d E;
      apply ity_pi;
      [ pin_for (pi A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity ].

Ltac wc6 := unfold WTy, WTm; (* ity_of *) intros rho A k w v nf Dv IHv delta rho0 d E;
      apply ity_of; [destruct A; cbn in nf |- *; exact nf | apply IHv; exact E].

Ltac wc7 := unfold WTy, WTm; (* i_ty *) intros rho A k w F D IH delta rho0 d E;
      apply i_ty; apply IH; exact E.

Ltac wc8 := unfold WTy, WTm; (* i_var0 *) intros rho k Sy F w x delta rho0 d E;
      destruct delta as [| d0 delta]; cbn in E |- *;
      [ rewrite <- E; apply i_varS, i_var0
      | inversion E; subst; apply i_var0 ].

Ltac wc9 := unfold WTy, WTm; (* i_varS *) intros rho en i k Sy F w x D IH delta rho0 d E;
      destruct delta as [| d0 delta]; cbn in E |- *;
      [ rewrite <- E; apply i_varS, i_varS; exact D
      | inversion E; subst; apply i_varS; apply (IH delta rho0 d eq_refl) ].

Ltac wc10 := unfold WTy, WTm; (* i_zero *) intros rho delta rho0 d E; apply i_zero.

Ltac wc11 := unfold WTy, WTm; (* i_succ *) intros rho n wn x D IH delta rho0 d E;
      apply i_succ; apply IH; exact E.

Ltac wc12 := unfold WTy, WTm; (* i_lam *) intros rho A B t k wA FA B0 wB FB redB isoB gPi w x wt xt Ew Ep
      DA IHA DB IHB Dt IHt Hbeh delta rho0 d E;
      apply (i_lam _ _ _ _ k wA FA B0 wB FB redB isoB gPi w x wt xt);
      [ pin_for (lam A B t)
      | pin_for (pi A B)
      | apply IHA; exact E
      | intros u y; apply (IHB u y (Build_Entry k wA FA u y :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | intros u y; apply (IHt u y (Build_Entry k wA FA u y :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | exact Hbeh ].

Ltac wc13 := unfold WTy, WTm; (* i_app *) intros rho A B f a k wA FA B0 wB FB redB isoB gPi wf xf wa xa Ep
      DA IHA DB IHB Df IHf Da IHa delta rho0 d E;
      apply (i_app _ _ _ _ _ k wA FA B0 wB FB redB isoB gPi wf xf wa xa);
      [ pin_for (pi A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHf; exact E
      | apply IHa; exact E ].

(* natrec: the step term is renamed at depth |delta| + 2, its two binders
   being the scrutinee's predecessor and the recursive result, and its
   induction hypothesis is used at the correspondingly doubly-extended
   environment. *)
Ltac wc14 := unfold WTy, WTm; (* i_natrec *) intros rho C z s n k SC FC isoC S0
      wz xz ws xs redS wn xn ES DC IHC Dz IHz Ds IHs Dn IHn
      delta rho0 d E;
      apply (i_natrec _ (C ⟨upnr (S (length delta)) shift⟩) _
               (s ⟨upnr (S (S (length delta))) shift⟩) _ k SC FC isoC S0
               wz xz ws xs redS wn xn);
      [ pin_for (stepWrap s)
      | intros m x; apply (IHC m x (Build_Entry 0 enat (natFam 0) m x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHz; exact E
      | intros m x w y;
          apply (IHs m x w y (Build_Entry k (SC m) (FC m x) w y
                              :: Build_Entry 0 enat (natFam 0) m x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHn; exact E ].

Ltac wc15 := unfold WTy, WTm; (* i_false *) intros rho w g Ew delta rho0 d E;
      apply (i_false _ w g); pin_for false_.

Ltac wc16 := unfold WTy, WTm; (* i_all *) intros rho A p k wA FA wp xp w g Ew DA IHA Dp IHp delta rho0 d E;
      apply (i_all _ _ _ k wA FA wp xp w g);
      [ pin_for (all A p)
      | apply IHA; exact E
      | intros u y; apply (IHp u y (Build_Entry k wA FA u y :: delta) rho0 d);
          cbn; rewrite E; reflexivity ].

Ltac wc17 := unfold WTy, WTm; (* i_proof *) intros rho t p wp xp h w g Ew Dp IHp delta rho0 d E;
      apply (i_proof _ _ (p ⟨upnr (length delta) shift⟩) wp xp h w g); [pin_for t | apply IHp; exact E].

Ltac wc18 := unfold WTy, WTm; (* ity_up *) intros rho A k w F D IH delta rho0 d E;
      apply ity_up; apply IH; exact E.

Ltac wc25 := unfold WTy, WTm; (* ity_conv *)
      intros rho A k w F F' P D IH delta rho0 d E;
      apply (ity_conv _ _ _ _ F F' P); apply IH; exact E.

Ltac wc19 := unfold WTy, WTm; (* i_up_tm *) intros rho A t k Sy F w x DA IHA D IH delta rho0 d E;
      apply i_up_tm; [apply IHA; exact E | apply IH; exact E].

Ltac wc20 := unfold WTy, WTm; (* ity_sig *) intros rho A B k wA FA B0 wB FB redB isoB gSig Ew DA IHA DB IHB
      delta rho0 d E;
      apply ity_sig;
      [ pin_for (sig_ A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity ].

Ltac wc21 := unfold WTy, WTm; (* i_pair *) intros rho A B t a2 k wA FA B0 wB FB redB isoB gSig wt xt wa xa g Ep
      DA IHA DB IHB Dt IHt Da IHa delta rho0 d E;
      apply (i_pair _ _ _ _ _ k wA FA B0 wB FB redB isoB gSig wt xt wa xa g);
      [ pin_for (sig_ A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHt; exact E
      | apply IHa; exact E ].

Ltac wc22 := unfold WTy, WTm; (* i_fst *) intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
      DA IHA DB IHB Dp IHp delta rho0 d E;
      apply (i_fst _ _ _ _ k wA FA B0 wB FB redB isoB gSig wp xp);
      [ pin_for (sig_ A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHp; exact E ].

Ltac wc23 := unfold WTy, WTm; (* i_snd *) intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep
      DA IHA DB IHB Dp IHp delta rho0 d E;
      apply (i_snd _ _ _ _ k wA FA B0 wB FB redB isoB gSig wp xp);
      [ pin_for (sig_ A B)
      | apply IHA; exact E
      | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta) rho0 d);
          cbn; rewrite E; reflexivity
      | apply IHp; exact E ].

Ltac wc24 := unfold WTy, WTm; (* i_conv *) intros rho t k Sy F Sy' F' w x P D IH delta rho0 d E;
      apply (i_conv _ _ k Sy F Sy' F' w x P); apply IH; exact E.

Lemma weaken_ITy rho A k w F (D : ITy rho A k w F) : WTy rho A k w F.
Proof.
  revert rho A k w F D.
  apply (ITy_mut (fun rho A k w F _ => WTy rho A k w F)
                 (fun rho t k Sy F w x _ => WTm rho t k Sy F w x)); [wc1 | wc2 | wc3 | wc4 | wc5 | wc20 | wc18 | wc6 | wc25 | wc7 | wc8 | wc9 | wc10 | wc11 | wc12 | wc13 | wc21 | wc22 | wc23 | wc14 | wc15 | wc16 | wc17 | wc19 | wc24].
Qed.

Lemma weaken_ITm rho t k Sy F w x (D : ITm rho t k Sy F w x) : WTm rho t k Sy F w x.
Proof.
  revert rho t k Sy F w x D.
  apply (ITm_mut (fun rho A k w F _ => WTy rho A k w F)
                 (fun rho t k Sy F w x _ => WTm rho t k Sy F w x)); [wc1 | wc2 | wc3 | wc4 | wc5 | wc20 | wc18 | wc6 | wc25 | wc7 | wc8 | wc9 | wc10 | wc11 | wc12 | wc13 | wc21 | wc22 | wc23 | wc14 | wc15 | wc16 | wc17 | wc19 | wc24].
Qed.

(* Weakening by one entry at the front, which is the form the substitution
   lemma needs. *)
Corollary weaken1 rho t k Sy F w x (d : Entry) :
  ITm rho t k Sy F w x -> ITm (d :: rho) (t ⟨↑⟩) k Sy F w x.
Proof. intros D; exact (weaken_ITm rho t k Sy F w x D nil rho d eq_refl). Qed.

Corollary weaken1_ITy rho A k w F (d : Entry) :
  ITy rho A k w F -> ITy (d :: rho) (A ⟨↑⟩) k w F.
Proof. intros D; exact (weaken_ITy rho A k w F D nil rho d eq_refl). Qed.

(* ------------------------------------------------------------------ *)
(* Lemma 9.1: substituting a term for a variable IS extending the      *)
(* environment by that term's value.                                   *)
(*                                                                    *)
(* Cast-free for the same reason weakening is: the realiser, the family *)
(* and the value are untouched, and only the pin travels (ers_upn).     *)
(*                                                                    *)
(* One clause needs an extra hypothesis.  `ity_of` requires            *)
(* `notFormer A`, and notFormer is NOT stable under substitution: A may *)
(* be a variable -- a non-former, so ity_of is the clause that applies  *)
(* -- while its substituted form is `a`, which may be a former.  The    *)
(* hypothesis DaU says exactly what that case needs: for the terms that *)
(* substitution puts in a variable's place, an ITm-derivation at a      *)
(* universe yields an ITy-derivation.  It is stated in the very form    *)
(* the case produces, `upn |delta| (a..) i`, so no arithmetic about     *)
(* iterated shifts is needed, and the fundamental lemma can supply it   *)
(* from its own induction hypothesis for a.                            *)
(* ------------------------------------------------------------------ *)

Definition STy (rho0 : Env) (a : tm) (en : Entry)
  (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  forall delta, rho = delta ++ en :: rho0 ->
    ITy (delta ++ rho0) (A [upn (length delta) (a..)]) k w F.

Definition STm (rho0 : Env) (a : tm) (en : Entry)
  (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy) (w : etm)
  (x : kElAt F w) : Type :=
  forall delta, rho = delta ++ en :: rho0 ->
    ITm (delta ++ rho0) (t [upn (length delta) (a..)]) k Sy F w x.

(* What the ity_of case needs: see the note above. *)
Definition SubUniv (rho0 : Env) (a : tm) : Type :=
  forall delta i k' w' (v' : kElAt (univFam k') w'),
    ITm (delta ++ rho0) (upn (length delta) (a..) i)
        (S k') (euniv k') (univFam k') w' v' ->
    ITy (delta ++ rho0) (upn (length delta) (a..) i) k' w' (elFam v').

Ltac spin_for a en Hua t0 :=
  subst;
  first
    [ reflexivity
    | match goal with
      | |- ?w = ers (?delta ++ ?rho0) _ =>
          first
            [ match goal with
              | H : w = ers (delta ++ en :: rho0) t0 |- _ =>
                  exact (eq_trans H (eq_sym (ers_upn rho0 a en Hua delta t0)))
              end
            | exact (eq_sym (ers_upn rho0 a en Hua delta t0)) ]
      end ].

Ltac sc1 a en Hua Da DaU := unfold STy, STm; intros rho w Ew delta E;
  apply (ity_nat _ w); spin_for a en Hua nat_.
Ltac sc2 a en Hua Da DaU := unfold STy, STm; intros rho w Ew delta E;
  apply (ity_prop _ w); spin_for a en Hua prop.
Ltac sc3 a en Hua Da DaU := unfold STy, STm; intros rho m w Ew delta E;
  apply (ity_univ _ _ w); spin_for a en Hua (univ m).
Ltac sc4 a en Hua Da DaU := unfold STy, STm; intros rho p wp xp Dp IHp delta E;
  apply ity_prf; apply IHp; exact E.
Ltac sc5 a en Hua Da DaU := unfold STy, STm;
  intros rho A B k wA FA B0 wB FB redB isoB gPi Ew DA IHA DB IHB delta E;
  apply ity_pi;
  [ spin_for a en Hua (pi A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity ].
Ltac sc25 a en Hua Da DaU := unfold STy, STm; (* ity_conv *)
  intros rho A k w F F' P D IH delta E;
  apply (ity_conv _ _ _ _ F F' P); apply IH; exact E.
Ltac sc6 a en Hua Da DaU := unfold STy, STm; intros rho A k w v nf Dv IHv delta E;
  destruct A;
    try (destruct nf);
    try (apply ity_of; [exact I | apply IHv; exact E]);
  apply DaU; exact (IHv delta E).
Ltac sc7 a en Hua Da DaU := unfold STy, STm; intros rho A k w F D IH delta E;
  apply i_ty; apply IH; exact E.
Ltac sc8 a en Hua Da DaU := unfold STy, STm; intros rho k Sy F w x delta E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ inversion E; subst en; subst rho; exact Da
  | inversion E; subst; apply i_var0 ].
Ltac sc9 a en Hua Da DaU := unfold STy, STm;
  intros rho e2 i k Sy F w x D IH delta E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ inversion E; subst; exact D
  | inversion E; subst; apply weaken1; apply (IH delta eq_refl) ].
Ltac sc10 a en Hua Da DaU := unfold STy, STm; intros rho delta E; apply i_zero.
Ltac sc11 a en Hua Da DaU := unfold STy, STm; intros rho n wn x D IH delta E;
  apply i_succ; apply IH; exact E.
Ltac sc12 a en Hua Da DaU := unfold STy, STm;
  intros rho A B t k wA FA B0 wB FB redB isoB gPi w x wt xt Ew Ep
    DA IHA DB IHB Dt IHt Hbeh delta E;
  apply (i_lam _ _ _ _ k wA FA B0 wB FB redB isoB gPi w x wt xt);
  [ spin_for a en Hua (lam A B t)
  | spin_for a en Hua (pi A B)
  | apply IHA; exact E
  | intros u y; apply (IHB u y (Build_Entry k wA FA u y :: delta));
      cbn; rewrite E; reflexivity
  | intros u y; apply (IHt u y (Build_Entry k wA FA u y :: delta));
      cbn; rewrite E; reflexivity
  | exact Hbeh ].
Ltac sc13 a en Hua Da DaU := unfold STy, STm;
  intros rho A B f b k wA FA B0 wB FB redB isoB gPi wf xf wb xb Ep
    DA IHA DB IHB Df IHf Db IHb delta E;
  apply (i_app _ _ _ _ _ k wA FA B0 wB FB redB isoB gPi wf xf wb xb);
  [ spin_for a en Hua (pi A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHf; exact E
  | apply IHb; exact E ].
Ltac sc14 a en Hua Da DaU := unfold STy, STm;
  intros rho C z s n k SC FC isoC S0 wz xz ws xs redS wn xn
    ES DC IHC Dz IHz Ds IHs Dn IHn delta E;
  apply (i_natrec _ (C [upn (S (length delta)) (a..)]) _
           (s [upn (S (S (length delta))) (a..)]) _ k SC FC isoC S0
           wz xz ws xs redS wn xn);
  [ spin_for a en Hua (stepWrap s)
  | intros m x; apply (IHC m x (Build_Entry 0 enat (natFam 0) m x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHz; exact E
  | intros m x w y;
      apply (IHs m x w y (Build_Entry k (SC m) (FC m x) w y
                          :: Build_Entry 0 enat (natFam 0) m x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHn; exact E ].
Ltac sc15 a en Hua Da DaU := unfold STy, STm; intros rho w g Ew delta E;
  apply (i_false _ w g); spin_for a en Hua false_.
Ltac sc16 a en Hua Da DaU := unfold STy, STm;
  intros rho A p k wA FA wp xp w g Ew DA IHA Dp IHp delta E;
  apply (i_all _ _ _ k wA FA wp xp w g);
  [ spin_for a en Hua (all A p)
  | apply IHA; exact E
  | intros u y; apply (IHp u y (Build_Entry k wA FA u y :: delta));
      cbn; rewrite E; reflexivity ].
Ltac sc17 a en Hua Da DaU := unfold STy, STm;
  intros rho t p wp xp h w g Ew Dp IHp delta E;
  apply (i_proof _ _ (p [upn (length delta) (a..)]) wp xp h w g);
  [ spin_for a en Hua t | apply IHp; exact E ].

Ltac sc18 a en Hua Da DaU := unfold STy, STm; intros rho A k w F D IH delta E;
  apply ity_up; apply IH; exact E.
Ltac sc19 a en Hua Da DaU := unfold STy, STm;
  intros rho A t k Sy F w x DA IHA D IH delta E;
  apply i_up_tm; [apply IHA; exact E | apply IH; exact E].

Ltac sc20 a en Hua Da DaU := unfold STy, STm;
  intros rho A B k wA FA B0 wB FB redB isoB gSig Ew DA IHA DB IHB delta E;
  apply ity_sig;
  [ spin_for a en Hua (sig_ A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity ].
Ltac sc21 a en Hua Da DaU := unfold STy, STm;
  intros rho A B t a2 k wA FA B0 wB FB redB isoB gSig wt xt wa xa g Ep
    DA IHA DB IHB Dt IHt Da2 IHa2 delta E;
  apply (i_pair _ _ _ _ _ k wA FA B0 wB FB redB isoB gSig wt xt wa xa g);
  [ spin_for a en Hua (sig_ A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHt; exact E
  | apply IHa2; exact E ].
Ltac sc22 a en Hua Da DaU := unfold STy, STm;
  intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep DA IHA DB IHB Dp IHp delta E;
  apply (i_fst _ _ _ _ k wA FA B0 wB FB redB isoB gSig wp xp);
  [ spin_for a en Hua (sig_ A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHp; exact E ].
Ltac sc23 a en Hua Da DaU := unfold STy, STm;
  intros rho A B p k wA FA B0 wB FB redB isoB gSig wp xp Ep DA IHA DB IHB Dp IHp delta E;
  apply (i_snd _ _ _ _ k wA FA B0 wB FB redB isoB gSig wp xp);
  [ spin_for a en Hua (sig_ A B)
  | apply IHA; exact E
  | intros u x; apply (IHB u x (Build_Entry k wA FA u x :: delta));
      cbn; rewrite E; reflexivity
  | apply IHp; exact E ].

Ltac sc24 a en Hua Da DaU := unfold STy, STm;
  intros rho t k Sy F Sy' F' w x P D IH delta E;
  apply (i_conv _ _ k Sy F Sy' F' w x P); apply IH; exact E.

Lemma subst_ITy (rho0 : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho0 a)
  (Da : ITm rho0 a (en_k en) (en_S en) (en_F en) (en_u en) (en_x en))
  (DaU : SubUniv rho0 a)
  rho A k w F (D : ITy rho A k w F) : STy rho0 a en rho A k w F.
Proof.
  revert rho A k w F D.
  apply (ITy_mut (fun rho A k w F _ => STy rho0 a en rho A k w F)
                 (fun rho t k Sy F w x _ => STm rho0 a en rho t k Sy F w x));
    [ sc1 a en Hua Da DaU | sc2 a en Hua Da DaU | sc3 a en Hua Da DaU
    | sc4 a en Hua Da DaU | sc5 a en Hua Da DaU | sc20 a en Hua Da DaU
    | sc18 a en Hua Da DaU | sc6 a en Hua Da DaU | sc25 a en Hua Da DaU
    | sc7 a en Hua Da DaU | sc8 a en Hua Da DaU | sc9 a en Hua Da DaU
    | sc10 a en Hua Da DaU | sc11 a en Hua Da DaU | sc12 a en Hua Da DaU
    | sc13 a en Hua Da DaU | sc21 a en Hua Da DaU | sc22 a en Hua Da DaU
    | sc23 a en Hua Da DaU
    | sc14 a en Hua Da DaU | sc15 a en Hua Da DaU | sc16 a en Hua Da DaU
    | sc17 a en Hua Da DaU | sc19 a en Hua Da DaU
    | sc24 a en Hua Da DaU ].
Qed.

Lemma subst_ITm (rho0 : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho0 a)
  (Da : ITm rho0 a (en_k en) (en_S en) (en_F en) (en_u en) (en_x en))
  (DaU : SubUniv rho0 a)
  rho t k Sy F w x (D : ITm rho t k Sy F w x) : STm rho0 a en rho t k Sy F w x.
Proof.
  revert rho t k Sy F w x D.
  apply (ITm_mut (fun rho A k w F _ => STy rho0 a en rho A k w F)
                 (fun rho t k Sy F w x _ => STm rho0 a en rho t k Sy F w x));
    [ sc1 a en Hua Da DaU | sc2 a en Hua Da DaU | sc3 a en Hua Da DaU
    | sc4 a en Hua Da DaU | sc5 a en Hua Da DaU | sc20 a en Hua Da DaU
    | sc18 a en Hua Da DaU | sc6 a en Hua Da DaU | sc25 a en Hua Da DaU
    | sc7 a en Hua Da DaU | sc8 a en Hua Da DaU | sc9 a en Hua Da DaU
    | sc10 a en Hua Da DaU | sc11 a en Hua Da DaU | sc12 a en Hua Da DaU
    | sc13 a en Hua Da DaU | sc21 a en Hua Da DaU | sc22 a en Hua Da DaU
    | sc23 a en Hua Da DaU
    | sc14 a en Hua Da DaU | sc15 a en Hua Da DaU | sc16 a en Hua Da DaU
    | sc17 a en Hua Da DaU | sc19 a en Hua Da DaU
    | sc24 a en Hua Da DaU ].
Qed.

(* The form the fundamental lemma uses: substitution at the top. *)
Corollary subst1_ITm (rho : Env) (b : tm) k' Sy' (FA : kUFam k' Sy') (ub : etm)
  (xb : kElAt FA ub) (Hub : ub = ers rho b)
  (Db : ITm rho b k' Sy' FA ub xb) (DbU : SubUniv rho b)
  t k Sy (F : kUFam k Sy) w (x : kElAt F w) :
  ITm (Build_Entry k' Sy' FA ub xb :: rho) t k Sy F w x ->
  ITm rho (t [b..]) k Sy F w x.
Proof.
  intros D.
  exact (subst_ITm rho b (Build_Entry k' Sy' FA ub xb) Hub Db DbU
           _ _ _ _ _ _ _ D nil eq_refl).
Qed.

Corollary subst1_ITy (rho : Env) (b : tm) k' Sy' (FA : kUFam k' Sy') (ub : etm)
  (xb : kElAt FA ub) (Hub : ub = ers rho b)
  (Db : ITm rho b k' Sy' FA ub xb) (DbU : SubUniv rho b)
  A k w (F : kUFam k w) :
  ITy (Build_Entry k' Sy' FA ub xb :: rho) A k w F ->
  ITy rho (A [b..]) k w F.
Proof.
  intros D.
  exact (subst_ITy rho b (Build_Entry k' Sy' FA ub xb) Hub Db DbU
           _ _ _ _ _ D nil eq_refl).
Qed.
