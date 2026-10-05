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
  Interp.Def Interp.Inv Interp.Ctx.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* Blueprint Lemma 9.1: semantic substitution.

   Substituting a term for a variable IS extending the environment by that
   term's value.  The lemma is stated under a prefix of extra entries, because
   the induction goes under binders: `delta` is what the binders added, and the
   syntactic substitution is correspondingly `a..` pushed under |delta| ups.

   Entries are self-contained -- an Entry carries its own family and realiser,
   with no reference to the environment it sits in -- so `delta ++ rho` and
   `delta ++ ext rho FA _ xa` are both environments without any adjustment.
   That is what keeps this lemma about substitutions and not about
   environments.

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
  | S n0 => Ann.up_subst (upn n0 sigma)
  end.

Fixpoint upnr (n : nat) (xi : ren) : ren :=
  match n with
  | 0 => xi
  | S n0 => up_ren (upnr n0 xi)
  end.

Lemma rsub_upnr (rho : Env) (d : Entry) :
  forall (delta : list Entry) i,
    rsub (delta ++ d :: rho) (upnr (length delta) ↑ i) = rsub (delta ++ rho) i.
Proof.
  induction delta as [| e delta IH]; intros i; cbn; [reflexivity |].
  destruct i as [| j]; cbn; [reflexivity | apply IH].
Qed.

Lemma ers_upnr (rho : Env) (d : Entry) (delta : list Entry) (t : tm) :
  ers (delta ++ d :: rho) (t ⟨upnr (length delta) ↑⟩) = ers (delta ++ rho) t.
Proof.
  unfold ers; rewrite er_ren, subst_ren_etm.
  apply ext_etm; intros i; apply (rsub_upnr rho d delta i).
Qed.

(* The same ONE BINDER IN.  `i_wrec` pins its motive's realiser as an
   erasure under the tree entry (`forall w1, SC w1 = subst_etm (scons w1
   (rsub rho)) (er C)`), and that entry is not part of the environment the
   pin mentions -- it is the Pi's own argument -- so the equation travels at
   depth |delta| + 1 while the environment travels at |delta|. *)
Lemma ers_upnr1 (rho : Env) (d : Entry) (delta : list Entry) (w1 : etm) (t : tm) :
  subst_etm (scons w1 (rsub (delta ++ d :: rho)))
    (er (t ⟨upnr (S (length delta)) ↑⟩))
  = subst_etm (scons w1 (rsub (delta ++ rho))) (er t).
Proof.
  rewrite er_ren, subst_ren_etm.
  apply ext_etm; intros [| i]; [reflexivity |].
  exact (rsub_upnr rho d delta i).
Qed.

(* And the same for a substitution at depth |delta|. *)
Lemma upn_S (n : nat) (sigma : nat -> tm) (j : nat) :
  upn (S n) sigma (S j) = (upn n sigma j) ⟨↑⟩.
Proof. reflexivity. Qed.

Lemma upn_S0 (n : nat) (sigma : nat -> tm) : upn (S n) sigma 0 = var_tm 0.
Proof. reflexivity. Qed.

Lemma rsub_upn (rho : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho a) :
  forall (delta : list Entry) i,
    subst_etm (rsub (delta ++ rho)) (er (upn (length delta) (a..) i))
    = rsub (delta ++ en :: rho) i.
Proof.
  induction delta as [| d delta IH]; intros i.
  - cbn [length upn rsub Datatypes.app].
    destruct i as [| j]; cbn; [exact (eq_sym Hua) | reflexivity].
  - cbn [length]; destruct i as [| j].
    + rewrite upn_S0; cbn; reflexivity.
    + rewrite upn_S, er_ren; cbn [rsub Datatypes.app].
      rewrite subst_cons_shift_etm.
      apply IH.
Qed.

Lemma ers_upn (rho : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho a)
  (delta : list Entry) (t : tm) :
  ers (delta ++ rho) (t [upn (length delta) (a..)])
  = ers (delta ++ en :: rho) t.
Proof.
  unfold ers.
  rewrite (er_subst t (upn (length delta) (a..))
             (fun i => er (upn (length delta) (a..) i)) (fun i => eq_refl)).
  rewrite subst_subst_etm.
  apply ext_etm; intros i; apply (rsub_upn rho a en Hua delta i).
Qed.

(* and the substitution's version of the same, one binder in *)
Lemma ers_upn1 (rho : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho a)
  (delta : list Entry) (w1 : etm) (t : tm) :
  subst_etm (scons w1 (rsub (delta ++ rho))) (er (t [upn (S (length delta)) (a..)]))
  = subst_etm (scons w1 (rsub (delta ++ en :: rho))) (er t).
Proof.
  rewrite (er_subst t (upn (S (length delta)) (a..))
             (fun i => er (upn (S (length delta)) (a..) i)) (fun i => eq_refl)).
  rewrite subst_subst_etm.
  apply ext_etm; intros [| i]; [reflexivity |].
  unfold scomp; rewrite upn_S, er_ren, subst_cons_shift_etm.
  exact (rsub_upn rho a en Hua delta i).
Qed.

(* ------------------------------------------------------------------ *)
(* Weakening.  The family, the realiser and the value are UNCHANGED;   *)
(* only the environment, the term and the pinning equation move.       *)
(* ------------------------------------------------------------------ *)

Definition WTy (rho : Env) (A : tm) (k : nat) (w : etm) (F : kUFam k w) : Type :=
  forall delta rho0 d, rho = delta ++ rho0 ->
    ITy (delta ++ d :: rho0) (A ⟨upnr (length delta) ↑⟩) k w F.

Definition WTm (rho : Env) (t : tm) (k : nat) (Sy : etm) (F : kUFam k Sy) (w : etm)
  (x : kElAt F w) : Type :=
  forall delta rho0 d, rho = delta ++ rho0 ->
    ITm (delta ++ d :: rho0) (t ⟨upnr (length delta) ↑⟩) k Sy F w x.

Scheme ITy_mut := Induction for ITy Sort Type
  with ITm_mut := Induction for ITm Sort Type.

(* The pin, moved: the realiser is unchanged, so only the equation that ties
   it to the erasure has to travel, and ers_upnr is exactly that travel. *)
(* `subst rho` and not `subst`: the clause's level equations (dA + i = k) are
   in context too, and substituting THEM would rewrite the level inside the
   term the pin mentions. *)
Ltac pin_for t0 :=
  try (match goal with | Ee : ?r = _ ++ _ |- _ => subst r end);
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

(* and the environment equation, one entry further in *)
Ltac wenv en := cbn; match goal with | E : _ = _ |- _ => rewrite E; reflexivity end.

Ltac wc1 := unfold WTy, WTm; (* ity_nat *)
  intros rho k w Ew delta rho0 d E;
  apply (ity_nat _ k w); pin_for (nat_ k).

Ltac wc2 := unfold WTy, WTm; (* ity_prop *)
  intros rho k w Ew delta rho0 d E;
  apply (ity_prop _ k w); pin_for (prop k).

Ltac wc3 := unfold WTy, WTm; (* ity_univ *)
  intros rho k dl jj EE w Ew delta rho0 d E;
  apply (ity_univ _ k dl jj EE w); pin_for (univ k jj).

Ltac wc4 := unfold WTy, WTm; (* ity_prf *)
  intros rho k jj p wp xp Dp IHp delta rho0 d E;
  apply ity_prf; apply IHp; exact E.

Ltac wc5 := unfold WTy, WTm; (* ity_pi *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi Ew DA IHA DB IHB
    delta rho0 d E;
  apply ity_pi;
  [ pin_for (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity ].

Ltac wc6 := unfold WTy, WTm; (* ity_sig *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig Ew DA IHA DB IHB
    delta rho0 d E;
  apply ity_sig;
  [ pin_for (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity ].

Ltac wc7 := unfold WTy, WTm; (* ity_w *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW Ew DA IHA DB IHB
    delta rho0 d E;
  apply ity_w;
  [ pin_for (wt k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity ].

Ltac wc8 := unfold WTy, WTm; (* ity_up *)
  intros rho A k w F DA IHA delta rho0 d E;
  apply ity_up; apply IHA; exact E.

Ltac wc9 := unfold WTy, WTm; (* ity_of *)
  intros rho A k w v nf Dv IHv delta rho0 d E;
  apply ity_of; [destruct A; cbn in nf |- *; exact nf | apply IHv; exact E].

Ltac wc10 := unfold WTy, WTm; (* ity_conv *)
  intros rho A k w F F' P Dc IHc delta rho0 d E;
  apply (ity_conv _ _ _ _ F F' P); apply IHc; exact E.

Ltac wc11 := unfold WTy, WTm; (* i_ty *)
  intros rho A k w F D IH delta rho0 d E;
  apply i_ty; apply IH; exact E.

Ltac wc12 := unfold WTy, WTm; (* i_var0 *)
  intros rho k Sy F w x delta rho0 d E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ rewrite <- E; apply i_varS, i_var0
  | inversion E; subst; apply i_var0 ].

Ltac wc13 := unfold WTy, WTm; (* i_varS *)
  intros rho en ii k Sy F w x D IH delta rho0 d E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ rewrite <- E; apply i_varS, i_varS; exact D
  | inversion E; subst; apply i_varS; apply (IH delta rho0 d eq_refl) ].

Ltac wc14 := unfold WTy, WTm; (* i_zero *)
  intros rho k delta rho0 d E; apply i_zero.

Ltac wc15 := unfold WTy, WTm; (* i_succ *)
  intros rho k n wn x D IH delta rho0 d E;
  apply i_succ; apply IH; exact E.

Ltac wc16 := unfold WTy, WTm; (* i_lam *)
  intros rho A B t k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    w wt xt redt xtext gd Ew Ep DA IHA DB IHB Dt IHt delta rho0 d E;
  apply (i_lam _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
           w wt xt redt xtext gd);
  [ pin_for (lam k A B t)
  | pin_for (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | intros u x;
    apply (IHt u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity ].

Ltac wc17 := unfold WTy, WTm; (* i_app *)
  intros rho A B f a k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    wf xf wa xa Ep DA IHA DB IHB Df IHf Da IHa delta rho0 d E;
  apply (i_app _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
           wf xf wa xa);
  [ pin_for (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHf; exact E
  | apply IHa; exact E ].

Ltac wc18 := unfold WTy, WTm; (* i_pair *)
  intros rho A B t a k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wt xt wa xa g Ep DA IHA DB IHB Dt IHt Da IHa delta rho0 d E;
  apply (i_pair _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
           wt xt wa xa g);
  [ pin_for (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHt; exact E
  | apply IHa; exact E ].

Ltac wc19 := unfold WTy, WTm; (* i_fst *)
  intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp delta rho0 d E;
  apply (i_fst _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp);
  [ pin_for (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHp; exact E ].

Ltac wc20 := unfold WTy, WTm; (* i_snd *)
  intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp delta rho0 d E;
  apply (i_snd _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp);
  [ pin_for (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHp; exact E ].

Ltac wc21 := unfold WTy, WTm; (* i_sup *)
  intros rho A B a f k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
    Bbr redBbr gBr wa xa wf xf gd Ew DA IHA DB IHB Da IHa Df IHf delta rho0 d E;
  apply (i_sup _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
           Bbr redBbr gBr wa xa wf xf gd);
  [ pin_for (wt k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHa; exact E
  | apply IHf; exact E ].

(* wrec: the motive is renamed at depth |delta| + 1, under the tree entry, and
   the step at depth |delta| + 3, under its own three binders -- the label,
   the branching function and the induction hypothesis -- and its induction
   hypothesis is used at the correspondingly triply-extended environment. *)
Ltac wc22 := unfold WTy, WTm; (* i_wrec *)
  intros rho A B C s w k i jj m n dA dB dBn dC EA EB EBn EC En
    wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr
    gf gih ws xs redS stepSrel ww xw
    ESr Ew ESC DA IHA DB IHB DC IHC Dstep IHstep Dw IHw delta rho0 d E;
  apply (i_wrec _ _ _ _ _ _ k i jj m n dA dB dBn dC EA EB EBn EC En
           wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red
           Sr gf gih ws xs redS stepSrel ww xw);
  [ pin_for (stepWrap3 s)
  | pin_for (wt k A B)
  | (* the motive's pin, which lives one binder in *)
    subst rho; intros w1;
    exact (eq_trans (ESC w1) (eq_sym (ers_upnr1 rho0 d delta w1 C)))
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | intros u x;
    apply (IHC u x
             (Build_Entry k (ew wA B0)
                (wFam k wA B0 (upF dA k EA FA) wB
                   (fun u0 x0 => upF dB k EB (FB u0 x0)) redB cohB gW) u x
              :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | intros u0 z f sub subext gd ih ihext;
    apply (IHstep u0 z f sub subext gd ih ihext
             (Build_Entry n (epi (wB u0 z) (Bih u0 z f))
                (ihFam k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                   n dBn dC EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                (ihR Sr f)
                (ihEl k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                   n dBn dC EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                   (gih u0 z f gd))
              :: Build_Entry k (epi (wB u0 z) Bbr)
                   (brFam k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
                      Bbr redBbr gBr u0 z) f
                   (brEl k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
                      Bbr redBbr gBr u0 z f sub subext (gf u0 z f gd))
              :: Build_Entry i wA FA u0 (dnEl dA k EA FA u0 z)
              :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHw; exact E ].

(* natrec: the step term is renamed at depth |delta| + 2, its two binders
   being the scrutinee's predecessor and the recursive result. *)
Ltac wc23 := unfold WTy, WTm; (* i_natrec *)
  intros rho C z s n k jj SC FC cohC S0 wz xz ws xs redS wn xn
    ES DC IHC Dz IHz Ds IHs Dn IHn delta rho0 d E;
  apply (i_natrec _ _ _ _ _ k jj SC FC cohC S0 wz xz ws xs redS wn xn);
  [ pin_for (stepWrap s)
  | intros m x;
    apply (IHC m x (Build_Entry jj enat (natFam jj) m x :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHz; exact E
  | intros m x w y;
    apply (IHs m x w y (Build_Entry k (SC m) (FC m x) w y
                        :: Build_Entry jj enat (natFam jj) m x :: delta) rho0 d);
    cbn; rewrite E; reflexivity
  | apply IHn; exact E ].

Ltac wc24 := unfold WTy, WTm; (* i_false *)
  intros rho k w g Ew delta rho0 d E;
  apply (i_false _ k w g); pin_for (false_ k).

Ltac wc25 := unfold WTy, WTm; (* i_all *)
  intros rho jj A p k wA FA wp xp w g Ew DA IHA Dp IHp delta rho0 d E;
  apply (i_all _ jj _ _ k wA FA wp xp w g);
  [ pin_for (all jj A p)
  | apply IHA; exact E
  | intros u y; apply (IHp u y (Build_Entry k wA FA u y :: delta) rho0 d);
    cbn; rewrite E; reflexivity ].

Ltac wc26 := unfold WTy, WTm; (* i_proof *)
  intros rho t p k jj wp xp h w g Ew Dp IHp delta rho0 d E;
  apply (i_proof _ _ (p ⟨upnr (length delta) ↑⟩) k jj wp xp h w g);
  [ pin_for t | apply IHp; exact E ].

Ltac wc27 := unfold WTy, WTm; (* i_up_tm *)
  intros rho A t k Sy F w x DA IHA D IH delta rho0 d E;
  apply i_up_tm; [apply IHA; exact E | apply IH; exact E].

Ltac wc28 := unfold WTy, WTm; (* i_conv *)
  intros rho t k Sy F Sy' F' w x P D IH delta rho0 d E;
  apply (i_conv _ _ k Sy F Sy' F' w x P); apply IH; exact E.

Lemma weaken_ITy rho A k w F (D : ITy rho A k w F) : WTy rho A k w F.
Proof.
  revert rho A k w F D.
  apply (ITy_mut (fun rho A k w F _ => WTy rho A k w F)
                 (fun rho t k Sy F w x _ => WTm rho t k Sy F w x));
    [ wc1 | wc2 | wc3 | wc4 | wc5 | wc6 | wc7 | wc8 | wc9 | wc10 | wc11 | wc12 | wc13 | wc14 | wc15 | wc16 | wc17 | wc18 | wc19 | wc20 | wc21 | wc22 | wc23 | wc24 | wc25 | wc26 | wc27 | wc28 ].
Qed.

Lemma weaken_ITm rho t k Sy F w x (D : ITm rho t k Sy F w x) : WTm rho t k Sy F w x.
Proof.
  revert rho t k Sy F w x D.
  apply (ITm_mut (fun rho A k w F _ => WTy rho A k w F)
                 (fun rho t k Sy F w x _ => WTm rho t k Sy F w x));
    [ wc1 | wc2 | wc3 | wc4 | wc5 | wc6 | wc7 | wc8 | wc9 | wc10 | wc11 | wc12 | wc13 | wc14 | wc15 | wc16 | wc17 | wc18 | wc19 | wc20 | wc21 | wc22 | wc23 | wc24 | wc25 | wc26 | wc27 | wc28 ].
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
(* -- while its substituted form may be a former.  The hypothesis DaU   *)
(* says exactly what that case needs: for the terms that substitution   *)
(* puts in a variable's place, an ITm-derivation at a universe yields an *)
(* ITy-derivation.  It is stated in the very form the case produces,    *)
(* `upn |delta| (a..) i`, so no arithmetic about iterated shifts is      *)
(* needed, and the fundamental lemma can supply it from its own          *)
(* induction hypothesis for a.                                          *)
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
  try (match goal with | Ee : ?r = _ ++ _ |- _ => subst r end);
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

Ltac sc1 a en Hua Da DaU := unfold STy, STm; (* ity_nat *)
  intros rho k w Ew delta E;
  apply (ity_nat _ k w); spin_for a en Hua (nat_ k).

Ltac sc2 a en Hua Da DaU := unfold STy, STm; (* ity_prop *)
  intros rho k w Ew delta E;
  apply (ity_prop _ k w); spin_for a en Hua (prop k).

Ltac sc3 a en Hua Da DaU := unfold STy, STm; (* ity_univ *)
  intros rho k dl jj EE w Ew delta E;
  apply (ity_univ _ k dl jj EE w); spin_for a en Hua (univ k jj).

Ltac sc4 a en Hua Da DaU := unfold STy, STm; (* ity_prf *)
  intros rho k jj p wp xp Dp IHp delta E;
  apply ity_prf; apply IHp; exact E.

Ltac sc5 a en Hua Da DaU := unfold STy, STm; (* ity_pi *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi Ew DA IHA DB IHB
    delta E;
  apply ity_pi;
  [ spin_for a en Hua (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity ].

Ltac sc6 a en Hua Da DaU := unfold STy, STm; (* ity_sig *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig Ew DA IHA DB IHB
    delta E;
  apply ity_sig;
  [ spin_for a en Hua (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity ].

Ltac sc7 a en Hua Da DaU := unfold STy, STm; (* ity_w *)
  intros rho A B k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW Ew DA IHA DB IHB
    delta E;
  apply ity_w;
  [ spin_for a en Hua (wt k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity ].

Ltac sc8 a en Hua Da DaU := unfold STy, STm; (* ity_up *)
  intros rho A k w F DA IHA delta E;
  apply ity_up; apply IHA; exact E.

Ltac sc9 a en Hua Da DaU := unfold STy, STm; (* ity_of *)
  (* `notFormer` is NOT stable under substitution: A may be a VARIABLE -- a
     non-former, so ity_of is the clause that applies -- while the term
     substitution puts in its place may be a former.  DaU is exactly what that
     case needs. *)
  intros rho A k w v nf Dv IHv delta E;
  destruct A;
    try (destruct nf);
    try (apply ity_of; [exact I | apply IHv; exact E]);
  apply DaU; exact (IHv delta E).

Ltac sc10 a en Hua Da DaU := unfold STy, STm; (* ity_conv *)
  intros rho A k w F F' P Dc IHc delta E;
  apply (ity_conv _ _ _ _ F F' P); apply IHc; exact E.

Ltac sc11 a en Hua Da DaU := unfold STy, STm; (* i_ty *)
  intros rho A k w F D IH delta E;
  apply i_ty; apply IH; exact E.

Ltac sc12 a en Hua Da DaU := unfold STy, STm; (* i_var0 *)
  intros rho k Sy F w x delta E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ inversion E; subst en; subst rho; exact Da
  | inversion E; subst; apply i_var0 ].

Ltac sc13 a en Hua Da DaU := unfold STy, STm; (* i_varS *)
  intros rho e2 ii k Sy F w x D IH delta E;
  destruct delta as [| d0 delta]; cbn in E |- *;
  [ inversion E; subst; exact D
  | inversion E; subst; apply weaken1; apply (IH delta eq_refl) ].

Ltac sc14 a en Hua Da DaU := unfold STy, STm; (* i_zero *)
  intros rho k delta E; apply i_zero.

Ltac sc15 a en Hua Da DaU := unfold STy, STm; (* i_succ *)
  intros rho k n wn x D IH delta E;
  apply i_succ; apply IH; exact E.

Ltac sc16 a en Hua Da DaU := unfold STy, STm; (* i_lam *)
  intros rho A B t k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    w wt xt redt xtext gd Ew Ep DA IHA DB IHB Dt IHt delta E;
  apply (i_lam _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
           w wt xt redt xtext gd);
  [ spin_for a en Hua (lam k A B t)
  | spin_for a en Hua (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | intros u x;
    apply (IHt u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity ].

Ltac sc17 a en Hua Da DaU := unfold STy, STm; (* i_app *)
  intros rho A B f a2 k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
    wf xf wa xa Ep DA IHA DB IHB Df IHf Da2 IHa delta E;
  apply (i_app _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gPi
           wf xf wa xa);
  [ spin_for a en Hua (pi k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | apply IHf; exact E
  | apply IHa; exact E ].

Ltac sc18 a en Hua Da DaU := unfold STy, STm; (* i_pair *)
  intros rho A B t a2 k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wt xt wa xa g Ep DA IHA DB IHB Dt IHt Da2 IHa delta E;
  apply (i_pair _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
           wt xt wa xa g);
  [ spin_for a en Hua (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | apply IHt; exact E
  | apply IHa; exact E ].

Ltac sc19 a en Hua Da DaU := unfold STy, STm; (* i_fst *)
  intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp delta E;
  apply (i_fst _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp);
  [ spin_for a en Hua (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | apply IHp; exact E ].

Ltac sc20 a en Hua Da DaU := unfold STy, STm; (* i_snd *)
  intros rho A B p k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig
    wp xp Ep DA IHA DB IHB Dp IHp delta E;
  apply (i_snd _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gSig wp xp);
  [ spin_for a en Hua (sig_ k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | apply IHp; exact E ].

Ltac sc21 a en Hua Da DaU := unfold STy, STm; (* i_sup *)
  intros rho A B a2 f k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
    Bbr redBbr gBr wa xa wf xf gd Ew DA IHA DB IHB Da2 IHa Df IHf delta E;
  apply (i_sup _ _ _ _ _ k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
           Bbr redBbr gBr wa xa wf xf gd);
  [ spin_for a en Hua (wt k A B)
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | apply IHa; exact E
  | apply IHf; exact E ].

(* wrec: the motive is renamed at depth |delta| + 1, under the tree entry, and
   the step at depth |delta| + 3, under its own three binders -- the label,
   the branching function and the induction hypothesis -- and its induction
   hypothesis is used at the correspondingly triply-extended environment. *)
Ltac sc22 a en Hua Da DaU := unfold STy, STm; (* i_wrec *)
  intros rho A B C s w k i jj m n dA dB dBn dC EA EB EBn EC En
    wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red Sr
    gf gih ws xs redS stepSrel ww xw
    ESr Ew ESC DA IHA DB IHB DC IHC Dstep IHstep Dw IHw delta E;
  apply (i_wrec _ _ _ _ _ _ k i jj m n dA dB dBn dC EA EB EBn EC En
           wA FA B0 wB FB redB cohB gW SC FC cohC Bbr redBbr gBr Bih gIh Bih_red
           Sr gf gih ws xs redS stepSrel ww xw);
  [ spin_for a en Hua (stepWrap3 s)
  | spin_for a en Hua (wt k A B)
  | (* the motive's pin, which lives one binder in *)
    subst rho; intros w1;
    match goal with
    | |- _ = subst_etm (scons _ (rsub (_ ++ ?r0))) _ =>
        exact (eq_trans (ESC w1) (eq_sym (ers_upn1 r0 a en Hua delta w1 C)))
    end
  | apply IHA; exact E
  | intros u x;
    apply (IHB u x (Build_Entry i wA FA u (dnEl dA k EA FA u x) :: delta));
    cbn; rewrite E; reflexivity
  | intros u x;
    apply (IHC u x
             (Build_Entry k (ew wA B0)
                (wFam k wA B0 (upF dA k EA FA) wB
                   (fun u0 x0 => upF dB k EB (FB u0 x0)) redB cohB gW) u x
              :: delta));
    cbn; rewrite E; reflexivity
  | intros u0 z f sub subext gd ih ihext;
    apply (IHstep u0 z f sub subext gd ih ihext
             (Build_Entry n (epi (wB u0 z) (Bih u0 z f))
                (ihFam k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                   n dBn dC EBn EC Bih gIh Bih_red u0 z f gd sub subext)
                (ihR Sr f)
                (ihEl k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW m SC FC cohC
                   n dBn dC EBn EC Bih gIh Bih_red Sr u0 z f gd sub subext ih ihext
                   (gih u0 z f gd))
              :: Build_Entry k (epi (wB u0 z) Bbr)
                   (brFam k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
                      Bbr redBbr gBr u0 z) f
                   (brEl k i jj dA dB EA EB wA FA B0 wB FB redB cohB gW
                      Bbr redBbr gBr u0 z f sub subext (gf u0 z f gd))
              :: Build_Entry i wA FA u0 (dnEl dA k EA FA u0 z)
              :: delta));
    cbn; rewrite E; reflexivity
  | apply IHw; exact E ].

(* natrec: the step term is renamed at depth |delta| + 2, its two binders
   being the scrutinee's predecessor and the recursive result. *)
Ltac sc23 a en Hua Da DaU := unfold STy, STm; (* i_natrec *)
  intros rho C z s n k jj SC FC cohC S0 wz xz ws xs redS wn xn
    ES DC IHC Dz IHz Ds IHs Dn IHn delta E;
  apply (i_natrec _ _ _ _ _ k jj SC FC cohC S0 wz xz ws xs redS wn xn);
  [ spin_for a en Hua (stepWrap s)
  | intros m x;
    apply (IHC m x (Build_Entry jj enat (natFam jj) m x :: delta));
    cbn; rewrite E; reflexivity
  | apply IHz; exact E
  | intros m x w y;
    apply (IHs m x w y (Build_Entry k (SC m) (FC m x) w y
                        :: Build_Entry jj enat (natFam jj) m x :: delta));
    cbn; rewrite E; reflexivity
  | apply IHn; exact E ].

Ltac sc24 a en Hua Da DaU := unfold STy, STm; (* i_false *)
  intros rho k w g Ew delta E;
  apply (i_false _ k w g); spin_for a en Hua (false_ k).

Ltac sc25 a en Hua Da DaU := unfold STy, STm; (* i_all *)
  intros rho jj A p k wA FA wp xp w g Ew DA IHA Dp IHp delta E;
  apply (i_all _ jj _ _ k wA FA wp xp w g);
  [ spin_for a en Hua (all jj A p)
  | apply IHA; exact E
  | intros u y; apply (IHp u y (Build_Entry k wA FA u y :: delta));
    cbn; rewrite E; reflexivity ].

Ltac sc26 a en Hua Da DaU := unfold STy, STm; (* i_proof *)
  intros rho t p k jj wp xp h w g Ew Dp IHp delta E;
  apply (i_proof _ _ (p [upn (length delta) (a..)]) k jj wp xp h w g);
  [ spin_for a en Hua t | apply IHp; exact E ].

Ltac sc27 a en Hua Da DaU := unfold STy, STm; (* i_up_tm *)
  intros rho A t k Sy F w x DA IHA D IH delta E;
  apply i_up_tm; [apply IHA; exact E | apply IH; exact E].

Ltac sc28 a en Hua Da DaU := unfold STy, STm; (* i_conv *)
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
    [ sc1 a en Hua Da DaU | sc2 a en Hua Da DaU | sc3 a en Hua Da DaU | sc4 a en Hua Da DaU | sc5 a en Hua Da DaU | sc6 a en Hua Da DaU | sc7 a en Hua Da DaU | sc8 a en Hua Da DaU | sc9 a en Hua Da DaU | sc10 a en Hua Da DaU | sc11 a en Hua Da DaU | sc12 a en Hua Da DaU | sc13 a en Hua Da DaU | sc14 a en Hua Da DaU | sc15 a en Hua Da DaU | sc16 a en Hua Da DaU | sc17 a en Hua Da DaU | sc18 a en Hua Da DaU | sc19 a en Hua Da DaU | sc20 a en Hua Da DaU | sc21 a en Hua Da DaU | sc22 a en Hua Da DaU | sc23 a en Hua Da DaU | sc24 a en Hua Da DaU | sc25 a en Hua Da DaU | sc26 a en Hua Da DaU | sc27 a en Hua Da DaU | sc28 a en Hua Da DaU ].
Qed.

Lemma subst_ITm (rho0 : Env) (a : tm) (en : Entry) (Hua : en_u en = ers rho0 a)
  (Da : ITm rho0 a (en_k en) (en_S en) (en_F en) (en_u en) (en_x en))
  (DaU : SubUniv rho0 a)
  rho t k Sy F w x (D : ITm rho t k Sy F w x) : STm rho0 a en rho t k Sy F w x.
Proof.
  revert rho t k Sy F w x D.
  apply (ITm_mut (fun rho A k w F _ => STy rho0 a en rho A k w F)
                 (fun rho t k Sy F w x _ => STm rho0 a en rho t k Sy F w x));
    [ sc1 a en Hua Da DaU | sc2 a en Hua Da DaU | sc3 a en Hua Da DaU | sc4 a en Hua Da DaU | sc5 a en Hua Da DaU | sc6 a en Hua Da DaU | sc7 a en Hua Da DaU | sc8 a en Hua Da DaU | sc9 a en Hua Da DaU | sc10 a en Hua Da DaU | sc11 a en Hua Da DaU | sc12 a en Hua Da DaU | sc13 a en Hua Da DaU | sc14 a en Hua Da DaU | sc15 a en Hua Da DaU | sc16 a en Hua Da DaU | sc17 a en Hua Da DaU | sc18 a en Hua Da DaU | sc19 a en Hua Da DaU | sc20 a en Hua Da DaU | sc21 a en Hua Da DaU | sc22 a en Hua Da DaU | sc23 a en Hua Da DaU | sc24 a en Hua Da DaU | sc25 a en Hua Da DaU | sc26 a en Hua Da DaU | sc27 a en Hua Da DaU | sc28 a en Hua Da DaU ].
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
