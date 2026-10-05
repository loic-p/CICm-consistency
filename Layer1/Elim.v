From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle.
From Stdlib Require Import Arith Lia.

(* Elimination principles for Rel (blueprint Lemma 6.5): the working
   interface of layer 1.  Nothing downstream names a PER; everything goes
   through Rel, Good and eqty. *)

Lemma tau_fun_lvl n m T T' T'' P Q : tau n T T' P -> tau m T T'' Q -> P ≐ Q.
Proof.
  intros H1 H2; eapply tau_fun;
    [apply (tau_cumul n (Nat.max n m)); [apply Nat.le_max_l | exact H1]
    |apply (tau_cumul m (Nat.max n m)); [apply Nat.le_max_r | exact H2]].
Qed.

Lemma Rel_intro n P T a b : tau n T T P -> P a b -> Rel T a b.
Proof. intros; exists n, P; auto. Qed.

Lemma Rel_elim n P T T' a b : tau n T T' P -> Rel T a b -> P a b.
Proof.
  intros H [m [Q [HQ Hab]]]. apply (tau_fun_lvl _ _ _ _ _ _ _ H HQ); assumption.
Qed.

Lemma tau_refl_l n T T' P : tau n T T' P -> tau n T T P.
Proof. intros H; eapply tau_trans; [exact H | apply tau_sym; exact H]. Qed.

Lemma tau_refl_r n T T' P : tau n T T' P -> tau n T' T' P.
Proof. intros H; eapply tau_trans; [apply tau_sym; exact H | exact H]. Qed.

(* E7 *)
Lemma Rel_resp n T T' : eqty n T T' -> Rel T ≐ Rel T'.
Proof.
  intros [P HP] a b; split; intros H.
  - eapply Rel_intro; [eapply tau_refl_r; exact HP | eapply Rel_elim; eauto].
  - eapply Rel_intro; [eapply tau_refl_l; exact HP |].
    eapply Rel_elim; [apply tau_sym; exact HP | exact H].
Qed.

(* E1 *)
Lemma Rel_sym T a b : Rel T a b -> Rel T b a.
Proof. intros [n [P [H Hab]]]; exists n, P; split; auto. apply (pk_sym _ (tau_ok _ _ _ _ H)); auto. Qed.

Lemma Rel_trans T a b c : Rel T a b -> Rel T b c -> Rel T a c.
Proof.
  intros [n [P [H Hab]]] Hbc; exists n, P; split; auto.
  apply (pk_trans _ (tau_ok _ _ _ _ H) _ b); auto. eapply Rel_elim; eauto.
Qed.

Lemma Rel_exp T a b a' b' : reds a a' -> reds b b' -> Rel T a' b' -> Rel T a b.
Proof.
  intros Ha Hb [n [P [H Hab]]]; exists n, P; split; auto.
  eapply (pk_exp _ (tau_ok _ _ _ _ H)); eauto.
Qed.

Lemma Rel_red T a b a' b' : reds a a' -> reds b b' -> Rel T a b -> Rel T a' b'.
Proof.
  intros Ha Hb [n [P [H Hab]]]; exists n, P; split; auto.
  eapply (pk_red _ (tau_ok _ _ _ _ H)); eauto.
Qed.

Lemma Rel_stuck T a b : Good_ty T -> stuckv a -> stuckv b -> Rel T a b.
Proof.
  intros [n [P H]] Ha Hb; exists n, P; split; [eapply tau_refl_l; exact H|].
  apply (pk_stuck _ (tau_ok _ _ _ _ H)); auto.
Qed.

Lemma Good_ty_resp n T T' : eqty n T T' -> Good_ty T -> Good_ty T'.
Proof. intros H _; exists n; eapply eqty_refl_r; eauto. Qed.

Lemma Rel_exp_ty T T' a b : reds T T' -> Rel T' a b -> Rel T a b.
Proof.
  intros H [n [P [HP Hab]]]; exists n, P; split; auto; eapply tau_exp; eauto using reds.
Qed.

Lemma Rel_red_ty T T' a b : reds T T' -> Rel T a b -> Rel T' a b.
Proof.
  intros H [n [P [HP Hab]]]; exists n, P; split; auto; eapply tau_red; eauto using reds.
Qed.

(* E2 *)
Lemma Rel_nat_elim T a b : eval T enat -> Rel T a b -> NatPer a b.
Proof.
  intros He [n [P [HP Hab]]].
  destruct (LR_inv_nat _ _ _ _ _ HP He) as [_ E]; apply E; assumption.
Qed.

Lemma Rel_nat_intro T a b : Good_ty T -> eval T enat -> NatPer a b -> Rel T a b.
Proof.
  intros [n [P HP]] He Hab; exists n, P; split; auto.
  destruct (LR_inv_nat _ _ _ _ _ HP He) as [_ E]; apply E; assumption.
Qed.

(* Prop *)
Lemma Rel_prop_elim T a b : eval T eprop -> Rel T a b -> PR a b.
Proof.
  intros He [n [P [HP Hab]]].
  destruct (LR_inv_prop _ _ _ _ _ HP He) as [_ E]; apply E; assumption.
Qed.

Lemma Rel_prop_intro T a b : Good_ty T -> eval T eprop -> PR a b -> Rel T a b.
Proof.
  intros [n [P HP]] He Hab; exists n, P; split; auto.
  destruct (LR_inv_prop _ _ _ _ _ HP He) as [_ E]; apply E; assumption.
Qed.

(* E6 *)
Lemma Rel_prf_intro T p a b : Good_ty T -> eval T (eprf p) -> Rel T a b.
Proof.
  intros [n [P HP]] He; exists n, P; split; auto.
  destruct (LR_inv_prf _ _ _ _ _ _ HP He) as [? [_ [_ E]]]; apply E; exact I.
Qed.

(* E5 *)
Lemma Rel_univ_elim T m C C' : eval T (euniv m) -> Rel T C C' -> eqty m C C'.
Proof.
  intros He [n [P [HP H]]].
  destruct (LR_inv_univ _ _ _ _ _ _ HP He) as [_ [_ E]].
  destruct (proj1 (E _ _) H) as [Q HQ]. exists Q. apply below_spec in HQ; tauto.
Qed.

Lemma Rel_univ_intro T m C C' : Good_ty T -> eval T (euniv m) -> eqty m C C' -> Rel T C C'.
Proof.
  intros [n [P HP]] He [Q HQ]; exists n, P; split; auto.
  destruct (LR_inv_univ _ _ _ _ _ _ HP He) as [Hm [_ E]].
  apply E. exists Q. apply below_spec; auto.
Qed.

(* E3 / E4 *)
Lemma Rel_pi_elim T A0 B0 f g : eval T (epi A0 B0) -> Rel T f g ->
  forall u u', Rel A0 u u' -> Rel (eapp B0 u) (eapp f u) (eapp g u').
Proof.
  intros He [n [P [HP Hfg]]] u u' Hu.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  assert (Hu' : PA u u') by (eapply Rel_elim; eauto).
  eapply Rel_intro; [eapply tau_refl_l; apply HB; exact Hu' |].
  apply E in Hfg. apply Hfg; assumption.
Qed.

Lemma Rel_pi_intro T A0 B0 f g : Good_ty T -> eval T (epi A0 B0) ->
  (forall u u', Rel A0 u u' -> Rel (eapp B0 u) (eapp f u) (eapp g u')) -> Rel T f g.
Proof.
  intros [n [P HP]] He H; exists n, P; split; auto.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  apply E. intros u u' Hu.
  eapply Rel_elim; [apply HB; exact Hu |].
  apply H. eapply Rel_intro; [eapply tau_refl_l; exact HA | exact Hu].
Qed.

Lemma Rel_pi_dom T A0 B0 : Good_ty T -> eval T (epi A0 B0) -> Good_ty A0.
Proof.
  intros [n [P HP]] He.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA _]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, PA; eapply tau_refl_l; exact HA.
Qed.

Lemma Rel_pi_cod T A0 B0 u u' : Good_ty T -> eval T (epi A0 B0) -> Rel A0 u u' ->
  exists n, eqty n (eapp B0 u) (eapp B0 u').
Proof.
  intros [n [P HP]] He Hu.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB _]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, (PB u u'); apply HB; eapply Rel_elim; eauto.
Qed.

(* Sigma *)
Lemma Rel_sig_elim T A0 B0 p q : eval T (esig A0 B0) -> Rel T p q ->
  Rel A0 (efst p) (efst q) /\ Rel (eapp B0 (efst p)) (esnd p) (esnd q).
Proof.
  intros He [n [P [HP Hpq]]].
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  apply E in Hpq; destruct Hpq as [H1 H2]; split.
  - eapply Rel_intro; [eapply tau_refl_l; exact HA | exact H1].
  - eapply Rel_intro; [eapply tau_refl_l; apply HB; exact H1 | exact H2].
Qed.

Lemma Rel_sig_intro T A0 B0 p q : Good_ty T -> eval T (esig A0 B0) ->
  Rel A0 (efst p) (efst q) -> Rel (eapp B0 (efst p)) (esnd p) (esnd q) -> Rel T p q.
Proof.
  intros [n [P HP]] He H1 H2; exists n, P; split; auto.
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  apply E.
  assert (H1' : PA (efst p) (efst q)) by (eapply Rel_elim; eauto).
  split; [exact H1' | eapply Rel_elim; [apply HB; exact H1' | exact H2]].
Qed.

Lemma Rel_sig_dom T A0 B0 : Good_ty T -> eval T (esig A0 B0) -> Good_ty A0.
Proof.
  intros [n [P HP]] He.
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA _]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, PA; eapply tau_refl_l; exact HA.
Qed.

Lemma Rel_sig_cod T A0 B0 u u' : Good_ty T -> eval T (esig A0 B0) -> Rel A0 u u' ->
  exists n, eqty n (eapp B0 u) (eapp B0 u').
Proof.
  intros [n [P HP]] He Hu.
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB _]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, (PB u u'); apply HB; eapply Rel_elim; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* W.  The domain and codomain lemmas are the Sigma ones verbatim; the  *)
(* interesting one is the ELIMINATOR, which is the Rel-level induction  *)
(* principle of WPer.  Nothing outside layer 1 may name a PER, so the   *)
(* principle has to be restated with `Rel T` in place of `WPer PA PB`   *)
(* and `Rel (B0 . a)` in place of `PB a a'` -- that translation is what  *)
(* makes it bureaucratic, not the induction itself.  Both minor premises *)
(* are handed the layer-1 equality of the two subjects as well, because  *)
(* the consumer needs it to move the motive along the scrutinee.        *)
(* ------------------------------------------------------------------ *)

Lemma Rel_w_dom T A0 B0 : Good_ty T -> eval T (ew A0 B0) -> Good_ty A0.
Proof.
  intros [n [P HP]] He.
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA _]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, PA; eapply tau_refl_l; exact HA.
Qed.

Lemma Rel_w_cod T A0 B0 u u' : Good_ty T -> eval T (ew A0 B0) -> Rel A0 u u' ->
  exists n, eqty n (eapp B0 u) (eapp B0 u').
Proof.
  intros [n [P HP]] He Hu.
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB _]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'.
  exists n, (PB u u'); apply HB; eapply Rel_elim; eauto.
Qed.

(* Introduction: a tree is related as soon as its label is related in the
   domain and its branches are related in the W type itself, at related
   indices.  The branches' indices are compared at `B0 . a` -- the left
   label -- which is the same relation as `B0 . a'` because the codomain
   family is a family over the domain PER. *)
Lemma Rel_w_intro T A0 B0 a a' f f' : Good_ty T -> eval T (ew A0 B0) ->
  Rel A0 a a' ->
  (forall u u', Rel (eapp B0 a) u u' -> Rel T (eapp f u) (eapp f' u')) ->
  Rel T (esup a f) (esup a' f').
Proof.
  intros [n [P HP]] He Ha Hf; exists n, P; split; [exact HP|].
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  apply E.
  assert (HaP : PA a a') by (eapply Rel_elim; [exact HA | exact Ha]).
  eapply wp_sup;
    [ apply eval_whnf; left; apply v_sup
    | apply eval_whnf; left; apply v_sup
    | exact HaP |].
  intros u u' Hu.
  apply (proj1 (E _ _)). eapply Rel_elim; [exact HP |].
  apply Hf. eapply Rel_intro; [eapply tau_refl_l; apply HB; exact HaP | exact Hu].
Qed.

(* The eliminator.  `R` is the predicate being proved of every pair of
   related trees -- in the fundamental lemma, "the two recursors agree in
   the motive".  The sup premise receives the two whnfs, the layer-1
   equality of the subjects, the equality of the labels, the equality of
   the branches, and the induction hypothesis on the branches. *)
Lemma Rel_w_elim T A0 B0 (R : etm -> etm -> Prop) :
  Good_ty T -> eval T (ew A0 B0) ->
  (forall w w' a a' f f', eval w (esup a f) -> eval w' (esup a' f') ->
     Rel T w w' -> Rel A0 a a' ->
     (forall u u', Rel (eapp B0 a) u u' -> Rel T (eapp f u) (eapp f' u')) ->
     (forall u u', Rel (eapp B0 a) u u' -> R (eapp f u) (eapp f' u')) ->
     R w w') ->
  (forall w w', Rel T w w' -> stuckv w -> stuckv w' -> R w w') ->
  forall w w', Rel T w w' -> R w w'.
Proof.
  intros [n [P HP]] He Hsup Hstk w w' Hww.
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A0' [B0' [PA [PB [He' [HA [HB E]]]]]]].
  assert (E' := eval_det _ _ _ He He'); injection E'; intros; subst A0' B0'; clear E'.
  (* the three translations between the PERs and Rel *)
  assert (HRT : forall x y, WPer PA PB x y -> Rel T x y)
    by (intros x y Hxy; exists n, P; split; [exact HP | apply E; exact Hxy]).
  assert (HRA : forall x y, PA x y -> Rel A0 x y)
    by (intros x y Hxy; eapply Rel_intro; [eapply tau_refl_l; exact HA | exact Hxy]).
  assert (HRB : forall x y, PA x y -> forall u u', Rel (eapp B0 x) u u' -> PB x y u u')
    by (intros x y Hxy u u' Hu; eapply Rel_elim; [apply HB; exact Hxy | exact Hu]).
  assert (HRB' : forall x y, PA x y -> forall u u', PB x y u u' -> Rel (eapp B0 x) u u')
    by (intros x y Hxy u u' Hu;
        eapply Rel_intro; [eapply tau_refl_l; apply HB; exact Hxy | exact Hu]).
  (* now the induction is the one of WPer, with the premises translated *)
  assert (HW : WPer PA PB w w')
    by (apply (proj1 (E w w')); eapply Rel_elim; [exact HP | exact Hww]).
  clear Hww. induction HW as [w w' a a' f f' Hw Hw' Ha Hbr IH | w w' Hw Hw'].
  - eapply Hsup;
      [ exact Hw | exact Hw'
      | apply HRT; eapply wp_sup; [exact Hw | exact Hw' | exact Ha | exact Hbr]
      | apply HRA; exact Ha
      | intros u u' Hu; apply HRT, Hbr; eapply HRB; [exact Ha | exact Hu]
      | intros u u' Hu; apply IH; eapply HRB; [exact Ha | exact Hu] ].
  - apply Hstk; [apply HRT; apply wp_stuck; assumption | exact Hw | exact Hw'].
Qed.

(* A layer-1 good type evaluates to a type former or to a stuck term.  In
   particular nothing whose whnf is a lambda, a numeral, a pair or a star is
   a layer-1 type.  Used to show that a type's erasure being layer-1 good is
   a real constraint. *)
Lemma tau_value_shape n A A' P : tau n A A' P -> forall w, eval A w -> value w ->
  w = enat \/ w = eprop \/ (exists p, w = eprf p) \/ (exists m, w = euniv m)
  \/ (exists a b, w = epi a b) \/ (exists a b, w = esig a b)
  \/ (exists a b, w = ew a b).
Proof.
  unfold tau; intros H; induction H as
    [ A A' P Q HLR IH HPQ
    | A B A' B' P HrA HrA' HLR IH
    | A A' HeA HeA'
    | A A' HeA HeA'
    | A A' p p' HeA HeA' HPR
    | A A' m Hm HeA HeA'
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' N N' HeA HeA' HsN HsN' ];
    intros w Hw Hv.
  - apply IH; assumption.
  - apply IH; [eapply eval_reds_inv; eassumption | assumption].
  - left; exact (eval_det _ _ _ Hw HeA).
  - right; left; exact (eval_det _ _ _ Hw HeA).
  - right; right; left; exists p; exact (eval_det _ _ _ Hw HeA).
  - right; right; right; left; exists m; exact (eval_det _ _ _ Hw HeA).
  - right; right; right; right; left; exists A0, B0; exact (eval_det _ _ _ Hw HeA).
  - right; right; right; right; right; left; exists A0, B0; exact (eval_det _ _ _ Hw HeA).
  - right; right; right; right; right; right; exists A0, B0; exact (eval_det _ _ _ Hw HeA).
  - exfalso; rewrite (eval_det _ _ _ Hw HeA) in Hv.
    exact (stuck_not_value N HsN Hv).
Qed.

Lemma eqty_lam_absurd n s A' : eqty n (elam s) A' -> False.
Proof.
  intros [P HP].
  destruct (tau_value_shape n _ _ _ HP (elam s) (eval_whnf _ (or_introl (v_lam s)))
              (v_lam s)) as
    [E | [E | [[p E] | [[m E] | [[a [b E]] | [[a [b E]] | [a [b E]]]]]]]]; discriminate E.
Qed.

(* ------------------------------------------------------------------ *)
(* The HETEROGENEOUS inversions: the ones above read one type and its  *)
(* own components, these read the components of TWO equal types.  That *)
(* is what functionality of the interpretation needs -- it compares two *)
(* readings of one syntactic type in two related environments, and the  *)
(* two readings' realisers are only layer-1 equal, never identical.     *)
(* ------------------------------------------------------------------ *)

Lemma eqty_prf_inv n T T' p p' : eqty n T T' ->
  eval T (eprf p) -> eval T' (eprf p') -> PR p p'.
Proof.
  intros [P HP] He He'.
  destruct (LR_inv_prf _ _ _ _ _ _ HP He) as [q [Hq [Hpr _]]].
  assert (E := eval_det _ _ _ He' Hq); injection E; intros <-; exact Hpr.
Qed.

Lemma eqty_pi_dom n T T' A0 B0 A0' B0' : eqty n T T' ->
  eval T (epi A0 B0) -> eval T' (epi A0' B0') -> eqty n A0 A0'.
Proof.
  intros [P HP] He He'.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA _]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists PA; exact HA.
Qed.

Lemma eqty_pi_cod n T T' A0 B0 A0' B0' u u' : eqty n T T' ->
  eval T (epi A0 B0) -> eval T' (epi A0' B0') -> Rel A0 u u' ->
  eqty n (eapp B0 u) (eapp B0' u').
Proof.
  intros [P HP] He He' Hu.
  destruct (LR_inv_pi _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA [HB _]]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists (PB u u'); apply HB; eapply Rel_elim; [exact HA | exact Hu].
Qed.

Lemma eqty_sig_dom n T T' A0 B0 A0' B0' : eqty n T T' ->
  eval T (esig A0 B0) -> eval T' (esig A0' B0') -> eqty n A0 A0'.
Proof.
  intros [P HP] He He'.
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA _]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists PA; exact HA.
Qed.

Lemma eqty_sig_cod n T T' A0 B0 A0' B0' u u' : eqty n T T' ->
  eval T (esig A0 B0) -> eval T' (esig A0' B0') -> Rel A0 u u' ->
  eqty n (eapp B0 u) (eapp B0' u').
Proof.
  intros [P HP] He He' Hu.
  destruct (LR_inv_sig _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA [HB _]]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists (PB u u'); apply HB; eapply Rel_elim; [exact HA | exact Hu].
Qed.

Lemma eqty_w_dom n T T' A0 B0 A0' B0' : eqty n T T' ->
  eval T (ew A0 B0) -> eval T' (ew A0' B0') -> eqty n A0 A0'.
Proof.
  intros [P HP] He He'.
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA _]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists PA; exact HA.
Qed.

Lemma eqty_w_cod n T T' A0 B0 A0' B0' u u' : eqty n T T' ->
  eval T (ew A0 B0) -> eval T' (ew A0' B0') -> Rel A0 u u' ->
  eqty n (eapp B0 u) (eapp B0' u').
Proof.
  intros [P HP] He He' Hu.
  destruct (LR_inv_w _ _ _ _ _ _ _ HP He) as [A1 [B1 [PA [PB [He1 [HA [HB _]]]]]]].
  assert (E := eval_det _ _ _ He' He1); injection E; intros; subst A1 B1.
  exists (PB u u'); apply HB; eapply Rel_elim; [exact HA | exact Hu].
Qed.

(* ------------------------------------------------------------------ *)
(* LEVEL RESTRICTION.  Cumulativity (B7) moves a type equality UP; this *)
(* moves one DOWN, provided both sides are already types at the lower    *)
(* level.  It is what the interpretation's functionality needs at the    *)
(* universe-lift clause, where the subject is read at level k but the    *)
(* judgement concludes at level S k, so a level-indexed hypothesis would *)
(* not descend to the subderivation.                                     *)
(*                                                                      *)
(* The proof is an induction on the higher derivation.  Only two clauses *)
(* use the hypotheses: the universe, where `m < k` has to be recovered   *)
(* (and is, by inverting the lower derivation at the same whnf), and Pi  *)
(* and Sigma, where the components' own lower derivations come from the  *)
(* same inversion.  The codomain PER is not carried across -- it is      *)
(* rebuilt as `Rel (B0 . u)`, which every layer-1 PER is equal to.       *)
(* ------------------------------------------------------------------ *)

Lemma tau_Rel n X Y Q : tau n X Y Q -> Rel X ≐ Q.
Proof.
  intros H a b; split.
  - apply (Rel_elim n Q X Y); exact H.
  - intros HQ; eapply Rel_intro; [eapply tau_refl_l; exact H | exact HQ].
Qed.

Lemma tau_restrict n A B P : tau n A B P ->
  forall k, eqty k A A -> eqty k B B -> eqty k A B.
Proof.
  unfold tau; intros H; induction H as
    [ A A' P0 Q HLR IH HPQ
    | A C A' C' P0 HrA HrA' HLR IH
    | A A' HeA HeA'
    | A A' HeA HeA'
    | A A' p p' HeA HeA' HPR
    | A A' m Hm HeA HeA'
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA IHA HB IHB
    | A A' N N' HeA HeA' HsN HsN' ];
    intros k HAA HBB.
  - exact (IH k HAA HBB).
  - eapply eqty_exp; [exact HrA | exact HrA' |].
    apply IH;
      [ eapply eqty_red; [exact HAA | exact HrA | exact HrA]
      | eapply eqty_red; [exact HBB | exact HrA' | exact HrA'] ].
  - exists NatPer; apply LR_nat; assumption.
  - exists PR; apply LR_prop; assumption.
  - exists TruePer; eapply LR_prf; [exact HeA | exact HeA' | exact HPR].
  - destruct HAA as [Q HQ].
    destruct (LR_inv_univ k (below k) _ _ _ _ HQ HeA) as [Hmk _].
    exists (fun C C' => exists R, below k m C C' R).
    apply LR_univ; assumption.
  - (* Pi *)
    destruct HAA as [QA HQA]; destruct HBB as [QB HQB].
    destruct (LR_inv_pi k (below k) _ _ _ _ _ HQA HeA)
      as [A1 [B1 [PA1 [PB1 [He1 [HA1 [HB1 _]]]]]]].
    assert (E1 := eval_det _ _ _ HeA He1); injection E1; intros; subst A1 B1.
    destruct (LR_inv_pi k (below k) _ _ _ _ _ HQB HeA')
      as [A2 [B2 [PA2 [PB2 [He2 [HA2 [HB2 _]]]]]]].
    assert (E2 := eval_det _ _ _ HeA' He2); injection E2; intros; subst A2 B2.
    destruct (IHA k (ex_intro _ PA1 HA1) (ex_intro _ PA2 HA2)) as [PAk HAk].
    exists (PiPer PAk (fun u u' => Rel (eapp B0 u))).
    eapply LR_pi; [exact HeA | exact HeA' | exact HAk |].
    intros u u' Hu.
    assert (HRu : Rel A0 u u') by exact (proj2 (tau_Rel k A0 A0' PAk HAk u u') Hu).
    assert (HRd : Rel A0 u' u')
      by (eapply Rel_trans; [apply Rel_sym; exact HRu | exact HRu]).
    assert (Hu1 : PA1 u u') by exact (proj1 (tau_Rel k A0 A0 PA1 HA1 u u') HRu).
    assert (Hu2 : PA2 u' u').
    { apply (proj1 (tau_Rel k A0' A0' PA2 HA2 u' u')).
      apply (proj2 (tau_Rel k A0' A0' PAk (tau_refl_r k A0 A0' PAk HAk) u' u')).
      exact (proj1 (tau_Rel k A0 A0' PAk HAk u' u') HRd). }
    assert (HuP : PA u u') by exact (proj1 (tau_Rel n A0 A0' PA HA u u') HRu).
    destruct (IHB u u' HuP k
                (ex_intro _ (PB1 u u') (tau_refl_l k _ _ _ (HB1 u u' Hu1)))
                (ex_intro _ (PB2 u' u') (tau_refl_l k _ _ _ (HB2 u' u' Hu2))))
      as [Qc HQc].
    eapply LR_ext; [exact HQc | apply PerEq_sym; exact (tau_Rel k _ _ _ HQc)].
  - (* Sigma, identically *)
    destruct HAA as [QA HQA]; destruct HBB as [QB HQB].
    destruct (LR_inv_sig k (below k) _ _ _ _ _ HQA HeA)
      as [A1 [B1 [PA1 [PB1 [He1 [HA1 [HB1 _]]]]]]].
    assert (E1 := eval_det _ _ _ HeA He1); injection E1; intros; subst A1 B1.
    destruct (LR_inv_sig k (below k) _ _ _ _ _ HQB HeA')
      as [A2 [B2 [PA2 [PB2 [He2 [HA2 [HB2 _]]]]]]].
    assert (E2 := eval_det _ _ _ HeA' He2); injection E2; intros; subst A2 B2.
    destruct (IHA k (ex_intro _ PA1 HA1) (ex_intro _ PA2 HA2)) as [PAk HAk].
    exists (SigPer PAk (fun u u' => Rel (eapp B0 u))).
    eapply LR_sig; [exact HeA | exact HeA' | exact HAk |].
    intros u u' Hu.
    assert (HRu : Rel A0 u u') by exact (proj2 (tau_Rel k A0 A0' PAk HAk u u') Hu).
    assert (HRd : Rel A0 u' u')
      by (eapply Rel_trans; [apply Rel_sym; exact HRu | exact HRu]).
    assert (Hu1 : PA1 u u') by exact (proj1 (tau_Rel k A0 A0 PA1 HA1 u u') HRu).
    assert (Hu2 : PA2 u' u').
    { apply (proj1 (tau_Rel k A0' A0' PA2 HA2 u' u')).
      apply (proj2 (tau_Rel k A0' A0' PAk (tau_refl_r k A0 A0' PAk HAk) u' u')).
      exact (proj1 (tau_Rel k A0 A0' PAk HAk u' u') HRd). }
    assert (HuP : PA u u') by exact (proj1 (tau_Rel n A0 A0' PA HA u u') HRu).
    destruct (IHB u u' HuP k
                (ex_intro _ (PB1 u u') (tau_refl_l k _ _ _ (HB1 u u' Hu1)))
                (ex_intro _ (PB2 u' u') (tau_refl_l k _ _ _ (HB2 u' u' Hu2))))
      as [Qc HQc].
    eapply LR_ext; [exact HQc | apply PerEq_sym; exact (tau_Rel k _ _ _ HQc)].
  - (* W, identically *)
    destruct HAA as [QA HQA]; destruct HBB as [QB HQB].
    destruct (LR_inv_w k (below k) _ _ _ _ _ HQA HeA)
      as [A1 [B1 [PA1 [PB1 [He1 [HA1 [HB1 _]]]]]]].
    assert (E1 := eval_det _ _ _ HeA He1); injection E1; intros; subst A1 B1.
    destruct (LR_inv_w k (below k) _ _ _ _ _ HQB HeA')
      as [A2 [B2 [PA2 [PB2 [He2 [HA2 [HB2 _]]]]]]].
    assert (E2 := eval_det _ _ _ HeA' He2); injection E2; intros; subst A2 B2.
    destruct (IHA k (ex_intro _ PA1 HA1) (ex_intro _ PA2 HA2)) as [PAk HAk].
    exists (WPer PAk (fun u u' => Rel (eapp B0 u))).
    eapply LR_w; [exact HeA | exact HeA' | exact HAk |].
    intros u u' Hu.
    assert (HRu : Rel A0 u u') by exact (proj2 (tau_Rel k A0 A0' PAk HAk u u') Hu).
    assert (HRd : Rel A0 u' u')
      by (eapply Rel_trans; [apply Rel_sym; exact HRu | exact HRu]).
    assert (Hu1 : PA1 u u') by exact (proj1 (tau_Rel k A0 A0 PA1 HA1 u u') HRu).
    assert (Hu2 : PA2 u' u').
    { apply (proj1 (tau_Rel k A0' A0' PA2 HA2 u' u')).
      apply (proj2 (tau_Rel k A0' A0' PAk (tau_refl_r k A0 A0' PAk HAk) u' u')).
      exact (proj1 (tau_Rel k A0 A0' PAk HAk u' u') HRd). }
    assert (HuP : PA u u') by exact (proj1 (tau_Rel n A0 A0' PA HA u u') HRu).
    destruct (IHB u u' HuP k
                (ex_intro _ (PB1 u u') (tau_refl_l k _ _ _ (HB1 u u' Hu1)))
                (ex_intro _ (PB2 u' u') (tau_refl_l k _ _ _ (HB2 u' u' Hu2))))
      as [Qc HQc].
    eapply LR_ext; [exact HQc | apply PerEq_sym; exact (tau_Rel k _ _ _ HQc)].
  - exists NePer; eapply LR_ne; [exact HeA | exact HeA' | exact HsN | exact HsN'].
Qed.

Lemma eqty_restrict k n A B : eqty n A B -> eqty k A A -> eqty k B B -> eqty k A B.
Proof. intros [P HP]; apply (tau_restrict n A B P HP k). Qed.

