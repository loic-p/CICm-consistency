From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle.Inv Layer1.Bundle.Fun.

(* PER-ness of the index (B1) and symmetry (B2), proved together: symmetry
   at Pi needs index irrelevance, which needs functionality (Fun.v) and
   symmetry of the sub-derivations; PER-ness of PiPer needs symmetry of the
   domain PER, i.e. B1 at the sub-derivation. *)

Record PerOK (P : PER) := {
  pk_sym : forall a b, P a b -> P b a;
  pk_trans : forall a b c, P a b -> P b c -> P a c;
  pk_exp : forall a b a' b', reds a b -> reds a' b' -> P b b' -> P a a';
  pk_red : forall a b a' b', P a b -> reds a a' -> reds b b' -> P a' b';
  pk_stuck : forall a b, stuckv a -> stuckv b -> P a b
}.

(* What the universe clause needs from the lower levels. *)
Record XOK (Y : etm -> etm -> PER -> Prop) := {
  xo_sym : forall A A' P, Y A A' P -> Y A' A P;
  xo_trans : forall A A' A'' P Q, Y A A' P -> Y A' A'' Q -> Y A A'' P;
  xo_exp : forall A B A' B' P, reds A B -> reds A' B' -> Y B B' P -> Y A A' P;
  xo_red : forall A A' B B' P, Y A A' P -> reds A B -> reds A' B' -> Y B B' P;
  xo_stuck : forall A A', stuckv A -> stuckv A' -> exists P, Y A A' P
}.

Lemma PerOK_ext P Q : PerOK P -> P ≐ Q -> PerOK Q.
Proof.
  intros [Hs Ht He Hr Hk] E; constructor; intros.
  - apply E, Hs, E; assumption.
  - apply E; eapply Ht; apply E; eassumption.
  - apply E; eapply He; eauto; apply E; assumption.
  - apply E; eapply Hr; eauto; apply E; assumption.
  - apply E, Hk; assumption.
Qed.

Lemma NatPer_sym a b : NatPer a b -> NatPer b a.
Proof.
  induction 1; [eapply np_zero | eapply np_succ | eapply np_stuck]; eauto.
Qed.

Lemma NatPer_trans a b c : NatPer a b -> NatPer b c -> NatPer a c.
Proof.
  intros H; revert c.
  induction H as [a b Ha Hb | a b a0 b0 Ha Hb H IH | a b Ha Hb]; intros c H2.
  - inversion H2 as [b1 c1 Hb1 Hc1 | b1 c1 b2 c2 Hb1 Hc1 H3 | b1 c1 Hb1 Hc1]; subst.
    + eapply np_zero; eauto.
    + exfalso; assert (E := eval_det _ _ _ Hb Hb1); discriminate E.
    + exfalso; eapply stuckv_not_value; [exact Hb1 | exact Hb | constructor].
  - inversion H2 as [b1 c1 Hb1 Hc1 | b1 c1 b2 c2 Hb1 Hc1 H3 | b1 c1 Hb1 Hc1]; subst.
    + exfalso; assert (E := eval_det _ _ _ Hb Hb1); discriminate E.
    + assert (E := eval_det _ _ _ Hb Hb1); injection E; intros; subst.
      eapply np_succ; [exact Ha | exact Hc1 | apply IH; exact H3].
    + exfalso; eapply stuckv_not_value; [exact Hb1 | exact Hb | constructor].
  - inversion H2 as [b1 c1 Hb1 Hc1 | b1 c1 b2 c2 Hb1 Hc1 H3 | b1 c1 Hb1 Hc1]; subst.
    + exfalso; eapply stuckv_not_value; [exact Hb | exact Hb1 | constructor].
    + exfalso; eapply stuckv_not_value; [exact Hb | exact Hb1 | constructor].
    + eapply np_stuck; eauto.
Qed.

Lemma NatPer_ok : PerOK NatPer.
Proof.
  constructor.
  - exact NatPer_sym.
  - exact NatPer_trans.
  - intros a b a' b' Ha Hb H;
      destruct H as [c c' H1 H2 | c c' d d' H1 H2 H3 | c c' H1 H2].
    + eapply np_zero; eauto using eval_reds.
    + eapply np_succ; eauto using eval_reds.
    + eapply np_stuck; eauto using stuckv_exp.
  - intros a b a' b' H Ha Hb;
      destruct H as [c c' H1 H2 | c c' d d' H1 H2 H3 | c c' H1 H2].
    + eapply np_zero; eauto using eval_reds_inv.
    + eapply np_succ; eauto using eval_reds_inv.
    + eapply np_stuck; eauto using stuckv_red.
  - intros; apply np_stuck; auto.
Qed.

Lemma NePer_ok : PerOK NePer.
Proof.
  constructor; unfold NePer.
  - intros a b [? ?]; auto.
  - intros a b c [? ?] [? ?]; auto.
  - intros a b a' b' Ha Hb [? ?]; split; eauto using stuckv_exp.
  - intros a b a' b' [? ?] Ha Hb; split; eauto using stuckv_red.
  - auto.
Qed.

Lemma TruePer_ok : PerOK TruePer.
Proof. constructor; unfold TruePer; auto. Qed.

Lemma PR_ok : PerOK PR.
Proof. constructor; eauto using PR_sym, PR_trans, PR_exp, PR_red, PR_stuck. Qed.

Lemma UnivPer_ok Y : XOK Y -> PerOK (fun C C' => exists P, Y C C' P).
Proof.
  intros [Hs Ht He Hr Hk]; constructor.
  - intros a b [P HP]; exists P; auto.
  - intros a b c [P HP] [Q HQ]; exists P; eauto.
  - intros a b a' b' Ha Hb [P HP]; exists P; eauto.
  - intros a b a' b' [P HP] Ha Hb; exists P; eauto.
  - auto.
Qed.

Definition Irr (PA : PER) (PB : etm -> etm -> PER) :=
  forall u u' v v', PA u u' -> PA v v' -> PA u v -> PB u u' ≐ PB v v'.

Lemma PiPer_ok PA PB : PerOK PA -> (forall u u', PA u u' -> PerOK (PB u u')) ->
  Irr PA PB -> PerOK (PiPer PA PB).
Proof.
  intros HA HB Hirr; constructor.
  - intros f g H u u' Hu.
    assert (Hu' : PA u' u) by (apply (pk_sym _ HA); assumption).
    apply (Hirr u' u u u' Hu' Hu Hu').
    apply (pk_sym _ (HB _ _ Hu')). apply H; assumption.
  - intros f g h H1 H2 u u' Hu.
    assert (Hu'' : PA u' u') by (eapply (pk_trans _ HA); [apply (pk_sym _ HA)|]; eassumption).
    eapply (pk_trans _ (HB _ _ Hu)); [apply H1; assumption|].
    apply (Hirr u' u' u u' Hu'' Hu (pk_sym _ HA _ _ Hu)).
    apply H2; assumption.
  - intros f g f' g' Hf Hg H u u' Hu.
    eapply (pk_exp _ (HB _ _ Hu)); [apply reds_app; exact Hf | apply reds_app; exact Hg |].
    apply H; assumption.
  - intros f g f' g' H Hf Hg u u' Hu.
    eapply (pk_red _ (HB _ _ Hu)); [apply H; exact Hu | apply reds_app; exact Hf | apply reds_app; exact Hg].
  - intros f g Hf Hg u u' Hu. apply (pk_stuck _ (HB _ _ Hu)); apply stuckv_app; assumption.
Qed.

Lemma SigPer_ok PA PB : PerOK PA -> (forall u u', PA u u' -> PerOK (PB u u')) ->
  Irr PA PB -> PerOK (SigPer PA PB).
Proof.
  intros HA HB Hirr; constructor.
  - intros p q [H1 H2].
    assert (H1' : PA (efst q) (efst p)) by (apply (pk_sym _ HA); assumption).
    split; [assumption|].
    apply (Hirr _ _ _ _ H1' H1 H1'). apply (pk_sym _ (HB _ _ H1)); assumption.
  - intros p q r [H1 H2] [H3 H4].
    assert (H13 : PA (efst p) (efst r)) by (eapply (pk_trans _ HA); eassumption).
    split; [assumption|].
    apply (Hirr _ _ _ _ H1 H13 (pk_trans _ HA _ _ _ H1 (pk_sym _ HA _ _ H1))).
    eapply (pk_trans _ (HB _ _ H1)); [exact H2|].
    apply (Hirr _ _ _ _ H3 H1 (pk_sym _ HA _ _ H1)); exact H4.
  - intros p p0 q q0 Hp Hq [H1 H2].
    assert (H1' : PA (efst p) (efst q)).
    { eapply (pk_exp _ HA); [apply reds_fst; exact Hp | apply reds_fst; exact Hq | exact H1]. }
    split; [assumption|].
    assert (H01 : PA (efst p0) (efst p)).
    { eapply (pk_trans _ HA); [exact H1|]. apply (pk_sym _ HA).
      eapply (pk_exp _ HA); [apply reds_fst; exact Hp | apply reds_refl | exact H1]. }
    apply (Hirr _ _ _ _ H1 H1' H01).
    eapply (pk_exp _ (HB _ _ H1)); [apply reds_snd; exact Hp | apply reds_snd; exact Hq | exact H2].
  - intros p q p' q' [H1 H2] Hp Hq.
    assert (H1' : PA (efst p') (efst q')).
    { eapply (pk_red _ HA); [exact H1 | apply reds_fst; exact Hp | apply reds_fst; exact Hq]. }
    split; [exact H1'|].
    assert (H01 : PA (efst p) (efst p')).
    { eapply (pk_trans _ HA); [eapply (pk_red _ HA); [exact H1 | apply reds_refl | apply reds_fst; exact Hq]
                              | apply (pk_sym _ HA); exact H1']. }
    apply (Hirr _ _ _ _ H1 H1' H01).
    eapply (pk_red _ (HB _ _ H1)); [exact H2 | apply reds_snd; exact Hp | apply reds_snd; exact Hq].
  - intros p q Hp Hq.
    assert (H1 : PA (efst p) (efst q)) by (apply (pk_stuck _ HA); apply stuckv_fst; assumption).
    split; [assumption|]. apply (pk_stuck _ (HB _ _ H1)); apply stuckv_snd; assumption.
Qed.

(* W.  The two interesting clauses are symmetry and transitivity, and both
   turn on index irrelevance: the branches of the two trees are compared at
   PB a a', and to swap or to compose the trees that relation has to be
   moved to PB a' a, resp. PB a2 a3, which is exactly what Irr provides. *)
Lemma WPer_ok PA PB : PerOK PA -> (forall u u', PA u u' -> PerOK (PB u u')) ->
  Irr PA PB -> PerOK (WPer PA PB).
Proof.
  intros HA HB Hirr; constructor.
  - (* symmetry *)
    intros w w' H; induction H as [w w' a a' f f' Hw Hw' Ha Hf IH | w w' Hw Hw'].
    + assert (Ha' : PA a' a) by (apply (pk_sym _ HA); exact Ha).
      eapply wp_sup; [exact Hw' | exact Hw | exact Ha' |].
      intros u u' Hu; apply (IH u' u).
      apply (pk_sym _ (HB _ _ Ha)).
      exact (proj1 (Hirr a' a a a' Ha' Ha Ha' u u') Hu).
    + apply wp_stuck; assumption.
  - (* transitivity *)
    intros w1 w2 w3 H1; revert w3.
    induction H1 as [w1 w2 a1 a2 f1 f2 Hw1 Hw2 Ha Hf IH | w1 w2 Hw1 Hw2];
      intros w3 H2.
    + inversion H2 as [x y b2 a3 g2 f3 Hx Hy Ha2 Hf2 | x y Hx Hy]; subst.
      * assert (E := eval_det _ _ _ Hw2 Hx); injection E as Ea Ef;
          subst b2 g2.
        assert (Ha13 : PA a1 a3) by (eapply (pk_trans _ HA); eassumption).
        assert (Ha11 : PA a1 a1)
          by (eapply (pk_trans _ HA); [exact Ha | apply (pk_sym _ HA); exact Ha]).
        eapply wp_sup; [exact Hw1 | exact Hy | exact Ha13 |].
        intros u u' Hu.
        assert (Hu1 : PB a1 a2 u u')
          by exact (proj1 (Hirr a1 a3 a1 a2 Ha13 Ha Ha11 u u') Hu).
        assert (Hu2 : PB a1 a2 u' u').
        { eapply (pk_trans _ (HB _ _ Ha));
            [apply (pk_sym _ (HB _ _ Ha)); exact Hu1 | exact Hu1]. }
        apply (IH u u' Hu1).
        apply Hf2.
        exact (proj1 (Hirr a1 a2 a2 a3 Ha Ha2 Ha u' u') Hu2).
      * exfalso; eapply stuckv_not_value; [exact Hx | exact Hw2 | constructor].
    + inversion H2 as [x y b2 a3 g2 f3 Hx Hy Ha2 Hf2 | x y Hx Hy]; subst.
      * exfalso; eapply stuckv_not_value; [exact Hw2 | exact Hx | constructor].
      * apply wp_stuck; assumption.
  - (* closure under expansion *)
    intros w w' w0 w0' Hr Hr' H;
      destruct H as [x y a a' f f' Hx Hy Ha Hf | x y Hx Hy].
    + eapply wp_sup; eauto using eval_reds.
    + apply wp_stuck; eauto using stuckv_exp.
  - (* closure under reduction *)
    intros w w' w0 w0' H Hr Hr';
      destruct H as [x y a a' f f' Hx Hy Ha Hf | x y Hx Hy].
    + eapply wp_sup; eauto using eval_reds_inv.
    + apply wp_stuck; eauto using stuckv_red.
  - intros; apply wp_stuck; assumption.
Qed.

Section Sym.
Context (n : nat) (X : nat -> etm -> etm -> PER -> Prop).
Context (HX : forall m, m < n -> XOK (X m)).

Lemma LR_ok_sym A A' P : LR n X A A' P -> PerOK P /\ LR n X A' A P.
Proof.
  induction 1 as
    [ A A' P Q HLR [IHok IHsym] HPQ
    | A B A' B' P HrA HrA' HLR [IHok IHsym]
    | A A' HeA HeA'
    | A A' HeA HeA'
    | A A' p p' HeA HeA' HPR
    | A A' m Hm HeA HeA'
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA [IHAok IHAsym] HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA [IHAok IHAsym] HB IHB
    | A A' A0 B0 A0' B0' PA PB HeA HeA' HA [IHAok IHAsym] HB IHB
    | A A' N N' HeA HeA' HsN HsN' ].
  - split; [eapply PerOK_ext; eassumption | eapply LR_ext; eassumption].
  - split; [assumption | eapply LR_exp; eassumption].
  - split; [apply NatPer_ok | apply LR_nat; assumption].
  - split; [apply PR_ok | apply LR_prop; assumption].
  - split; [apply TruePer_ok | eapply LR_prf; eauto using PR_sym].
  - split; [apply UnivPer_ok, HX, Hm | apply LR_univ; assumption].
  - assert (Hirr : Irr PA PB).
    { intros u u' v v' Hu Hv Huv.
      assert (Huv' : PA u v') by (eapply (pk_trans _ IHAok); eassumption).
      eapply PerEq_trans.
      - eapply LR_fun; [apply (HB _ _ Hu) | apply (HB _ _ Huv')].
      - eapply LR_fun; [apply (proj2 (IHB _ _ Huv')) | apply (proj2 (IHB _ _ Hv))]. }
    split.
    + apply PiPer_ok; auto. intros u u' Hu; apply (proj1 (IHB _ _ Hu)).
    + eapply LR_ext.
      * eapply LR_pi; [exact HeA' | exact HeA | exact IHAsym |].
        intros u u' Hu. apply (proj2 (IHB u' u (pk_sym _ IHAok _ _ Hu))).
      * apply PiPer_ext; [apply PerEq_refl|].
        intros u u' Hu. exact (Hirr u' u u u' (pk_sym _ IHAok _ _ Hu) Hu (pk_sym _ IHAok _ _ Hu)).
  - assert (Hirr : Irr PA PB).
    { intros u u' v v' Hu Hv Huv.
      assert (Huv' : PA u v') by (eapply (pk_trans _ IHAok); eassumption).
      eapply PerEq_trans.
      - eapply LR_fun; [apply (HB _ _ Hu) | apply (HB _ _ Huv')].
      - eapply LR_fun; [apply (proj2 (IHB _ _ Huv')) | apply (proj2 (IHB _ _ Hv))]. }
    split.
    + apply SigPer_ok; auto. intros u u' Hu; apply (proj1 (IHB _ _ Hu)).
    + eapply LR_ext.
      * eapply LR_sig; [exact HeA' | exact HeA | exact IHAsym |].
        intros u u' Hu. apply (proj2 (IHB u' u (pk_sym _ IHAok _ _ Hu))).
      * apply SigPer_ext; [apply PerEq_refl|].
        intros u u' Hu. exact (Hirr u' u u u' (pk_sym _ IHAok _ _ Hu) Hu (pk_sym _ IHAok _ _ Hu)).
  - assert (Hirr : Irr PA PB).
    { intros u u' v v' Hu Hv Huv.
      assert (Huv' : PA u v') by (eapply (pk_trans _ IHAok); eassumption).
      eapply PerEq_trans.
      - eapply LR_fun; [apply (HB _ _ Hu) | apply (HB _ _ Huv')].
      - eapply LR_fun; [apply (proj2 (IHB _ _ Huv')) | apply (proj2 (IHB _ _ Hv))]. }
    split.
    + apply WPer_ok; auto. intros u u' Hu; apply (proj1 (IHB _ _ Hu)).
    + eapply LR_ext.
      * eapply LR_w; [exact HeA' | exact HeA | exact IHAsym |].
        intros u u' Hu. apply (proj2 (IHB u' u (pk_sym _ IHAok _ _ Hu))).
      * apply WPer_ext; [apply PerEq_refl|].
        intros u u' Hu. exact (Hirr u' u u u' (pk_sym _ IHAok _ _ Hu) Hu (pk_sym _ IHAok _ _ Hu)).
  - split; [apply NePer_ok | eapply LR_ne; eauto].
Qed.

Lemma LR_ok A A' P : LR n X A A' P -> PerOK P.
Proof. intros H; apply (LR_ok_sym _ _ _ H). Qed.

Lemma LR_sym A A' P : LR n X A A' P -> LR n X A' A P.
Proof. intros H; apply (LR_ok_sym _ _ _ H). Qed.

End Sym.
