From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def.

(* Contraction and shape inversion for LR (blueprint B6).  Both are single
   inductions consuming determinism only; nothing here needs symmetry,
   transitivity or functionality. *)

Ltac eval_confl :=
  repeat match goal with
  | H1 : eval ?A ?w, H2 : eval ?A ?w' |- _ =>
      tryif constr_eq w w' then fail else
      (let E := fresh "E" in
       assert (E := eval_det _ _ _ H1 H2); clear H2;
       try discriminate E; try (injection E; intros; subst); try subst)
  end;
  try match goal with H : stuck _ |- _ => solve [inversion H] end.

Lemma PiPer_ext PA PA' PB PB' :
  PA ≐ PA' -> (forall u u', PA u u' -> PB u u' ≐ PB' u u') ->
  PiPer PA PB ≐ PiPer PA' PB'.
Proof.
  intros HA HB f g; split; intros H u u' Hu.
  - apply HB; [apply HA | apply H; apply HA]; assumption.
  - apply HB; [assumption | apply H; apply HA; assumption].
Qed.

Lemma SigPer_ext PA PA' PB PB' :
  PA ≐ PA' -> (forall u u', PA u u' -> PB u u' ≐ PB' u u') ->
  SigPer PA PB ≐ SigPer PA' PB'.
Proof.
  intros HA HB p q; split; intros [H1 H2]; split.
  - apply HA; assumption.
  - apply HB; assumption.
  - apply HA; assumption.
  - apply HB; [apply HA|]; assumption.
Qed.

Lemma WPer_ext PA PA' PB PB' :
  PA ≐ PA' -> (forall u u', PA u u' -> PB u u' ≐ PB' u u') ->
  WPer PA PB ≐ WPer PA' PB'.
Proof.
  intros HA HB w w'; split; intros H.
  - induction H as [w w' a a' f f' Hw Hw' Ha Hf IH | w w' Hw Hw'].
    + eapply wp_sup; [exact Hw | exact Hw' | apply HA; exact Ha |].
      intros u u' Hu; apply IH, HB; [exact Ha | exact Hu].
    + apply wp_stuck; assumption.
  - induction H as [w w' a a' f f' Hw Hw' Ha Hf IH | w w' Hw Hw'].
    + assert (Ha' : PA a a') by (apply HA; exact Ha).
      eapply wp_sup; [exact Hw | exact Hw' | exact Ha' |].
      intros u u' Hu; apply IH, HB; [exact Ha' | exact Hu].
    + apply wp_stuck; assumption.
Qed.

Section Inv.
Context (n : nat) (X : nat -> etm -> etm -> PER -> Prop).

Lemma LR_red A A' P : LR n X A A' P ->
  forall B B', reds A B -> reds A' B' -> LR n X B B' P.
Proof.
  induction 1; intros B1 B1' HB HB';
    try solve [ first
    [ solve [eapply LR_nat; eauto using eval_reds_inv]
    | solve [eapply LR_prop; eauto using eval_reds_inv]
    | solve [eapply LR_prf; eauto using eval_reds_inv]
    | solve [eapply LR_univ; eauto using eval_reds_inv]
    | solve [eapply LR_pi; eauto using eval_reds_inv]
    | solve [eapply LR_sig; eauto using eval_reds_inv]
    | solve [eapply LR_w; eauto using eval_reds_inv]
    | solve [eapply LR_ne; eauto using eval_reds_inv] ] ].
  - eapply LR_ext; [apply IHLR; assumption | assumption].
  - destruct (reds_diamond _ _ _ H HB) as [D1 | D1];
      destruct (reds_diamond _ _ _ H0 HB') as [D2 | D2].
    + apply IHLR; assumption.
    + apply (LR_exp n X B1 B1 B1' B');
        [apply reds_refl | exact D2 | apply IHLR; [exact D1 | apply reds_refl]].
    + apply (LR_exp n X B1 B B1' B1');
        [exact D1 | apply reds_refl | apply IHLR; [apply reds_refl | exact D2]].
    + apply (LR_exp n X B1 B B1' B'); [exact D1 | exact D2 | exact H1].
Qed.

Ltac lr_induction He :=
  induction 1 as
    [ A A' P Q HLR IH HPQ
    | A B A' B' P HrA HrA' HLR IH
    | A A' HeA HeA'
    | A A' HeA HeA'
    | A A' q q' HeA HeA' HPR
    | A A' m0 Hm HeA HeA'
    | A A' C0 D0 C0' D0' PA PB HeA HeA' HA IHA HB IHB
    | A A' C0 D0 C0' D0' PA PB HeA HeA' HA IHA HB IHB
    | A A' C0 D0 C0' D0' PA PB HeA HeA' HA IHA HB IHB
    | A A' M M' HeA HeA' HsM HsM' ];
  intros He.

Lemma LR_inv_nat A A' P : LR n X A A' P -> eval A enat ->
  eval A' enat /\ P ≐ NatPer.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [H1 H2]; split; [exact H1|].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H2].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [H1 H2]; split; [|exact H2].
    eapply eval_reds; eauto.
  - split; [assumption | apply PerEq_refl].
Qed.

Lemma LR_inv_prop A A' P : LR n X A A' P -> eval A eprop ->
  eval A' eprop /\ P ≐ PR.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [H1 H2]; split; [exact H1|].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H2].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [H1 H2]; split; [|exact H2].
    eapply eval_reds; eauto.
  - split; [assumption | apply PerEq_refl].
Qed.

Lemma LR_inv_prf A A' P p : LR n X A A' P -> eval A (eprf p) ->
  exists p', eval A' (eprf p') /\ PR p p' /\ P ≐ TruePer.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [p' [H1 [H2 H3]]]; exists p'; split; [exact H1 | split; [exact H2 |]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H3].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [p'' [H1 [H2 H3]]]; exists p''.
    split; [eapply eval_reds; eauto | split; [exact H2 | exact H3]].
  - eval_confl. exists q'; split; [assumption | split; [assumption | apply PerEq_refl]].
Qed.

Lemma LR_inv_univ A A' P m : LR n X A A' P -> eval A (euniv m) ->
  m < n /\ eval A' (euniv m) /\ P ≐ (fun C C' => exists Q, X m C C' Q).
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [H1 [H2 H3]]; split; [exact H1 | split; [exact H2 |]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H3].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [H1 [H2 H3]].
    split; [exact H1 | split; [eapply eval_reds; eauto | exact H3]].
  - eval_confl. split; [assumption | split; [assumption | apply PerEq_refl]].
Qed.

Lemma LR_inv_pi A A' P A0 B0 : LR n X A A' P -> eval A (epi A0 B0) ->
  exists A0' B0' PA PB, eval A' (epi A0' B0') /\ LR n X A0 A0' PA /\
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) /\
    P ≐ PiPer PA PB.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H4].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [eapply eval_reds; eauto | split; [exact H2 | split; [exact H3 | exact H4]]].
  - eval_confl. exists C0', D0', PA, PB; split; [assumption | split; [assumption | split; [assumption | apply PerEq_refl]]].
Qed.

Lemma LR_inv_sig A A' P A0 B0 : LR n X A A' P -> eval A (esig A0 B0) ->
  exists A0' B0' PA PB, eval A' (esig A0' B0') /\ LR n X A0 A0' PA /\
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) /\
    P ≐ SigPer PA PB.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H4].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [eapply eval_reds; eauto | split; [exact H2 | split; [exact H3 | exact H4]]].
  - eval_confl. exists C0', D0', PA, PB; split; [assumption | split; [assumption | split; [assumption | apply PerEq_refl]]].
Qed.

Lemma LR_inv_w A A' P A0 B0 : LR n X A A' P -> eval A (ew A0 B0) ->
  exists A0' B0' PA PB, eval A' (ew A0' B0') /\ LR n X A0 A0' PA /\
    (forall u u', PA u u' -> LR n X (eapp B0 u) (eapp B0' u') (PB u u')) /\
    P ≐ WPer PA PB.
Proof.
  lr_induction He; try solve [eval_confl].
  - destruct (IH He) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H4].
  - destruct (IH (eval_reds_inv _ _ _ HrA He)) as [A0' [B0' [PA [PB [H1 [H2 [H3 H4]]]]]]].
    exists A0', B0', PA, PB; split; [eapply eval_reds; eauto | split; [exact H2 | split; [exact H3 | exact H4]]].
  - eval_confl. exists C0', D0', PA, PB; split; [assumption | split; [assumption | split; [assumption | apply PerEq_refl]]].
Qed.

Lemma LR_inv_ne A A' P N : LR n X A A' P -> eval A N -> stuck N ->
  exists N', eval A' N' /\ stuck N' /\ P ≐ NePer.
Proof.
  lr_induction He; intros Hs; try solve [eval_confl].
  - destruct (IH He Hs) as [N' [H1 [H2 H3]]]; exists N'; split; [exact H1 | split; [exact H2 |]].
    eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact H3].
  - destruct (IH (eval_reds_inv _ _ _ HrA He) Hs) as [N'' [H1 [H2 H3]]]; exists N''.
    split; [eapply eval_reds; eauto | split; [exact H2 | exact H3]].
  - exists M'; split; [assumption | split; [assumption | apply PerEq_refl]].
Qed.

End Inv.
