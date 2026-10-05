From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle.Inv Layer1.Bundle.Fun Layer1.Bundle.Sym.

(* Transitivity (B3): induction on the first derivation, inversion of the
   second at the common middle whnf; uses symmetry and functionality to
   identify the two domain PERs at Pi and Sigma. *)

Section Trans.
Context (n : nat) (X : nat -> etm -> etm -> PER -> Prop).
Context (HX : forall m, m < n -> XOK (X m)).

Lemma LR_trans A A' P : LR n X A A' P ->
  forall A'' Q, LR n X A' A'' Q -> LR n X A A'' P.
Proof.
  induction 1 as
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
    intros A'' Q' HQ.
  - eapply LR_ext; [exact (IH _ _ HQ) | exact HPQ].
  - eapply LR_exp; [exact HrA | apply reds_refl |].
    apply (IH A'' Q'). eapply LR_red; [exact HQ | exact HrA' | apply reds_refl].
  - destruct (LR_inv_nat n X _ _ _ HQ HeA') as [H _]; apply LR_nat; assumption.
  - destruct (LR_inv_prop n X _ _ _ HQ HeA') as [H _]; apply LR_prop; assumption.
  - destruct (LR_inv_prf n X _ _ _ _ HQ HeA') as [p'' [H1 [H2 _]]].
    eapply LR_prf; [exact HeA | exact H1 | eapply PR_trans; eassumption].
  - destruct (LR_inv_univ n X _ _ _ _ HQ HeA') as [_ [H _]]; apply LR_univ; assumption.
  - destruct (LR_inv_pi n X _ _ _ _ _ HQ HeA') as [A0'' [B0'' [PA' [PB' [H1 [H2 [H3 _]]]]]]].
    assert (EA : PA ≐ PA').
    { eapply LR_fun; [apply (LR_sym n X HX); exact HA | exact H2]. }
    eapply LR_pi; [exact HeA | exact H1 | exact (IHA _ _ H2) |].
    intros u u' Hu. eapply (IHB u u' Hu). apply H3. apply EA.
    eapply (pk_trans _ (LR_ok n X HX _ _ _ HA)); [apply (pk_sym _ (LR_ok n X HX _ _ _ HA))|]; exact Hu.
  - destruct (LR_inv_sig n X _ _ _ _ _ HQ HeA') as [A0'' [B0'' [PA' [PB' [H1 [H2 [H3 _]]]]]]].
    assert (EA : PA ≐ PA').
    { eapply LR_fun; [apply (LR_sym n X HX); exact HA | exact H2]. }
    eapply LR_sig; [exact HeA | exact H1 | exact (IHA _ _ H2) |].
    intros u u' Hu. eapply (IHB u u' Hu). apply H3. apply EA.
    eapply (pk_trans _ (LR_ok n X HX _ _ _ HA)); [apply (pk_sym _ (LR_ok n X HX _ _ _ HA))|]; exact Hu.
  - destruct (LR_inv_w n X _ _ _ _ _ HQ HeA') as [A0'' [B0'' [PA' [PB' [H1 [H2 [H3 _]]]]]]].
    assert (EA : PA ≐ PA').
    { eapply LR_fun; [apply (LR_sym n X HX); exact HA | exact H2]. }
    eapply LR_w; [exact HeA | exact H1 | exact (IHA _ _ H2) |].
    intros u u' Hu. eapply (IHB u u' Hu). apply H3. apply EA.
    eapply (pk_trans _ (LR_ok n X HX _ _ _ HA)); [apply (pk_sym _ (LR_ok n X HX _ _ _ HA))|]; exact Hu.
  - destruct (LR_inv_ne n X _ _ _ _ HQ HeA' HsN') as [N'' [H1 [H2 _]]].
    eapply LR_ne; eauto.
Qed.

End Trans.
