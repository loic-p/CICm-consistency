From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle.Inv.

(* Functionality (blueprint B4): the PER is determined by the left type.
   Induction on one derivation with shape inversion of the other; needs
   neither symmetry nor transitivity. *)

Section Fun.
Context (n : nat) (X : nat -> etm -> etm -> PER -> Prop).

Lemma LR_fun A A' P : LR n X A A' P -> forall A'' Q, LR n X A A'' Q -> P ≐ Q.
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
    | A A' N N' HeA HeA' HsN HsN' ];
    intros A'' Q' HQ.
  - eapply PerEq_trans; [apply PerEq_sym; exact HPQ | exact (IH _ _ HQ)].
  - apply (IH A'' Q'). eapply LR_red; [exact HQ | exact HrA | apply reds_refl].
  - destruct (LR_inv_nat n X _ _ _ HQ HeA) as [_ E]; apply PerEq_sym; exact E.
  - destruct (LR_inv_prop n X _ _ _ HQ HeA) as [_ E]; apply PerEq_sym; exact E.
  - destruct (LR_inv_prf n X _ _ _ _ HQ HeA) as [? [_ [_ E]]]; apply PerEq_sym; exact E.
  - destruct (LR_inv_univ n X _ _ _ _ HQ HeA) as [_ [_ E]]; apply PerEq_sym; exact E.
  - destruct (LR_inv_pi n X _ _ _ _ _ HQ HeA) as [A0'' [B0'' [PA'' [PB'' [_ [HA'' [HB'' E]]]]]]].
    eapply PerEq_trans; [|apply PerEq_sym; exact E].
    apply PiPer_ext; [exact (IHA _ _ HA'')|].
    intros u u' Hu. eapply (IHB u u' Hu). apply HB''. apply (IHA _ _ HA''); exact Hu.
  - destruct (LR_inv_sig n X _ _ _ _ _ HQ HeA) as [A0'' [B0'' [PA'' [PB'' [_ [HA'' [HB'' E]]]]]]].
    eapply PerEq_trans; [|apply PerEq_sym; exact E].
    apply SigPer_ext; [exact (IHA _ _ HA'')|].
    intros u u' Hu. eapply (IHB u u' Hu). apply HB''. apply (IHA _ _ HA''); exact Hu.
  - destruct (LR_inv_ne n X _ _ _ _ HQ HeA HsN) as [? [_ [_ E]]]; apply PerEq_sym; exact E.
Qed.

End Fun.
