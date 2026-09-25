From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def.

(* The unary equality of a code is a PER (half of blueprint Lemma 8.5; the
   other half, about the heterogeneous equality, is in Codes/Iso.v).

   No well-formedness hypothesis is needed.  Symmetry is componentwise and
   uses that the Pi clause states its condition in both directions;
   transitivity is where the composition law carried by a Pi-code is spent,
   and the goodness side condition of that law is discharged by StGood,
   since the decoding of a code holds only self-related elements. *)

Definition EqSym (st : Stage) (s : st.(St)) :=
  forall u x u' x', st.(StEq) s u x u' x' -> st.(StEq) s u' x' u x.
Definition EqTrans (st : Stage) (s : st.(St)) :=
  forall u x u' x' u'' x'',
    st.(StEq) s u x u' x' -> st.(StEq) s u' x' u'' x'' -> st.(StEq) s u x u'' x''.

Section EqRefine.
  Context (st : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).

  Local Notation eqS := st.(StEq).
  Local Notation eqEl_ := (eqEl st Univ UnivEq UnivOK).

  Lemma eqRefine_sym
    (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
    {T} (r : Refine st UnivOK T) :
    forall u x u' x', eqEl_ r u x u' x' -> eqEl_ r u' x' u x.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh compL idL|T A0 B0 e a ea b eb coh compL idL|T N e s0]; cbn;
      intros u x u' x' H.
    - destruct H; split; auto using Rel_sym.
    - destruct H as [H1 H2]; split; [tauto | auto using Rel_sym].
    - auto using Rel_sym.
    - auto.
    - destruct H as [H HR].
      split; [| apply Rel_sym; exact HR].
      intros u1 x1 u1' x1' r r'. destruct (H _ _ _ _ r' r) as [H1 H2]; split; [exact H2 | exact H1].
    - (* Sigma: the two directions of the clause exchange places, which is
         why each is stated with its own existential. *)
      destruct H as [H1 [H2 HR]].
      split; [exact H2 | split; [exact H1 | apply Rel_sym; exact HR]].
    - exact I.
  Qed.

  Lemma eqRefine_trans
    (UnivEq_trans : forall m u x u' x' u'' x'',
        UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'')
    (Hgood : StGood st)
    (IH : forall s, EqSym st s /\ EqTrans st s)
    {T} (r : Refine st UnivOK T) :
    forall u x u' x' u'' x'',
      eqEl_ r u x u' x' -> eqEl_ r u' x' u'' x'' -> eqEl_ r u x u'' x''.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh compL idL|T A0 B0 e a ea b eb coh compL idL|T N e s0]; cbn;
      intros u x u' x' u'' x'' H1 H2.
    - destruct H1, H2; split; [congruence | eauto using Rel_trans].
    - destruct H1, H2; split; [tauto | eauto using Rel_trans].
    - eauto using Rel_trans.
    - eauto.
    - destruct H1 as [H HR]; destruct H2 as [H' HR'].
      destruct (IH a) as [Sa Ta].
      split; [| eapply Rel_trans; eassumption].
      intros u1 x1 u1' x1' r r'.
      destruct (IH (b u1 x1)) as [Sb Tb].
      destruct (IH (b u1' x1')) as [Sb' Tb'].
      pose (r11 := Ta _ _ _ _ _ _ r r').
      split.
      + destruct (H _ _ _ _ r11 r11) as [A1 _].
        destruct (H' _ _ _ _ r r') as [A2 _].
        eapply Tb; [exact A1|].
        eapply Tb; [apply (tr_eq _ _ _ (coh _ _ _ _ r11)); exact A2|].
        apply compL; apply Hgood.
      + destruct (H' _ _ _ _ r r') as [_ B1].
        destruct (H _ _ _ _ r11 r11) as [_ B2].
        eapply Tb'; [exact B1|].
        eapply Tb'; [apply (tr_eq _ _ _ (coh _ _ _ _ r')); exact B2|].
        apply compL; apply Hgood.
    - (* Sigma: componentwise, and in each direction the composition law of
         the codomain's coherence closes the gap between the composite of the
         two transports and the transport of the composite. *)
      destruct H1 as [[r01 A1] [[r10 B2] HR1]].
      destruct H2 as [[r12 A2] [[r21 B1] HR2]].
      destruct (IH a) as [Sa Ta].
      destruct (IH (b (efst u) (projT1 (Datatypes.fst x)))) as [Sb Tb].
      destruct (IH (b (efst u'') (projT1 (Datatypes.fst x'')))) as [Sb2 Tb2].
      split; [| split].
      + exists (Ta _ _ _ _ _ _ r01 r12).
        eapply Tb; [exact A1 |].
        eapply Tb; [apply (tr_eq _ _ _ (coh _ _ _ _ r01)); exact A2 |].
        apply compL; apply Hgood.
      + exists (Ta _ _ _ _ _ _ r21 r10).
        eapply Tb2; [exact B1 |].
        eapply Tb2; [apply (tr_eq _ _ _ (coh _ _ _ _ r21)); exact B2 |].
        apply compL; apply Hgood.
      + eapply Rel_trans; eassumption.
    - exact I.
  Qed.
End EqRefine.

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).

  Lemma eqs_PER alpha : forall s, EqSym (stage_ alpha) s /\ EqTrans (stage_ alpha) s.
  Proof.
    induction alpha as [| beta IHb | T f IHf]; cbn.
    - intros [].
    - intros [c | s].
      + split.
        * intros u x u' x'; apply (eqRefine_sym _ Univ UnivEq UnivOK UnivEq_sym).
        * intros u x u' x' u'' x''.
          apply (eqRefine_trans _ Univ UnivEq UnivOK UnivEq_trans (stage_good _ _ _ beta) IHb).
      + apply IHb.
    - intros [p [c | s]].
      + split.
        * intros u x u' x'; apply (eqRefine_sym _ Univ UnivEq UnivOK UnivEq_sym).
        * intros u x u' x' u'' x''.
          apply (eqRefine_trans _ Univ UnivEq UnivOK UnivEq_trans (stage_good _ _ _ (f p)) (IHf p)).
      + apply (IHf p).
  Qed.

  Lemma eqU_sym beta (c : U Univ UnivEq UnivOK beta) : EqSym (Ust Univ UnivEq UnivOK beta) c.
  Proof. apply (proj1 (eqs_PER (osucc beta) (inl c))). Qed.

  Lemma eqU_trans beta (c : U Univ UnivEq UnivOK beta) : EqTrans (Ust Univ UnivEq UnivOK beta) c.
  Proof. apply (proj2 (eqs_PER (osucc beta) (inl c))). Qed.

  Lemma eqs_sym alpha (s : Sub Univ UnivEq UnivOK alpha) : EqSym (stage_ alpha) s.
  Proof. apply eqs_PER. Qed.

  Lemma eqs_trans alpha (s : Sub Univ UnivEq UnivOK alpha) : EqTrans (stage_ alpha) s.
  Proof. apply eqs_PER. Qed.
End Level.
