From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.EqPER.

(* Lemma 8.7: the decoding of a code is closed under expansion and reduction
   of the realiser, and the two maps are equalities of the code -- which is
   available, because the equality of a code is heterogeneous in the
   realiser.  That last clause is what makes the maps natural: any two
   transports commute with them up to the equality, by tr_eq, so no
   naturality condition has to be built into Transp. *)

Record SExp (st : Stage) := {
  se_red : forall s u u1, reds u u1 -> st.(StEl) s u -> st.(StEl) s u1;
  se_exp : forall s u u1, reds u u1 -> st.(StEl) s u1 -> st.(StEl) s u;
  se_red_rel : forall s u u1 (H : reds u u1) x, st.(StEq) s u x u1 (se_red s u u1 H x);
  se_exp_rel : forall s u u1 (H : reds u u1) y, st.(StEq) s u (se_exp s u u1 H y) u1 y
}.
Arguments se_red {st}. Arguments se_exp {st}.
Arguments se_red_rel {st}. Arguments se_exp_rel {st}.

(* The same, of the parameter that decodes the universes. *)
Record UnivExp (Univ : nat -> etm -> Type)
               (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop) := {
  ue_red : forall m u u1, reds u u1 -> Univ m u -> Univ m u1;
  ue_exp : forall m u u1, reds u u1 -> Univ m u1 -> Univ m u;
  ue_red_rel : forall m u u1 (H : reds u u1) x, UnivEq m u x u1 (ue_red m u u1 H x);
  ue_exp_rel : forall m u u1 (H : reds u u1) y, UnivEq m u (ue_exp m u u1 H y) u1 y
}.
Arguments ue_red {Univ UnivEq}. Arguments ue_exp {Univ UnivEq}.
Arguments ue_red_rel {Univ UnivEq}. Arguments ue_exp_rel {Univ UnivEq}.

Lemma Good_red T u u1 : reds u u1 -> Good T u -> Good T u1.
Proof. intros H G; eapply Rel_red; [exact H | exact H | exact G]. Qed.

Lemma Good_exp T u u1 : reds u u1 -> Good T u1 -> Good T u.
Proof. intros H G; eapply Rel_exp; [exact H | exact H | exact G]. Qed.

Lemma Rel_red_r T u u1 : reds u u1 -> Good T u -> Rel T u u1.
Proof. intros H G; eapply Rel_red; [apply reds_refl | exact H | exact G]. Qed.

Lemma Rel_exp_l T u u1 : reds u u1 -> Good T u1 -> Rel T u u1.
Proof. intros H G; eapply Rel_exp; [exact H | apply reds_refl | exact G]. Qed.

Section ExpRefine.
  Context (st : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (SE : SExp st) (UE : UnivExp Univ UnivEq).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'')
          (Hgood : StGood st)
          (IH : forall s, EqSym st s /\ EqTrans st s).

  Local Notation El_ := (El st Univ UnivOK).
  Local Notation eqEl_ := (eqEl st Univ UnivEq UnivOK).
  Local Notation eqS := st.(StEq).

  (* The two moves a Sigma-code's decoding needs when the realiser reduces.
     The first component's realiser reduces with the pair; but its VALUE
     moves too, so the second component's code moves with it, and the
     coherence of the codomain family is what carries the second component
     across.  (At Pi nothing of the kind happens: the argument is given from
     outside and does not reduce.) *)
  Definition sigRedFst (a : st.(St)) u u1 (H : reds u u1) (z : st.(StEl) a (efst u))
    : st.(StEl) a (efst u1) := se_red SE a (efst u) (efst u1) (reds_fst u u1 H) z.

  Definition sigRedRel (a : st.(St)) u u1 (H : reds u u1) (z : st.(StEl) a (efst u))
    : eqS a (efst u) z (efst u1) (sigRedFst a u u1 H z) :=
    se_red_rel SE a (efst u) (efst u1) (reds_fst u u1 H) z.

  Definition sigRedRel' (a : st.(St)) u u1 (H : reds u u1) (z : st.(StEl) a (efst u))
    : eqS a (efst u1) (sigRedFst a u u1 H z) (efst u) z :=
    proj1 (IH a) _ _ _ _ (sigRedRel a u u1 H z).

  Definition sigExpFst (a : st.(St)) u u1 (H : reds u u1) (z : st.(StEl) a (efst u1))
    : st.(StEl) a (efst u) := se_exp SE a (efst u) (efst u1) (reds_fst u u1 H) z.

  Definition sigExpRel (a : st.(St)) u u1 (H : reds u u1) (z : st.(StEl) a (efst u1))
    : eqS a (efst u) (sigExpFst a u u1 H z) (efst u1) z :=
    se_exp_rel SE a (efst u) (efst u1) (reds_fst u u1 H) z.

  Definition elRed {T} (r : Refine st UnivOK T)
    : forall u u1, reds u u1 -> El_ r u -> El_ r u1 :=
    match r as r0 return forall u u1, reds u u1 -> El_ r0 u -> El_ r0 u1 with
    | r_nat _ _ T _ => fun u u1 H x =>
        (existT _ (projT1 (Datatypes.fst x))
                (NatAt_red _ _ _ H (projT2 (Datatypes.fst x))),
         Good_red T u u1 H (Datatypes.snd x))
    | r_prop _ _ T _ => fun u u1 H x => (Datatypes.fst x, Good_red T u u1 H (Datatypes.snd x))
    | r_prf _ _ T _ _ _ => fun u u1 H x => (Datatypes.fst x, Good_red T u u1 H (Datatypes.snd x))
    | r_univ _ _ _ m _ _ => fun u u1 H x => ue_red UE m u u1 H x
    | r_pi _ _ T _ _ _ a _ b _ _ _ _ => fun u u1 H x =>
        (fun u' y => se_red SE (b u' y) (eapp u u') (eapp u1 u')
                            (reds_app _ _ u' H) (Datatypes.fst x u' y),
         Good_red T u u1 H (Datatypes.snd x))
    | r_sig _ _ T _ _ _ a _ b _ coh _ _ => fun u u1 H x =>
        (existT _ (sigRedFst a u u1 H (projT1 (Datatypes.fst x)))
           (tr (coh _ _ _ _ (sigRedRel' a u u1 H (projT1 (Datatypes.fst x)))) (esnd u1)
              (se_red SE (b (efst u) (projT1 (Datatypes.fst x))) (esnd u) (esnd u1)
                 (reds_snd u u1 H) (projT2 (Datatypes.fst x)))),
         Good_red T u u1 H (Datatypes.snd x))
    | r_ne _ _ _ _ _ _ => fun u u1 H x => match x with end
    end.

  Definition elExp {T} (r : Refine st UnivOK T)
    : forall u u1, reds u u1 -> El_ r u1 -> El_ r u :=
    match r as r0 return forall u u1, reds u u1 -> El_ r0 u1 -> El_ r0 u with
    | r_nat _ _ T _ => fun u u1 H y =>
        (existT _ (projT1 (Datatypes.fst y))
                (NatAt_exp _ _ _ H (projT2 (Datatypes.fst y))),
         Good_exp T u u1 H (Datatypes.snd y))
    | r_prop _ _ T _ => fun u u1 H y => (Datatypes.fst y, Good_exp T u u1 H (Datatypes.snd y))
    | r_prf _ _ T _ _ _ => fun u u1 H y => (Datatypes.fst y, Good_exp T u u1 H (Datatypes.snd y))
    | r_univ _ _ _ m _ _ => fun u u1 H y => ue_exp UE m u u1 H y
    | r_pi _ _ T _ _ _ a _ b _ _ _ _ => fun u u1 H y =>
        (fun u' z => se_exp SE (b u' z) (eapp u u') (eapp u1 u')
                            (reds_app _ _ u' H) (Datatypes.fst y u' z),
         Good_exp T u u1 H (Datatypes.snd y))
    | r_sig _ _ T _ _ _ a _ b _ coh _ _ => fun u u1 H y =>
        (existT _ (sigExpFst a u u1 H (projT1 (Datatypes.fst y)))
           (se_exp SE (b (efst u) (sigExpFst a u u1 H (projT1 (Datatypes.fst y))))
              (esnd u) (esnd u1) (reds_snd u u1 H)
              (tr (coh _ _ _ _ (sigExpRel a u u1 H (projT1 (Datatypes.fst y)))) (esnd u1)
                 (projT2 (Datatypes.fst y)))),
         Good_exp T u u1 H (Datatypes.snd y))
    | r_ne _ _ _ _ _ _ => fun u u1 H y => match y with end
    end.

  Lemma elRed_rel {T} (r : Refine st UnivOK T) :
    forall u u1 (H : reds u u1) x, eqEl_ r u x u x -> eqEl_ r u x u1 (elRed r u u1 H x).
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh compL idL|T A0 B0 e a ea b eb coh compL idL|T N e s0]; cbn;
      intros u u1 H x G.
    - split; [reflexivity | apply Rel_red_r; [exact H | exact (Datatypes.snd x)]].
    - split; [tauto | apply Rel_red_r; [exact H | exact (Datatypes.snd x)]].
    - apply Rel_red_r; [exact H | exact (Datatypes.snd x)].
    - apply ue_red_rel.
    - destruct G as [G _].
      split; [| apply Rel_red_r; [exact H | exact (Datatypes.snd x)]].
      intros u2 x2 u2' x2' r2 r2'.
      destruct (IH (b u2 x2)) as [S2 T2]; destruct (IH (b u2' x2')) as [S2' T2'].
      destruct (G _ _ _ _ r2 r2') as [G1 G2]; split.
      + eapply T2; [exact G1 |].
        apply (tr_eq _ _ _ (coh _ _ _ _ r2)).
        apply se_red_rel.
      + eapply T2'; [| exact G2].
        apply S2'; apply se_red_rel.
    - (* Sigma: the first component's own reduction relation is the witness;
         the round trip through the coherence is undone by the composition
         and identity laws the code carries. *)
      destruct (IH a) as [Sa Ta].
      destruct (IH (b (efst u) (projT1 (Datatypes.fst x)))) as [Sb Tb].
      split; [| split].
      + exists (sigRedRel a u u1 H (projT1 (Datatypes.fst x))).
        eapply Tb; [apply se_red_rel |].
        apply Sb.
        eapply Tb;
          [ apply (compL _ _ _ _ _ _
                     (sigRedRel a u u1 H (projT1 (Datatypes.fst x)))
                     (sigRedRel' a u u1 H (projT1 (Datatypes.fst x)))
                     (Hgood a (efst u) (projT1 (Datatypes.fst x))));
            apply Hgood
          | apply idL; apply Hgood ].
      + exists (sigRedRel' a u u1 H (projT1 (Datatypes.fst x))).
        apply (tr_eq _ _ _ (coh _ _ _ _ (sigRedRel' a u u1 H (projT1 (Datatypes.fst x))))).
        apply Sb; apply se_red_rel.
      + apply Rel_red_r; [exact H | exact (Datatypes.snd x)].
    - destruct x.
  Qed.

  Lemma elExp_rel {T} (r : Refine st UnivOK T) :
    forall u u1 (H : reds u u1) y, eqEl_ r u1 y u1 y -> eqEl_ r u (elExp r u u1 H y) u1 y.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh compL idL|T A0 B0 e a ea b eb coh compL idL|T N e s0]; cbn;
      intros u u1 H y G.
    - split; [reflexivity | apply Rel_exp_l; [exact H | exact (Datatypes.snd y)]].
    - split; [tauto | apply Rel_exp_l; [exact H | exact (Datatypes.snd y)]].
    - apply Rel_exp_l; [exact H | exact (Datatypes.snd y)].
    - apply ue_exp_rel.
    - destruct G as [G _].
      split; [| apply Rel_exp_l; [exact H | exact (Datatypes.snd y)]].
      intros u2 x2 u2' x2' r2 r2'.
      destruct (IH (b u2 x2)) as [S2 T2]; destruct (IH (b u2' x2')) as [S2' T2'].
      destruct (G _ _ _ _ r2 r2') as [G1 G2]; split.
      + eapply T2; [apply se_exp_rel | exact G1].
      + eapply T2'; [exact G2 |].
        apply (tr_eq _ _ _ (coh _ _ _ _ r2')).
        apply S2; apply se_exp_rel.
    - (* Sigma, the other way round: here the coherence goes in the direction
         the transport already has, so only the second direction of the clause
         has to undo a round trip. *)
      destruct (IH a) as [Sa Ta].
      destruct (IH (b (efst u) (sigExpFst a u u1 H (projT1 (Datatypes.fst y))))) as [Sb0 Tb0].
      destruct (IH (b (efst u1) (projT1 (Datatypes.fst y)))) as [Sb1 Tb1].
      split; [| split].
      + exists (sigExpRel a u u1 H (projT1 (Datatypes.fst y))).
        apply se_exp_rel.
      + exists (Sa _ _ _ _ (sigExpRel a u u1 H (projT1 (Datatypes.fst y)))).
        eapply Tb1;
          [ apply Sb1; eapply Tb1;
              [ apply (compL _ _ _ _ _ _
                         (Sa _ _ _ _ (sigExpRel a u u1 H (projT1 (Datatypes.fst y))))
                         (sigExpRel a u u1 H (projT1 (Datatypes.fst y)))
                         (Hgood a (efst u1) (projT1 (Datatypes.fst y))));
                apply Hgood
              | apply idL; apply Hgood ] |].
        apply (tr_eq _ _ _ (coh _ _ _ _
                 (Sa _ _ _ _ (sigExpRel a u u1 H (projT1 (Datatypes.fst y)))))).
        apply Sb0; apply se_exp_rel.
      + apply Rel_exp_l; [exact H | exact (Datatypes.snd y)].
    - destruct y.
  Qed.

  (* Goodness of the images, which is what the sig in Stage_next asks for. *)
  Lemma elRed_good {T} (r : Refine st UnivOK T) u u1 (H : reds u u1) x :
    eqEl_ r u x u x -> eqEl_ r u1 (elRed r u u1 H x) u1 (elRed r u u1 H x).
  Proof.
    intros G; pose proof (elRed_rel r u u1 H x G) as R.
    eapply (eqRefine_trans st Univ UnivEq UnivOK UnivEq_trans Hgood IH);
      [eapply (eqRefine_sym st Univ UnivEq UnivOK UnivEq_sym); exact R | exact R].
  Qed.

  Lemma elExp_good {T} (r : Refine st UnivOK T) u u1 (H : reds u u1) y :
    eqEl_ r u1 y u1 y -> eqEl_ r u (elExp r u u1 H y) u (elExp r u u1 H y).
  Proof.
    intros G; pose proof (elExp_rel r u u1 H y G) as R.
    eapply (eqRefine_trans st Univ UnivEq UnivOK UnivEq_trans Hgood IH);
      [exact R | eapply (eqRefine_sym st Univ UnivEq UnivOK UnivEq_sym); exact R].
  Qed.

  Definition SExp_next : SExp (Stage_next st Univ UnivEq UnivOK) :=
    Build_SExp (Stage_next st Univ UnivEq UnivOK)
      (fun c u u1 H x =>
         exist (fun z => eqEl_ (projT2 c) u1 z u1 z)
               (elRed (projT2 c) u u1 H (proj1_sig x))
               (elRed_good (projT2 c) u u1 H (proj1_sig x) (proj2_sig x)))
      (fun c u u1 H y =>
         exist (fun z => eqEl_ (projT2 c) u z u z)
               (elExp (projT2 c) u u1 H (proj1_sig y))
               (elExp_good (projT2 c) u u1 H (proj1_sig y) (proj2_sig y)))
      (fun c u u1 H x => elRed_rel (projT2 c) u u1 H (proj1_sig x) (proj2_sig x))
      (fun c u u1 H y => elExp_rel (projT2 c) u u1 H (proj1_sig y) (proj2_sig y)).
End ExpRefine.

Definition SExp_empty : SExp Stage_empty :=
  Build_SExp Stage_empty
    (fun s => match s with end) (fun s => match s with end)
    (fun s => match s with end) (fun s => match s with end).

Definition SExp_sum st1 st2 (S1 : SExp st1) (S2 : SExp st2) : SExp (Stage_sum st1 st2).
Proof.
  refine (Build_SExp (Stage_sum st1 st2)
            (fun s => match s return forall u u1, reds u u1 ->
                        (Stage_sum st1 st2).(StEl) s u -> (Stage_sum st1 st2).(StEl) s u1 with
                      | inl s => se_red S1 s | inr s => se_red S2 s end)
            (fun s => match s return forall u u1, reds u u1 ->
                        (Stage_sum st1 st2).(StEl) s u1 -> (Stage_sum st1 st2).(StEl) s u with
                      | inl s => se_exp S1 s | inr s => se_exp S2 s end)
            _ _).
  - intros [s|s]; [apply (se_red_rel S1) | apply (se_red_rel S2)].
  - intros [s|s]; [apply (se_exp_rel S1) | apply (se_exp_rel S2)].
Defined.

Definition SExp_sup T F (H : forall p, SExp (F p)) : SExp (Stage_sup T F) :=
  Build_SExp (Stage_sup T F)
    (fun s => se_red (H (projT1 s)) (projT2 s))
    (fun s => se_exp (H (projT1 s)) (projT2 s))
    (fun s => se_red_rel (H (projT1 s)) (projT2 s))
    (fun s => se_exp_rel (H (projT1 s)) (projT2 s)).

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UE : UnivExp Univ UnivEq).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).

  Fixpoint sexp (alpha : Ord) : SExp (stage_ alpha) :=
    match alpha as a return SExp (stage_ a) with
    | ozero => SExp_empty
    | osucc beta =>
        SExp_sum _ _
          (SExp_next (stage_ beta) Univ UnivEq UnivOK (sexp beta) UE
             UnivEq_sym UnivEq_trans (stage_good _ _ _ beta)
             (eqs_PER Univ UnivEq UnivOK UnivEq_sym UnivEq_trans beta))
          (sexp beta)
    | osup T f =>
        SExp_sup T _ (fun p =>
          SExp_sum _ _
            (SExp_next (stage_ (f p)) Univ UnivEq UnivOK (sexp (f p)) UE
               UnivEq_sym UnivEq_trans (stage_good _ _ _ (f p))
               (eqs_PER Univ UnivEq UnivOK UnivEq_sym UnivEq_trans (f p)))
            (sexp (f p)))
    end.

  Definition sexpU (beta : Ord) : SExp (Ust Univ UnivEq UnivOK beta) :=
    SExp_next (stage_ beta) Univ UnivEq UnivOK (sexp beta) UE
      UnivEq_sym UnivEq_trans (stage_good _ _ _ beta)
      (eqs_PER Univ UnivEq UnivOK UnivEq_sym UnivEq_trans beta).
End Level.
