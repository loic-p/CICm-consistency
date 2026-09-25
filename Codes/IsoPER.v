From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.EqPER Codes.Iso.
From Stdlib Require Import Arith Eqdep_dec.

(* Blueprint Lemma 8.6, first clause: the isomorphism of codes is an
   equivalence.  Symmetry and transitivity relate *different* records of the
   hj family, so each is a nested induction on the pair of stages; what makes
   that possible is that in Codes/Iso.v every peeling of a stage, on either
   side, is a projection of hj at strictly smaller stages on the nose.  The
   two directions have to be proved simultaneously, because flipping the
   codomain family of a Pi-code needs symmetry of the heterogeneous equality
   at the domain, which needs symmetry in the other direction. *)

Section SymRefine.
  Context (st st' : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (h : HJ st st') (h' : HJ st' st).
  Context (sym1 : forall s s', hj_rel h s s' -> hj_rel h' s' s)
          (sym2 : forall s s', hj_rel h' s' s -> hj_rel h s s')
          (to1 : forall s s' (P : hj_rel h s s') (Q : hj_rel h' s' s) u y,
                   st.(StEq) s u (hj_to h' s' s Q u y) u (hj_pull h s s' P u y))
          (to2 : forall s s' (P : hj_rel h s s') (Q : hj_rel h' s' s) u x,
                   st'.(StEq) s' u (hj_to h s s' P u x) u (hj_pull h' s' s Q u x)).
  Context (Hgood : StGood st) (Hgood' : StGood st').
  Context (HsymL : forall s, EqSym st s) (HtransL : forall s, EqTrans st s)
          (HsymR : forall s, EqSym st' s) (HtransR : forall s, EqTrans st' s).

  Local Notation Refine_ s := (Refine s UnivOK).
  Local Notation eqL := st.(StEq).
  Local Notation eqR := st'.(StEq).

  Lemma hjhet_sym1 s s' u x u' x' :
    hjhet h s s' u x u' x' -> hjhet h' s' s u' x' u x.
  Proof.
    intros [P HP]; exists (sym1 _ _ P).
    eapply HtransL; [apply (to1 s s' P) |].
    apply HsymL.
    eapply HtransL; [apply HsymL; apply (hj_to_pull h s s' P u x) |].
    apply (hj_pull_eq h s s' P); exact HP.
  Qed.

  Lemma hjhet_sym2 s s' u x u' x' :
    hjhet h' s' s u x u' x' -> hjhet h s s' u' x' u x.
  Proof.
    intros [Q HQ]; exists (sym2 _ _ Q).
    eapply HtransR; [apply (to2 s s' (sym2 _ _ Q) Q) |].
    apply HsymR.
    eapply HtransR; [apply HsymR; apply (hj_to_pull h' s' s Q u x) |].
    apply (hj_pull_eq h' s' s Q); exact HQ.
  Qed.

  Ltac iso_absurd := try (intros i; exact (match i with end)).

  Lemma isoRefine_sym {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    isoRefine st st' UnivOK h r r' -> isoRefine st' st UnivOK h' r' r.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i.
    - apply tyeq_sym; exact i.
    - apply tyeq_sym; exact i.
    - split; [apply tyeq_sym; exact (proj1 i) | split; apply (proj2 i)].
    - split; [apply tyeq_sym; exact (proj1 i) | exact (eq_sym (proj2 i))].
    - destruct i as [ty [Pa [ibb sq]]].
      split; [apply tyeq_sym; exact ty |].
      split; [exact (sym1 _ _ Pa) |].
      split.
      + intros u x u' x' H.
        exact (sym1 _ _ (ibb _ _ _ _ (hjhet_sym2 _ _ _ _ _ _ H))).
      + intros u1 x1 u1' x1' y1 y1' Hy Hy' r1 s1 Q Q' v w.
        eapply HtransL; [apply (to1 (b u1 y1) (b' u1 x1) (sym2 _ _ Q) Q) |].
        eapply HtransL;
          [ apply (pull_square st st' h HsymL HtransL HsymR HtransR
                     (b u1 y1) (b' u1 x1) (b u1' y1') (b' u1' x1')
                     (sym2 _ _ Q) (sym2 _ _ Q') (coh _ _ _ _ s1) (coh' _ _ _ _ r1)
                     (fun v0 w0 => sq u1 y1 u1' y1' x1 x1'
                                      (hjhet_sym2 a a' u1 x1 u1 y1 Hy)
                                      (hjhet_sym2 a a' u1' x1' u1' y1' Hy')
                                      s1 r1 (sym2 _ _ Q) (sym2 _ _ Q') v0 w0)) |].
        apply (tr_eq _ _ _ (coh _ _ _ _ s1)); apply HsymL.
        apply (to1 (b u1' y1') (b' u1' x1') (sym2 _ _ Q') Q').
    (* Sigma: the clause IS the Pi clause, so its proof is too. *)
    - destruct i as [ty [Pa [ibb sq]]].
      split; [apply tyeq_sym; exact ty |].
      split; [exact (sym1 _ _ Pa) |].
      split.
      + intros u x u' x' H.
        exact (sym1 _ _ (ibb _ _ _ _ (hjhet_sym2 _ _ _ _ _ _ H))).
      + intros u1 x1 u1' x1' y1 y1' Hy Hy' r1 s1 Q Q' v w.
        eapply HtransL; [apply (to1 (b u1 y1) (b' u1 x1) (sym2 _ _ Q) Q) |].
        eapply HtransL;
          [ apply (pull_square st st' h HsymL HtransL HsymR HtransR
                     (b u1 y1) (b' u1 x1) (b u1' y1') (b' u1' x1')
                     (sym2 _ _ Q) (sym2 _ _ Q') (coh _ _ _ _ s1) (coh' _ _ _ _ r1)
                     (fun v0 w0 => sq u1 y1 u1' y1' x1 x1'
                                      (hjhet_sym2 a a' u1 x1 u1 y1 Hy)
                                      (hjhet_sym2 a a' u1' x1' u1' y1' Hy')
                                      s1 r1 (sym2 _ _ Q) (sym2 _ _ Q') v0 w0)) |].
        apply (tr_eq _ _ _ (coh _ _ _ _ s1)); apply HsymL.
        apply (to1 (b u1' y1') (b' u1' x1') (sym2 _ _ Q') Q').
    - apply tyeq_sym; exact i.
  Qed.

  (* The shape of the Pi case of the transport half, isolated: the reverse
     transport of one record is the forward pullback of the other. *)
  Lemma key (s : St st) (s1 s2 : St st')
    (P1 : hj_rel h s s1) (Q1 : hj_rel h' s2 s)
    (trR : Transp st' s2 s1) (trL : Transp st s s)
    (Hsq : forall v w, eqR s1 v (hj_to h s s1 P1 v (tr trL v w))
                          v (tr trR v (hj_to h s s2 (sym2 _ _ Q1) v w)))
    (Hid : forall v y, eqL s v (tr trL v y) v y)
    v (Y : StEl st' s2 v) (W : StEl st' s1 v)
    (HYW : eqR s1 v W v (tr trR v Y)) :
    eqL s v (hj_to h' s2 s Q1 v Y) v (hj_pull h s s1 P1 v W).
  Proof.
    eapply HtransL; [apply (to1 s s2 (sym2 _ _ Q1) Q1) |].
    apply HsymL.
    eapply HtransL; [apply (hj_pull_eq h s s1 P1 _ _ _ _ HYW) |].
    eapply HtransL;
      [ apply (pull_square st st' h HsymL HtransL HsymR HtransR
                 s s1 s s2 P1 (sym2 _ _ Q1) trL trR Hsq) |].
    apply Hid.
  Qed.

  Lemma toRefine_sym {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (P : isoRefine st st' UnivOK h r r') (Q : isoRefine st' st UnivOK h' r' r) u y,
      eqEl st' Univ UnivEq UnivOK r' u y u y ->
      eqEl st Univ UnivEq UnivOK r u (toRefine st' st Univ UnivOK h' r' r Q u y) u
                                     (pullRefine st st' Univ UnivOK h r r' P u y).
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; try (intros P; exact (match P with end)); intros P Q u y H.
    - split; [reflexivity | exact (Good_tyeq T' T u (tyeq_sym _ _ P) (Datatypes.snd y))].
    - split; [tauto | exact (Good_tyeq T' T u (tyeq_sym _ _ P) (Datatypes.snd y))].
    - exact (Good_tyeq T' T u (tyeq_sym _ _ (proj1 P)) (Datatypes.snd y)).
    - assert (Em : m' = m) by exact (proj2 Q); subst m'.
      destruct (Nat.eq_dec m m) as [E1 | N1]; [| destruct (N1 eq_refl)].
      replace E1 with (eq_refl : m = m) by (apply UIP_dec; apply Nat.eq_dec).
      exact H.
    - destruct H as [Hg HR].
      pose proof (pullRefine_eq st st' Univ UnivEq UnivOK h HsymL HtransL HsymR HtransR
                    (r_pi st UnivOK T A0 B0 e a ea b eb coh cL iL)
                    (r_pi st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL')
                    P u y u y (conj Hg HR)) as HG.
      destruct HG as [HG _]; cbn in HG.
      split; [| exact (Good_tyeq T' T u (tyeq_sym _ _ (proj1 P)) HR)].
      intros u1 x1 u1' x1' r2 r2'.
      assert (KEY : forall ua (xa : StEl st a ua),
                 eqL (b ua xa) (eapp u ua)
                   (hj_to h' (b' ua (hj_pull h' a' a (proj1 (proj2 Q)) ua xa)) (b ua xa)
                      (proj1 (proj2 (proj2 Q)) ua (hj_pull h' a' a (proj1 (proj2 Q)) ua xa) ua xa
                         (ex_intro _ (proj1 (proj2 Q))
                            (hj_pull_to h' a' a (proj1 (proj2 Q)) ua xa)))
                      (eapp u ua)
                      (Datatypes.fst y ua (hj_pull h' a' a (proj1 (proj2 Q)) ua xa)))
                   (eapp u ua)
                   (hj_pull h (b ua xa) (b' ua (hj_to h a a' (proj1 (proj2 P)) ua xa))
                      (proj1 (proj2 (proj2 P)) ua xa ua (hj_to h a a' (proj1 (proj2 P)) ua xa)
                         (ex_intro _ (proj1 (proj2 P))
                            (hj_irr h a a' (proj1 (proj2 P)) (proj1 (proj2 P)) ua xa)))
                      (eapp u ua)
                      (Datatypes.fst y ua (hj_to h a a' (proj1 (proj2 P)) ua xa)))).
      { intros ua xa.
        pose proof (to2 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) ua xa) as eab.
        pose proof (HsymR a' _ _ _ _ eab) as eab'.
        eapply (key _ _ _ _ _ (coh' _ _ _ _ eab) (coh _ _ _ _ (Hgood a ua xa))).
        - intros v0 w0.
          apply ((proj2 (proj2 (proj2 P))) ua xa ua xa
                   (hj_to h a a' (proj1 (proj2 P)) ua xa)
                   (hj_pull h' a' a (proj1 (proj2 Q)) ua xa)
                   (ex_intro _ (proj1 (proj2 P))
                      (hj_irr h a a' (proj1 (proj2 P)) (proj1 (proj2 P)) ua xa))
                   (ex_intro _ (proj1 (proj2 P)) eab)).
        - intros v0 y0; apply iL; apply Hgood.
        - exact (proj1 (Hg ua _ ua _ eab eab')). }
      split.
      + eapply HtransL; [apply KEY | exact (proj1 (HG u1 x1 u1' x1' r2 r2'))].
      + eapply HtransL; [exact (proj2 (HG u1 x1 u1' x1' r2 r2')) |].
        apply (tr_eq _ _ _ (coh _ _ _ _ r2')); apply HsymL; apply KEY.
    - (* Sigma.  The two sides live at DIFFERENT codomain codes -- the image of
         the first component under h' on one side, its pullback under h on the
         other -- so the Pi argument (key) has to be followed by a transport
         along the coherence at the relation to1 provides between them. *)
      destruct H as [H1 [H2 HR]].
      assert (HET : hjhet h a a' (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y))).
      { exists (proj1 (proj2 P)).
        eapply (HtransR a');
          [ apply (hj_to_eq h a a' (proj1 (proj2 P)) _ _ _ _ (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) | apply (hj_pull_to h) ]. }
      split;
        [| split; [| exact (Good_tyeq T' T u (tyeq_sym _ _ (proj1 P)) HR)]].
      + exists (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))).
        eapply (HtransL (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))));
          [ apply (key (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) (b' (efst u) (projT1 (Datatypes.fst y)))
                     ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 Q))) (efst u) (projT1 (Datatypes.fst y)) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h' a' a (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))
                     (coh' (efst u) (projT1 (Datatypes.fst y)) (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))))
                     (coh (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))
                     (fun v0 w0 => (proj2 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (projT1 (Datatypes.fst y)) (projT1 (Datatypes.fst y))
                                     HET HET (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))))
                                     (Hgood' a' (efst u) (projT1 (Datatypes.fst y)))
                                     ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) (sym2 _ _ ((proj1 (proj2 (proj2 Q))) (efst u) (projT1 (Datatypes.fst y)) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h' a' a (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))) v0 w0)
                     (fun v0 y0 => iL (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) v0 y0
                                     (Hgood _ _ _))
                     (esnd u) (projT2 (Datatypes.fst y)) (projT2 (Datatypes.fst y))
                     (HsymR (b' (efst u) (projT1 (Datatypes.fst y))) _ _ _ _
                        (iL' (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))) (esnd u) (projT2 (Datatypes.fst y))
                           (Hgood' _ _ _)))) |].
        eapply (HtransL (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))));
          [ apply (hj_pull_eq h (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) _ _ _ _
                     (HsymR (b' (efst u) (projT1 (Datatypes.fst y))) _ _ _ _
                        (iL' (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))) (esnd u) (projT2 (Datatypes.fst y))
                           (Hgood' _ _ _)))) |].
        apply (pull_square st st' h HsymL HtransL HsymR HtransR
                 (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) (b (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y)))
                 ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 P))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y))
                   (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))))
                 (coh (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))))
                 (coh' (efst u) (projT1 (Datatypes.fst y)) (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))))
                 (fun v0 w0 => (proj2 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (projT1 (Datatypes.fst y)) (projT1 (Datatypes.fst y))
                                 HET (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))) (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood' a' (efst u) (projT1 (Datatypes.fst y)))
                                 ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 P))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y))
                   (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))))) v0 w0)).
      + exists (HsymL a _ _ _ _ (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))).
        apply (sig_flipL st Hgood HsymL HtransL a b coh cL iL
                 (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (HsymL a _ _ _ _ (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))))).
        eapply (HtransL (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))));
          [ apply (key (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) (b' (efst u) (projT1 (Datatypes.fst y)))
                     ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 Q))) (efst u) (projT1 (Datatypes.fst y)) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h' a' a (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))
                     (coh' (efst u) (projT1 (Datatypes.fst y)) (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))))
                     (coh (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))
                     (fun v0 w0 => (proj2 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (projT1 (Datatypes.fst y)) (projT1 (Datatypes.fst y))
                                     HET HET (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))))
                                     (Hgood' a' (efst u) (projT1 (Datatypes.fst y)))
                                     ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) (sym2 _ _ ((proj1 (proj2 (proj2 Q))) (efst u) (projT1 (Datatypes.fst y)) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h' a' a (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))))) v0 w0)
                     (fun v0 y0 => iL (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) v0 y0
                                     (Hgood _ _ _))
                     (esnd u) (projT2 (Datatypes.fst y)) (projT2 (Datatypes.fst y))
                     (HsymR (b' (efst u) (projT1 (Datatypes.fst y))) _ _ _ _
                        (iL' (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))) (esnd u) (projT2 (Datatypes.fst y))
                           (Hgood' _ _ _)))) |].
        eapply (HtransL (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))));
          [ apply (hj_pull_eq h (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) _ _ _ _
                     (HsymR (b' (efst u) (projT1 (Datatypes.fst y))) _ _ _ _
                        (iL' (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))) (esnd u) (projT2 (Datatypes.fst y))
                           (Hgood' _ _ _)))) |].
        apply (pull_square st st' h HsymL HtransL HsymR HtransR
                 (b (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y))) (b (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))) (b' (efst u) (projT1 (Datatypes.fst y)))
                 ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 P))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y))
                   (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))))
                 (coh (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))))
                 (coh' (efst u) (projT1 (Datatypes.fst y)) (efst u) (projT1 (Datatypes.fst y)) (Hgood' a' (efst u) (projT1 (Datatypes.fst y))))
                 (fun v0 w0 => (proj2 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (projT1 (Datatypes.fst y)) (projT1 (Datatypes.fst y))
                                 HET (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y)))) (to1 a a' (proj1 (proj2 P)) (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (Hgood' a' (efst u) (projT1 (Datatypes.fst y)))
                                 ((proj1 (proj2 (proj2 P))) (efst u) (hj_to h' a' a (proj1 (proj2 Q)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y)) HET) ((proj1 (proj2 (proj2 P))) (efst u) (hj_pull h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (projT1 (Datatypes.fst y))
                   (ex_intro _ (proj1 (proj2 P)) (hj_pull_to h a a' (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst y))))) v0 w0)).
    - destruct y.
  Qed.
End SymRefine.

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).
  Local Notation Ust_ := (Ust Univ UnivEq UnivOK).
  Local Notation hj_ := (hj Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation hjU_ := (hjU Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation sgood_ := (sgood Univ UnivEq UnivOK).
  Local Notation ssym_ := (ssym Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation strans_ := (strans Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).

  Definition SymRel (alpha alpha' : Ord) : Prop :=
    forall (s : (stage_ alpha).(St)) (s' : (stage_ alpha').(St)),
      hj_rel (hj_ alpha alpha') s s' -> hj_rel (hj_ alpha' alpha) s' s.

  Definition SymTo (alpha alpha' : Ord) : Prop :=
    forall (s : (stage_ alpha).(St)) (s' : (stage_ alpha').(St))
           (P : hj_rel (hj_ alpha alpha') s s') (Q : hj_rel (hj_ alpha' alpha) s' s) u y,
      (stage_ alpha).(StEq) s u (hj_to (hj_ alpha' alpha) s' s Q u y)
                            u (hj_pull (hj_ alpha alpha') s s' P u y).

  Definition SymP (alpha alpha' : Ord) : Prop := SymRel alpha alpha' /\ SymTo alpha alpha'.

  (* One node pair, from the two directions at the stages below it. *)
  Lemma symNode b1 b2 : SymP b1 b2 -> SymP b2 b1 ->
    (forall (c : (Ust_ b1).(St)) (c' : (Ust_ b2).(St)),
       hj_rel (hjU_ b1 b2) c c' -> hj_rel (hjU_ b2 b1) c' c) /\
    (forall (c : (Ust_ b1).(St)) (c' : (Ust_ b2).(St))
            (P : hj_rel (hjU_ b1 b2) c c') (Q : hj_rel (hjU_ b2 b1) c' c) u y,
       (Ust_ b1).(StEq) c u (hj_to (hjU_ b2 b1) c' c Q u y)
                        u (hj_pull (hjU_ b1 b2) c c' P u y)).
  Proof.
    intros [S1 T1] [S2 T2]; split.
    - intros c c'.
      apply (isoRefine_sym (stage_ b1) (stage_ b2) UnivOK (hj_ b1 b2) (hj_ b2 b1)
               S1 (fun s s' H => S2 s' s H) T1 (fun s s' P Q u x => T2 s' s Q P u x)
               (ssym_ b1) (strans_ b1) (ssym_ b2) (strans_ b2)).
    - intros c c' P Q u y.
      apply (toRefine_sym (stage_ b1) (stage_ b2) Univ UnivEq UnivOK (hj_ b1 b2) (hj_ b2 b1)
               (fun s s' H => S2 s' s H) T1 (fun s s' P0 Q0 u0 x => T2 s' s Q0 P0 u0 x)
               (sgood_ b1) (sgood_ b2) (ssym_ b1) (strans_ b1) (ssym_ b2) (strans_ b2)
               (projT2 c) (projT2 c') P Q u (proj1_sig y) (proj2_sig y)).
  Qed.

  Lemma hj_symP : forall alpha alpha', SymP alpha alpha' /\ SymP alpha' alpha.
  Proof.
    induction alpha as [| beta IHb | T f IHf].
    - intros alpha'; split; split;
        [intros [] | intros [] | intros s [] | intros s []].
    - intros alpha'; induction alpha' as [| beta' IHb' | T' f' IHf'].
      + split; split; [intros s [] | intros s [] | intros [] | intros []].
      + pose proof (IHb beta') as Hbb'.
        pose proof (IHb (osucc beta')) as Hbs'.
        pose proof (symNode beta beta' (proj1 Hbb') (proj2 Hbb')) as N1.
        pose proof (symNode beta' beta (proj2 Hbb') (proj1 Hbb')) as N2.
        split; split.
        * intros [c|s0] [c'|s0'].
          -- exact (proj1 N1 c c').
          -- exact (proj1 (proj1 IHb') (inl c) s0').
          -- exact (proj1 (proj1 Hbs') s0 (inl c')).
          -- exact (proj1 (proj1 Hbb') s0 s0').
        * intros [c|s0] [c'|s0'].
          -- exact (proj2 N1 c c').
          -- exact (proj2 (proj1 IHb') (inl c) s0').
          -- exact (proj2 (proj1 Hbs') s0 (inl c')).
          -- exact (proj2 (proj1 Hbb') s0 s0').
        * intros [c'|s0'] [c|s0].
          -- exact (proj1 N2 c' c).
          -- exact (proj1 (proj2 Hbs') (inl c') s0).
          -- exact (proj1 (proj2 IHb') s0' (inl c)).
          -- exact (proj1 (proj2 Hbb') s0' s0).
        * intros [c'|s0'] [c|s0].
          -- exact (proj2 N2 c' c).
          -- exact (proj2 (proj2 Hbs') (inl c') s0).
          -- exact (proj2 (proj2 IHb') s0' (inl c)).
          -- exact (proj2 (proj2 Hbb') s0' s0).
      + split; split.
        * intros [c|s0] [p' [c'|s0']].
          -- exact (proj1 (symNode beta (f' p') (proj1 (IHb (f' p'))) (proj2 (IHb (f' p')))) c c').
          -- exact (proj1 (proj1 (IHf' p')) (inl c) s0').
          -- exact (proj1 (proj1 (IHb (osup T' f'))) s0 (existT _ p' (inl c'))).
          -- exact (proj1 (proj1 (IHb (f' p'))) s0 s0').
        * intros [c|s0] [p' [c'|s0']].
          -- exact (proj2 (symNode beta (f' p') (proj1 (IHb (f' p'))) (proj2 (IHb (f' p')))) c c').
          -- exact (proj2 (proj1 (IHf' p')) (inl c) s0').
          -- exact (proj2 (proj1 (IHb (osup T' f'))) s0 (existT _ p' (inl c'))).
          -- exact (proj2 (proj1 (IHb (f' p'))) s0 s0').
        * intros [p' [c'|s0']] [c|s0].
          -- exact (proj1 (symNode (f' p') beta (proj2 (IHb (f' p'))) (proj1 (IHb (f' p')))) c' c).
          -- exact (proj1 (proj2 (IHb (osup T' f'))) (existT _ p' (inl c')) s0).
          -- exact (proj1 (proj2 (IHf' p')) s0' (inl c)).
          -- exact (proj1 (proj2 (IHb (f' p'))) s0' s0).
        * intros [p' [c'|s0']] [c|s0].
          -- exact (proj2 (symNode (f' p') beta (proj2 (IHb (f' p'))) (proj1 (IHb (f' p')))) c' c).
          -- exact (proj2 (proj2 (IHb (osup T' f'))) (existT _ p' (inl c')) s0).
          -- exact (proj2 (proj2 (IHf' p')) s0' (inl c)).
          -- exact (proj2 (proj2 (IHb (f' p'))) s0' s0).
    - intros alpha'; induction alpha' as [| beta' IHb' | T' f' IHf'].
      + split; split; [intros s [] | intros s [] | intros [] | intros []].
      + split; split.
        * intros [p [c|s0]] [c'|s0'].
          -- exact (proj1 (symNode (f p) beta' (proj1 (IHf p beta')) (proj2 (IHf p beta'))) c c').
          -- exact (proj1 (proj1 IHb') (existT _ p (inl c)) s0').
          -- exact (proj1 (proj1 (IHf p (osucc beta'))) s0 (inl c')).
          -- exact (proj1 (proj1 (IHf p beta')) s0 s0').
        * intros [p [c|s0]] [c'|s0'].
          -- exact (proj2 (symNode (f p) beta' (proj1 (IHf p beta')) (proj2 (IHf p beta'))) c c').
          -- exact (proj2 (proj1 IHb') (existT _ p (inl c)) s0').
          -- exact (proj2 (proj1 (IHf p (osucc beta'))) s0 (inl c')).
          -- exact (proj2 (proj1 (IHf p beta')) s0 s0').
        * intros [c'|s0'] [p [c|s0]].
          -- exact (proj1 (symNode beta' (f p) (proj2 (IHf p beta')) (proj1 (IHf p beta'))) c' c).
          -- exact (proj1 (proj2 (IHf p (osucc beta'))) (inl c') s0).
          -- exact (proj1 (proj2 IHb') s0' (existT _ p (inl c))).
          -- exact (proj1 (proj2 (IHf p beta')) s0' s0).
        * intros [c'|s0'] [p [c|s0]].
          -- exact (proj2 (symNode beta' (f p) (proj2 (IHf p beta')) (proj1 (IHf p beta'))) c' c).
          -- exact (proj2 (proj2 (IHf p (osucc beta'))) (inl c') s0).
          -- exact (proj2 (proj2 IHb') s0' (existT _ p (inl c))).
          -- exact (proj2 (proj2 (IHf p beta')) s0' s0).
      + split; split.
        * intros [p [c|s0]] [p' [c'|s0']].
          -- exact (proj1 (symNode (f p) (f' p') (proj1 (IHf p (f' p'))) (proj2 (IHf p (f' p')))) c c').
          -- exact (proj1 (proj1 (IHf' p')) (existT _ p (inl c)) s0').
          -- exact (proj1 (proj1 (IHf p (osup T' f'))) s0 (existT _ p' (inl c'))).
          -- exact (proj1 (proj1 (IHf p (f' p'))) s0 s0').
        * intros [p [c|s0]] [p' [c'|s0']].
          -- exact (proj2 (symNode (f p) (f' p') (proj1 (IHf p (f' p'))) (proj2 (IHf p (f' p')))) c c').
          -- exact (proj2 (proj1 (IHf' p')) (existT _ p (inl c)) s0').
          -- exact (proj2 (proj1 (IHf p (osup T' f'))) s0 (existT _ p' (inl c'))).
          -- exact (proj2 (proj1 (IHf p (f' p'))) s0 s0').
        * intros [p' [c'|s0']] [p [c|s0]].
          -- exact (proj1 (symNode (f' p') (f p) (proj2 (IHf p (f' p'))) (proj1 (IHf p (f' p')))) c' c).
          -- exact (proj1 (proj2 (IHf p (osup T' f'))) (existT _ p' (inl c')) s0).
          -- exact (proj1 (proj2 (IHf' p')) s0' (existT _ p (inl c))).
          -- exact (proj1 (proj2 (IHf p (f' p')))  s0' s0).
        * intros [p' [c'|s0']] [p [c|s0]].
          -- exact (proj2 (symNode (f' p') (f p) (proj2 (IHf p (f' p'))) (proj1 (IHf p (f' p')))) c' c).
          -- exact (proj2 (proj2 (IHf p (osup T' f'))) (existT _ p' (inl c')) s0).
          -- exact (proj2 (proj2 (IHf' p')) s0' (existT _ p (inl c))).
          -- exact (proj2 (proj2 (IHf p (f' p')))  s0' s0).
  Qed.

  (* The working interface: the isomorphism of Codes/Iso.v is symmetric, and
     the reverse transport is the forward pullback. *)
  Lemma ciso_sym {beta beta'} (c : U Univ UnivEq UnivOK beta) (c' : U Univ UnivEq UnivOK beta') :
    ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c c' ->
    ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c' c.
  Proof.
    exact (proj1 (symNode beta beta' (proj1 (hj_symP beta beta')) (proj2 (hj_symP beta beta'))) c c').
  Qed.

  Lemma cto_sym {beta beta'} (c : U Univ UnivEq UnivOK beta) (c' : U Univ UnivEq UnivOK beta')
    (P : ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c c')
    (Q : ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c' c) u y :
    (Ust_ beta).(StEq) c u (cto Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c' c Q u y)
                        u (cpull Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c c' P u y).
  Proof.
    exact (proj2 (symNode beta beta' (proj1 (hj_symP beta beta')) (proj2 (hj_symP beta beta')))
             c c' P Q u y).
  Qed.
End Level.

Lemma tyeq_trans A B C : tyeq A B -> tyeq B C -> tyeq A C.
Proof.
  intros [n H1] [m H2]; exists (Nat.max n m).
  eapply eqty_trans;
    [ apply (eqty_cumul n (Nat.max n m)); [apply Nat.le_max_l | exact H1]
    | apply (eqty_cumul m (Nat.max n m)); [apply Nat.le_max_r | exact H2]].
Qed.

Section TransRefine.
  Context (st1 st2 st3 : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (h12 : HJ st1 st2) (h23 : HJ st2 st3) (h13 : HJ st1 st3).
  (* What has to hold of the three records at the stages below. *)
  Context (trel : forall a b c, hj_rel h12 a b -> hj_rel h23 b c -> hj_rel h13 a c)
          (tfun : forall a b c (P : hj_rel h12 a b) (Q : hj_rel h23 b c) (R : hj_rel h13 a c) u x,
                    st3.(StEq) c u (hj_to h13 a c R u x)
                                 u (hj_to h23 b c Q u (hj_to h12 a b P u x))).
  Context (Hg1 : StGood st1) (Hg2 : StGood st2) (Hg3 : StGood st3).
  Context (Hs1 : forall s, EqSym st1 s) (Ht1 : forall s, EqTrans st1 s)
          (Hs2 : forall s, EqSym st2 s) (Ht2 : forall s, EqTrans st2 s)
          (Hs3 : forall s, EqSym st3 s) (Ht3 : forall s, EqTrans st3 s).

  (* Splitting a heterogeneous relatedness through the middle stage: the
     middle element is the image of the first, and this is the one place
     where functoriality of the transport is spent. *)
  Lemma hjhet_split a1 a2 a3 (P12 : hj_rel h12 a1 a2) (P23 : hj_rel h23 a2 a3) u x u' x' :
    hjhet h13 a1 a3 u x u' x' ->
    hjhet h12 a1 a2 u x u (hj_to h12 a1 a2 P12 u x) /\
    hjhet h23 a2 a3 u (hj_to h12 a1 a2 P12 u x) u' x'.
  Proof.
    intros [R HR]; split.
    - exists P12; apply Hg2.
    - exists P23.
      eapply Ht3; [apply Hs3; apply (tfun a1 a2 a3 P12 P23 R) | exact HR].
  Qed.

  Ltac iso_absurd1 := try (intros i1; exact (match i1 with end)).
  Ltac iso_absurd2 := try (intros i1 i2; exact (match i2 with end)).

  Lemma isoRefine_trans {T1 T2 T3} (r1 : Refine st1 UnivOK T1) (r2 : Refine st2 UnivOK T2)
    (r3 : Refine st3 UnivOK T3) :
    isoRefine st1 st2 UnivOK h12 r1 r2 -> isoRefine st2 st3 UnivOK h23 r2 r3 ->
    isoRefine st1 st3 UnivOK h13 r1 r3.
  Proof.
    destruct r1 as [T1 e1|T1 e1|T1 p1 e1 H1|T1 m1 ok1 e1
                   |T1 A1 B1 e1 a1 ea1 b1 eb1 coh1 cL1 iL1|T1 A1 B1 e1 a1 ea1 b1 eb1 coh1 cL1 iL1|T1 N1 e1 s1];
    destruct r2 as [T2 e2|T2 e2|T2 p2 e2 H2|T2 m2 ok2 e2
                   |T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2|T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2|T2 N2 e2 s2];
      cbn; iso_absurd1;
    destruct r3 as [T3 e3|T3 e3|T3 p3 e3 H3|T3 m3 ok3 e3
                   |T3 A3 B3 e3 a3 ea3 b3 eb3 coh3 cL3 iL3|T3 A3 B3 e3 a3 ea3 b3 eb3 coh3 cL3 iL3|T3 N3 e3 s3];
      cbn; iso_absurd2; intros i1 i2.
    - eapply tyeq_trans; eassumption.
    - eapply tyeq_trans; eassumption.
    - split; [eapply tyeq_trans; [exact (proj1 i1) | exact (proj1 i2)] |].
      destruct i1 as [_ [f1 g1]]; destruct i2 as [_ [f2 g2]]; split; auto.
    - split; [eapply tyeq_trans; [exact (proj1 i1) | exact (proj1 i2)]
             | eapply eq_trans; [exact (proj2 i1) | exact (proj2 i2)]].
    - destruct i1 as [ty1 [Pa1 [ib1 sq1]]].
      destruct i2 as [ty2 [Pa2 [ib2 sq2]]].
      split; [eapply tyeq_trans; eassumption |].
      split; [exact (trel _ _ _ Pa1 Pa2) |].
      split.
      { intros u x u' x' Hx.
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u x u' x' Hx) as [G1 G2].
        exact (trel _ _ _ (ib1 _ _ _ _ G1) (ib2 _ _ _ _ G2)). }
      { intros u1 x1 u1' x1' z1 z1' Hz Hz' rr ss Q Q' v w.
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u1 x1 u1 z1 Hz) as [G1z G2z].
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u1' x1' u1' z1' Hz') as [G1z' G2z'].
        pose proof (hj_to_eq h12 a1 a2 Pa1 _ _ _ _ rr) as ss2.
        eapply Ht3;
          [ apply (tfun (b1 u1 x1) (b2 u1 (hj_to h12 a1 a2 Pa1 u1 x1)) (b3 u1 z1)
                     (ib1 _ _ _ _ G1z) (ib2 _ _ _ _ G2z) Q) |].
        eapply Ht3;
          [ apply (hj_to_eq h23 _ _ (ib2 _ _ _ _ G2z) _ _ _ _
                     (sq1 u1 x1 u1' x1' _ _ G1z G1z' rr ss2
                        (ib1 _ _ _ _ G1z) (ib1 _ _ _ _ G1z') v w)) |].
        eapply Ht3;
          [ apply (sq2 u1 _ u1' _ z1 z1' G2z G2z' ss2 ss
                     (ib2 _ _ _ _ G2z) (ib2 _ _ _ _ G2z') v _) |].
        apply (tr_eq _ _ _ (coh3 _ _ _ _ ss)); apply Hs3.
        apply (tfun (b1 u1' x1') (b2 u1' (hj_to h12 a1 a2 Pa1 u1' x1')) (b3 u1' z1')
                 (ib1 _ _ _ _ G1z') (ib2 _ _ _ _ G2z') Q'). }
    (* Sigma: the clause IS the Pi clause, so its proof is too. *)
    - destruct i1 as [ty1 [Pa1 [ib1 sq1]]].
      destruct i2 as [ty2 [Pa2 [ib2 sq2]]].
      split; [eapply tyeq_trans; eassumption |].
      split; [exact (trel _ _ _ Pa1 Pa2) |].
      split.
      { intros u x u' x' Hx.
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u x u' x' Hx) as [G1 G2].
        exact (trel _ _ _ (ib1 _ _ _ _ G1) (ib2 _ _ _ _ G2)). }
      { intros u1 x1 u1' x1' z1 z1' Hz Hz' rr ss Q Q' v w.
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u1 x1 u1 z1 Hz) as [G1z G2z].
        destruct (hjhet_split a1 a2 a3 Pa1 Pa2 u1' x1' u1' z1' Hz') as [G1z' G2z'].
        pose proof (hj_to_eq h12 a1 a2 Pa1 _ _ _ _ rr) as ss2.
        eapply Ht3;
          [ apply (tfun (b1 u1 x1) (b2 u1 (hj_to h12 a1 a2 Pa1 u1 x1)) (b3 u1 z1)
                     (ib1 _ _ _ _ G1z) (ib2 _ _ _ _ G2z) Q) |].
        eapply Ht3;
          [ apply (hj_to_eq h23 _ _ (ib2 _ _ _ _ G2z) _ _ _ _
                     (sq1 u1 x1 u1' x1' _ _ G1z G1z' rr ss2
                        (ib1 _ _ _ _ G1z) (ib1 _ _ _ _ G1z') v w)) |].
        eapply Ht3;
          [ apply (sq2 u1 _ u1' _ z1 z1' G2z G2z' ss2 ss
                     (ib2 _ _ _ _ G2z) (ib2 _ _ _ _ G2z') v _) |].
        apply (tr_eq _ _ _ (coh3 _ _ _ _ ss)); apply Hs3.
        apply (tfun (b1 u1' x1') (b2 u1' (hj_to h12 a1 a2 Pa1 u1' x1')) (b3 u1' z1')
                 (ib1 _ _ _ _ G1z') (ib2 _ _ _ _ G2z') Q'). }
    - eapply tyeq_trans; eassumption.
  Qed.

  (* The shape of the Pi case of functoriality, isolated. *)
  Lemma keyFun (sa : St st1) (sa' : St st1) (t2 : St st2) (t3 : St st3)
    (Q13 : hj_rel h13 sa t3) (Q13' : hj_rel h13 sa' t3)
    (Q12 : hj_rel h12 sa' t2) (Q23 : hj_rel h23 t2 t3)
    (trL : Transp st1 sa' sa) (trR : Transp st3 t3 t3)
    (Hsq : forall v w, st3.(StEq) t3 v (hj_to h13 sa t3 Q13 v (tr trL v w))
                                    v (tr trR v (hj_to h13 sa' t3 Q13' v w)))
    (Hid : forall v y, st3.(StEq) t3 v (tr trR v y) v y)
    v (Y : StEl st1 sa v) (Y' : StEl st1 sa' v)
    (HY : st1.(StEq) sa v Y v (tr trL v Y')) :
    st3.(StEq) t3 v (hj_to h13 sa t3 Q13 v Y)
                  v (hj_to h23 t2 t3 Q23 v (hj_to h12 sa' t2 Q12 v Y')).
  Proof.
    eapply Ht3; [apply (hj_to_eq h13 sa t3 Q13 _ _ _ _ HY) |].
    eapply Ht3; [apply Hsq |].
    eapply Ht3; [apply Hid |].
    apply (tfun sa' t2 t3 Q12 Q23 Q13').
  Qed.

  Lemma toRefine_fun {T1 T2 T3} (r1 : Refine st1 UnivOK T1) (r2 : Refine st2 UnivOK T2)
    (r3 : Refine st3 UnivOK T3) :
    forall (P : isoRefine st1 st2 UnivOK h12 r1 r2) (Q : isoRefine st2 st3 UnivOK h23 r2 r3)
           (R : isoRefine st1 st3 UnivOK h13 r1 r3) u x,
      eqEl st1 Univ UnivEq UnivOK r1 u x u x ->
      eqEl st3 Univ UnivEq UnivOK r3 u
        (toRefine st1 st3 Univ UnivOK h13 r1 r3 R u x) u
        (toRefine st2 st3 Univ UnivOK h23 r2 r3 Q u
           (toRefine st1 st2 Univ UnivOK h12 r1 r2 P u x)).
  Proof.
    destruct r1 as [T1 e1|T1 e1|T1 p1 e1 H1|T1 m1 ok1 e1
                   |T1 A1 B1 e1 a1 ea1 b1 eb1 coh1 cL1 iL1|T1 A1 B1 e1 a1 ea1 b1 eb1 coh1 cL1 iL1|T1 N1 e1 s1];
    destruct r2 as [T2 e2|T2 e2|T2 p2 e2 H2|T2 m2 ok2 e2
                   |T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2|T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2|T2 N2 e2 s2];
      cbn; iso_absurd1;
    destruct r3 as [T3 e3|T3 e3|T3 p3 e3 H3|T3 m3 ok3 e3
                   |T3 A3 B3 e3 a3 ea3 b3 eb3 coh3 cL3 iL3|T3 A3 B3 e3 a3 ea3 b3 eb3 coh3 cL3 iL3|T3 N3 e3 s3];
      cbn; iso_absurd2; intros P Q R u x H.
    - split; [reflexivity
             | exact (Good_tyeq T1 T3 u (tyeq_trans _ _ _ P Q) (Datatypes.snd x))].
    - split; [tauto
             | exact (Good_tyeq T1 T3 u (tyeq_trans _ _ _ P Q) (Datatypes.snd x))].
    - exact (Good_tyeq T1 T3 u (tyeq_trans _ _ _ (proj1 P) (proj1 Q)) (Datatypes.snd x)).
    - assert (Em1 : m1 = m2) by exact (proj2 P).
      assert (Em2 : m2 = m3) by exact (proj2 Q).
      subst m2; subst m3.
      destruct (Nat.eq_dec m1 m1) as [E | NE]; [| destruct (NE eq_refl)].
      replace E with (eq_refl : m1 = m1) by (apply UIP_dec; apply Nat.eq_dec).
      exact H.
    - pose proof H as H0.
      destruct H as [Hf HR].
      pose proof (toRefine_eq st1 st2 Univ UnivEq UnivOK h12 Ht2
                    (r_pi st1 UnivOK T1 A1 B1 e1 a1 ea1 b1 eb1 coh1 cL1 iL1)
                    (r_pi st2 UnivOK T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2)
                    P u x u x H0) as HR1.
      pose proof (toRefine_eq st2 st3 Univ UnivEq UnivOK h23 Ht3
                    (r_pi st2 UnivOK T2 A2 B2 e2 a2 ea2 b2 eb2 coh2 cL2 iL2)
                    (r_pi st3 UnivOK T3 A3 B3 e3 a3 ea3 b3 eb3 coh3 cL3 iL3)
                    Q u _ u _ HR1) as HRR.
      destruct HRR as [HRR _]; cbn in HRR.
      split; [| exact (Good_tyeq T1 T3 u (tyeq_trans _ _ _ (proj1 P) (proj1 Q)) HR)].
      intros u1 z1 u1' z1' rr rr'.
      assert (Hw : st3.(StEq) a3 u1
                     (hj_to h13 a1 a3 (proj1 (proj2 R)) u1
                        (hj_pull h12 a1 a2 (proj1 (proj2 P)) u1
                           (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1))) u1 z1).
      { eapply Ht3;
          [apply (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R))) |].
        eapply Ht3;
          [apply (hj_to_eq h23 a2 a3 (proj1 (proj2 Q)) _ _ _ _
                    (hj_pull_to h12 a1 a2 (proj1 (proj2 P)) u1 _)) |].
        apply (hj_pull_to h23 a2 a3 (proj1 (proj2 Q))). }
      assert (Hd : st1.(StEq) a1 u1 (hj_pull h13 a1 a3 (proj1 (proj2 R)) u1 z1) u1
                     (hj_pull h12 a1 a2 (proj1 (proj2 P)) u1
                        (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1))).
      { apply (to_inj st1 st3 h13 Hs1 Ht1 a1 a3 (proj1 (proj2 R))).
        eapply Ht3; [apply (hj_pull_to h13 a1 a3 (proj1 (proj2 R))) | apply Hs3; exact Hw]. }
      assert (KEY : st3.(StEq) (b3 u1 z1) (eapp u u1)
                      (hj_to h13 (b1 u1 (hj_pull h13 a1 a3 (proj1 (proj2 R)) u1 z1)) (b3 u1 z1)
                         ((proj1 (proj2 (proj2 R))) u1
                            (hj_pull h13 a1 a3 (proj1 (proj2 R)) u1 z1) u1 z1
                            (ex_intro _ (proj1 (proj2 R))
                               (hj_pull_to h13 a1 a3 (proj1 (proj2 R)) u1 z1)))
                         (eapp u u1)
                         (Datatypes.fst x u1 (hj_pull h13 a1 a3 (proj1 (proj2 R)) u1 z1)))
                      (eapp u u1)
                      (hj_to h23 (b2 u1 (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1)) (b3 u1 z1)
                         ((proj1 (proj2 (proj2 Q))) u1
                            (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1) u1 z1
                            (ex_intro _ (proj1 (proj2 Q))
                               (hj_pull_to h23 a2 a3 (proj1 (proj2 Q)) u1 z1)))
                         (eapp u u1)
                         (hj_to h12
                            (b1 u1 (hj_pull h12 a1 a2 (proj1 (proj2 P)) u1
                                      (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1)))
                            (b2 u1 (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1))
                            ((proj1 (proj2 (proj2 P))) u1
                               (hj_pull h12 a1 a2 (proj1 (proj2 P)) u1
                                  (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1))
                               u1 (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1)
                               (ex_intro _ (proj1 (proj2 P))
                                  (hj_pull_to h12 a1 a2 (proj1 (proj2 P)) u1
                                     (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1))))
                            (eapp u u1)
                            (Datatypes.fst x u1
                               (hj_pull h12 a1 a2 (proj1 (proj2 P)) u1
                                  (hj_pull h23 a2 a3 (proj1 (proj2 Q)) u1 z1)))))).
      { eapply (keyFun _ _ _ _ _
                  ((proj1 (proj2 (proj2 R))) u1 _ u1 z1
                     (ex_intro _ (proj1 (proj2 R)) Hw))
                  _ _ (coh1 _ _ _ _ Hd) (coh3 _ _ _ _ (Hg3 a3 u1 z1))).
        - intros v0 w0.
          apply ((proj2 (proj2 (proj2 R))) u1 _ u1 _ z1 z1
                   (ex_intro _ (proj1 (proj2 R))
                      (hj_pull_to h13 a1 a3 (proj1 (proj2 R)) u1 z1))
                   (ex_intro _ (proj1 (proj2 R)) Hw)
                   Hd (Hg3 a3 u1 z1)).
        - intros v0 y0; apply iL3; apply Hg3.
        - exact (proj1 (Hf u1 _ u1 _ Hd (Hs1 a1 _ _ _ _ Hd))). }
      split.
      + eapply Ht3; [exact KEY | exact (proj1 (HRR u1 z1 u1' z1' rr rr'))].
      + eapply Ht3; [exact (proj2 (HRR u1 z1 u1' z1' rr rr')) |].
        apply (tr_eq _ _ _ (coh3 _ _ _ _ rr')); apply Hs3; exact KEY.
    - (* Sigma.  The composite lands at a different codomain code from the
         direct transport -- b3 at the image of the first component under h13
         on one side, under h23 o h12 on the other -- so keyFun is followed by
         the naturality square of the second isomorphism at the relation tfun
         provides between them. *)
      destruct H as [H1 [H2 HR]].
      pose proof (ex_intro (fun p => st3.(StEq) a3 (efst u)
                    (hj_to h13 a1 a3 p (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))
                    (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) as HIR.
      assert (HET : hjhet h23 a2 a3 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))).
      { exists (proj1 (proj2 Q)); apply Hs3; exact (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))). }
      split;
        [| split;
           [| exact (Good_tyeq T1 T3 u (tyeq_trans _ _ _ (proj1 P) (proj1 Q)) HR)]].
      + exists (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))).
        eapply (Ht3 (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))));
          [ apply (keyFun (b1 (efst u) (projT1 (Datatypes.fst x))) (b1 (efst u) (projT1 (Datatypes.fst x)))
                     (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))
                     ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 P))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 P)) (hj_irr h12 a1 a2 (proj1 (proj2 P)) (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET)
                     (coh1 (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (Hg1 a1 (efst u) (projT1 (Datatypes.fst x))))
                     (coh3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))))
                     (fun v0 w0 => (proj2 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                                     HIR HIR (Hg1 a1 (efst u) (projT1 (Datatypes.fst x)))
                                     (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) v0 w0)
                     (fun v0 y0 => iL3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) v0 y0
                                     (Hg3 _ _ _))
                     (esnd u) (projT2 (Datatypes.fst x)) (projT2 (Datatypes.fst x))
                     (Hs1 (b1 (efst u) (projT1 (Datatypes.fst x))) _ _ _ _
                        (iL1 (efst u) (projT1 (Datatypes.fst x)) (Hg1 a1 (efst u) (projT1 (Datatypes.fst x))) (esnd u) (projT2 (Datatypes.fst x))
                           (Hg1 _ _ _)))) |].
        eapply (Ht3 (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))));
          [ apply (hj_to_eq h23 (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET) _ _ _ _
                     (Hs2 (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) _ _ _ _
                        (iL2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (Hg2 a2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (esnd u) _
                           (Hg2 _ _ _)))) |].
        apply ((proj2 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h23 a2 a3 (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))
                 HET (ex_intro _ (proj1 (proj2 Q)) (hj_irr h23 a2 a3 (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))))
                 (Hg2 a2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h23 a2 a3 (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h23 a2 a3 (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))))).
      + exists (Hs3 a3 _ _ _ _ (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))).
        apply (sig_flipR st3 Hg3 Hs3 Ht3 a3 b3 coh3 cL3 iL3
                 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h23 a2 a3 (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (Hs3 a3 _ _ _ _ (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))).
        eapply (Ht3 (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))));
          [ apply (keyFun (b1 (efst u) (projT1 (Datatypes.fst x))) (b1 (efst u) (projT1 (Datatypes.fst x)))
                     (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))
                     ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 P))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 P)) (hj_irr h12 a1 a2 (proj1 (proj2 P)) (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET)
                     (coh1 (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (Hg1 a1 (efst u) (projT1 (Datatypes.fst x))))
                     (coh3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))))
                     (fun v0 w0 => (proj2 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                                     HIR HIR (Hg1 a1 (efst u) (projT1 (Datatypes.fst x)))
                                     (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) ((proj1 (proj2 (proj2 R))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))
                   (ex_intro _ (proj1 (proj2 R)) (hj_irr h13 a1 a3 (proj1 (proj2 R)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))))) v0 w0)
                     (fun v0 y0 => iL3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (Hg3 a3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) v0 y0
                                     (Hg3 _ _ _))
                     (esnd u) (projT2 (Datatypes.fst x)) (projT2 (Datatypes.fst x))
                     (Hs1 (b1 (efst u) (projT1 (Datatypes.fst x))) _ _ _ _
                        (iL1 (efst u) (projT1 (Datatypes.fst x)) (Hg1 a1 (efst u) (projT1 (Datatypes.fst x))) (esnd u) (projT2 (Datatypes.fst x))
                           (Hg1 _ _ _)))) |].
        eapply (Ht3 (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))));
          [ apply (hj_to_eq h23 (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (b3 (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x)))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET) _ _ _ _
                     (Hs2 (b2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) _ _ _ _
                        (iL2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (Hg2 a2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (esnd u) _
                           (Hg2 _ _ _)))) |].
        apply ((proj2 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h23 a2 a3 (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))
                 HET (ex_intro _ (proj1 (proj2 Q)) (hj_irr h23 a2 a3 (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))))
                 (Hg2 a2 (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x)))) (tfun a1 a2 a3 (proj1 (proj2 P)) (proj1 (proj2 Q)) (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h13 a1 a3 (proj1 (proj2 R)) (efst u) (projT1 (Datatypes.fst x))) HET) ((proj1 (proj2 (proj2 Q))) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h23 a2 a3 (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))
                   (ex_intro _ (proj1 (proj2 Q)) (hj_irr h23 a2 a3 (proj1 (proj2 Q)) (proj1 (proj2 Q)) (efst u) (hj_to h12 a1 a2 (proj1 (proj2 P)) (efst u) (projT1 (Datatypes.fst x))))))).
    - destruct x.
  Qed.
End TransRefine.

Section Level2.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).
  Local Notation Ust_ := (Ust Univ UnivEq UnivOK).
  Local Notation hj_ := (hj Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation hjU_ := (hjU Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation sgood_ := (sgood Univ UnivEq UnivOK).
  Local Notation ssym_ := (ssym Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).
  Local Notation strans_ := (strans Univ UnivEq UnivOK UnivEq_sym UnivEq_trans).

  Definition TransRel (a b c : Ord) : Prop :=
    forall (s : (stage_ a).(St)) (s' : (stage_ b).(St)) (s'' : (stage_ c).(St)),
      hj_rel (hj_ a b) s s' -> hj_rel (hj_ b c) s' s'' -> hj_rel (hj_ a c) s s''.

  Definition TransTo (a b c : Ord) : Prop :=
    forall (s : (stage_ a).(St)) (s' : (stage_ b).(St)) (s'' : (stage_ c).(St))
           (P : hj_rel (hj_ a b) s s') (Q : hj_rel (hj_ b c) s' s'')
           (R : hj_rel (hj_ a c) s s'') u x,
      (stage_ c).(StEq) s'' u (hj_to (hj_ a c) s s'' R u x)
                          u (hj_to (hj_ b c) s' s'' Q u (hj_to (hj_ a b) s s' P u x)).

  Definition TransP (a b c : Ord) : Prop := TransRel a b c /\ TransTo a b c.

  Lemma transNode b1 b2 b3 : TransP b1 b2 b3 ->
    (forall (c1 : (Ust_ b1).(St)) (c2 : (Ust_ b2).(St)) (c3 : (Ust_ b3).(St)),
       hj_rel (hjU_ b1 b2) c1 c2 -> hj_rel (hjU_ b2 b3) c2 c3 -> hj_rel (hjU_ b1 b3) c1 c3)
    /\ (forall (c1 : (Ust_ b1).(St)) (c2 : (Ust_ b2).(St)) (c3 : (Ust_ b3).(St))
               (P : hj_rel (hjU_ b1 b2) c1 c2) (Q : hj_rel (hjU_ b2 b3) c2 c3)
               (R : hj_rel (hjU_ b1 b3) c1 c3) u y,
          (Ust_ b3).(StEq) c3 u (hj_to (hjU_ b1 b3) c1 c3 R u y)
                             u (hj_to (hjU_ b2 b3) c2 c3 Q u
                                  (hj_to (hjU_ b1 b2) c1 c2 P u y))).
  Proof.
    intros [TR TT]; split.
    - intros c1 c2 c3.
      apply (isoRefine_trans (stage_ b1) (stage_ b2) (stage_ b3) UnivOK
               (hj_ b1 b2) (hj_ b2 b3) (hj_ b1 b3) TR TT (sgood_ b2)
               (ssym_ b3) (strans_ b3) (projT2 c1) (projT2 c2) (projT2 c3)).
    - intros c1 c2 c3 P Q R u y.
      apply (toRefine_fun (stage_ b1) (stage_ b2) (stage_ b3) Univ UnivEq UnivOK
               (hj_ b1 b2) (hj_ b2 b3) (hj_ b1 b3) TT
               (sgood_ b1) (sgood_ b2) (sgood_ b3)
               (ssym_ b1) (strans_ b1) (ssym_ b2) (strans_ b2) (ssym_ b3) (strans_ b3)
               (projT2 c1) (projT2 c2) (projT2 c3) P Q R u (proj1_sig y) (proj2_sig y)).
  Qed.

  Lemma hj_transP : forall a b c, TransP a b c.
  Proof.
    induction a as [| ba IHa | Ta fa IHa].
    - intros b c; split; [intros [] | intros []].
    - intros b; induction b as [| bb IHb | Tb fb IHb].
      + intros c; split; [intros s [] | intros s []].
      + intros c; induction c as [| bc IHc | Tc fc IHc].
        * split; [intros s s' [] | intros s s' []].
        * (* S S S *)
          split.
          -- intros [ca|sa] [cb|sb] [cc|sc].
             ++ exact (proj1 (transNode ba bb bc (IHa bb bc)) ca cb cc).
             ++ exact (proj1 IHc (inl ca) (inl cb) sc).
             ++ exact (proj1 (IHb (osucc bc)) (inl ca) sb (inl cc)).
             ++ exact (proj1 (IHb bc) (inl ca) sb sc).
             ++ exact (proj1 (IHa (osucc bb) (osucc bc)) sa (inl cb) (inl cc)).
             ++ exact (proj1 (IHa (osucc bb) bc) sa (inl cb) sc).
             ++ exact (proj1 (IHa bb (osucc bc)) sa sb (inl cc)).
             ++ exact (proj1 (IHa bb bc) sa sb sc).
          -- intros [ca|sa] [cb|sb] [cc|sc].
             ++ exact (proj2 (transNode ba bb bc (IHa bb bc)) ca cb cc).
             ++ exact (proj2 IHc (inl ca) (inl cb) sc).
             ++ exact (proj2 (IHb (osucc bc)) (inl ca) sb (inl cc)).
             ++ exact (proj2 (IHb bc) (inl ca) sb sc).
             ++ exact (proj2 (IHa (osucc bb) (osucc bc)) sa (inl cb) (inl cc)).
             ++ exact (proj2 (IHa (osucc bb) bc) sa (inl cb) sc).
             ++ exact (proj2 (IHa bb (osucc bc)) sa sb (inl cc)).
             ++ exact (proj2 (IHa bb bc) sa sb sc).
        * (* S S P *)
          split.
          -- intros [ca|sa] [cb|sb] [pc [cc|sc]].
             ++ exact (proj1 (transNode ba bb (fc pc) (IHa bb (fc pc))) ca cb cc).
             ++ exact (proj1 (IHc pc) (inl ca) (inl cb) sc).
             ++ exact (proj1 (IHb (osup Tc fc)) (inl ca) sb (existT _ pc (inl cc))).
             ++ exact (proj1 (IHb (fc pc)) (inl ca) sb sc).
             ++ exact (proj1 (IHa (osucc bb) (osup Tc fc)) sa (inl cb) (existT _ pc (inl cc))).
             ++ exact (proj1 (IHa (osucc bb) (fc pc)) sa (inl cb) sc).
             ++ exact (proj1 (IHa bb (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj1 (IHa bb (fc pc)) sa sb sc).
          -- intros [ca|sa] [cb|sb] [pc [cc|sc]].
             ++ exact (proj2 (transNode ba bb (fc pc) (IHa bb (fc pc))) ca cb cc).
             ++ exact (proj2 (IHc pc) (inl ca) (inl cb) sc).
             ++ exact (proj2 (IHb (osup Tc fc)) (inl ca) sb (existT _ pc (inl cc))).
             ++ exact (proj2 (IHb (fc pc)) (inl ca) sb sc).
             ++ exact (proj2 (IHa (osucc bb) (osup Tc fc)) sa (inl cb) (existT _ pc (inl cc))).
             ++ exact (proj2 (IHa (osucc bb) (fc pc)) sa (inl cb) sc).
             ++ exact (proj2 (IHa bb (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj2 (IHa bb (fc pc)) sa sb sc).
      + intros c; induction c as [| bc IHc | Tc fc IHc].
        * split; [intros s s' [] | intros s s' []].
        * (* S P S *)
          split.
          -- intros [ca|sa] [pb [cb|sb]] [cc|sc].
             ++ exact (proj1 (transNode ba (fb pb) bc (IHa (fb pb) bc)) ca cb cc).
             ++ exact (proj1 IHc (inl ca) (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHb pb) (osucc bc)) (inl ca) sb (inl cc)).
             ++ exact (proj1 ((IHb pb) bc) (inl ca) sb sc).
             ++ exact (proj1 (IHa (osup Tb fb) (osucc bc)) sa (existT _ pb (inl cb)) (inl cc)).
             ++ exact (proj1 (IHa (osup Tb fb) bc) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj1 (IHa (fb pb) (osucc bc)) sa sb (inl cc)).
             ++ exact (proj1 (IHa (fb pb) bc) sa sb sc).
          -- intros [ca|sa] [pb [cb|sb]] [cc|sc].
             ++ exact (proj2 (transNode ba (fb pb) bc (IHa (fb pb) bc)) ca cb cc).
             ++ exact (proj2 IHc (inl ca) (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHb pb) (osucc bc)) (inl ca) sb (inl cc)).
             ++ exact (proj2 ((IHb pb) bc) (inl ca) sb sc).
             ++ exact (proj2 (IHa (osup Tb fb) (osucc bc)) sa (existT _ pb (inl cb)) (inl cc)).
             ++ exact (proj2 (IHa (osup Tb fb) bc) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj2 (IHa (fb pb) (osucc bc)) sa sb (inl cc)).
             ++ exact (proj2 (IHa (fb pb) bc) sa sb sc).
        * (* S P P *)
          split.
          -- intros [ca|sa] [pb [cb|sb]] [pc [cc|sc]].
             ++ exact (proj1 (transNode ba (fb pb) (fc pc) (IHa (fb pb) (fc pc))) ca cb cc).
             ++ exact (proj1 (IHc pc) (inl ca) (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHb pb) (osup Tc fc)) (inl ca) sb (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHb pb) (fc pc)) (inl ca) sb sc).
             ++ exact (proj1 (IHa (osup Tb fb) (osup Tc fc)) sa (existT _ pb (inl cb)) (existT _ pc (inl cc))).
             ++ exact (proj1 (IHa (osup Tb fb) (fc pc)) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj1 (IHa (fb pb) (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj1 (IHa (fb pb) (fc pc)) sa sb sc).
          -- intros [ca|sa] [pb [cb|sb]] [pc [cc|sc]].
             ++ exact (proj2 (transNode ba (fb pb) (fc pc) (IHa (fb pb) (fc pc))) ca cb cc).
             ++ exact (proj2 (IHc pc) (inl ca) (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHb pb) (osup Tc fc)) (inl ca) sb (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHb pb) (fc pc)) (inl ca) sb sc).
             ++ exact (proj2 (IHa (osup Tb fb) (osup Tc fc)) sa (existT _ pb (inl cb)) (existT _ pc (inl cc))).
             ++ exact (proj2 (IHa (osup Tb fb) (fc pc)) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj2 (IHa (fb pb) (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj2 (IHa (fb pb) (fc pc)) sa sb sc).
    - intros b; induction b as [| bb IHb | Tb fb IHb].
      + intros c; split; [intros s [] | intros s []].
      + intros c; induction c as [| bc IHc | Tc fc IHc].
        * split; [intros s s' [] | intros s s' []].
        * (* P S S *)
          split.
          -- intros [pa [ca|sa]] [cb|sb] [cc|sc].
             ++ exact (proj1 (transNode (fa pa) bb bc ((IHa pa) bb bc)) ca cb cc).
             ++ exact (proj1 IHc (existT _ pa (inl ca)) (inl cb) sc).
             ++ exact (proj1 (IHb (osucc bc)) (existT _ pa (inl ca)) sb (inl cc)).
             ++ exact (proj1 (IHb bc) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj1 ((IHa pa) (osucc bb) (osucc bc)) sa (inl cb) (inl cc)).
             ++ exact (proj1 ((IHa pa) (osucc bb) bc) sa (inl cb) sc).
             ++ exact (proj1 ((IHa pa) bb (osucc bc)) sa sb (inl cc)).
             ++ exact (proj1 ((IHa pa) bb bc) sa sb sc).
          -- intros [pa [ca|sa]] [cb|sb] [cc|sc].
             ++ exact (proj2 (transNode (fa pa) bb bc ((IHa pa) bb bc)) ca cb cc).
             ++ exact (proj2 IHc (existT _ pa (inl ca)) (inl cb) sc).
             ++ exact (proj2 (IHb (osucc bc)) (existT _ pa (inl ca)) sb (inl cc)).
             ++ exact (proj2 (IHb bc) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj2 ((IHa pa) (osucc bb) (osucc bc)) sa (inl cb) (inl cc)).
             ++ exact (proj2 ((IHa pa) (osucc bb) bc) sa (inl cb) sc).
             ++ exact (proj2 ((IHa pa) bb (osucc bc)) sa sb (inl cc)).
             ++ exact (proj2 ((IHa pa) bb bc) sa sb sc).
        * (* P S P *)
          split.
          -- intros [pa [ca|sa]] [cb|sb] [pc [cc|sc]].
             ++ exact (proj1 (transNode (fa pa) bb (fc pc) ((IHa pa) bb (fc pc))) ca cb cc).
             ++ exact (proj1 (IHc pc) (existT _ pa (inl ca)) (inl cb) sc).
             ++ exact (proj1 (IHb (osup Tc fc)) (existT _ pa (inl ca)) sb (existT _ pc (inl cc))).
             ++ exact (proj1 (IHb (fc pc)) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj1 ((IHa pa) (osucc bb) (osup Tc fc)) sa (inl cb) (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHa pa) (osucc bb) (fc pc)) sa (inl cb) sc).
             ++ exact (proj1 ((IHa pa) bb (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHa pa) bb (fc pc)) sa sb sc).
          -- intros [pa [ca|sa]] [cb|sb] [pc [cc|sc]].
             ++ exact (proj2 (transNode (fa pa) bb (fc pc) ((IHa pa) bb (fc pc))) ca cb cc).
             ++ exact (proj2 (IHc pc) (existT _ pa (inl ca)) (inl cb) sc).
             ++ exact (proj2 (IHb (osup Tc fc)) (existT _ pa (inl ca)) sb (existT _ pc (inl cc))).
             ++ exact (proj2 (IHb (fc pc)) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj2 ((IHa pa) (osucc bb) (osup Tc fc)) sa (inl cb) (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHa pa) (osucc bb) (fc pc)) sa (inl cb) sc).
             ++ exact (proj2 ((IHa pa) bb (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHa pa) bb (fc pc)) sa sb sc).
      + intros c; induction c as [| bc IHc | Tc fc IHc].
        * split; [intros s s' [] | intros s s' []].
        * (* P P S *)
          split.
          -- intros [pa [ca|sa]] [pb [cb|sb]] [cc|sc].
             ++ exact (proj1 (transNode (fa pa) (fb pb) bc ((IHa pa) (fb pb) bc)) ca cb cc).
             ++ exact (proj1 IHc (existT _ pa (inl ca)) (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHb pb) (osucc bc)) (existT _ pa (inl ca)) sb (inl cc)).
             ++ exact (proj1 ((IHb pb) bc) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj1 ((IHa pa) (osup Tb fb) (osucc bc)) sa (existT _ pb (inl cb)) (inl cc)).
             ++ exact (proj1 ((IHa pa) (osup Tb fb) bc) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHa pa) (fb pb) (osucc bc)) sa sb (inl cc)).
             ++ exact (proj1 ((IHa pa) (fb pb) bc) sa sb sc).
          -- intros [pa [ca|sa]] [pb [cb|sb]] [cc|sc].
             ++ exact (proj2 (transNode (fa pa) (fb pb) bc ((IHa pa) (fb pb) bc)) ca cb cc).
             ++ exact (proj2 IHc (existT _ pa (inl ca)) (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHb pb) (osucc bc)) (existT _ pa (inl ca)) sb (inl cc)).
             ++ exact (proj2 ((IHb pb) bc) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj2 ((IHa pa) (osup Tb fb) (osucc bc)) sa (existT _ pb (inl cb)) (inl cc)).
             ++ exact (proj2 ((IHa pa) (osup Tb fb) bc) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHa pa) (fb pb) (osucc bc)) sa sb (inl cc)).
             ++ exact (proj2 ((IHa pa) (fb pb) bc) sa sb sc).
        * (* P P P *)
          split.
          -- intros [pa [ca|sa]] [pb [cb|sb]] [pc [cc|sc]].
             ++ exact (proj1 (transNode (fa pa) (fb pb) (fc pc) ((IHa pa) (fb pb) (fc pc))) ca cb cc).
             ++ exact (proj1 (IHc pc) (existT _ pa (inl ca)) (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHb pb) (osup Tc fc)) (existT _ pa (inl ca)) sb (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHb pb) (fc pc)) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj1 ((IHa pa) (osup Tb fb) (osup Tc fc)) sa (existT _ pb (inl cb)) (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHa pa) (osup Tb fb) (fc pc)) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj1 ((IHa pa) (fb pb) (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj1 ((IHa pa) (fb pb) (fc pc)) sa sb sc).
          -- intros [pa [ca|sa]] [pb [cb|sb]] [pc [cc|sc]].
             ++ exact (proj2 (transNode (fa pa) (fb pb) (fc pc) ((IHa pa) (fb pb) (fc pc))) ca cb cc).
             ++ exact (proj2 (IHc pc) (existT _ pa (inl ca)) (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHb pb) (osup Tc fc)) (existT _ pa (inl ca)) sb (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHb pb) (fc pc)) (existT _ pa (inl ca)) sb sc).
             ++ exact (proj2 ((IHa pa) (osup Tb fb) (osup Tc fc)) sa (existT _ pb (inl cb)) (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHa pa) (osup Tb fb) (fc pc)) sa (existT _ pb (inl cb)) sc).
             ++ exact (proj2 ((IHa pa) (fb pb) (osup Tc fc)) sa sb (existT _ pc (inl cc))).
             ++ exact (proj2 ((IHa pa) (fb pb) (fc pc)) sa sb sc).
  Qed.

  Lemma ciso_trans {b1 b2 b3} (c1 : U Univ UnivEq UnivOK b1) (c2 : U Univ UnivEq UnivOK b2)
    (c3 : U Univ UnivEq UnivOK b3) :
    ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c2 ->
    ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c2 c3 ->
    ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c3.
  Proof. exact (proj1 (transNode b1 b2 b3 (hj_transP b1 b2 b3)) c1 c2 c3). Qed.

  Lemma cto_fun {b1 b2 b3} (c1 : U Univ UnivEq UnivOK b1) (c2 : U Univ UnivEq UnivOK b2)
    (c3 : U Univ UnivEq UnivOK b3)
    (P : ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c2)
    (Q : ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c2 c3)
    (R : ciso Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c3) u x :
    (Ust_ b3).(StEq) c3 u (cto Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c3 R u x)
                        u (cto Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c2 c3 Q u
                             (cto Univ UnivEq UnivOK UnivEq_sym UnivEq_trans c1 c2 P u x)).
  Proof. exact (proj2 (transNode b1 b2 b3 (hj_transP b1 b2 b3)) c1 c2 c3 P Q R u x). Qed.
End Level2.
