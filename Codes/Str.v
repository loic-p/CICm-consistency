From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.Eq Codes.WF Codes.Sym.
From Stdlib Require Import Arith Lia.

(* Transitivity, the coercion and its coherence.

   These three cannot be separated.  At a Pi code, chaining a (1,2)-equality
   with a (2,3)-equality needs an argument of the MIDDLE domain related to the
   two given ones, and the only way to produce one is to coerce; while the
   coercion of a function has to be shown extensional, which is a
   transitivity one stage down.  So all of it is one bundle, built by one
   recursion -- as `cast_lemmas_conclusion` is in the setoid universe.

   The third stage of transitivity is a PARAMETER here and is universally
   quantified in the bundle of Codes/Str.v's Level section, so the recursion
   stays double.  Symmetry is not part of the bundle: Codes/Sym.v proves it
   for every pair, with no coercion and no well-formedness. *)

Ltac dA r := destruct r as [Ta eva | Ta eva | Ta pa eva Pa | Ta ma oka eva
                | Ta A0a B0a eva aa eaa aeqa ba eba beqa
                | Ta A0a B0a eva aa eaa ba eba
                | Ta A0a B0a eva aa eaa aeqa ba eba beqa].
Ltac dB r := destruct r as [Tb evb | Tb evb | Tb pb evb Pb | Tb mb okb evb
                | Tb A0b B0b evb ab eab aeqb bb ebb beqb
                | Tb A0b B0b evb ab eab bb ebb
                | Tb A0b B0b evb ab eab aeqb bb ebb beqb].
Ltac dC r := destruct r as [Tc evc | Tc evc | Tc pc evc Pc | Tc mc okc evc
                | Tc A0c B0c evc ac eac aeqc bc ebc beqc
                | Tc A0c B0c evc ac eac bc ebc
                | Tc A0c B0c evc ac eac aeqc bc ebc beqc].

(* The tree relation is transitive.  The middle BRANCH has to be produced --
   the branch conditions of the two given relations quantify over related
   branches of different codes -- which is where the coercion is spent. *)
Lemma WRel_trans {st1 st2 st3 : Stage} (T1 T2 T3 : etm)
  (a1 : St st1) (a2 : St st2) (a3 : St st3)
  (b1 : forall u, StEl st1 a1 u -> St st1) (b2 : forall u, StEl st2 a2 u -> St st2)
  (b3 : forall u, StEl st3 a3 u -> St st3)
  (R12l : forall u, StEl st1 a1 u -> forall u', StEl st2 a2 u' -> Prop)
  (R12b : forall u (x : StEl st1 a1 u) u' (x' : StEl st2 a2 u') v, StEl st1 (b1 u x) v ->
          forall v', StEl st2 (b2 u' x') v' -> Prop)
  (R23l : forall u, StEl st2 a2 u -> forall u', StEl st3 a3 u' -> Prop)
  (R23b : forall u (x : StEl st2 a2 u) u' (x' : StEl st3 a3 u') v, StEl st2 (b2 u x) v ->
          forall v', StEl st3 (b3 u' x') v' -> Prop)
  (R13l : forall u, StEl st1 a1 u -> forall u', StEl st3 a3 u' -> Prop)
  (R13b : forall u (x : StEl st1 a1 u) u' (x' : StEl st3 a3 u') v, StEl st1 (b1 u x) v ->
          forall v', StEl st3 (b3 u' x') v' -> Prop)
  (Hlab : forall u x u' x' u'' x'', R12l u x u' x' -> R23l u' x' u'' x'' -> R13l u x u'' x'')
  (* the middle branch, and the two relations it satisfies *)
  (mid : forall u x u' x' v (y : StEl st1 (b1 u x) v), R12l u x u' x' -> StEl st2 (b2 u' x') v)
  (mid12 : forall u x u' x' v y (e : R12l u x u' x'),
      R12b u x u' x' v y v (mid u x u' x' v y e))
  (mid23 : forall u x u' x' u'' x'' v y v'' y'' (e : R12l u x u' x') (e' : R23l u' x' u'' x''),
      R13b u x u'' x'' v y v'' y'' -> R23b u' x' u'' x'' v (mid u x u' x' v y e) v'' y'')
  (Hbr : forall u x u' x' u'' x'' (e : R12l u x u' x') (e' : R23l u' x' u'' x'')
                v y v' y' v'' y'',
      R12b u x u' x' v y v' y' -> R23b u' x' u'' x'' v' y' v'' y'' ->
      R13b u x u'' x'' v y v'' y'')
  {w1} (t1 : WEl T1 a1 b1 w1) : forall {w2} (t2 : WEl T2 a2 b2 w2) {w3} (t3 : WEl T3 a3 b3 w3),
  WRel T1 T2 a1 a2 b1 b2 R12l R12b t1 t2 -> WRel T2 T3 a2 a3 b2 b3 R23l R23b t2 t3 ->
  WRel T1 T3 a1 a3 b1 b3 R13l R13b t1 t3.
Proof.
  induction t1 as [w1 u1 x1 f1 ev1 gd1 sub1 IH]; intros w2 t2 w3 t3.
  destruct t2 as [w2 u2 x2 f2 ev2 gd2 sub2].
  destruct t3 as [w3 u3 x3 f3 ev3 gd3 sub3]; cbn.
  intros [Hl12 Hs12] [Hl23 Hs23]; split.
  - eapply Hlab; eassumption.
  - intros v1 y1 v3 y3 Hr13.
    pose (y2 := mid u1 x1 u2 x2 v1 y1 Hl12).
    apply (IH v1 y1 _ (sub2 v1 y2) _ (sub3 v3 y3)).
    + apply Hs12, mid12.
    + apply Hs23. eapply mid23; [exact Hl23 | exact Hr13].
Qed.

(* The tree relation is monotone in the label relation and ANTItone in the
   branch relation, which is how the carried relations of a W code and the
   canonical ones are exchanged. *)
Lemma WRel_mono {st st' : Stage} (T T' : etm) (a : St st) (a' : St st')
  (b : forall u, StEl st a u -> St st) (b' : forall u, StEl st' a' u -> St st')
  (Rl Rl' : forall u, StEl st a u -> forall u', StEl st' a' u' -> Prop)
  (Rb Rb' : forall u (x : StEl st a u) u' (x' : StEl st' a' u') v, StEl st (b u x) v ->
            forall v', StEl st' (b' u' x') v' -> Prop)
  (Hl : forall u x u' x', Rl u x u' x' -> Rl' u x u' x')
  (Hb : forall u x u' x' v y v' y', Rb' u x u' x' v y v' y' -> Rb u x u' x' v y v' y')
  {w} (t : WEl T a b w) : forall {w'} (t' : WEl T' a' b' w'),
  WRel T T' a a' b b' Rl Rb t t' -> WRel T T' a a' b b' Rl' Rb' t t'.
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hlab Hsub]; split; [apply Hl; exact Hlab |].
  intros v y v' y' Hy; apply (IH v y), Hsub, Hb, Hy.
Qed.

(* ------------------------------------------------------------------ *)
(* Transitivity at one node against another, with the third stage a    *)
(* parameter.                                                          *)
(* ------------------------------------------------------------------ *)

Section TransNode.
Context (st1 st2 st3 : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (c12 : Cmp st1 st2) (c23 : Cmp st2 st3) (c13 : Cmp st1 st3) (c21 : Cmp st2 st1).
Context (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop) (wf3 : St st3 -> Prop).
Context (d1 : Cmp st1 st1) (d2 : Cmp st2 st2) (d3 : Cmp st3 st3).

(* symmetry of the comparison, from Codes/Sym.v *)
Context (symU12 : forall s1 s2, cU c12 s1 s2 -> cU c21 s2 s1)
        (sym12 : forall s1 u x s2 u' x',
            cEl c12 s1 u x s2 u' x' -> cEl c21 s2 u' x' s1 u x).
(* the bundles one stage down *)
Context (LtrU123 : forall s1 s2 s3, wf1 s1 -> wf2 s2 -> wf3 s3 ->
            cU c12 s1 s2 -> cU c23 s2 s3 -> cU c13 s1 s3)
        (LtrE123 : forall s1 s2 s3 u x u' x' u'' x'', wf1 s1 -> wf2 s2 -> wf3 s3 ->
            cU c12 s1 s2 -> cEl c12 s1 u x s2 u' x' -> cEl c23 s2 u' x' s3 u'' x'' ->
            cEl c13 s1 u x s3 u'' x'')
        (LtrU213 : forall s2 s1 s3, wf2 s2 -> wf1 s1 -> wf3 s3 ->
            cU c21 s2 s1 -> cU c13 s1 s3 -> cU c23 s2 s3)
        (LtrE213 : forall s2 s1 s3 u x u' x' u'' x'', wf2 s2 -> wf1 s1 -> wf3 s3 ->
            cU c21 s2 s1 -> cEl c21 s2 u x s1 u' x' -> cEl c13 s1 u' x' s3 u'' x'' ->
            cEl c23 s2 u x s3 u'' x'')
        (Lto : forall s1 s2, wf1 s1 -> wf2 s2 -> cU c12 s1 s2 ->
            forall u, StEl st1 s1 u -> StEl st2 s2 u)
        (LtoCoh : forall s1 s2 w1 w2 (e : cU c12 s1 s2) u x,
            cEl c12 s1 u x s2 u (Lto s1 s2 w1 w2 e u x)).
Context (UEtrans : forall m u x m' u' x' m'' u'' x'',
            UnivEq m u x m' u' x' -> UnivEq m' u' x' m'' u'' x'' ->
            UnivEq m u x m'' u'' x'').

Ltac dest3 r := destruct r as [?T ?e | ?T ?e | ?T ?p ?e ?P0 | ?T ?m ?ok ?e
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq
                | ?T ?A1 ?B1 ?e ?a ?ea ?b ?eb
                | ?T ?A1 ?B1 ?e ?a ?ea ?aeq ?b ?eb ?beq].

Lemma eqU_trans {T1 T2 T3} (r1 : Refine st1 UnivOK T1) (r2 : Refine st2 UnivOK T2)
  (r3 : Refine st3 UnivOK T3) :
  wfRefine d1 wf1 r1 -> wfRefine d2 wf2 r2 -> wfRefine d3 wf3 r3 ->
  eqU c12 r1 r2 -> eqU c23 r2 r3 -> eqU c13 r1 r3.
Proof.
  dest3 r1; dest3 r2; cbn;
    try (exact (fun _ _ _ H => match H with end));
  dest3 r3; cbn;
    try (exact (fun _ _ _ _ H => match H with end));
  intros W1 W2 W3.
  (* nat, prop *)
  1,2: intros H1 H2; eapply tyeq_trans; eassumption.
  (* prf *)
  1: intros [H1 H1'] [H2 H2']; split;
       [eapply tyeq_trans; eassumption | eapply iff_trans; eassumption].
  (* univ *)
  1: intros [H1 H1'] [H2 H2']; split;
       [eapply tyeq_trans; eassumption | eapply eq_trans; eassumption].
  (* pi, sig, w: the same three conjuncts and the same proof *)
  all: intros [T12 [A12 B12]] [T23 [A23 B23]];
    destruct W1 as [[WA1 [WB1 _]] _]; destruct W2 as [[WA2 [WB2 _]] _];
    destruct W3 as [[WA3 [WB3 _]] _];
    split; [eapply tyeq_trans; eassumption |];
    split; [eapply LtrU123; eassumption |];
    intros u x u'' x'' r;
    (* the middle argument, and its two relations *)
    pose proof (LtoCoh _ _ WA1 WA2 A12 u x) as Hm;
    eapply LtrU123;
      [ apply WB1 | apply WB2 | apply WB3
      | apply B12; exact Hm
      | apply B23; eapply LtrE213;
          [ exact WA2 | exact WA1 | exact WA3 | apply symU12; exact A12
          | apply sym12; exact Hm | exact r ] ].
Qed.


Lemma eqEl_trans {T1 T2 T3} (r1 : Refine st1 UnivOK T1) (r2 : Refine st2 UnivOK T2)
  (r3 : Refine st3 UnivOK T3) u1 x1 u2 x2 u3 x3 :
  wfRefine d1 wf1 r1 -> wfRefine d2 wf2 r2 -> wfRefine d3 wf3 r3 ->
  eqU c12 r1 r2 ->
  eqEl c12 UnivEq r1 r2 u1 x1 u2 x2 -> eqEl c23 UnivEq r2 r3 u2 x2 u3 x3 ->
  eqEl c13 UnivEq r1 r3 u1 x1 u3 x3.
Proof.
  revert x1 x2 x3; dA r1; dB r2; cbn; intros x1 x2 x3;
    try (exact (fun _ _ _ H => match H with end));
  revert x3; dC r3; cbn; intros x3;
    try (exact (fun _ _ _ _ _ H => match H with end));
  intros W1 W2 W3 EU.
  (* nat *)
  - intros [H1 [H2 H3]] [H1' [H2' H3']]; split; [eapply eq_trans; eassumption |].
    split; [eapply tyeq_trans; eassumption |].
    eapply Rel_trans; [exact H3 |].
    eapply Rel_tyeq; [apply tyeq_sym; exact H2 | exact H3'].
  (* prop *)
  - intros [H1 [H2 H3]] [H1' [H2' H3']]; split; [eapply iff_trans; eassumption |].
    split; [eapply tyeq_trans; eassumption |].
    eapply Rel_trans; [exact H3 |].
    eapply Rel_tyeq; [apply tyeq_sym; exact H2 | exact H3'].
  (* prf *)
  - intros [H2 H3] [H2' H3']; split; [eapply tyeq_trans; eassumption |].
    eapply Rel_trans; [exact H3 |].
    eapply Rel_tyeq; [apply tyeq_sym; exact H2 | exact H3'].
  (* univ *)
  - intros [H1 H2] [H1' H2']; split;
      [eapply UEtrans; eassumption | eapply tyeq_trans; eassumption].
  (* pi *)
  - destruct W1 as [[WA1 [WB1 _]] _]; destruct W2 as [[WA2 [WB2 _]] _];
      destruct W3 as [[WA3 [WB3 _]] _]; destruct EU as [_ [A12 B12]].
    intros [F12 [tyF12 R12]] [F23 [tyF23 R23]]; split.
    + intros w x w'' x'' r.
      pose proof (LtoCoh _ _ WA1 WA2 A12 w x) as Hm.
      eapply LtrE123;
        [ apply WB1 | apply WB2 | apply WB3
        | apply B12; exact Hm
        | apply F12; exact Hm
        | apply F23; eapply LtrE213;
            [ exact WA2 | exact WA1 | exact WA3 | apply symU12; exact A12
            | apply sym12; exact Hm | exact r ] ].
    + split; [eapply tyeq_trans; eassumption |].
      eapply Rel_trans; [exact R12 |].
      eapply Rel_tyeq; [apply tyeq_sym; exact tyF12 | exact R23].
  (* sig: no middle element is needed, the arguments ARE the components *)
  - destruct W1 as [[WA1 [WB1 _]] _]; destruct W2 as [[WA2 [WB2 _]] _];
      destruct W3 as [[WA3 [WB3 _]] _]; destruct EU as [_ [A12 B12]].
    intros [P12 [Q12 [tyF12 R12]]] [P23 [Q23 [tyF23 R23]]].
    split; [eapply LtrE123; [exact WA1 | exact WA2 | exact WA3 | exact A12
                            | exact P12 | exact P23] |].
    split.
    + eapply LtrE123;
        [ apply WB1 | apply WB2 | apply WB3 | apply B12; exact P12
        | exact Q12 | exact Q23 ].
    + split; [eapply tyeq_trans; eassumption |].
      eapply Rel_trans; [exact R12 |].
      eapply Rel_tyeq; [apply tyeq_sym; exact tyF12 | exact R23].
  (* w *)
  - destruct W1 as [[WA1 [WB1 _]] _]; destruct W2 as [[WA2 [WB2 _]] _];
      destruct W3 as [[WA3 [WB3 _]] _]; destruct EU as [_ [A12 B12]].
    intros [H12 [tyF12 R12]] [H23 [tyF23 R23]]; split.
    + unshelve eapply (WRel_trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                         _ (fun w x w' x' v y e =>
                              Lto (ba w x) (bb w' x') (WB1 w x) (WB2 w' x')
                                  (B12 w x w' x' e) v y) _ _ _ _ _ _ H12 H23).
      * (* labels *)
        intros w x w' x' w'' x'' e e'.
        eapply LtrE123; [exact WA1 | exact WA2 | exact WA3 | exact A12
                        | exact e | exact e'].
      * (* the middle branch is related to the first *)
        intros w x w' x' v y e; apply LtoCoh.
      * (* and to the third *)
        intros w x w' x' w'' x'' v y v'' y'' e e' Hy.
        eapply LtrE213;
          [ apply WB2 | apply WB1 | apply WB3
          | apply symU12; apply B12; exact e
          | apply sym12; apply LtoCoh | exact Hy ].
      * (* the branches compose *)
        intros w x w' x' w'' x'' e e' v y v' y' v'' y'' Hy Hy'.
        eapply LtrE123;
          [ apply WB1 | apply WB2 | apply WB3 | apply B12; exact e
          | exact Hy | exact Hy' ].
    + split; [eapply tyeq_trans; eassumption |].
      eapply Rel_trans; [exact R12 |].
      eapply Rel_tyeq; [apply tyeq_sym; exact tyF12 | exact R23].
Qed.
End TransNode.

(* ------------------------------------------------------------------ *)
(* The coercion at one node into another, and its coherence.           *)
(*                                                                    *)
(* Every branch matches on the two CODES, which are data; the          *)
(* Prop-valued equality is consumed only by projecting conjunctions,   *)
(* by eliminating False at a shape mismatch, and by transporting along *)
(* the equality of two universe indices.  That is what lets a          *)
(* Type-valued coercion come out of a Prop-valued equality.            *)
(* ------------------------------------------------------------------ *)

Section CoeNode.
Context (st1 st2 : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (c12 : Cmp st1 st2) (c21 : Cmp st2 st1) (d1 : Cmp st1 st1) (d2 : Cmp st2 st2).
Context (wf1 : St st1 -> Prop) (wf2 : St st2 -> Prop).
Context (UErefl : forall m u x, UnivEq m u x m u x).
(* symmetry, from Codes/Sym.v *)
Context (sym12 : forall s u x s' u' x', cEl c12 s u x s' u' x' -> cEl c21 s' u' x' s u x).
(* the coercion one stage down, both ways, with its coherence and the fact
   that it respects the equality *)
Context (Lto : forall s s', wf1 s -> wf2 s' -> cU c12 s s' ->
            forall u, StEl st1 s u -> StEl st2 s' u)
        (LtoCoh : forall s s' w w' (e : cU c12 s s') u x,
            cEl c12 s u x s' u (Lto s s' w w' e u x))
        (Lfrom : forall s s', wf1 s -> wf2 s' -> cU c12 s s' ->
            forall u, StEl st2 s' u -> StEl st1 s u)
        (LfromCoh : forall s s' w w' (e : cU c12 s s') u y,
            cEl c12 s u (Lfrom s s' w w' e u y) s' u y)
        (LtoEq : forall s s' w w' (e : cU c12 s s') s0 s0' w0 w0' (e0 : cU c12 s0 s0')
                        u x u0 x0,
            cU d1 s s0 -> cEl d1 s u x s0 u0 x0 ->
            cEl d2 s' u (Lto s s' w w' e u x) s0' u0 (Lto s0 s0' w0 w0' e0 u0 x0)).
(* transitivity one stage down, in the three mixed forms that are needed *)
Context (Ltr_12_22 : forall s s' s0' u x u' x' u0 x0, wf1 s -> wf2 s' -> wf2 s0' ->
            cU c12 s s' -> cEl c12 s u x s' u' x' -> cEl d2 s' u' x' s0' u0 x0 ->
            cEl c12 s u x s0' u0 x0)
        (Ltr_12_21 : forall s s' s0 u x u' x' u0 x0, wf1 s -> wf2 s' -> wf1 s0 ->
            cU c12 s s' -> cEl c12 s u x s' u' x' -> cEl c21 s' u' x' s0 u0 x0 ->
            cEl d1 s u x s0 u0 x0)
        (* the diagonal code equality of a well-formed code *)
        (Lself : forall s, wf1 s -> cU d1 s s).

(* ---- the tree coercion ---- *)
Section Wcoe.
Context (T1 T2 : etm) (a1 : St st1) (a2 : St st2)
        (b1 : forall u, StEl st1 a1 u -> St st1) (b2 : forall u, StEl st2 a2 u -> St st2)
        (wa1 : wf1 a1) (wa2 : wf2 a2)
        (wb1 : forall u x, wf1 (b1 u x)) (wb2 : forall u x, wf2 (b2 u x))
        (eA : cU c12 a1 a2)
        (eB : forall u x u' x', cEl c12 a1 u x a2 u' x' -> cU c12 (b1 u x) (b2 u' x'))
        (ety : tyeq T1 T2).

(* the label's image, and the code equality of the two branch families it
   induces -- named because the tree recursion mentions them at every node *)
Definition lab (u0 : etm) (x : StEl st1 a1 u0) : StEl st2 a2 u0 := Lto a1 a2 wa1 wa2 eA u0 x.

Definition brE (u0 : etm) (x : StEl st1 a1 u0) : cU c12 (b1 u0 x) (b2 u0 (lab u0 x)) :=
  eB u0 x u0 (lab u0 x) (LtoCoh a1 a2 wa1 wa2 eA u0 x).

Fixpoint Wto {w} (t : WEl T1 a1 b1 w) : WEl T2 a2 b2 w :=
  match t with
  | wel_sup w u0 x f ev gd sub =>
      wel_sup w u0 (lab u0 x) f ev (Good_tyeq _ _ _ ety gd)
        (fun v y => Wto (sub v (Lfrom (b1 u0 x) (b2 u0 (lab u0 x))
                                  (wb1 u0 x) (wb2 u0 (lab u0 x)) (brE u0 x) v y)))
  end.

Notation Rlab12 := (fun u x u' x' => cEl c12 a1 u x a2 u' x').
Notation Rbr12 := (fun u x u' x' v y v' y' => cEl c12 (b1 u x) v y (b2 u' x') v' y').
Notation Rlab11 := (fun u x u' x' => cEl d1 a1 u x a1 u' x').
Notation Rbr11 := (fun u x u' x' v y v' y' => cEl d1 (b1 u x) v y (b1 u' x') v' y').
Notation Rlab22 := (fun u x u' x' => cEl d2 a2 u x a2 u' x').
Notation Rbr22 := (fun u x u' x' v y v' y' => cEl d2 (b2 u x) v y (b2 u' x') v' y').

(* The coherence, generalised: the coercion of anything related to t is
   related to t.  At t' := t this is "t is related to its own coercion", and
   the generalisation is what makes the induction go through -- the branches of
   t and of the coerced tree are indexed differently. *)
Lemma Wto_coh {w} (t : WEl T1 a1 b1 w) :
  forall {w'} (t' : WEl T1 a1 b1 w'),
  WRel T1 T1 a1 a1 b1 b1 Rlab11 Rbr11 t t' ->
  WRel T1 T2 a1 a2 b1 b2 Rlab12 Rbr12 t (Wto t').
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hl Hs].
  (* the label of t and the label of the coerced t' *)
  assert (Hlab : cEl c12 a1 u0 x a2 u0' (lab u0' x')).
  { eapply Ltr_12_22;
      [ exact wa1 | exact wa2 | exact wa2 | exact eA | apply LtoCoh
      | apply (LtoEq a1 a2 wa1 wa2 eA a1 a2 wa1 wa2 eA);
          [apply Lself; exact wa1 | exact Hl] ]. }
  split; [exact Hlab |].
  intros v y v'' y'' Hy.
  apply (IH v y).
  apply Hs.
  eapply Ltr_12_21;
    [ apply wb1 | apply wb2 | apply wb1 | apply eB; exact Hlab | exact Hy
    | apply sym12, LfromCoh ].
Qed.

(* And the coercion respects the equality: same induction. *)
Lemma Wto_eq {w} (t : WEl T1 a1 b1 w) :
  forall {w'} (t' : WEl T1 a1 b1 w'),
  WRel T1 T1 a1 a1 b1 b1 Rlab11 Rbr11 t t' ->
  WRel T2 T2 a2 a2 b2 b2 Rlab22 Rbr22 (Wto t) (Wto t').
Proof.
  induction t as [w u0 x f ev gd sub IH]; intros w' t'.
  destruct t' as [w' u0' x' f' ev' gd' sub']; cbn.
  intros [Hl Hs].
  assert (Hlab : cEl c12 a1 u0 x a2 u0' (lab u0' x')).
  { eapply Ltr_12_22;
      [ exact wa1 | exact wa2 | exact wa2 | exact eA | apply LtoCoh
      | apply (LtoEq a1 a2 wa1 wa2 eA a1 a2 wa1 wa2 eA);
          [apply Lself; exact wa1 | exact Hl] ]. }
  split.
  - apply (LtoEq a1 a2 wa1 wa2 eA a1 a2 wa1 wa2 eA);
      [apply Lself; exact wa1 | exact Hl].
  - intros v y v'' y'' Hy.
    apply (IH v _).
    apply Hs.
    eapply Ltr_12_21;
      [ apply wb1 | apply wb2 | apply wb1 | apply eB; exact Hlab
      | eapply Ltr_12_22;
          [ apply wb1 | apply wb2 | apply wb2 | apply brE
          | apply LfromCoh | exact Hy ]
      | apply sym12, LfromCoh ].
Qed.

End Wcoe.

(* The coercion at a pair of codes, TOGETHER with its coherence: bundling the
   two means nothing downstream has to reason about the definition of the
   coercion, and the Pi clause needs the coherence of its components anyway. *)
Definition toRefine {T1 T2} (r1 : Refine st1 UnivOK T1) (r2 : Refine st2 UnivOK T2)
  (W1 : wfRefine d1 wf1 r1) (W2 : wfRefine d2 wf2 r2) (e : eqU c12 r1 r2) (u : etm)
  (x : El (Univ := Univ) r1 u)
  : { y : El (Univ := Univ) r2 u | eqEl c12 UnivEq r1 r2 u x u y }.
Proof.
  revert W1 W2 e x; dA r1; dB r2; cbn; intros W1 W2 e x;
    try (exact (match e with end)).
  (* nat *)
  - exists (Datatypes.fst x, Good_tyeq _ _ _ e (Datatypes.snd x)).
    split; [reflexivity | split; [exact e | exact (Datatypes.snd x)]].
  (* prop *)
  - exists (Datatypes.fst x, Good_tyeq _ _ _ e (Datatypes.snd x)).
    split; [split; exact (fun h => h) |].
    split; [exact e | exact (Datatypes.snd x)].
  (* prf *)
  - destruct e as [ety eH].
    exists (proj1 eH (Datatypes.fst x), Good_tyeq _ _ _ ety (Datatypes.snd x)).
    split; [exact ety | exact (Datatypes.snd x)].
  (* univ: the only place an equality of indices is transported along *)
  - destruct e as [ety Em]; destruct Em.
    exists x; split; [apply UErefl | exact ety].
  (* pi *)
  - destruct W1 as [[wa1 [wb1 [aeq1c beq1c]]] [_ [_ coh1]]].
    destruct W2 as [[wa2 [wb2 [aeq2c beq2c]]] [_ [_ coh2]]].
    destruct e as [ety [eA eB]]; destruct x as [[f fext] gd].
    (* the pulled-back argument and the two relations it satisfies *)
    pose (pull := fun w (x2 : StEl st2 ab w) => Lfrom aa ab wa1 wa2 eA w x2).
    assert (pullCoh : forall w x2, cEl c12 aa w (pull w x2) ab w x2)
      by (intros w x2; apply LfromCoh).
    (* the coerced function *)
    pose (g := fun w x2 =>
      Lto (ba w (pull w x2)) (bb w x2) (wb1 _ _) (wb2 _ _)
          (eB w (pull w x2) w x2 (pullCoh w x2)) (eapp u w) (f w (pull w x2))).
    (* related arguments of the target domain pull back to related ones *)
    assert (pullEq : forall w x2 w' x2', cEl d2 ab w x2 ab w' x2' ->
                     cEl d1 aa w (pull w x2) aa w' (pull w' x2')).
    { intros w x2 w' x2' H.
      eapply Ltr_12_21;
        [ exact wa1 | exact wa2 | exact wa1 | exact eA
        | eapply Ltr_12_22;
            [ exact wa1 | exact wa2 | exact wa2 | exact eA | apply pullCoh | exact H ]
        | apply sym12, pullCoh ]. }
    unshelve eexists (exist _ g _, Good_tyeq _ _ _ ety gd).
    + (* the coerced function is extensional *)
      intros w x2 w' x2' H.
      apply beq2c.
      unfold g; eapply LtoEq;
        [ apply coh1, pullEq, aeq2c, H
        | apply beq1c, fext, aeq1c, pullEq, aeq2c, H ].
    + (* and it is related to the function it came from *)
      cbn; split; [| split; [exact ety | exact gd]].
      intros w x1 w' x2' r.
      (* x1 and the pullback of x2' are related in the source domain *)
      assert (Hd : cEl d1 aa w x1 aa w' (pull w' x2')).
      { eapply Ltr_12_21;
          [ exact wa1 | exact wa2 | exact wa1 | exact eA | exact r
          | apply sym12, pullCoh ]. }
      (* f w x1 ~ its own coercion ~ g w' x2', the second step by LtoEq *)
      set (x1' := Lto aa ab wa1 wa2 eA w x1).
      assert (e1 : cU c12 (ba w x1) (bb w x1')) by (apply eB, LtoCoh).
      apply (Ltr_12_22 (ba w x1) (bb w x1') (bb w' x2')
               (eapp u w) (f w x1)
               (eapp u w)
               (Lto (ba w x1) (bb w x1') (wb1 w x1) (wb2 w x1') e1 (eapp u w) (f w x1))
               (eapp u w') (g w' x2')
               (wb1 w x1) (wb2 w x1') (wb2 w' x2') e1
               (LtoCoh (ba w x1) (bb w x1') (wb1 w x1) (wb2 w x1') e1 (eapp u w) (f w x1))).
      unfold g; eapply LtoEq;
        [ apply coh1; exact Hd | apply beq1c, fext, aeq1c; exact Hd ].
  (* sig: the two components, each coerced *)
  - destruct W1 as [[wa1 [wb1 _]] _]; destruct W2 as [[wa2 [wb2 _]] _].
    destruct e as [ety [eA eB]]; destruct x as [[x1 y1] gd].
    unshelve eexists
      (existT _ (Lto aa ab wa1 wa2 eA (efst u) x1)
                (Lto (ba (efst u) x1) (bb (efst u) (Lto aa ab wa1 wa2 eA (efst u) x1))
                     (wb1 _ _) (wb2 _ _)
                     (eB (efst u) x1 (efst u) _ (LtoCoh aa ab wa1 wa2 eA (efst u) x1))
                     (esnd u) y1),
       Good_tyeq _ _ _ ety gd).
    cbn; split; [apply LtoCoh |].
    split; [apply LtoCoh | split; [exact ety | exact gd]].
  (* w: the tree coercion, with Wto_coh for the coherence and Wto_eq for the
     self-relatedness the decoding asks of the coerced tree.  The carried
     relations are exchanged for the canonical ones by WRel_mono. *)
  - destruct W1 as [[wa1 [wb1 [aeq1c beq1c]]] [_ [_ coh1]]].
    destruct W2 as [[wa2 [wb2 [aeq2c beq2c]]] [_ [_ coh2]]].
    destruct e as [ety [eA eB]]; destruct x as [[t tself] gd].
    assert (tcan : WRel Ta Ta aa aa ba ba
                     (fun w x w' x' => cEl d1 aa w x aa w' x')
                     (fun w x w' x' v y v' y' => cEl d1 (ba w x) v y (ba w' x') v' y')
                     t t).
    { apply (WRel_mono Ta Ta aa aa ba ba
               aeqa (fun w x w' x' => cEl d1 aa w x aa w' x')
               beqa (fun w x w' x' v y v' y' => cEl d1 (ba w x) v y (ba w' x') v' y'));
        [ intros w x w' x' H; apply aeq1c; exact H
        | intros w x w' x' v y v' y' H; apply beq1c; exact H
        | exact tself ]. }
    unshelve eexists (exist _ (Wto Ta Tb aa ab ba bb wa1 wa2 wb1 wb2 eA eB ety t) _,
                      Good_tyeq _ _ _ ety gd).
    + apply (WRel_mono Tb Tb ab ab bb bb
               (fun w x w' x' => cEl d2 ab w x ab w' x') aeqb
               (fun w x w' x' v y v' y' => cEl d2 (bb w x) v y (bb w' x') v' y') beqb);
        [ intros w x w' x' H; apply aeq2c; exact H
        | intros w x w' x' v y v' y' H; apply beq2c; exact H
        | eapply Wto_eq; exact tcan ].
    + cbn; split; [| split; [exact ety | exact gd]].
      eapply Wto_coh; exact tcan.
Defined.
End CoeNode.

(* ------------------------------------------------------------------ *)
(* The bundle.                                                         *)
(*                                                                    *)
(* Transitivity is a statement about THREE stages, and the three have  *)
(* to be dispatched together: `cU (xcmp alpha' gamma) s' s''` does not *)
(* reduce until both ordinals are concrete, so the third stage cannot  *)
(* be quantified inside a field and peeled later.  v1 pays for this    *)
(* with a triple induction (Codes/IsoPER.v's hj_transP, 27 blocks).    *)
(*                                                                    *)
(* Here transitivity and the coercion are mutually dependent -- the    *)
(* coercion of a function has to be shown extensional, which is a      *)
(* transitivity one stage down, and transitivity at a Pi code needs a  *)
(* middle element, which is a coercion one stage down -- so both live  *)
(* in one record, built by ONE recursion on the first ordinal with      *)
(* inner recursions on the others.  Nothing inside a record depends on *)
(* the record itself: the coercion at alpha uses only the record at the *)
(* predecessors, and so does transitivity.                             *)
(* ------------------------------------------------------------------ *)

Section Bundle.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (UErefl : forall m u x, UnivEq m u x m u x)
        (UEsym : forall m u x m' u' x', UnivEq m u x m' u' x' -> UnivEq m' u' x' m u x)
        (UEtrans : forall m u x m' u' x' m'' u'' x'',
            UnivEq m u x m' u' x' -> UnivEq m' u' x' m'' u'' x'' ->
            UnivEq m u x m'' u'' x'').

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation Sub_ := (Sub Univ UnivOK).
Local Notation U_ := (U Univ UnivOK).
Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).
Local Notation wfsub_ := (wfsub Univ UnivEq UnivOK).
Local Notation wfc_ := (wfc Univ UnivEq UnivOK).
Local Notation xsymU_ := (xsymU Univ UnivEq UnivOK UEsym).
Local Notation xsym_ := (xsym Univ UnivEq UnivOK UEsym).
Local Notation self_ := (wfsub_self Univ UnivEq UnivOK).

(* the coercion from one stage into another, with its coherence.  The
   pointwise form is named, because the recursion's matches need it as their
   return annotation. *)
Definition ToPat (alpha alpha' : Ord) (s : Sub_ alpha) (s' : Sub_ alpha') : Type :=
  wfsub_ alpha s -> wfsub_ alpha' s' -> cU (xcmp_ alpha alpha') s s' ->
  forall u (x : StEl (stage_ alpha) s u),
  { y : StEl (stage_ alpha') s' u | cEl (xcmp_ alpha alpha') s u x s' u y }.

Definition ToP (alpha alpha' : Ord) : Type :=
  forall (s : Sub_ alpha) (s' : Sub_ alpha'), ToPat alpha alpha' s s'.

Definition TrU (a b c : Ord) (s : Sub_ a) (s' : Sub_ b) (s'' : Sub_ c) : Prop :=
  wfsub_ a s -> wfsub_ b s' -> wfsub_ c s'' ->
  cU (xcmp_ a b) s s' -> cU (xcmp_ b c) s' s'' -> cU (xcmp_ a c) s s''.

Definition TrE (a b c : Ord) (s : Sub_ a) (s' : Sub_ b) (s'' : Sub_ c) : Prop :=
  forall u x u' x' u'' x'',
    wfsub_ a s -> wfsub_ b s' -> wfsub_ c s'' ->
    cU (xcmp_ a b) s s' ->
    cEl (xcmp_ a b) s u x s' u' x' -> cEl (xcmp_ b c) s' u' x' s'' u'' x'' ->
    cEl (xcmp_ a c) s u x s'' u'' x''.

(* Transitivity in the two orders the node lemmas need: `alpha` first and
   `alpha` in the middle.  The other four permutations follow from these by
   the symmetry of Codes/Sym.v, and the arguments are quantified OUTSIDE the
   conjunction so that the eight-way dispatch of the three stages can discharge
   all four components with one recursive call. *)
Definition TrAll (alpha b c : Ord) (s : Sub_ alpha) (s' : Sub_ b) (s'' : Sub_ c) : Prop :=
  TrU alpha b c s s' s'' /\ TrE alpha b c s s' s'' /\
  TrU b alpha c s' s s'' /\ TrE b alpha c s' s s''.

Record Pack (alpha : Ord) : Type := {
  pk_to : forall alpha', ToP alpha alpha' * ToP alpha' alpha;
  pk_tr : forall b c s s' s'', TrAll alpha b c s s' s''
}.
Arguments pk_to {alpha}. Arguments pk_tr {alpha}.

Local Notation ceq_ := (ceq Univ UnivEq UnivOK).
Local Notation cel_ := (cel Univ UnivEq UnivOK).

(* ---- the pieces a pack hands to the node-level lemmas ---- *)

Definition pto {b1 : Ord} (P : Pack b1) (b2 : Ord) : ToP b1 b2 := fst (pk_to P b2).
Definition pfrom {b1 : Ord} (P : Pack b1) (b2 : Ord) : ToP b2 b1 := snd (pk_to P b2).

Definition Lto_of {b1} (P : Pack b1) (b2 : Ord)
  : forall s s', wfsub_ b1 s -> wfsub_ b2 s' -> cU (xcmp_ b1 b2) s s' ->
    forall u, StEl (stage_ b1) s u -> StEl (stage_ b2) s' u :=
  fun s s' w w' e u x => proj1_sig (pto P b2 s s' w w' e u x).

Definition LtoCoh_of {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b1 b2) s s') u x,
      cEl (xcmp_ b1 b2) s u x s' u (Lto_of P b2 s s' w w' e u x) :=
  fun s s' w w' e u x => proj2_sig (pto P b2 s s' w w' e u x).

Definition Lfrom_of {b1} (P : Pack b1) (b2 : Ord)
  : forall s s', wfsub_ b1 s -> wfsub_ b2 s' -> cU (xcmp_ b1 b2) s s' ->
    forall u, StEl (stage_ b2) s' u -> StEl (stage_ b1) s u :=
  fun s s' w w' e u y => proj1_sig (pfrom P b2 s' s w' w (xsymU_ s s' e) u y).

Definition LfromCoh_of {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b1 b2) s s') u y,
      cEl (xcmp_ b1 b2) s u (Lfrom_of P b2 s s' w w' e u y) s' u y :=
  fun s s' w w' e u y =>
    xsym_ s' u y s u _ (proj2_sig (pfrom P b2 s' s w' w (xsymU_ s s' e) u y)).

(* the coercion respects the equality: coherence, symmetry, transitivity *)
Definition LtoEq_of {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b1 b2) s s')
           s0 s0' w0 w0' (e0 : cU (xcmp_ b1 b2) s0 s0') u x u0 x0,
    cU (xcmp_ b1 b1) s s0 -> cEl (xcmp_ b1 b1) s u x s0 u0 x0 ->
    cEl (xcmp_ b2 b2) s' u (Lto_of P b2 s s' w w' e u x)
                       s0' u0 (Lto_of P b2 s0 s0' w0 w0' e0 u0 x0).
Proof.
  intros s s' w w' e s0 s0' w0 w0' e0 u x u0 x0 EU H.
  (* (to x) ~ x ~ x0, then x0 ~ (to x0) *)
  assert (H1 : cEl (xcmp_ b2 b1) s' u (Lto_of P b2 s s' w w' e u x) s0 u0 x0).
  { apply (proj2 (proj2 (proj2 (pk_tr P b2 b1 s s' s0)))
             u (Lto_of P b2 s s' w w' e u x) u x u0 x0 w' w w0);
      [ apply xsymU_; exact e
      | apply xsym_; apply LtoCoh_of
      | exact H ]. }
  apply (proj2 (proj2 (proj2 (pk_tr P b2 b2 s0 s' s0')))
           u (Lto_of P b2 s s' w w' e u x) u0 x0 u0 (Lto_of P b2 s0 s0' w0 w0' e0 u0 x0)
           w' w0 w0');
    [ apply (proj1 (proj2 (proj2 (pk_tr P b2 b1 s s' s0))) w' w w0);
        [apply xsymU_; exact e | exact EU]
    | exact H1
    | apply LtoCoh_of ].
Defined.

(* ---- the node-level facts ---- *)

Definition to_node (b1 b2 : Ord) (P : Pack b1) (c1 : U_ b1) (c2 : U_ b2)
  : wfc_ c1 -> wfc_ c2 -> ceq_ c1 c2 ->
    forall u (x : StEl (Ust_ b1) c1 u), { y : StEl (Ust_ b2) c2 u | cel_ c1 u x c2 u y } :=
  toRefine (stage_ b1) (stage_ b2) Univ UnivEq UnivOK
    (xcmp_ b1 b2) (xcmp_ b2 b1) (xcmp_ b1 b1) (xcmp_ b2 b2)
    (wfsub_ b1) (wfsub_ b2) UErefl xsym_
    (Lto_of P b2) (LtoCoh_of P b2) (Lfrom_of P b2) (LfromCoh_of P b2) (LtoEq_of P b2)
    (fun s s' s0' => proj1 (proj2 (pk_tr P b2 b2 s s' s0')))
    (fun s s' s0 => proj1 (proj2 (pk_tr P b2 b1 s s' s0)))
    (self_ b1) (projT2 c1) (projT2 c2).

Definition trU_node (b1 b2 b3 : Ord) (P : Pack b1) (c1 : U_ b1) (c2 : U_ b2) (c3 : U_ b3)
  : wfc_ c1 -> wfc_ c2 -> wfc_ c3 -> ceq_ c1 c2 -> ceq_ c2 c3 -> ceq_ c1 c3 :=
  eqU_trans (stage_ b1) (stage_ b2) (stage_ b3) UnivOK
    (xcmp_ b1 b2) (xcmp_ b2 b3) (xcmp_ b1 b3) (xcmp_ b2 b1)
    (wfsub_ b1) (wfsub_ b2) (wfsub_ b3)
    (xcmp_ b1 b1) (xcmp_ b2 b2) (xcmp_ b3 b3) xsymU_ xsym_
    (fun s s' s'' => proj1 (pk_tr P b2 b3 s s' s''))
    (fun s2 s1 s3 => proj2 (proj2 (proj2 (pk_tr P b2 b3 s1 s2 s3))))
    (Lto_of P b2) (LtoCoh_of P b2)
    (projT2 c1) (projT2 c2) (projT2 c3).

Definition trE_node (b1 b2 b3 : Ord) (P : Pack b1) (c1 : U_ b1) (c2 : U_ b2) (c3 : U_ b3)
  : forall u x u' x' u'' x'',
    wfc_ c1 -> wfc_ c2 -> wfc_ c3 -> ceq_ c1 c2 ->
    cel_ c1 u x c2 u' x' -> cel_ c2 u' x' c3 u'' x'' -> cel_ c1 u x c3 u'' x'' :=
  eqEl_trans (stage_ b1) (stage_ b2) (stage_ b3) Univ UnivEq UnivOK
    (xcmp_ b1 b2) (xcmp_ b2 b3) (xcmp_ b1 b3) (xcmp_ b2 b1)
    (wfsub_ b1) (wfsub_ b2) (wfsub_ b3)
    (xcmp_ b1 b1) (xcmp_ b2 b2) (xcmp_ b3 b3) xsymU_ xsym_
    (fun s s' s'' => proj1 (proj2 (pk_tr P b2 b3 s s' s'')))
    (fun s2 s1 s3 => proj2 (proj2 (proj2 (pk_tr P b2 b3 s1 s2 s3))))
    (Lto_of P b2) (LtoCoh_of P b2) UEtrans
    (projT2 c1) (projT2 c2) (projT2 c3).
(* ---- the mirrored pieces: the same facts for the pair (b2,b1), still read
   off the pack at b1, since that is the only pack available when the
   recursion is at b1 ---- *)

Definition Lto_of' {b1} (P : Pack b1) (b2 : Ord)
  : forall s s', wfsub_ b2 s -> wfsub_ b1 s' -> cU (xcmp_ b2 b1) s s' ->
    forall u, StEl (stage_ b2) s u -> StEl (stage_ b1) s' u :=
  fun s s' w w' e u x => proj1_sig (pfrom P b2 s s' w w' e u x).

Definition LtoCoh_of' {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b2 b1) s s') u x,
      cEl (xcmp_ b2 b1) s u x s' u (Lto_of' P b2 s s' w w' e u x) :=
  fun s s' w w' e u x => proj2_sig (pfrom P b2 s s' w w' e u x).

Definition Lfrom_of' {b1} (P : Pack b1) (b2 : Ord)
  : forall s s', wfsub_ b2 s -> wfsub_ b1 s' -> cU (xcmp_ b2 b1) s s' ->
    forall u, StEl (stage_ b1) s' u -> StEl (stage_ b2) s u :=
  fun s s' w w' e u y => proj1_sig (pto P b2 s' s w' w (xsymU_ s s' e) u y).

Definition LfromCoh_of' {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b2 b1) s s') u y,
      cEl (xcmp_ b2 b1) s u (Lfrom_of' P b2 s s' w w' e u y) s' u y :=
  fun s s' w w' e u y =>
    xsym_ s' u y s u _ (proj2_sig (pto P b2 s' s w' w (xsymU_ s s' e) u y)).

Definition LtoEq_of' {b1} (P : Pack b1) (b2 : Ord)
  : forall s s' w w' (e : cU (xcmp_ b2 b1) s s')
           s0 s0' w0 w0' (e0 : cU (xcmp_ b2 b1) s0 s0') u x u0 x0,
    cU (xcmp_ b2 b2) s s0 -> cEl (xcmp_ b2 b2) s u x s0 u0 x0 ->
    cEl (xcmp_ b1 b1) s' u (Lto_of' P b2 s s' w w' e u x)
                       s0' u0 (Lto_of' P b2 s0 s0' w0 w0' e0 u0 x0).
Proof.
  intros s s' w w' e s0 s0' w0 w0' e0 u x u0 x0 EU H.
  assert (H1 : cEl (xcmp_ b1 b2) s' u (Lto_of' P b2 s s' w w' e u x) s0 u0 x0).
  { apply (proj1 (proj2 (pk_tr P b2 b2 s' s s0))
             u (Lto_of' P b2 s s' w w' e u x) u x u0 x0 w' w w0);
      [ apply xsymU_; exact e
      | apply xsym_; apply LtoCoh_of'
      | exact H ]. }
  apply (proj1 (proj2 (pk_tr P b2 b1 s' s0 s0'))
           u (Lto_of' P b2 s s' w w' e u x) u0 x0 u0 (Lto_of' P b2 s0 s0' w0 w0' e0 u0 x0)
           w' w0 w0');
    [ apply (proj1 (pk_tr P b2 b2 s' s s0) w' w w0);
        [apply xsymU_; exact e | exact EU]
    | exact H1
    | apply LtoCoh_of' ].
Defined.

Definition to_node' (b1 b2 : Ord) (P : Pack b1) (c2 : U_ b2) (c1 : U_ b1)
  : wfc_ c2 -> wfc_ c1 -> ceq_ c2 c1 ->
    forall u (x : StEl (Ust_ b2) c2 u), { y : StEl (Ust_ b1) c1 u | cel_ c2 u x c1 u y } :=
  toRefine (stage_ b2) (stage_ b1) Univ UnivEq UnivOK
    (xcmp_ b2 b1) (xcmp_ b1 b2) (xcmp_ b2 b2) (xcmp_ b1 b1)
    (wfsub_ b2) (wfsub_ b1) UErefl xsym_
    (Lto_of' P b2) (LtoCoh_of' P b2) (Lfrom_of' P b2) (LfromCoh_of' P b2) (LtoEq_of' P b2)
    (fun s s' s0' => proj2 (proj2 (proj2 (pk_tr P b2 b1 s' s s0'))))
    (fun s s' s0 => proj2 (proj2 (proj2 (pk_tr P b2 b2 s' s s0))))
    (self_ b2) (projT2 c2) (projT2 c1).

Definition trU_node' (b1 b2 b3 : Ord) (P : Pack b1) (c2 : U_ b2) (c1 : U_ b1) (c3 : U_ b3)
  : wfc_ c2 -> wfc_ c1 -> wfc_ c3 -> ceq_ c2 c1 -> ceq_ c1 c3 -> ceq_ c2 c3 :=
  eqU_trans (stage_ b2) (stage_ b1) (stage_ b3) UnivOK
    (xcmp_ b2 b1) (xcmp_ b1 b3) (xcmp_ b2 b3) (xcmp_ b1 b2)
    (wfsub_ b2) (wfsub_ b1) (wfsub_ b3)
    (xcmp_ b2 b2) (xcmp_ b1 b1) (xcmp_ b3 b3) xsymU_ xsym_
    (fun s2 s1 s3 => proj1 (proj2 (proj2 (pk_tr P b2 b3 s1 s2 s3))))
    (fun s1 s2 s3 => proj1 (proj2 (pk_tr P b2 b3 s1 s2 s3)))
    (Lto_of' P b2) (LtoCoh_of' P b2)
    (projT2 c2) (projT2 c1) (projT2 c3).

Definition trE_node' (b1 b2 b3 : Ord) (P : Pack b1) (c2 : U_ b2) (c1 : U_ b1) (c3 : U_ b3)
  : forall u x u' x' u'' x'',
    wfc_ c2 -> wfc_ c1 -> wfc_ c3 -> ceq_ c2 c1 ->
    cel_ c2 u x c1 u' x' -> cel_ c1 u' x' c3 u'' x'' -> cel_ c2 u x c3 u'' x'' :=
  eqEl_trans (stage_ b2) (stage_ b1) (stage_ b3) Univ UnivEq UnivOK
    (xcmp_ b2 b1) (xcmp_ b1 b3) (xcmp_ b2 b3) (xcmp_ b1 b2)
    (wfsub_ b2) (wfsub_ b1) (wfsub_ b3)
    (xcmp_ b2 b2) (xcmp_ b1 b1) (xcmp_ b3 b3) xsymU_ xsym_
    (fun s s' s'' => proj2 (proj2 (proj2 (pk_tr P b2 b3 s' s s''))))
    (fun s1 s2 s3 => proj1 (proj2 (pk_tr P b2 b3 s1 s2 s3)))
    (Lto_of' P b2) (LtoCoh_of' P b2) UEtrans
    (projT2 c2) (projT2 c1) (projT2 c3).
(* the empty stage, as an eliminator: `Sub Univ UnivOK ozero` is Empty_set
   only after unfolding, so the recursion's base cases go through this *)
Definition Sub0_elim (X : Type) (s : Sub_ ozero) : X.
Proof. cbn in s; destruct s. Defined.

Fixpoint big (alpha : Ord) : Pack alpha :=
  match alpha as a return Pack a with
  | ozero =>
      Build_Pack ozero
        (fun alpha' => ((fun s => Sub0_elim _ s), (fun s s' => Sub0_elim _ s')))
        (fun b c s s' s'' => Sub0_elim _ s)
  | osucc a0 =>
      Build_Pack _
        (fix innerTo (alpha' : Ord) : ToP (osucc a0) alpha' * ToP alpha' (osucc a0) :=
           match alpha' as a' return ToP (osucc a0) a' * ToP a' (osucc a0) with
           | ozero => ((fun s s' => Sub0_elim _ s'), (fun s => Sub0_elim _ s))
           | osucc d0 =>
             ((fun s s' => match s as s0, s' as s0' return ToPat (osucc a0) (osucc d0) s0 s0' with
                | (inl c), (inl c') => to_node a0 d0 (big a0) c c'
                | (inl c), (inr t') => fst (innerTo d0) (inl c) t'
                | (inr t), (inl c') => fst (pk_to (big a0) (osucc d0)) t (inl c')
                | (inr t), (inr t') => fst (pk_to (big a0) d0) t t'
               end),
              (fun s' s => match s' as s0', s as s0 return ToPat (osucc d0) (osucc a0) s0' s0 with
                | (inl c'), (inl c) => to_node' a0 d0 (big a0) c' c
                | (inl c'), (inr t) => snd (pk_to (big a0) (osucc d0)) (inl c') t
                | (inr t'), (inl c) => snd (innerTo d0) t' (inl c)
                | (inr t'), (inr t) => snd (pk_to (big a0) d0) t' t
               end))
           | osup Td fd =>
             ((fun s s' => match s as s0, s' as s0' return ToPat (osucc a0) (osup Td fd) s0 s0' with
                | (inl c), (existT _ p2 (inl c')) => to_node a0 (fd p2) (big a0) c c'
                | (inl c), (existT _ p2 (inr t')) => fst (innerTo (fd p2)) (inl c) t'
                | (inr t), (existT _ p2 (inl c')) => fst (pk_to (big a0) (osup Td fd)) t (existT _ p2 (inl c'))
                | (inr t), (existT _ p2 (inr t')) => fst (pk_to (big a0) (fd p2)) t t'
               end),
              (fun s' s => match s' as s0', s as s0 return ToPat (osup Td fd) (osucc a0) s0' s0 with
                | (existT _ p2 (inl c')), (inl c) => to_node' a0 (fd p2) (big a0) c' c
                | (existT _ p2 (inl c')), (inr t) => snd (pk_to (big a0) (osup Td fd)) (existT _ p2 (inl c')) t
                | (existT _ p2 (inr t')), (inl c) => snd (innerTo (fd p2)) t' (inl c)
                | (existT _ p2 (inr t')), (inr t) => snd (pk_to (big a0) (fd p2)) t' t
               end))
           end)
        (fix innerB (b : Ord) : forall c s s' s'', TrAll (osucc a0) b c s s' s'' :=
           match b as b1 return forall c s s' s'', TrAll (osucc a0) b1 c s s' s'' with
           | ozero => fun c s s' s'' => Sub0_elim _ s'
           | osucc b0 =>
             (fix innerC (c : Ord) : forall s s' s'', TrAll (osucc a0) (osucc b0) c s s' s'' :=
                match c as c1 return forall s s' s'', TrAll (osucc a0) (osucc b0) c1 s s' s'' with
                | ozero => fun s s' s'' => Sub0_elim _ s''
                | osucc c0 => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osucc a0) (osucc b0) (osucc c0) s0 s0' s0'' with
                | (inl x), (inl y), (inl z) =>
                      conj (trU_node a0 b0 c0 (big a0) x y z)
                      (conj (trE_node a0 b0 c0 (big a0) x y z)
                      (conj (trU_node' a0 b0 c0 (big a0) y x z)
                            (trE_node' a0 b0 c0 (big a0) y x z)))
                | (inl x), (inl y), (inr z) => innerC c0 (inl x) (inl y) z
                | (inl x), (inr y), (inl z) => innerB b0 (osucc c0) (inl x) y (inl z)
                | (inl x), (inr y), (inr z) => innerB b0 c0 (inl x) y z
                | (inr x), (inl y), (inl z) => pk_tr (big a0) (osucc b0) (osucc c0) x (inl y) (inl z)
                | (inr x), (inl y), (inr z) => pk_tr (big a0) (osucc b0) c0 x (inl y) z
                | (inr x), (inr y), (inl z) => pk_tr (big a0) b0 (osucc c0) x y (inl z)
                | (inr x), (inr y), (inr z) => pk_tr (big a0) b0 c0 x y z
                  end
                | osup Tc fc => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osucc a0) (osucc b0) (osup Tc fc) s0 s0' s0'' with
                | (inl x), (inl y), (existT _ r (inl z)) =>
                      conj (trU_node a0 b0 (fc r) (big a0) x y z)
                      (conj (trE_node a0 b0 (fc r) (big a0) x y z)
                      (conj (trU_node' a0 b0 (fc r) (big a0) y x z)
                            (trE_node' a0 b0 (fc r) (big a0) y x z)))
                | (inl x), (inl y), (existT _ r (inr z)) => innerC (fc r) (inl x) (inl y) z
                | (inl x), (inr y), (existT _ r (inl z)) => innerB b0 (osup Tc fc) (inl x) y (existT _ r (inl z))
                | (inl x), (inr y), (existT _ r (inr z)) => innerB b0 (fc r) (inl x) y z
                | (inr x), (inl y), (existT _ r (inl z)) => pk_tr (big a0) (osucc b0) (osup Tc fc) x (inl y) (existT _ r (inl z))
                | (inr x), (inl y), (existT _ r (inr z)) => pk_tr (big a0) (osucc b0) (fc r) x (inl y) z
                | (inr x), (inr y), (existT _ r (inl z)) => pk_tr (big a0) b0 (osup Tc fc) x y (existT _ r (inl z))
                | (inr x), (inr y), (existT _ r (inr z)) => pk_tr (big a0) b0 (fc r) x y z
                  end
                end)
           | osup Tb fb =>
             (fix innerC (c : Ord) : forall s s' s'', TrAll (osucc a0) (osup Tb fb) c s s' s'' :=
                match c as c1 return forall s s' s'', TrAll (osucc a0) (osup Tb fb) c1 s s' s'' with
                | ozero => fun s s' s'' => Sub0_elim _ s''
                | osucc c0 => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osucc a0) (osup Tb fb) (osucc c0) s0 s0' s0'' with
                | (inl x), (existT _ q (inl y)), (inl z) =>
                      conj (trU_node a0 (fb q) c0 (big a0) x y z)
                      (conj (trE_node a0 (fb q) c0 (big a0) x y z)
                      (conj (trU_node' a0 (fb q) c0 (big a0) y x z)
                            (trE_node' a0 (fb q) c0 (big a0) y x z)))
                | (inl x), (existT _ q (inl y)), (inr z) => innerC c0 (inl x) (existT _ q (inl y)) z
                | (inl x), (existT _ q (inr y)), (inl z) => innerB (fb q) (osucc c0) (inl x) y (inl z)
                | (inl x), (existT _ q (inr y)), (inr z) => innerB (fb q) c0 (inl x) y z
                | (inr x), (existT _ q (inl y)), (inl z) => pk_tr (big a0) (osup Tb fb) (osucc c0) x (existT _ q (inl y)) (inl z)
                | (inr x), (existT _ q (inl y)), (inr z) => pk_tr (big a0) (osup Tb fb) c0 x (existT _ q (inl y)) z
                | (inr x), (existT _ q (inr y)), (inl z) => pk_tr (big a0) (fb q) (osucc c0) x y (inl z)
                | (inr x), (existT _ q (inr y)), (inr z) => pk_tr (big a0) (fb q) c0 x y z
                  end
                | osup Tc fc => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osucc a0) (osup Tb fb) (osup Tc fc) s0 s0' s0'' with
                | (inl x), (existT _ q (inl y)), (existT _ r (inl z)) =>
                      conj (trU_node a0 (fb q) (fc r) (big a0) x y z)
                      (conj (trE_node a0 (fb q) (fc r) (big a0) x y z)
                      (conj (trU_node' a0 (fb q) (fc r) (big a0) y x z)
                            (trE_node' a0 (fb q) (fc r) (big a0) y x z)))
                | (inl x), (existT _ q (inl y)), (existT _ r (inr z)) => innerC (fc r) (inl x) (existT _ q (inl y)) z
                | (inl x), (existT _ q (inr y)), (existT _ r (inl z)) => innerB (fb q) (osup Tc fc) (inl x) y (existT _ r (inl z))
                | (inl x), (existT _ q (inr y)), (existT _ r (inr z)) => innerB (fb q) (fc r) (inl x) y z
                | (inr x), (existT _ q (inl y)), (existT _ r (inl z)) => pk_tr (big a0) (osup Tb fb) (osup Tc fc) x (existT _ q (inl y)) (existT _ r (inl z))
                | (inr x), (existT _ q (inl y)), (existT _ r (inr z)) => pk_tr (big a0) (osup Tb fb) (fc r) x (existT _ q (inl y)) z
                | (inr x), (existT _ q (inr y)), (existT _ r (inl z)) => pk_tr (big a0) (fb q) (osup Tc fc) x y (existT _ r (inl z))
                | (inr x), (existT _ q (inr y)), (existT _ r (inr z)) => pk_tr (big a0) (fb q) (fc r) x y z
                  end
                end)
           end)
  | osup Ta fa =>
      Build_Pack _
        (fix innerTo (alpha' : Ord) : ToP (osup Ta fa) alpha' * ToP alpha' (osup Ta fa) :=
           match alpha' as a' return ToP (osup Ta fa) a' * ToP a' (osup Ta fa) with
           | ozero => ((fun s s' => Sub0_elim _ s'), (fun s => Sub0_elim _ s))
           | osucc d0 =>
             ((fun s s' => match s as s0, s' as s0' return ToPat (osup Ta fa) (osucc d0) s0 s0' with
                | (existT _ p (inl c)), (inl c') => to_node (fa p) d0 (big (fa p)) c c'
                | (existT _ p (inl c)), (inr t') => fst (innerTo d0) (existT _ p (inl c)) t'
                | (existT _ p (inr t)), (inl c') => fst (pk_to (big (fa p)) (osucc d0)) t (inl c')
                | (existT _ p (inr t)), (inr t') => fst (pk_to (big (fa p)) d0) t t'
               end),
              (fun s' s => match s' as s0', s as s0 return ToPat (osucc d0) (osup Ta fa) s0' s0 with
                | (inl c'), (existT _ p (inl c)) => to_node' (fa p) d0 (big (fa p)) c' c
                | (inl c'), (existT _ p (inr t)) => snd (pk_to (big (fa p)) (osucc d0)) (inl c') t
                | (inr t'), (existT _ p (inl c)) => snd (innerTo d0) t' (existT _ p (inl c))
                | (inr t'), (existT _ p (inr t)) => snd (pk_to (big (fa p)) d0) t' t
               end))
           | osup Td fd =>
             ((fun s s' => match s as s0, s' as s0' return ToPat (osup Ta fa) (osup Td fd) s0 s0' with
                | (existT _ p (inl c)), (existT _ p2 (inl c')) => to_node (fa p) (fd p2) (big (fa p)) c c'
                | (existT _ p (inl c)), (existT _ p2 (inr t')) => fst (innerTo (fd p2)) (existT _ p (inl c)) t'
                | (existT _ p (inr t)), (existT _ p2 (inl c')) => fst (pk_to (big (fa p)) (osup Td fd)) t (existT _ p2 (inl c'))
                | (existT _ p (inr t)), (existT _ p2 (inr t')) => fst (pk_to (big (fa p)) (fd p2)) t t'
               end),
              (fun s' s => match s' as s0', s as s0 return ToPat (osup Td fd) (osup Ta fa) s0' s0 with
                | (existT _ p2 (inl c')), (existT _ p (inl c)) => to_node' (fa p) (fd p2) (big (fa p)) c' c
                | (existT _ p2 (inl c')), (existT _ p (inr t)) => snd (pk_to (big (fa p)) (osup Td fd)) (existT _ p2 (inl c')) t
                | (existT _ p2 (inr t')), (existT _ p (inl c)) => snd (innerTo (fd p2)) t' (existT _ p (inl c))
                | (existT _ p2 (inr t')), (existT _ p (inr t)) => snd (pk_to (big (fa p)) (fd p2)) t' t
               end))
           end)
        (fix innerB (b : Ord) : forall c s s' s'', TrAll (osup Ta fa) b c s s' s'' :=
           match b as b1 return forall c s s' s'', TrAll (osup Ta fa) b1 c s s' s'' with
           | ozero => fun c s s' s'' => Sub0_elim _ s'
           | osucc b0 =>
             (fix innerC (c : Ord) : forall s s' s'', TrAll (osup Ta fa) (osucc b0) c s s' s'' :=
                match c as c1 return forall s s' s'', TrAll (osup Ta fa) (osucc b0) c1 s s' s'' with
                | ozero => fun s s' s'' => Sub0_elim _ s''
                | osucc c0 => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osup Ta fa) (osucc b0) (osucc c0) s0 s0' s0'' with
                | (existT _ p (inl x)), (inl y), (inl z) =>
                      conj (trU_node (fa p) b0 c0 (big (fa p)) x y z)
                      (conj (trE_node (fa p) b0 c0 (big (fa p)) x y z)
                      (conj (trU_node' (fa p) b0 c0 (big (fa p)) y x z)
                            (trE_node' (fa p) b0 c0 (big (fa p)) y x z)))
                | (existT _ p (inl x)), (inl y), (inr z) => innerC c0 (existT _ p (inl x)) (inl y) z
                | (existT _ p (inl x)), (inr y), (inl z) => innerB b0 (osucc c0) (existT _ p (inl x)) y (inl z)
                | (existT _ p (inl x)), (inr y), (inr z) => innerB b0 c0 (existT _ p (inl x)) y z
                | (existT _ p (inr x)), (inl y), (inl z) => pk_tr (big (fa p)) (osucc b0) (osucc c0) x (inl y) (inl z)
                | (existT _ p (inr x)), (inl y), (inr z) => pk_tr (big (fa p)) (osucc b0) c0 x (inl y) z
                | (existT _ p (inr x)), (inr y), (inl z) => pk_tr (big (fa p)) b0 (osucc c0) x y (inl z)
                | (existT _ p (inr x)), (inr y), (inr z) => pk_tr (big (fa p)) b0 c0 x y z
                  end
                | osup Tc fc => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osup Ta fa) (osucc b0) (osup Tc fc) s0 s0' s0'' with
                | (existT _ p (inl x)), (inl y), (existT _ r (inl z)) =>
                      conj (trU_node (fa p) b0 (fc r) (big (fa p)) x y z)
                      (conj (trE_node (fa p) b0 (fc r) (big (fa p)) x y z)
                      (conj (trU_node' (fa p) b0 (fc r) (big (fa p)) y x z)
                            (trE_node' (fa p) b0 (fc r) (big (fa p)) y x z)))
                | (existT _ p (inl x)), (inl y), (existT _ r (inr z)) => innerC (fc r) (existT _ p (inl x)) (inl y) z
                | (existT _ p (inl x)), (inr y), (existT _ r (inl z)) => innerB b0 (osup Tc fc) (existT _ p (inl x)) y (existT _ r (inl z))
                | (existT _ p (inl x)), (inr y), (existT _ r (inr z)) => innerB b0 (fc r) (existT _ p (inl x)) y z
                | (existT _ p (inr x)), (inl y), (existT _ r (inl z)) => pk_tr (big (fa p)) (osucc b0) (osup Tc fc) x (inl y) (existT _ r (inl z))
                | (existT _ p (inr x)), (inl y), (existT _ r (inr z)) => pk_tr (big (fa p)) (osucc b0) (fc r) x (inl y) z
                | (existT _ p (inr x)), (inr y), (existT _ r (inl z)) => pk_tr (big (fa p)) b0 (osup Tc fc) x y (existT _ r (inl z))
                | (existT _ p (inr x)), (inr y), (existT _ r (inr z)) => pk_tr (big (fa p)) b0 (fc r) x y z
                  end
                end)
           | osup Tb fb =>
             (fix innerC (c : Ord) : forall s s' s'', TrAll (osup Ta fa) (osup Tb fb) c s s' s'' :=
                match c as c1 return forall s s' s'', TrAll (osup Ta fa) (osup Tb fb) c1 s s' s'' with
                | ozero => fun s s' s'' => Sub0_elim _ s''
                | osucc c0 => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osup Ta fa) (osup Tb fb) (osucc c0) s0 s0' s0'' with
                | (existT _ p (inl x)), (existT _ q (inl y)), (inl z) =>
                      conj (trU_node (fa p) (fb q) c0 (big (fa p)) x y z)
                      (conj (trE_node (fa p) (fb q) c0 (big (fa p)) x y z)
                      (conj (trU_node' (fa p) (fb q) c0 (big (fa p)) y x z)
                            (trE_node' (fa p) (fb q) c0 (big (fa p)) y x z)))
                | (existT _ p (inl x)), (existT _ q (inl y)), (inr z) => innerC c0 (existT _ p (inl x)) (existT _ q (inl y)) z
                | (existT _ p (inl x)), (existT _ q (inr y)), (inl z) => innerB (fb q) (osucc c0) (existT _ p (inl x)) y (inl z)
                | (existT _ p (inl x)), (existT _ q (inr y)), (inr z) => innerB (fb q) c0 (existT _ p (inl x)) y z
                | (existT _ p (inr x)), (existT _ q (inl y)), (inl z) => pk_tr (big (fa p)) (osup Tb fb) (osucc c0) x (existT _ q (inl y)) (inl z)
                | (existT _ p (inr x)), (existT _ q (inl y)), (inr z) => pk_tr (big (fa p)) (osup Tb fb) c0 x (existT _ q (inl y)) z
                | (existT _ p (inr x)), (existT _ q (inr y)), (inl z) => pk_tr (big (fa p)) (fb q) (osucc c0) x y (inl z)
                | (existT _ p (inr x)), (existT _ q (inr y)), (inr z) => pk_tr (big (fa p)) (fb q) c0 x y z
                  end
                | osup Tc fc => fun s s' s'' =>
                  match s as s0, s' as s0', s'' as s0'' return TrAll (osup Ta fa) (osup Tb fb) (osup Tc fc) s0 s0' s0'' with
                | (existT _ p (inl x)), (existT _ q (inl y)), (existT _ r (inl z)) =>
                      conj (trU_node (fa p) (fb q) (fc r) (big (fa p)) x y z)
                      (conj (trE_node (fa p) (fb q) (fc r) (big (fa p)) x y z)
                      (conj (trU_node' (fa p) (fb q) (fc r) (big (fa p)) y x z)
                            (trE_node' (fa p) (fb q) (fc r) (big (fa p)) y x z)))
                | (existT _ p (inl x)), (existT _ q (inl y)), (existT _ r (inr z)) => innerC (fc r) (existT _ p (inl x)) (existT _ q (inl y)) z
                | (existT _ p (inl x)), (existT _ q (inr y)), (existT _ r (inl z)) => innerB (fb q) (osup Tc fc) (existT _ p (inl x)) y (existT _ r (inl z))
                | (existT _ p (inl x)), (existT _ q (inr y)), (existT _ r (inr z)) => innerB (fb q) (fc r) (existT _ p (inl x)) y z
                | (existT _ p (inr x)), (existT _ q (inl y)), (existT _ r (inl z)) => pk_tr (big (fa p)) (osup Tb fb) (osup Tc fc) x (existT _ q (inl y)) (existT _ r (inl z))
                | (existT _ p (inr x)), (existT _ q (inl y)), (existT _ r (inr z)) => pk_tr (big (fa p)) (osup Tb fb) (fc r) x (existT _ q (inl y)) z
                | (existT _ p (inr x)), (existT _ q (inr y)), (existT _ r (inl z)) => pk_tr (big (fa p)) (fb q) (osup Tc fc) x y (existT _ r (inl z))
                | (existT _ p (inr x)), (existT _ q (inr y)), (existT _ r (inr z)) => pk_tr (big (fa p)) (fb q) (fc r) x y z
                  end
                end)
           end)
  end.

(* ------------------------------------------------------------------ *)
(* The working interface: for well-formed codes at ANY two nodes of one *)
(* level the equality is a PER, and there is a coercion that preserves  *)
(* the realiser, is coherent with the equality, and respects it.        *)
(* Symmetry comes from Codes/Sym.v, everything else from `big`.         *)
(* ------------------------------------------------------------------ *)

Definition xto {b b'} (c : U_ b) (c' : U_ b') (W : wfc_ c) (W' : wfc_ c')
  (e : ceq_ c c') u (x : StEl (Ust_ b) c u) : StEl (Ust_ b') c' u :=
  proj1_sig (to_node b b' (big b) c c' W W' e u x).

Definition xto_coh {b b'} (c : U_ b) (c' : U_ b') W W' e u x
  : cel_ c u x c' u (xto c c' W W' e u x) :=
  proj2_sig (to_node b b' (big b) c c' W W' e u x).

Definition xtrU {b b' b''} (c : U_ b) (c' : U_ b') (c'' : U_ b'')
  : wfc_ c -> wfc_ c' -> wfc_ c'' -> ceq_ c c' -> ceq_ c' c'' -> ceq_ c c'' :=
  trU_node b b' b'' (big b) c c' c''.

Definition xtrE {b b' b''} (c : U_ b) (c' : U_ b') (c'' : U_ b'')
  : forall u x u' x' u'' x'', wfc_ c -> wfc_ c' -> wfc_ c'' -> ceq_ c c' ->
    cel_ c u x c' u' x' -> cel_ c' u' x' c'' u'' x'' -> cel_ c u x c'' u'' x'' :=
  trE_node b b' b'' (big b) c c' c''.

(* symmetry at the level of codes, from Codes/Sym.v *)
Definition nsymU {b b'} (c : U_ b) (c' : U_ b') : ceq_ c c' -> ceq_ c' c :=
  symU_node Univ UnivEq UnivOK b b'
    (proj1 (sym_pair Univ UnivEq UnivOK UEsym b b'))
    (proj2 (sym_pair Univ UnivEq UnivOK UEsym b b'))
    _ _ (projT2 c) (projT2 c').

Definition nsym {b b'} (c : U_ b) (c' : U_ b') u x u' x'
  : cel_ c u x c' u' x' -> cel_ c' u' x' c u x :=
  symEl_node Univ UnivEq UnivOK UEsym b b'
    (proj1 (sym_pair Univ UnivEq UnivOK UEsym b b'))
    (proj2 (sym_pair Univ UnivEq UnivOK UEsym b b'))
    _ _ (projT2 c) (projT2 c') u x u' x'.

(* the coercion respects the equality: coherence, symmetry, transitivity *)
Lemma xto_eq {b b'} (c : U_ b) (c' : U_ b') W W' (e : ceq_ c c')
  (c0 : U_ b) (c0' : U_ b') W0 W0' (e0 : ceq_ c0 c0') u x u0 x0 :
  ceq_ c c0 -> cel_ c u x c0 u0 x0 ->
  cel_ c' u (xto c c' W W' e u x) c0' u0 (xto c0 c0' W0 W0' e0 u0 x0).
Proof.
  intros EU H.
  assert (H1 : cel_ c' u (xto c c' W W' e u x) c0 u0 x0).
  { apply (xtrE c' c c0 u (xto c c' W W' e u x) u x u0 x0 W' W W0);
      [ apply nsymU; exact e
      | apply nsym; apply xto_coh
      | exact H ]. }
  apply (xtrE c' c0 c0' u (xto c c' W W' e u x) u0 x0 u0
               (xto c0 c0' W0 W0' e0 u0 x0) W' W0 W0');
    [ apply (xtrU c' c c0); [exact W' | exact W | exact W0
                            | apply nsymU; exact e | exact EU]
    | exact H1
    | apply xto_coh ].
Qed.
End Bundle.
