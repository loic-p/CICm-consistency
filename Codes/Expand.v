From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.Eq Codes.WF Codes.Sym
  Codes.Str Codes.Sound.
From Stdlib Require Import Arith Lia.

(* Lemma 8.7: the decoding of a code is closed under reduction and expansion
   of the realiser, and the two maps are equalities of the code -- which is
   sayable because the equality is heterogeneous in the realiser.

   Two clauses differ from v1.  Sigma: when the pair's realiser reduces, its
   first component's VALUE moves too, so the second component's code moves with
   it; v1 pushed the second component along the transport the code carries,
   here it is the coercion of Codes/Str.v and the code equality it needs is the
   code's own coherence, i.e. a conjunct of well-formedness.  W: only the top
   node's realiser moves -- the subtrees are indexed by branches, which do not
   -- so the tree is rebuilt at its root and its self-relatedness is literally
   the same proposition. *)

Lemma Good_red T u u1 : reds u u1 -> Good T u -> Good T u1.
Proof. intros H G; eapply Rel_red; [exact H | exact H | exact G]. Qed.

Lemma Good_exp T u u1 : reds u u1 -> Good T u1 -> Good T u.
Proof. intros H G; eapply Rel_exp; [exact H | exact H | exact G]. Qed.

Lemma Rel_red_r T u u1 : reds u u1 -> Good T u -> Rel T u u1.
Proof. intros H G; eapply Rel_red; [apply reds_refl | exact H | exact G]. Qed.

Lemma Rel_exp_l T u u1 : reds u u1 -> Good T u1 -> Rel T u u1.
Proof. intros H G; eapply Rel_exp; [exact H | apply reds_refl | exact G]. Qed.

(* the same, of the parameter that decodes the universes *)
Record UnivExp (Univ : nat -> etm -> Type)
               (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop) := {
  ue_red : forall m u u1, reds u u1 -> Univ m u -> Univ m u1;
  ue_exp : forall m u u1, reds u u1 -> Univ m u1 -> Univ m u;
  ue_red_rel : forall m u u1 (H : reds u u1) x, UnivEq m u x m u1 (ue_red m u u1 H x);
  ue_exp_rel : forall m u u1 (H : reds u u1) y, UnivEq m u (ue_exp m u u1 H y) m u1 y
}.
Arguments ue_red {Univ UnivEq}. Arguments ue_exp {Univ UnivEq}.
Arguments ue_red_rel {Univ UnivEq}. Arguments ue_exp_rel {Univ UnivEq}.

(* ------------------------------------------------------------------ *)
(* The trees move at their root only.                                  *)
(* ------------------------------------------------------------------ *)

Definition WEl_red {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  : forall w w1, reds w w1 -> WEl T a b w -> WEl T a b w1 :=
  fun w w1 H t =>
    match t in WEl _ _ _ w0 return reds w0 w1 -> WEl T a b w1 with
    | wel_sup w0 u0 x f ev gd sub =>
        fun H' => wel_sup w1 u0 x f (eval_reds_inv _ _ _ H' ev) (Good_red T _ _ H' gd) sub
    end H.

Definition WEl_exp {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  : forall w w1, reds w w1 -> WEl T a b w1 -> WEl T a b w :=
  fun w w1 H t =>
    match t in WEl _ _ _ w0 return reds w w0 -> WEl T a b w with
    | wel_sup w0 u0 x f ev gd sub =>
        fun H' => wel_sup w u0 x f (eval_reds _ _ _ H' ev) (Good_exp T _ _ H' gd) sub
    end H.

(* moving a tree does not change what its self-relatedness says: the labels
   and the branches are untouched, only the root's realiser and its two
   witnesses.  It is one case analysis, because `WEl_red t` is a match on t. *)
Lemma WRel_red_self {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  (Rlab : forall u, StEl st a u -> forall u', StEl st a u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st a u') v, StEl st (b u x) v ->
         forall v', StEl st (b u' x') v' -> Prop)
  w w1 (H : reds w w1) (t : WEl T a b w) :
  WRel T T a a b b Rlab Rbr t t ->
  WRel T T a a b b Rlab Rbr (WEl_red T a b w w1 H t) (WEl_red T a b w w1 H t).
Proof. destruct t; cbn; exact (fun h => h). Qed.

Lemma WRel_exp_self {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  (Rlab : forall u, StEl st a u -> forall u', StEl st a u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st a u') v, StEl st (b u x) v ->
         forall v', StEl st (b u' x') v' -> Prop)
  w w1 (H : reds w w1) (t : WEl T a b w1) :
  WRel T T a a b b Rlab Rbr t t ->
  WRel T T a a b b Rlab Rbr (WEl_exp T a b w w1 H t) (WEl_exp T a b w w1 H t).
Proof. destruct t; cbn; exact (fun h => h). Qed.

(* and moving a tree relates it to itself, for the same reason *)
Lemma WRel_red_coh {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  (Rlab : forall u, StEl st a u -> forall u', StEl st a u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st a u') v, StEl st (b u x) v ->
         forall v', StEl st (b u' x') v' -> Prop)
  w w1 (H : reds w w1) (t : WEl T a b w) :
  WRel T T a a b b Rlab Rbr t t ->
  WRel T T a a b b Rlab Rbr t (WEl_red T a b w w1 H t).
Proof. destruct t; cbn; exact (fun h => h). Qed.

Lemma WRel_exp_coh {st : Stage} (T : etm) (a : St st) (b : forall u, StEl st a u -> St st)
  (Rlab : forall u, StEl st a u -> forall u', StEl st a u' -> Prop)
  (Rbr : forall u (x : StEl st a u) u' (x' : StEl st a u') v, StEl st (b u x) v ->
         forall v', StEl st (b u' x') v' -> Prop)
  w w1 (H : reds w w1) (t : WEl T a b w1) :
  WRel T T a a b b Rlab Rbr t t ->
  WRel T T a a b b Rlab Rbr (WEl_exp T a b w w1 H t) t.
Proof. destruct t; cbn; exact (fun h => h). Qed.

Section ExpRefine.
Context (st : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (dg : Cmp st st) (wfS : St st -> Prop) (UE : UnivExp Univ UnivEq).
(* what the stage below supplies *)
Context (Sred : forall s, wfS s -> forall u u1, reds u u1 -> StEl st s u -> StEl st s u1)
        (Sexp : forall s, wfS s -> forall u u1, reds u u1 -> StEl st s u1 -> StEl st s u)
        (SredRel : forall s (w : wfS s) u u1 (H : reds u u1) x,
            cEl dg s u x s u1 (Sred s w u u1 H x))
        (SexpRel : forall s (w : wfS s) u u1 (H : reds u u1) y,
            cEl dg s u (Sexp s w u u1 H y) s u1 y)
        (Ssym : forall s u x s' u' x', cEl dg s u x s' u' x' -> cEl dg s' u' x' s u x)
        (StrE : forall s s' s'' u x u' x' u'' x'', wfS s -> wfS s' -> wfS s'' ->
            cU dg s s' -> cEl dg s u x s' u' x' -> cEl dg s' u' x' s'' u'' x'' ->
            cEl dg s u x s'' u'' x'')
        (Sto : forall s s', wfS s -> wfS s' -> cU dg s s' ->
            forall u, StEl st s u -> StEl st s' u)
        (StoCoh : forall s s' w w' (e : cU dg s s') u x,
            cEl dg s u x s' u (Sto s s' w w' e u x))
        (Sself : forall s, wfS s -> cU dg s s).

Local Notation El_ := (El (st := st) (Univ := Univ)).
Local Notation eqEl_ := (eqEl dg UnivEq (UnivOK := UnivOK)).

Definition elRed {T} (r : Refine st UnivOK T) (W : wfRefine dg wfS r)
  : forall u u1, reds u u1 -> El_ r u -> El_ r u1.
Proof.
  revert W; dest_code r; cbn; intros W u u1 H x.
  (* nat *)
  - exact (existT _ (projT1 (Datatypes.fst x))
             (NatAt_red _ _ _ H (projT2 (Datatypes.fst x))),
           Good_red _ _ _ H (Datatypes.snd x)).
  (* prop *)
  - exact (Datatypes.fst x, Good_red _ _ _ H (Datatypes.snd x)).
  (* prf *)
  - exact (Datatypes.fst x, Good_red _ _ _ H (Datatypes.snd x)).
  (* univ *)
  - exact (ue_red UE _ _ _ H x).
  (* pi: every value moves, and the moved function is extensional because the
     moves are equalities of its codomain codes *)
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[f fext] gd].
    refine (exist _ (fun w y => Sred (b w y) (wb w y) (eapp u w) (eapp u1 w)
                                     (reds_app _ _ w H) (f w y)) _,
            Good_red _ _ _ H gd).
    intros w y w' y' Hy; apply beqc.
    apply (StrE (b w y) (b w y) (b w' y')
             (eapp u1 w) _ (eapp u w) (f w y) (eapp u1 w') _
             (wb w y) (wb w y) (wb w' y') (Sself _ (wb w y)));
      [ apply Ssym, SredRel |].
    apply (StrE (b w y) (b w' y') (b w' y')
             (eapp u w) (f w y) (eapp u w') (f w' y') (eapp u1 w') _
             (wb w y) (wb w' y') (wb w' y') (coh w y w' y' (proj1 (aeqc _ _ _ _) Hy)));
      [ apply beqc, fext, Hy | apply SredRel ].
  (* sig: the first component's value moves, so the second component's code
     moves with it, and the coercion takes it across *)
  - destruct W as [[wa [wb _]] [_ [_ coh]]]; destruct x as [[y z] gd].
    refine (existT _ (Sred a wa (efst u) (efst u1) (reds_fst _ _ H) y) _,
            Good_red _ _ _ H gd).
    apply (Sto (b (efst u) y) (b (efst u1) (Sred a wa (efst u) (efst u1) (reds_fst _ _ H) y))
             (wb _ _) (wb _ _) (coh _ _ _ _ (SredRel _ _ _ _ _ _))).
    exact (Sred (b (efst u) y) (wb _ _) (esnd u) (esnd u1) (reds_snd _ _ H) z).
  (* w *)
  - destruct x as [[t tself] gd].
    exact (exist (fun z => WRel _ _ a a b b aeq beq z z)
             (WEl_red _ a b u u1 H t) (WRel_red_self _ a b aeq beq u u1 H t tself),
           Good_red _ _ _ H gd).
Defined.

Definition elExp {T} (r : Refine st UnivOK T) (W : wfRefine dg wfS r)
  : forall u u1, reds u u1 -> El_ r u1 -> El_ r u.
Proof.
  revert W; dest_code r; cbn; intros W u u1 H x.
  - exact (existT _ (projT1 (Datatypes.fst x))
             (NatAt_exp _ _ _ H (projT2 (Datatypes.fst x))),
           Good_exp _ _ _ H (Datatypes.snd x)).
  - exact (Datatypes.fst x, Good_exp _ _ _ H (Datatypes.snd x)).
  - exact (Datatypes.fst x, Good_exp _ _ _ H (Datatypes.snd x)).
  - exact (ue_exp UE _ _ _ H x).
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[f fext] gd].
    refine (exist _ (fun w y => Sexp (b w y) (wb w y) (eapp u w) (eapp u1 w)
                                     (reds_app _ _ w H) (f w y)) _,
            Good_exp _ _ _ H gd).
    intros w y w' y' Hy; apply beqc.
    apply (StrE (b w y) (b w y) (b w' y')
             (eapp u w) _ (eapp u1 w) (f w y) (eapp u w') _
             (wb w y) (wb w y) (wb w' y') (Sself _ (wb w y)));
      [ apply SexpRel |].
    apply (StrE (b w y) (b w' y') (b w' y')
             (eapp u1 w) (f w y) (eapp u1 w') (f w' y') (eapp u w') _
             (wb w y) (wb w' y') (wb w' y') (coh w y w' y' (proj1 (aeqc _ _ _ _) Hy)));
      [ apply beqc, fext, Hy | apply Ssym, SexpRel ].
  - destruct W as [[wa [wb _]] [_ [_ coh]]]; destruct x as [[y z] gd].
    refine (existT _ (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y) _,
            Good_exp _ _ _ H gd).
    apply (Sexp (b (efst u) (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y)) (wb _ _)
             (esnd u) (esnd u1) (reds_snd _ _ H)).
    apply (Sto (b (efst u1) y)
             (b (efst u) (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y))
             (wb _ _) (wb _ _)
             (coh _ _ _ _ (Ssym _ _ _ _ _ _ (SexpRel _ _ _ _ _ _)))).
    exact z.
  - destruct x as [[t tself] gd].
    exact (exist (fun z => WRel _ _ a a b b aeq beq z z)
             (WEl_exp _ a b u u1 H t) (WRel_exp_self _ a b aeq beq u u1 H t tself),
           Good_exp _ _ _ H gd).
Defined.
End ExpRefine.

(* ------------------------------------------------------------------ *)
(* The two maps are equalities of the code.                            *)
(* ------------------------------------------------------------------ *)

Section ExpRel.
Context (st : Stage) (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (dg : Cmp st st) (wfS : St st -> Prop) (UE : UnivExp Univ UnivEq).
Context (Sred : forall s, wfS s -> forall u u1, reds u u1 -> StEl st s u -> StEl st s u1)
        (Sexp : forall s, wfS s -> forall u u1, reds u u1 -> StEl st s u1 -> StEl st s u)
        (SredRel : forall s (w : wfS s) u u1 (H : reds u u1) x,
            cEl dg s u x s u1 (Sred s w u u1 H x))
        (SexpRel : forall s (w : wfS s) u u1 (H : reds u u1) y,
            cEl dg s u (Sexp s w u u1 H y) s u1 y)
        (Ssym : forall s u x s' u' x', cEl dg s u x s' u' x' -> cEl dg s' u' x' s u x)
        (StrE : forall s s' s'' u x u' x' u'' x'', wfS s -> wfS s' -> wfS s'' ->
            cU dg s s' -> cEl dg s u x s' u' x' -> cEl dg s' u' x' s'' u'' x'' ->
            cEl dg s u x s'' u'' x'')
        (Sto : forall s s', wfS s -> wfS s' -> cU dg s s' ->
            forall u, StEl st s u -> StEl st s' u)
        (StoCoh : forall s s' w w' (e : cU dg s s') u x,
            cEl dg s u x s' u (Sto s s' w w' e u x))
        (Sself : forall s, wfS s -> cU dg s s).

Local Notation elRed_ :=
  (elRed st Univ UnivEq UnivOK dg wfS UE Sred SredRel Ssym StrE Sto Sself).
Local Notation elExp_ :=
  (elExp st Univ UnivEq UnivOK dg wfS UE Sexp SexpRel Ssym StrE Sto Sself).

Lemma elRed_rel {T} (r : Refine st UnivOK T) (W : wfRefine dg wfS r) u u1 (H : reds u u1) x :
  eqEl dg UnivEq r r u x u1 (elRed_ r W u u1 H x).
Proof.
  pose proof (eqU_tyeq dg r r (proj2 W)) as ety.
  revert W ety x; dest_code r; cbn; intros W ety x.
  - split; [reflexivity | split; [exact ety | apply Rel_red_r; [exact H | exact (Datatypes.snd x)]]].
  - split; [split; exact (fun h => h) |
            split; [exact ety | apply Rel_red_r; [exact H | exact (Datatypes.snd x)]]].
  - split; [exact ety | apply Rel_red_r; [exact H | exact (Datatypes.snd x)]].
  - split; [apply ue_red_rel | exact ety].
  (* pi *)
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[f fext] gd]; cbn.
    split; [| split; [exact ety | apply Rel_red_r; [exact H | exact gd]]].
    intros w y w' y' Hy.
    apply (StrE (b w y) (b w' y') (b w' y')
             (eapp u w) (f w y) (eapp u w') (f w' y') (eapp u1 w') _
             (wb w y) (wb w' y') (wb w' y') (coh w y w' y' Hy));
      [ apply beqc, fext, aeqc, Hy | apply SredRel ].
  (* sig *)
  - destruct W as [[wa [wb _]] [_ [_ coh]]]; destruct x as [[y z] gd]; cbn.
    split; [apply SredRel |].
    split; [| split; [exact ety | apply Rel_red_r; [exact H | exact gd]]].
    apply (StrE (b (efst u) y) (b (efst u) y)
             (b (efst u1) (Sred a wa (efst u) (efst u1) (reds_fst _ _ H) y))
             (esnd u) z
             (esnd u1) (Sred (b (efst u) y) (wb _ _) (esnd u) (esnd u1) (reds_snd _ _ H) z)
             (esnd u1) _
             (wb _ _) (wb _ _) (wb _ _) (Sself _ (wb _ _)));
      [ apply SredRel | apply StoCoh ].
  (* w *)
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[t tself] gd]; cbn.
    split; [| split; [exact ety | apply Rel_red_r; [exact H | exact gd]]].
    apply WRel_red_coh.
    apply (WRel_mono T T a a b b aeq (fun w y w' y' => cEl dg a w y a w' y')
             beq (fun w y w' y' v z v' z' => cEl dg (b w y) v z (b w' y') v' z'));
      [ intros w y w' y' Hy; apply aeqc; exact Hy
      | intros w y w' y' v z v' z' Hz; apply beqc; exact Hz
      | exact tself ].
Qed.

Lemma elExp_rel {T} (r : Refine st UnivOK T) (W : wfRefine dg wfS r) u u1 (H : reds u u1) x :
  eqEl dg UnivEq r r u (elExp_ r W u u1 H x) u1 x.
Proof.
  pose proof (eqU_tyeq dg r r (proj2 W)) as ety.
  revert W ety x; dest_code r; cbn; intros W ety x.
  - split; [reflexivity | split; [exact ety | apply Rel_exp_l; [exact H | exact (Datatypes.snd x)]]].
  - split; [split; exact (fun h => h) |
            split; [exact ety | apply Rel_exp_l; [exact H | exact (Datatypes.snd x)]]].
  - split; [exact ety | apply Rel_exp_l; [exact H | exact (Datatypes.snd x)]].
  - split; [apply ue_exp_rel | exact ety].
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[f fext] gd]; cbn.
    split; [| split; [exact ety | apply Rel_exp_l; [exact H | exact gd]]].
    intros w y w' y' Hy.
    apply (StrE (b w y) (b w y) (b w' y')
             (eapp u w) _ (eapp u1 w) (f w y) (eapp u1 w') _
             (wb w y) (wb w y) (wb w' y') (Sself _ (wb w y)));
      [ apply SexpRel | apply beqc, fext, aeqc, Hy ].
  - destruct W as [[wa [wb _]] [_ [_ coh]]]; destruct x as [[y z] gd]; cbn.
    split; [apply SexpRel |].
    split; [| split; [exact ety | apply Rel_exp_l; [exact H | exact gd]]].
    apply (StrE (b (efst u) (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y))
             (b (efst u) (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y))
             (b (efst u1) y)
             (esnd u) _
             (esnd u1) (Sto (b (efst u1) y)
                          (b (efst u) (Sexp a wa (efst u) (efst u1) (reds_fst _ _ H) y))
                          (wb _ _) (wb _ _)
                          (coh _ _ _ _
                             (Ssym _ _ _ _ _ _
                                (SexpRel a wa (efst u) (efst u1) (reds_fst _ _ H) y)))
                          (esnd u1) z)
             (esnd u1) z
             (wb _ _) (wb _ _) (wb _ _) (Sself _ (wb _ _)));
      [ apply SexpRel | apply Ssym, StoCoh ].
  - destruct W as [[wa [wb [aeqc beqc]]] [_ [_ coh]]]; destruct x as [[t tself] gd]; cbn.
    split; [| split; [exact ety | apply Rel_exp_l; [exact H | exact gd]]].
    apply WRel_exp_coh.
    apply (WRel_mono T T a a b b aeq (fun w y w' y' => cEl dg a w y a w' y')
             beq (fun w y w' y' v z v' z' => cEl dg (b w y) v z (b w' y') v' z'));
      [ intros w y w' y' Hy; apply aeqc; exact Hy
      | intros w y w' y' v z v' z' Hz; apply beqc; exact Hz
      | exact tself ].
Qed.
End ExpRel.

(* ------------------------------------------------------------------ *)
(* The whole hierarchy: one induction on the Brouwer tree, because only *)
(* ONE stage is involved -- a realiser reduces, the codes do not move.  *)
(* ------------------------------------------------------------------ *)

Section Level.
Context (Univ : nat -> etm -> Type)
        (UnivEq : forall m u, Univ m u -> forall m' u', Univ m' u' -> Prop)
        (UnivOK : nat -> Prop).
Context (UErefl : forall m u x, UnivEq m u x m u x)
        (UEsym : forall m u x m' u' x', UnivEq m u x m' u' x' -> UnivEq m' u' x' m u x)
        (UEtrans : forall m u x m' u' x' m'' u'' x'',
            UnivEq m u x m' u' x' -> UnivEq m' u' x' m'' u'' x'' ->
            UnivEq m u x m'' u'' x'')
        (UE : UnivExp Univ UnivEq).

Local Notation stage_ := (stage Univ UnivOK).
Local Notation Ust_ := (Ust Univ UnivOK).
Local Notation xcmp_ := (xcmp Univ UnivEq UnivOK).
Local Notation wfsub_ := (wfsub Univ UnivEq UnivOK).
Local Notation wfc_ := (wfc Univ UnivEq UnivOK).
Local Notation big_ := (big Univ UnivEq UnivOK UErefl UEsym UEtrans).

Record Exp (alpha : Ord) : Type := {
  ex_red : forall (s : Sub Univ UnivOK alpha), wfsub_ alpha s ->
      forall u u1, reds u u1 -> StEl (stage_ alpha) s u -> StEl (stage_ alpha) s u1;
  ex_exp : forall (s : Sub Univ UnivOK alpha), wfsub_ alpha s ->
      forall u u1, reds u u1 -> StEl (stage_ alpha) s u1 -> StEl (stage_ alpha) s u;
  ex_red_rel : forall s (W : wfsub_ alpha s) u u1 (H : reds u u1) x,
      cEl (xcmp_ alpha alpha) s u x s u1 (ex_red s W u u1 H x);
  ex_exp_rel : forall s (W : wfsub_ alpha s) u u1 (H : reds u u1) y,
      cEl (xcmp_ alpha alpha) s u (ex_exp s W u u1 H y) s u1 y
}.
Arguments ex_red {alpha}. Arguments ex_exp {alpha}.
Arguments ex_red_rel {alpha}. Arguments ex_exp_rel {alpha}.

(* the pieces one stage down, as the clauses above want them *)
Local Notation Str_ b :=
  (fun s s' s'' => proj1 (proj2 (pk_tr Univ UnivEq UnivOK b (big_ b) b b s s' s''))).
Local Notation Sto_ b := (Lto_of Univ UnivEq UnivOK (big_ b) b).
Local Notation StoCoh_ b := (LtoCoh_of Univ UnivEq UnivOK (big_ b) b).
Local Notation Sself_ b := (wfsub_self Univ UnivEq UnivOK b).
Local Notation Ssym_ := (xsym Univ UnivEq UnivOK UEsym).

Definition nodeRed (b : Ord) (E : Exp b) (c : U Univ UnivOK b) (W : wfc_ c)
  : forall u u1, reds u u1 -> StEl (Ust_ b) c u -> StEl (Ust_ b) c u1 :=
  elRed (stage_ b) Univ UnivEq UnivOK (xcmp_ b b) (wfsub_ b) UE
    (ex_red E) (ex_red_rel E) Ssym_ (Str_ b) (Sto_ b) (Sself_ b) (projT2 c) W.

Definition nodeExp (b : Ord) (E : Exp b) (c : U Univ UnivOK b) (W : wfc_ c)
  : forall u u1, reds u u1 -> StEl (Ust_ b) c u1 -> StEl (Ust_ b) c u :=
  elExp (stage_ b) Univ UnivEq UnivOK (xcmp_ b b) (wfsub_ b) UE
    (ex_exp E) (ex_exp_rel E) Ssym_ (Str_ b) (Sto_ b) (Sself_ b) (projT2 c) W.

Definition nodeRedRel (b : Ord) (E : Exp b) (c : U Univ UnivOK b) (W : wfc_ c)
  : forall u u1 (H : reds u u1) x,
    cEl (xcmp_ (osucc b) (osucc b)) (inl c) u x (inl c) u1 (nodeRed b E c W u u1 H x) :=
  elRed_rel (stage_ b) Univ UnivEq UnivOK (xcmp_ b b) (wfsub_ b) UE
    (ex_red E) (ex_red_rel E) Ssym_ (Str_ b) (Sto_ b) (StoCoh_ b) (Sself_ b) (projT2 c) W.

Definition nodeExpRel (b : Ord) (E : Exp b) (c : U Univ UnivOK b) (W : wfc_ c)
  : forall u u1 (H : reds u u1) y,
    cEl (xcmp_ (osucc b) (osucc b)) (inl c) u (nodeExp b E c W u u1 H y) (inl c) u1 y :=
  elExp_rel (stage_ b) Univ UnivEq UnivOK (xcmp_ b b) (wfsub_ b) UE
    (ex_exp E) (ex_exp_rel E) Ssym_ (Str_ b) (Sto_ b) (StoCoh_ b) (Sself_ b) (projT2 c) W.

Fixpoint bigExp (alpha : Ord) : Exp alpha :=
  match alpha as a return Exp a with
  | ozero => Build_Exp ozero
      (fun s => Sub0_elim Univ UnivOK _ s) (fun s => Sub0_elim Univ UnivOK _ s)
      (fun s => Sub0_elim Univ UnivOK _ s) (fun s => Sub0_elim Univ UnivOK _ s)
  | osucc beta => Build_Exp _
      (fun s => match s as s0 return wfsub_ (osucc beta) s0 -> forall u u1, reds u u1 ->
                        StEl (stage_ (osucc beta)) s0 u -> StEl (stage_ (osucc beta)) s0 u1 with
                | inl c => nodeRed beta (bigExp beta) c
                | inr t => ex_red (bigExp beta) t
                end)
      (fun s => match s as s0 return wfsub_ (osucc beta) s0 -> forall u u1, reds u u1 ->
                        StEl (stage_ (osucc beta)) s0 u1 -> StEl (stage_ (osucc beta)) s0 u with
                | inl c => nodeExp beta (bigExp beta) c
                | inr t => ex_exp (bigExp beta) t
                end)
      (fun s => match s as s0 return forall (W : wfsub_ (osucc beta) s0) u u1 (H : reds u u1) x,
                        cEl (xcmp_ (osucc beta) (osucc beta)) s0 u x s0 u1
                          ((match s0 as s1 return wfsub_ (osucc beta) s1 -> forall u u1, reds u u1 ->
                                StEl (stage_ (osucc beta)) s1 u -> StEl (stage_ (osucc beta)) s1 u1 with
                            | inl c => nodeRed beta (bigExp beta) c
                            | inr t => ex_red (bigExp beta) t
                            end) W u u1 H x) with
                | inl c => nodeRedRel beta (bigExp beta) c
                | inr t => ex_red_rel (bigExp beta) t
                end)
      (fun s => match s as s0 return forall (W : wfsub_ (osucc beta) s0) u u1 (H : reds u u1) y,
                        cEl (xcmp_ (osucc beta) (osucc beta)) s0 u
                          ((match s0 as s1 return wfsub_ (osucc beta) s1 -> forall u u1, reds u u1 ->
                                StEl (stage_ (osucc beta)) s1 u1 -> StEl (stage_ (osucc beta)) s1 u with
                            | inl c => nodeExp beta (bigExp beta) c
                            | inr t => ex_exp (bigExp beta) t
                            end) W u u1 H y) s0 u1 y with
                | inl c => nodeExpRel beta (bigExp beta) c
                | inr t => ex_exp_rel (bigExp beta) t
                end)
  | osup T f => Build_Exp _
      (fun s => match s as s0 return wfsub_ (osup T f) s0 -> forall u u1, reds u u1 ->
                        StEl (stage_ (osup T f)) s0 u -> StEl (stage_ (osup T f)) s0 u1 with
                | existT _ p (inl c) => nodeRed (f p) (bigExp (f p)) c
                | existT _ p (inr t) => ex_red (bigExp (f p)) t
                end)
      (fun s => match s as s0 return wfsub_ (osup T f) s0 -> forall u u1, reds u u1 ->
                        StEl (stage_ (osup T f)) s0 u1 -> StEl (stage_ (osup T f)) s0 u with
                | existT _ p (inl c) => nodeExp (f p) (bigExp (f p)) c
                | existT _ p (inr t) => ex_exp (bigExp (f p)) t
                end)
      (fun s => match s as s0 return forall (W : wfsub_ (osup T f) s0) u u1 (H : reds u u1) x,
                        cEl (xcmp_ (osup T f) (osup T f)) s0 u x s0 u1
                          ((match s0 as s1 return wfsub_ (osup T f) s1 -> forall u u1, reds u u1 ->
                                StEl (stage_ (osup T f)) s1 u -> StEl (stage_ (osup T f)) s1 u1 with
                            | existT _ p (inl c) => nodeRed (f p) (bigExp (f p)) c
                            | existT _ p (inr t) => ex_red (bigExp (f p)) t
                            end) W u u1 H x) with
                | existT _ p (inl c) => nodeRedRel (f p) (bigExp (f p)) c
                | existT _ p (inr t) => ex_red_rel (bigExp (f p)) t
                end)
      (fun s => match s as s0 return forall (W : wfsub_ (osup T f) s0) u u1 (H : reds u u1) y,
                        cEl (xcmp_ (osup T f) (osup T f)) s0 u
                          ((match s0 as s1 return wfsub_ (osup T f) s1 -> forall u u1, reds u u1 ->
                                StEl (stage_ (osup T f)) s1 u1 -> StEl (stage_ (osup T f)) s1 u with
                            | existT _ p (inl c) => nodeExp (f p) (bigExp (f p)) c
                            | existT _ p (inr t) => ex_exp (bigExp (f p)) t
                            end) W u u1 H y) s0 u1 y with
                | existT _ p (inl c) => nodeExpRel (f p) (bigExp (f p)) c
                | existT _ p (inr t) => ex_exp_rel (bigExp (f p)) t
                end)
  end.

(* the working interface, at a node *)
Definition cRed {b} (c : U Univ UnivOK b) (W : wfc_ c) u u1 (H : reds u u1)
  (x : StEl (Ust_ b) c u) : StEl (Ust_ b) c u1 :=
  nodeRed b (bigExp b) c W u u1 H x.

Definition cExp {b} (c : U Univ UnivOK b) (W : wfc_ c) u u1 (H : reds u u1)
  (y : StEl (Ust_ b) c u1) : StEl (Ust_ b) c u :=
  nodeExp b (bigExp b) c W u u1 H y.

Definition cRed_rel {b} (c : U Univ UnivOK b) (W : wfc_ c) u u1 (H : reds u u1) x
  : cel Univ UnivEq UnivOK c u x c u1 (cRed c W u u1 H x) :=
  nodeRedRel b (bigExp b) c W u u1 H x.

Definition cExp_rel {b} (c : U Univ UnivOK b) (W : wfc_ c) u u1 (H : reds u u1) y
  : cel Univ UnivEq UnivOK c u (cExp c W u u1 H y) c u1 y :=
  nodeExpRel b (bigExp b) c W u u1 H y.
End Level.
