From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Codes.Def Codes.EqPER.
From Stdlib Require Import Arith.

(* Isomorphism of codes and the transport along it: paper Lemma 5.6,
   blueprint Lemma 8.6.

   The paper says "c ~= c' yields bijections theta_u".  In Rocq that is an
   elimination of a Prop into a Type, and it cannot be avoided: the equality
   on decodings has to be Prop-valued, because the refinement of an r_prf
   code -- which is what interprets Eq -- must be a Prop or Refine escalates
   one universe per object level; yet a Pi-code over a universe needs
   coh : eqS a u x u' x' -> Transp (b u' x') (b u x) where a is the u_k-code
   and b u x is the code carried by x, so a transport has to come out of
   that Prop.

   The way out is to bundle the whole mutual recursion into one record.  HJ
   holds the isomorphism *relation* hj_rel, Prop-valued, together with the
   transports hj_to and hj_pull, which take a proof of hj_rel as an
   ARGUMENT.  Nothing here eliminates a Prop into a Type: the construction
   only projects conjunctions of Props into Props, eliminates empty Props
   (two codes of different shape are not related, so the relation is False
   there) and decides the equality of two universe indices.  The witness
   that is needed halfway through the definition of hj_to at a Pi-code --
   that the pullback of an arbitrary argument of the target domain is
   heterogeneously equal to it -- is hj_pull_to, a FIELD, and that is what
   breaks the circularity that defeats every attempt to define the
   transport by recursion on the codes alone. *)

Record HJ (st st' : Stage) : Type := {
  hj_rel : st.(St) -> st'.(St) -> Prop;
  hj_to : forall s s', hj_rel s s' -> forall u, st.(StEl) s u -> st'.(StEl) s' u;
  hj_pull : forall s s', hj_rel s s' -> forall u, st'.(StEl) s' u -> st.(StEl) s u;
  hj_to_eq : forall s s' (P : hj_rel s s') u x u' x',
      st.(StEq) s u x u' x' ->
      st'.(StEq) s' u (hj_to s s' P u x) u' (hj_to s s' P u' x');
  hj_pull_eq : forall s s' (P : hj_rel s s') u y u' y',
      st'.(StEq) s' u y u' y' ->
      st.(StEq) s u (hj_pull s s' P u y) u' (hj_pull s s' P u' y');
  hj_pull_to : forall s s' (P : hj_rel s s') u y,
      st'.(StEq) s' u (hj_to s s' P u (hj_pull s s' P u y)) u y;
  hj_to_pull : forall s s' (P : hj_rel s s') u x,
      st.(StEq) s u (hj_pull s s' P u (hj_to s s' P u x)) u x;
  hj_irr : forall s s' (P P' : hj_rel s s') u x,
      st'.(StEq) s' u (hj_to s s' P u x) u (hj_to s s' P' u x)
}.
Arguments hj_rel {st st'}. Arguments hj_to {st st'}. Arguments hj_pull {st st'}.
Arguments hj_to_eq {st st'}. Arguments hj_pull_eq {st st'}.
Arguments hj_pull_to {st st'}. Arguments hj_to_pull {st st'}. Arguments hj_irr {st st'}.

(* The heterogeneous equality is derived, not primitive: x and x' correspond
   when some transport sends x to something equal to x'. *)
Definition hjhet {st st'} (h : HJ st st') s s' u (x : st.(StEl) s u) u' (x' : st'.(StEl) s' u')
  : Prop := exists P : hj_rel h s s', st'.(StEq) s' u (hj_to h s s' P u x) u' x'.

Lemma Good_tyeq T T' u : tyeq T T' -> Good T u -> Good T' u.
Proof. intros [n E] G; eapply (Rel_resp n T T' E); exact G. Qed.

Lemma Rel_tyeq T T' u u' : tyeq T T' -> Rel T u u' -> Rel T' u u'.
Proof. intros [n E] G; eapply (Rel_resp n T T' E); exact G. Qed.

Lemma tyeq_sym T T' : tyeq T T' -> tyeq T' T.
Proof. intros [n E]; exists n; apply eqty_sym; exact E. Qed.

Section IsoRefine.
  Context (st st' : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (h : HJ st st').
  Context (Hgood : StGood st) (Hgood' : StGood st').
  Context (HsymL : forall s, EqSym st s) (HtransL : forall s, EqTrans st s)
          (HsymR : forall s, EqSym st' s) (HtransR : forall s, EqTrans st' s).

  Local Notation Refine_ s := (Refine s UnivOK).
  Local Notation ElL := (El st Univ UnivOK).
  Local Notation ElR := (El st' Univ UnivOK).
  Local Notation eqL := st.(StEq).
  Local Notation eqR := st'.(StEq).

  (* The structural isomorphism.  The Pi clause has four conjuncts: the
     shadows agree, the domains are related, the codomains are related at
     corresponding arguments, and the transports of the two codes commute
     with the codomain isomorphisms -- the last is the naturality square,
     which the fundamental lemma discharges from functoriality of the
     isomorphism it builds.  The square is guarded by the heterogeneous
     relation at the domain: unguarded it cannot be composed, since
     transitivity would have to factor an arbitrary pair of codomain codes
     through the middle stage, and the middle stage need not contain
     anything isomorphic to them. *)
  Definition isoRefine {T T'} (r : Refine_ st T) (r' : Refine_ st' T') : Prop :=
    match r as r0 in Refine _ _ T0, r' as r0' in Refine _ _ T0'
      return Prop with
    | r_nat _ _ T _, r_nat _ _ T' _ => tyeq T T'
    | r_prop _ _ T _, r_prop _ _ T' _ => tyeq T T'
    | r_prf _ _ T _ _ H, r_prf _ _ T' _ _ H' => tyeq T T' /\ (H <-> H')
    | r_univ _ _ T m _ _, r_univ _ _ T' m' _ _ => tyeq T T' /\ m = m'
    | r_ne _ _ T _ _ _, r_ne _ _ T' _ _ _ => tyeq T T'
    | r_pi _ _ T _ _ _ a _ b _ coh _ _, r_pi _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        tyeq T T' /\
        hj_rel h a a' /\
        (forall u x u' x', hjhet h a a' u x u' x' -> hj_rel h (b u x) (b' u' x')) /\
        (forall u1 x1 u1' x1' y1 y1'
                (Hy : hjhet h a a' u1 x1 u1 y1) (Hy' : hjhet h a a' u1' x1' u1' y1')
                (r1 : eqL a u1 x1 u1' x1') (s1 : eqR a' u1 y1 u1' y1')
                (Q : hj_rel h (b u1 x1) (b' u1 y1))
                (Q' : hj_rel h (b u1' x1') (b' u1' y1'))
                v (w : st.(StEl) (b u1' x1') v),
           eqR (b' u1 y1) v (hj_to h _ _ Q v (tr (coh _ _ _ _ r1) v w))
                          v (tr (coh' _ _ _ _ s1) v (hj_to h _ _ Q' v w)))
    (* Sigma, verbatim the Pi clause: a Sigma-code carries the same data, so
       "the two codes are isomorphic" says the same thing about it.  What
       differs is only what the transport DOES with it, below. *)
    | r_sig _ _ T _ _ _ a _ b _ coh _ _, r_sig _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        tyeq T T' /\
        hj_rel h a a' /\
        (forall u x u' x', hjhet h a a' u x u' x' -> hj_rel h (b u x) (b' u' x')) /\
        (forall u1 x1 u1' x1' y1 y1'
                (Hy : hjhet h a a' u1 x1 u1 y1) (Hy' : hjhet h a a' u1' x1' u1' y1')
                (r1 : eqL a u1 x1 u1' x1') (s1 : eqR a' u1 y1 u1' y1')
                (Q : hj_rel h (b u1 x1) (b' u1 y1))
                (Q' : hj_rel h (b u1' x1') (b' u1' y1'))
                v (w : st.(StEl) (b u1' x1') v),
           eqR (b' u1 y1) v (hj_to h _ _ Q v (tr (coh _ _ _ _ r1) v w))
                          v (tr (coh' _ _ _ _ s1) v (hj_to h _ _ Q' v w)))
    | _, _ => False
    end.

  (* The transport, and its section.  Every branch is data built from data;
     the only Props consumed are conjunctions projected into Props, the
     empty Prop at a shape mismatch, and the equality of universe indices,
     which is decided. *)
  Definition toRefine {T T'} (r : Refine_ st T) (r' : Refine_ st' T')
    : isoRefine r r' -> forall u, ElL r u -> ElR r' u :=
    match r as r0 in Refine _ _ T0, r' as r0' in Refine _ _ T0'
      return isoRefine r0 r0' -> forall u, ElL r0 u -> ElR r0' u with
    | r_nat _ _ T _, r_nat _ _ T' _ => fun i u x =>
        (Datatypes.fst x, Good_tyeq T T' u i (Datatypes.snd x))
    | r_prop _ _ T _, r_prop _ _ T' _ => fun i u x =>
        (Datatypes.fst x, Good_tyeq T T' u i (Datatypes.snd x))
    | r_prf _ _ T _ _ H, r_prf _ _ T' _ _ H' => fun i u x =>
        (proj1 (proj2 i) (Datatypes.fst x), Good_tyeq T T' u (proj1 i) (Datatypes.snd x))
    | r_univ _ _ T m _ _, r_univ _ _ T' m' _ _ => fun i u x =>
        match Nat.eq_dec m m' with
        | left E => eq_rect m (fun k => Univ k u) x m' E
        | right NE => False_rect _ (NE (proj2 i))
        end
    | r_ne _ _ T _ _ _, r_ne _ _ T' _ _ _ => fun i u x => match x with end
    | r_pi _ _ T _ _ _ a _ b _ coh _ _, r_pi _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        fun i u f =>
          ((fun u1 y1 =>
              hj_to h (b u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1)) (b' u1 y1)
                (proj1 (proj2 (proj2 i)) u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1) u1 y1
                   (ex_intro _ (proj1 (proj2 i)) (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1)))
                (eapp u u1)
                (Datatypes.fst f u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1))),
           Good_tyeq T T' u (proj1 i) (Datatypes.snd f))
    (* At Sigma the argument is not quantified over: it IS the pair's first
       component, so the transport pushes it forward with hj_to and then
       pushes the second component along the codomain isomorphism at that
       very pair.  No pullback is needed, which is why this clause is
       shorter than Pi's. *)
    | r_sig _ _ T _ _ _ a _ b _ coh _ _, r_sig _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        fun i u p =>
          (existT _ (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)))
             (hj_to h (b (efst u) (projT1 (Datatypes.fst p)))
                      (b' (efst u)
                         (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst p))))
                (proj1 (proj2 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)) (efst u)
                   (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)))
                   (ex_intro _ (proj1 (proj2 i))
                      (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u)
                         (projT1 (Datatypes.fst p)))))
                (esnd u) (projT2 (Datatypes.fst p))),
           Good_tyeq T T' u (proj1 i) (Datatypes.snd p))
    | _, _ => fun i => match i with end
    end.

  (* The shadows of two isomorphic codes are layer-1 equal: every clause of
     isoRefine says so as its first conjunct, and this reads that conjunct off
     uniformly. *)
  Lemma isoRefine_sh {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    isoRefine r r' -> tyeq T T'.
  Proof.
    destruct r as [T0 e|T0 e|T0 p e P0|T0 m ok e|T0 A0 B0 e a ea b eb coh cL iL
                  |T0 A0 B0 e a ea b eb coh cL iL|T0 N e s0];
    destruct r' as [T0' e'|T0' e'|T0' p' e' P0'|T0' m' ok' e'
                   |T0' A0' B0' e' a' ea' b' eb' coh' cL' iL'
                   |T0' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T0' N' e' s0'];
      cbn [isoRefine]; try (intros i; exact (match i with end));
      try (exact (fun i => i)); exact (fun i => proj1 i).
  Qed.

  Definition pullRefine {T T'} (r : Refine_ st T) (r' : Refine_ st' T')
    : isoRefine r r' -> forall u, ElR r' u -> ElL r u :=
    match r as r0 in Refine _ _ T0, r' as r0' in Refine _ _ T0'
      return isoRefine r0 r0' -> forall u, ElR r0' u -> ElL r0 u with
    | r_nat _ _ T _, r_nat _ _ T' _ => fun i u y =>
        (Datatypes.fst y, Good_tyeq T' T u (tyeq_sym _ _ i) (Datatypes.snd y))
    | r_prop _ _ T _, r_prop _ _ T' _ => fun i u y =>
        (Datatypes.fst y, Good_tyeq T' T u (tyeq_sym _ _ i) (Datatypes.snd y))
    | r_prf _ _ T _ _ H, r_prf _ _ T' _ _ H' => fun i u y =>
        (proj2 (proj2 i) (Datatypes.fst y),
         Good_tyeq T' T u (tyeq_sym _ _ (proj1 i)) (Datatypes.snd y))
    | r_univ _ _ T m _ _, r_univ _ _ T' m' _ _ => fun i u y =>
        match Nat.eq_dec m m' with
        | left E => eq_rect m' (fun k => Univ k u) y m (eq_sym E)
        | right NE => False_rect _ (NE (proj2 i))
        end
    | r_ne _ _ T _ _ _, r_ne _ _ T' _ _ _ => fun i u y => match y with end
    | r_pi _ _ T _ _ _ a _ b _ coh _ _, r_pi _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        fun i u g =>
          ((fun u1 x1 =>
              hj_pull h (b u1 x1) (b' u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1))
                (proj1 (proj2 (proj2 i)) u1 x1 u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1)
                   (ex_intro _ (proj1 (proj2 i))
                      (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) u1 x1)))
                (eapp u u1)
                (Datatypes.fst g u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1))),
           Good_tyeq T' T u (tyeq_sym _ _ (proj1 i)) (Datatypes.snd g))
    | r_sig _ _ T _ _ _ a _ b _ coh _ _, r_sig _ _ T' _ _ _ a' _ b' _ coh' _ _ =>
        fun i u q =>
          (existT _ (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst q)))
             (hj_pull h (b (efst u)
                            (hj_pull h a a' (proj1 (proj2 i)) (efst u)
                               (projT1 (Datatypes.fst q))))
                        (b' (efst u) (projT1 (Datatypes.fst q)))
                (proj1 (proj2 (proj2 i)) (efst u)
                   (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst q)))
                   (efst u) (projT1 (Datatypes.fst q))
                   (ex_intro _ (proj1 (proj2 i))
                      (hj_pull_to h a a' (proj1 (proj2 i)) (efst u)
                         (projT1 (Datatypes.fst q)))))
                (esnd u) (projT2 (Datatypes.fst q))),
           Good_tyeq T' T u (tyeq_sym _ _ (proj1 i)) (Datatypes.snd q))
    | _, _ => fun i => match i with end
    end.
End IsoRefine.

Section IsoLaws.
  Context (st st' : Stage).
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (h : HJ st st').
  Context (Hgood : StGood st) (Hgood' : StGood st').
  Context (HsymL : forall s, EqSym st s) (HtransL : forall s, EqTrans st s)
          (HsymR : forall s, EqSym st' s) (HtransR : forall s, EqTrans st' s).

  Local Notation Refine_ s := (Refine s UnivOK).
  Local Notation ElL := (El st Univ UnivOK).
  Local Notation ElR := (El st' Univ UnivOK).
  Local Notation eqL := st.(StEq).
  Local Notation eqR := st'.(StEq).
  Local Notation eqElL := (eqEl st Univ UnivEq UnivOK).
  Local Notation eqElR := (eqEl st' Univ UnivEq UnivOK).
  Local Notation iso_ := (isoRefine st st' UnivOK h).
  Local Notation to_ := (toRefine st st' Univ UnivOK h).
  Local Notation pull_ := (pullRefine st st' Univ UnivOK h).

  (* hj_to is injective up to the equality, which is what turns the
     naturality square into its counterpart for hj_pull. *)
  Lemma to_inj s s' (P : hj_rel h s s') u x u' x' :
    eqR s' u (hj_to h s s' P u x) u' (hj_to h s s' P u' x') -> eqL s u x u' x'.
  Proof.
    intros Hq.
    eapply HtransL; [| apply (hj_to_pull h s s' P u' x')].
    eapply HtransL; [apply HsymL; apply (hj_to_pull h s s' P u x) |].
    apply (hj_pull_eq h s s' P); exact Hq.
  Qed.

  (* The naturality square for hj_pull, derived from the one for hj_to. *)
  Lemma pull_square s s' t t' (P : hj_rel h s s') (Q : hj_rel h t t')
    (trL : Transp st t s) (trR : Transp st' t' s')
    (Hsq : forall v w, eqR s' v (hj_to h s s' P v (tr trL v w))
                             v (tr trR v (hj_to h t t' Q v w)))
    v z : eqL s v (hj_pull h s s' P v (tr trR v z))
               v (tr trL v (hj_pull h t t' Q v z)).
  Proof.
    apply (to_inj s s' P).
    eapply HtransR; [apply (hj_pull_to h) |].
    eapply HtransR; [| apply HsymR; apply Hsq].
    apply HsymR; apply (tr_eq _ _ _ trR); apply (hj_pull_to h).
  Qed.

  (* The second direction of a Sigma-clause follows from the first: transport
     the equation along the reversed coherence, then undo the round trip with
     the composition and identity laws the code carries.  At Pi the two
     directions come from the hypothesis, quantified over the arguments; at
     Sigma the argument is the element's own projection, so the second
     direction has to be DERIVED, and this is the derivation.  It is needed at
     both stages, hence the two copies. *)
  Lemma sig_flipL (sa : st.(St)) (sb : forall u, st.(StEl) sa u -> st.(St))
    (cohb : forall u x u' x', eqL sa u x u' x' -> Transp st (sb u' x') (sb u x))
    (cLb : forall u0 x0 u1 x1 u2 x2
             (r01 : eqL sa u0 x0 u1 x1) (r12 : eqL sa u1 x1 u2 x2)
             (r02 : eqL sa u0 x0 u2 x2) v (y : st.(StEl) (sb u2 x2) v),
           goodS st (sb u2 x2) v y ->
           eqL (sb u0 x0) v (tr (cohb _ _ _ _ r01) v (tr (cohb _ _ _ _ r12) v y))
                          v (tr (cohb _ _ _ _ r02) v y))
    (iLb : forall u x (r : eqL sa u x u x) v (y : st.(StEl) (sb u x) v),
           goodS st (sb u x) v y -> eqL (sb u x) v (tr (cohb _ _ _ _ r) v y) v y)
    u0 x0 u1 x1 (r : eqL sa u0 x0 u1 x1) (r' : eqL sa u1 x1 u0 x0)
    v (y0 : st.(StEl) (sb u0 x0) v) v1 (y1 : st.(StEl) (sb u1 x1) v1) :
    eqL (sb u0 x0) v y0 v1 (tr (cohb _ _ _ _ r) v1 y1) ->
    eqL (sb u1 x1) v1 y1 v (tr (cohb _ _ _ _ r') v y0).
  Proof.
    intros E; apply HsymL.
    eapply HtransL; [apply (tr_eq _ _ _ (cohb _ _ _ _ r')); exact E |].
    eapply HtransL;
      [ apply (cLb u1 x1 u0 x0 u1 x1 r' r (Hgood sa u1 x1) v1 y1 (Hgood _ _ _))
      | apply iLb; apply Hgood ].
  Qed.

  Lemma sig_flipR (sa : st'.(St)) (sb : forall u, st'.(StEl) sa u -> st'.(St))
    (cohb : forall u x u' x', eqR sa u x u' x' -> Transp st' (sb u' x') (sb u x))
    (cLb : forall u0 x0 u1 x1 u2 x2
             (r01 : eqR sa u0 x0 u1 x1) (r12 : eqR sa u1 x1 u2 x2)
             (r02 : eqR sa u0 x0 u2 x2) v (y : st'.(StEl) (sb u2 x2) v),
           goodS st' (sb u2 x2) v y ->
           eqR (sb u0 x0) v (tr (cohb _ _ _ _ r01) v (tr (cohb _ _ _ _ r12) v y))
                          v (tr (cohb _ _ _ _ r02) v y))
    (iLb : forall u x (r : eqR sa u x u x) v (y : st'.(StEl) (sb u x) v),
           goodS st' (sb u x) v y -> eqR (sb u x) v (tr (cohb _ _ _ _ r) v y) v y)
    u0 x0 u1 x1 (r : eqR sa u0 x0 u1 x1) (r' : eqR sa u1 x1 u0 x0)
    v (y0 : st'.(StEl) (sb u0 x0) v) v1 (y1 : st'.(StEl) (sb u1 x1) v1) :
    eqR (sb u0 x0) v y0 v1 (tr (cohb _ _ _ _ r) v1 y1) ->
    eqR (sb u1 x1) v1 y1 v (tr (cohb _ _ _ _ r') v y0).
  Proof.
    intros E; apply HsymR.
    eapply HtransR; [apply (tr_eq _ _ _ (cohb _ _ _ _ r')); exact E |].
    eapply HtransR;
      [ apply (cLb u1 x1 u0 x0 u1 x1 r' r (Hgood' sa u1 x1) v1 y1 (Hgood' _ _ _))
      | apply iLb; apply Hgood' ].
  Qed.

  Ltac iso_absurd := try (intros i; exact (match i with end)).

  Lemma toRefine_eq {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (i : iso_ r r') u x u' x',
      eqElL r u x u' x' -> eqElR r' u (to_ r r' i u x) u' (to_ r r' i u' x').
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i u x u' x' H.
    - destruct H as [H1 H2]; split; [exact H1 | eapply Rel_tyeq; [exact i | exact H2]].
    - destruct H as [H1 H2]; split; [exact H1 | eapply Rel_tyeq; [exact i | exact H2]].
    - eapply Rel_tyeq; [exact (proj1 i) | exact H].
    - destruct (Nat.eq_dec m m') as [E | NE]; [destruct E; exact H | destruct (NE (proj2 i))].
    - destruct H as [H HR].
      split; [| eapply Rel_tyeq; [exact (proj1 i) | exact HR]].
      intros u1 y1 u1' y1' s1 s1'.
      pose proof (hj_pull_eq h a a' (proj1 (proj2 i)) _ _ _ _ s1) as r1.
      pose proof (hj_pull_eq h a a' (proj1 (proj2 i)) _ _ _ _ s1') as r1'.
      destruct (H _ _ _ _ r1 r1') as [H1 H2]; split.
      + eapply HtransR; [apply (hj_to_eq h _ _ _ _ _ _ _ H1) |].
        apply (proj2 (proj2 (proj2 i))); eexists; apply (hj_pull_to h).
      + eapply HtransR; [apply (hj_to_eq h _ _ _ _ _ _ _ H2) |].
        apply (proj2 (proj2 (proj2 i))); eexists; apply (hj_pull_to h).
    - (* Sigma: the first components' relation transports by hj_to_eq, and the
         second ones by hj_to_eq followed by the naturality square, whose two
         heterogeneous side conditions hold at (x, hj_to x) by hj_irr. *)
      destruct H as [[rz Ey] [[rz' Ey'] HR]].
      split; [| split; [| eapply Rel_tyeq; [exact (proj1 i) | exact HR]]].
      + exists (hj_to_eq h a a' (proj1 (proj2 i)) _ _ _ _ rz).
        eapply HtransR; [apply (hj_to_eq h _ _ _ _ _ _ _ Ey) |].
        apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_irr h).
      + exists (hj_to_eq h a a' (proj1 (proj2 i)) _ _ _ _ rz').
        eapply HtransR; [apply (hj_to_eq h _ _ _ _ _ _ _ Ey') |].
        apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_irr h).
    - destruct x.
  Qed.

  Lemma pullRefine_eq {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (i : iso_ r r') u y u' y',
      eqElR r' u y u' y' -> eqElL r u (pull_ r r' i u y) u' (pull_ r r' i u' y').
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i u y u' y' H.
    - destruct H as [H1 H2]; split;
        [exact H1 | eapply Rel_tyeq; [apply tyeq_sym; exact i | exact H2]].
    - destruct H as [H1 H2]; split;
        [exact H1 | eapply Rel_tyeq; [apply tyeq_sym; exact i | exact H2]].
    - eapply Rel_tyeq; [apply tyeq_sym; exact (proj1 i) | exact H].
    - destruct (Nat.eq_dec m m') as [E | NE]; [destruct E; exact H | destruct (NE (proj2 i))].
    - destruct H as [H HR].
      split; [| eapply Rel_tyeq; [apply tyeq_sym; exact (proj1 i) | exact HR]].
      intros u1 x1 u1' x1' r1 r1'.
      pose proof (hj_to_eq h a a' (proj1 (proj2 i)) _ _ _ _ r1) as s1.
      pose proof (hj_to_eq h a a' (proj1 (proj2 i)) _ _ _ _ r1') as s1'.
      destruct (H _ _ _ _ s1 s1') as [H1 H2]; split.
      + eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ H1) |].
        eapply pull_square; intros;
          apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_irr h).
      + eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ H2) |].
        eapply pull_square; intros;
          apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_irr h).
    - (* Sigma: dually, and the square for hj_pull is pull_square, whose side
         conditions hold at (hj_pull y, y) by hj_pull_to. *)
      destruct H as [[sz Ey] [[sz' Ey'] HR]].
      split; [| split;
              [| eapply Rel_tyeq; [apply tyeq_sym; exact (proj1 i) | exact HR]]].
      + exists (hj_pull_eq h a a' (proj1 (proj2 i)) _ _ _ _ sz).
        eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ Ey) |].
        eapply pull_square; intros;
          apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_pull_to h).
      + exists (hj_pull_eq h a a' (proj1 (proj2 i)) _ _ _ _ sz').
        eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ Ey') |].
        eapply pull_square; intros;
          apply (proj2 (proj2 (proj2 i)));
          exists (proj1 (proj2 i)); apply (hj_pull_to h).
    - destruct y.
  Qed.
  (* Two proofs of the isomorphism give equal pullbacks. *)
  Lemma pull_irr s s' (P P' : hj_rel h s s') u y :
    eqL s u (hj_pull h s s' P u y) u (hj_pull h s s' P' u y).
  Proof.
    apply (to_inj s s' P).
    eapply HtransR; [apply (hj_pull_to h) |].
    apply HsymR.
    eapply HtransR; [apply (hj_irr h s s' P P') | apply (hj_pull_to h)].
  Qed.

  Lemma toRefine_to_pull {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (i : iso_ r r') u x,
      eqElL r u x u x -> eqElL r u (pull_ r r' i u (to_ r r' i u x)) u x.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i u x H.
    - split; [reflexivity | exact (Datatypes.snd x)].
    - split; [tauto | exact (Datatypes.snd x)].
    - exact (Datatypes.snd x).
    - destruct (Nat.eq_dec m m') as [E | NE]; [destruct E; exact H | destruct (NE (proj2 i))].
    - destruct H as [Hf HR]; split; [| exact HR].
      intros u1 x1 u1' x1' r2 r2'.
      pose proof (hj_to_pull h a a' (proj1 (proj2 i)) u1 x1) as ez.
      pose proof (HsymL a _ _ _ _ ez) as ez'.
      assert (S1 : eqR (b' u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1)) (eapp u u1)
                     (hj_to h _ _ (proj1 (proj2 (proj2 i)) u1
                        (hj_pull h a a' (proj1 (proj2 i)) u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1))
                        u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1)
                        (ex_intro _ (proj1 (proj2 i))
                           (hj_pull_to h a a' (proj1 (proj2 i)) u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1))))
                        (eapp u u1)
                        (Datatypes.fst x u1 (hj_pull h a a' (proj1 (proj2 i)) u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1))))
                     (eapp u u1)
                     (hj_to h _ _ (proj1 (proj2 (proj2 i)) u1 x1 u1
                        (hj_to h a a' (proj1 (proj2 i)) u1 x1)
                        (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) u1 x1)))
                        (eapp u u1)
                        (tr (coh _ _ _ _ ez') (eapp u u1)
                           (Datatypes.fst x u1 (hj_pull h a a' (proj1 (proj2 i)) u1 (hj_to h a a' (proj1 (proj2 i)) u1 x1)))))).
      { apply HsymR.
        eapply HtransR;
          [ apply ((proj2 (proj2 (proj2 i))) u1 x1 u1 _ _ _
                     (ex_intro _ (proj1 (proj2 i))
                        (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) u1 x1))
                     (ex_intro _ (proj1 (proj2 i))
                        (hj_pull_to h a a' (proj1 (proj2 i)) u1
                           (hj_to h a a' (proj1 (proj2 i)) u1 x1)))
                     ez' (Hgood' a' u1 _))
          | apply iL'; apply Hgood' ]. }
      split.
      + eapply HtransL; [| exact (proj1 (Hf u1 x1 u1' x1' r2 r2'))].
        eapply HtransL; [| apply HsymL; exact (proj1 (Hf u1 x1 u1 _ ez' ez))].
        eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ S1) | apply (hj_to_pull h)].
      + eapply HtransL; [exact (proj2 (Hf u1 x1 u1' x1' r2 r2')) |].
        apply (tr_eq _ _ _ (coh _ _ _ _ r2')); apply HsymL.
        eapply HtransL; [| apply HsymL; exact (proj1 (Hf u1 x1 u1 _ ez' ez))].
        eapply HtransL; [apply (hj_pull_eq h _ _ _ _ _ _ _ S1) | apply (hj_to_pull h)].
    - (* Sigma.  The transport round trip is the identity on the first
         component up to hj_to_pull, and on the second one up to the
         naturality square followed by the codomain's identity law. *)
      destruct H as [H1 [H2 HR]].
      split; [| split; [| exact HR]].
      + exists (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))).
        eapply HtransL; [| apply (hj_to_pull h) ].
        apply (hj_pull_eq h).
        apply HsymR.
        eapply HtransR;
          [ apply ((proj2 (proj2 (proj2 i))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i)) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))))
                     (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))))
                     (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (Hgood' a' (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))))
          | apply iL'; apply Hgood' ].
      + exists (HsymL a _ _ _ _ (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))).
        apply (sig_flipL a b coh cL iL (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x))
                 (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (HsymL a _ _ _ _ (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))))).
        eapply HtransL; [| apply (hj_to_pull h) ].
        apply (hj_pull_eq h).
        apply HsymR.
        eapply HtransR;
          [ apply ((proj2 (proj2 (proj2 i))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))) (efst u) (projT1 (Datatypes.fst x)) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))
                     (ex_intro _ (proj1 (proj2 i)) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))))
                     (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))))
                     (hj_to_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (Hgood' a' (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x)))))
          | apply iL'; apply Hgood' ].
    - destruct x.
  Qed.

  Lemma toRefine_pull_to {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (i : iso_ r r') u y,
      eqElR r' u y u y -> eqElR r' u (to_ r r' i u (pull_ r r' i u y)) u y.
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i u y H.
    - split; [reflexivity | exact (Datatypes.snd y)].
    - split; [tauto | exact (Datatypes.snd y)].
    - exact (Datatypes.snd y).
    - destruct (Nat.eq_dec m m') as [E | NE]; [destruct E; exact H | destruct (NE (proj2 i))].
    - destruct H as [Hg HR]; split; [| exact HR].
      intros u1 y1 u1' y1' s2 s2'.
      pose proof (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1) as s0.
      pose proof (HsymR a' _ _ _ _ s0) as s0'.
      split.
      + eapply HtransR; [| exact (proj1 (Hg u1 y1 u1' y1' s2 s2'))].
        eapply HtransR; [| apply HsymR; exact (proj1 (Hg u1 y1 u1 _ s0' s0))].
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _ (iL _ _ (Hgood a u1 _) _ _ (Hgood _ _ _)))) |].
        eapply HtransR;
          [apply ((proj2 (proj2 (proj2 i))) u1 _ u1 _ y1 _
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1))
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) u1
                          (hj_pull h a a' (proj1 (proj2 i)) u1 y1)))) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ s0')); apply (hj_pull_to h).
      + eapply HtransR; [exact (proj2 (Hg u1 y1 u1' y1' s2 s2')) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ s2')); apply HsymR.
        eapply HtransR; [| apply HsymR; exact (proj1 (Hg u1 y1 u1 _ s0' s0))].
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _ (iL _ _ (Hgood a u1 _) _ _ (Hgood _ _ _)))) |].
        eapply HtransR;
          [apply ((proj2 (proj2 (proj2 i))) u1 _ u1 _ y1 _
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1))
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) u1
                          (hj_pull h a a' (proj1 (proj2 i)) u1 y1)))) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ s0')); apply (hj_pull_to h).
    - (* Sigma, the other round trip. *)
      destruct H as [H1 [H2 HR]].
      split; [| split; [| exact HR]].
      + exists (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))).
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _
                        (iL (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) _ _ (Hgood _ _ _)))) |].
        eapply HtransR;
          [ apply ((proj2 (proj2 (proj2 i))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (hj_to h a a' (proj1 (proj2 i)) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) (projT1 (Datatypes.fst y))
                     (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))))
                     (ex_intro _ (proj1 (proj2 i)) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))))
                     (Hgood a (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))))); apply (hj_pull_to h).
      + exists (HsymR a' _ _ _ _ (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))).
        apply (sig_flipR a' b' coh' cL' iL' (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) (efst u) (projT1 (Datatypes.fst y))
                 (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (HsymR a' _ _ _ _ (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))))).
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _
                        (iL (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (Hgood a (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) _ _ (Hgood _ _ _)))) |].
        eapply HtransR;
          [ apply ((proj2 (proj2 (proj2 i))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))) (hj_to h a a' (proj1 (proj2 i)) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) (projT1 (Datatypes.fst y))
                     (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))))
                     (ex_intro _ (proj1 (proj2 i)) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))))
                     (Hgood a (efst u) (hj_pull h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y)))) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ (hj_pull_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst y))))); apply (hj_pull_to h).
    - destruct y.
  Qed.

  (* Any two proofs of the isomorphism induce equal transports.  This is
     what makes the naturality square above -- which quantifies over
     arbitrary relatedness proofs -- no stronger than its instance at the
     canonical ones. *)
  (* The transport at a Sigma-code is COMPONENTWISE: toRefine's r_sig branch
     pushes the first component along the domains' isomorphism and the second
     along the codomains' at that very component.  Both are `reflexivity` HERE,
     where the two stages are variables and one iota step on the pair of
     refinements does it.  At a concrete pair of Sigma-FAMILIES they are not
     provable in practice: the conversion checker would be asked to unfold hj at
     a Brouwer tree built from rk.  So functionality on terms instantiates these
     -- through cto_refine, below -- rather than reducing anything itself. *)
  Lemma toRefine_sig_fst {T T' A0 B0 A0' B0'}
    (e : eval T (esig A0 B0)) (a : st.(St)) (ea : tyeq (StSh st a) A0)
    (b : forall u, st.(StEl) a u -> st.(St))
    (eb : forall u x, tyeq (StSh st (b u x)) (eapp B0 u))
    (coh : forall u x u' x', st.(StEq) a u x u' x' -> Transp st (b u' x') (b u x))
    cL iL
    (e' : eval T' (esig A0' B0')) (a' : st'.(St)) (ea' : tyeq (StSh st' a') A0')
    (b' : forall u, st'.(StEl) a' u -> st'.(St))
    (eb' : forall u x, tyeq (StSh st' (b' u x)) (eapp B0' u))
    (coh' : forall u x u' x', st'.(StEq) a' u x u' x' -> Transp st' (b' u' x') (b' u x))
    cL' iL'
    (i : iso_ (r_sig st UnivOK T A0 B0 e a ea b eb coh cL iL)
              (r_sig st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL'))
    u p :
    projT1 (Datatypes.fst
              (to_ (r_sig st UnivOK T A0 B0 e a ea b eb coh cL iL)
                   (r_sig st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL')
                   i u p))
    = hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)).
  Proof. reflexivity. Qed.

  Lemma toRefine_sig_snd {T T' A0 B0 A0' B0'}
    (e : eval T (esig A0 B0)) (a : st.(St)) (ea : tyeq (StSh st a) A0)
    (b : forall u, st.(StEl) a u -> st.(St))
    (eb : forall u x, tyeq (StSh st (b u x)) (eapp B0 u))
    (coh : forall u x u' x', st.(StEq) a u x u' x' -> Transp st (b u' x') (b u x))
    cL iL
    (e' : eval T' (esig A0' B0')) (a' : st'.(St)) (ea' : tyeq (StSh st' a') A0')
    (b' : forall u, st'.(StEl) a' u -> st'.(St))
    (eb' : forall u x, tyeq (StSh st' (b' u x)) (eapp B0' u))
    (coh' : forall u x u' x', st'.(StEq) a' u x u' x' -> Transp st' (b' u' x') (b' u x))
    cL' iL'
    (i : iso_ (r_sig st UnivOK T A0 B0 e a ea b eb coh cL iL)
              (r_sig st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL'))
    u p :
    projT2 (Datatypes.fst
              (to_ (r_sig st UnivOK T A0 B0 e a ea b eb coh cL iL)
                   (r_sig st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL')
                   i u p))
    = hj_to h (b (efst u) (projT1 (Datatypes.fst p)))
              (b' (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u)
                              (projT1 (Datatypes.fst p))))
              (proj1 (proj2 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)) (efst u)
                 (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst p)))
                 (ex_intro _ (proj1 (proj2 i))
                    (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u)
                       (projT1 (Datatypes.fst p)))))
              (esnd u) (projT2 (Datatypes.fst p)).
  Proof. reflexivity. Qed.

  (* And at a Pi-code.  Here the transport does not merely push components
     across: it applies the function at the argument PULLED BACK along the
     domains' isomorphism, which is why this clause is the one with real content
     for the consumer -- piApp_to has to reconcile that pullback with the
     argument in hand, using cto_pull and the function's own respect for the
     domain's equality. *)
  Lemma toRefine_pi_app {T T' A0 B0 A0' B0'}
    (e : eval T (epi A0 B0)) (a : st.(St)) (ea : tyeq (StSh st a) A0)
    (b : forall u, st.(StEl) a u -> st.(St))
    (eb : forall u x, tyeq (StSh st (b u x)) (eapp B0 u))
    (coh : forall u x u' x', st.(StEq) a u x u' x' -> Transp st (b u' x') (b u x))
    cL iL
    (e' : eval T' (epi A0' B0')) (a' : st'.(St)) (ea' : tyeq (StSh st' a') A0')
    (b' : forall u, st'.(StEl) a' u -> st'.(St))
    (eb' : forall u x, tyeq (StSh st' (b' u x)) (eapp B0' u))
    (coh' : forall u x u' x', st'.(StEq) a' u x u' x' -> Transp st' (b' u' x') (b' u x))
    cL' iL'
    (i : iso_ (r_pi st UnivOK T A0 B0 e a ea b eb coh cL iL)
              (r_pi st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL'))
    u f u1 y1 :
    Datatypes.fst
      (to_ (r_pi st UnivOK T A0 B0 e a ea b eb coh cL iL)
           (r_pi st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL') i u f) u1 y1
    = hj_to h (b u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1)) (b' u1 y1)
              (proj1 (proj2 (proj2 i)) u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1)
                 u1 y1
                 (ex_intro _ (proj1 (proj2 i))
                    (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1)))
              (eapp u u1)
              (Datatypes.fst f u1 (hj_pull h a a' (proj1 (proj2 i)) u1 y1)).
  Proof. reflexivity. Qed.

  Lemma toRefine_irr {T T'} (r : Refine_ st T) (r' : Refine_ st' T') :
    forall (i i' : iso_ r r') u x,
      eqElL r u x u x -> eqElR r' u (to_ r r' i u x) u (to_ r r' i' u x).
  Proof.
    destruct r as [T e|T e|T p e P0|T m ok e|T A0 B0 e a ea b eb coh cL iL|T A0 B0 e a ea b eb coh cL iL|T N e s0];
    destruct r' as [T' e'|T' e'|T' p' e' P0'|T' m' ok' e'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' A0' B0' e' a' ea' b' eb' coh' cL' iL'|T' N' e' s0'];
      cbn; iso_absurd; intros i i' u x H.
    - split; [reflexivity | exact (Good_tyeq T T' u i (Datatypes.snd x))].
    - split; [tauto | exact (Good_tyeq T T' u i (Datatypes.snd x))].
    - exact (Good_tyeq T T' u (proj1 i) (Datatypes.snd x)).
    - destruct (Nat.eq_dec m m') as [E | NE]; [destruct E; exact H | destruct (NE (proj2 i))].
    - destruct H as [Hf HR]; split;
        [| exact (Rel_tyeq T T' u u (proj1 i) HR)].
      intros u1 y1 u1' y1' s2 s2'.
      pose proof (pull_irr a a' (proj1 (proj2 i)) (proj1 (proj2 i')) u1 y1) as ee.
      pose proof (HsymL a _ _ _ _ ee) as ee'.
      pose proof (toRefine_eq (r_pi st UnivOK T A0 B0 e a ea b eb coh cL iL)
                              (r_pi st' UnivOK T' A0' B0' e' a' ea' b' eb' coh' cL' iL')
                              i' u x u x (conj Hf HR)) as Hi'.
      destruct Hi' as [Hi' _]; cbn in Hi'.
      split.
      + eapply HtransR; [| exact (proj1 (Hi' u1 y1 u1' y1' s2 s2'))].
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _ (proj1 (Hf u1 _ u1 _ ee ee'))) |].
        eapply HtransR;
          [apply ((proj2 (proj2 (proj2 i))) u1 _ u1 _ y1 y1
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1))
                    (ex_intro _ (proj1 (proj2 i'))
                       (hj_pull_to h a a' (proj1 (proj2 i')) u1 y1))
                    ee (Hgood' a' u1 y1)) |].
        apply iL'; apply Hgood'.
      + eapply HtransR; [exact (proj2 (Hi' u1 y1 u1' y1' s2 s2')) |].
        apply (tr_eq _ _ _ (coh' _ _ _ _ s2')); apply HsymR.
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _ (proj1 (Hf u1 _ u1 _ ee ee'))) |].
        eapply HtransR;
          [apply ((proj2 (proj2 (proj2 i))) u1 _ u1 _ y1 y1
                    (ex_intro _ (proj1 (proj2 i))
                       (hj_pull_to h a a' (proj1 (proj2 i)) u1 y1))
                    (ex_intro _ (proj1 (proj2 i'))
                       (hj_pull_to h a a' (proj1 (proj2 i')) u1 y1))
                    ee (Hgood' a' u1 y1)) |].
        apply iL'; apply Hgood'.
    - (* Sigma: the two transports differ only by hj_irr on the first
         component, and the square carries that difference to the second. *)
      destruct H as [H1 [H2 HR]].
      split; [| split; [| exact (Rel_tyeq T T' u u (proj1 i) HR)]].
      + exists (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x))).
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _
                        (iL (efst u) (projT1 (Datatypes.fst x)) (Hgood a (efst u) (projT1 (Datatypes.fst x))) _ _ (Hgood _ _ _)))) |].
        apply ((proj2 (proj2 (proj2 i))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h a a' (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))
                 (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))))
                 (ex_intro _ (proj1 (proj2 i')) (hj_irr h a a' (proj1 (proj2 i')) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x))))
                 (Hgood a (efst u) (projT1 (Datatypes.fst x))) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))).
      + exists (HsymR a' _ _ _ _ (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))).
        apply (sig_flipR a' b' coh' cL' iL' (efst u) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (efst u) (hj_to h a a' (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))
                 (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x))) (HsymR a' _ _ _ _ (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x))))).
        eapply HtransR;
          [ apply (hj_to_eq h _ _ _ _ _ _ _
                     (HsymL _ _ _ _ _
                        (iL (efst u) (projT1 (Datatypes.fst x)) (Hgood a (efst u) (projT1 (Datatypes.fst x))) _ _ (Hgood _ _ _)))) |].
        apply ((proj2 (proj2 (proj2 i))) (efst u) (projT1 (Datatypes.fst x)) (efst u) (projT1 (Datatypes.fst x)) (hj_to h a a' (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))) (hj_to h a a' (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))
                 (ex_intro _ (proj1 (proj2 i)) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i)) (efst u) (projT1 (Datatypes.fst x))))
                 (ex_intro _ (proj1 (proj2 i')) (hj_irr h a a' (proj1 (proj2 i')) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x))))
                 (Hgood a (efst u) (projT1 (Datatypes.fst x))) (hj_irr h a a' (proj1 (proj2 i)) (proj1 (proj2 i')) (efst u) (projT1 (Datatypes.fst x)))).
    - destruct x.
  Qed.

  (* One level up. *)
  Definition HJ_next
    : HJ (Stage_next st Univ UnivEq UnivOK) (Stage_next st' Univ UnivEq UnivOK).
  Proof.
    unshelve refine (Build_HJ (Stage_next st Univ UnivEq UnivOK)
                              (Stage_next st' Univ UnivEq UnivOK)
      (fun c c' => iso_ (projT2 c) (projT2 c')) _ _ _ _ _ _ _).
    - exact (fun c c' P u x =>
        exist (fun z => eqElR (projT2 c') u z u z)
              (to_ (projT2 c) (projT2 c') P u (proj1_sig x))
              (toRefine_eq (projT2 c) (projT2 c') P u (proj1_sig x) u (proj1_sig x)
                 (proj2_sig x))).
    - exact (fun c c' P u y =>
        exist (fun z => eqElL (projT2 c) u z u z)
              (pull_ (projT2 c) (projT2 c') P u (proj1_sig y))
              (pullRefine_eq (projT2 c) (projT2 c') P u (proj1_sig y) u (proj1_sig y)
                 (proj2_sig y))).
    - exact (fun c c' P u x u' x' H =>
        toRefine_eq (projT2 c) (projT2 c') P u (proj1_sig x) u' (proj1_sig x') H).
    - exact (fun c c' P u y u' y' H =>
        pullRefine_eq (projT2 c) (projT2 c') P u (proj1_sig y) u' (proj1_sig y') H).
    - exact (fun c c' P u y =>
        toRefine_pull_to (projT2 c) (projT2 c') P u (proj1_sig y) (proj2_sig y)).
    - exact (fun c c' P u x =>
        toRefine_to_pull (projT2 c) (projT2 c') P u (proj1_sig x) (proj2_sig x)).
    - exact (fun c c' P P' u x =>
        toRefine_irr (projT2 c) (projT2 c') P P' u (proj1_sig x) (proj2_sig x)).
  Defined.
End IsoLaws.

(* Combinators, one per way of building a stage. *)
Definition HJ_emptyL st' : HJ Stage_empty st'.
Proof. unshelve refine (Build_HJ Stage_empty st' (fun s => match s with end) _ _ _ _ _ _ _);
  intros []. Defined.

Definition HJ_emptyR st : HJ st Stage_empty.
Proof. unshelve refine (Build_HJ st Stage_empty (fun s s' => match s' with end) _ _ _ _ _ _ _);
  intros s []. Defined.

Definition HJ_sum_L {a b c} (hac : HJ a c) (hbc : HJ b c) : HJ (Stage_sum a b) c.
Proof.
  unshelve refine (Build_HJ (Stage_sum a b) c
    (fun s => match s with inl s => hj_rel hac s | inr s => hj_rel hbc s end) _ _ _ _ _ _ _).
  - intros [s|s]; [apply (hj_to hac) | apply (hj_to hbc)].
  - intros [s|s]; [apply (hj_pull hac) | apply (hj_pull hbc)].
  - intros [s|s]; [apply (hj_to_eq hac) | apply (hj_to_eq hbc)].
  - intros [s|s]; [apply (hj_pull_eq hac) | apply (hj_pull_eq hbc)].
  - intros [s|s]; [apply (hj_pull_to hac) | apply (hj_pull_to hbc)].
  - intros [s|s]; [apply (hj_to_pull hac) | apply (hj_to_pull hbc)].
  - intros [s|s]; [apply (hj_irr hac) | apply (hj_irr hbc)].
Defined.

Definition HJ_sum_R {a b c} (hab : HJ a b) (hac : HJ a c) : HJ a (Stage_sum b c).
Proof.
  unshelve refine (Build_HJ a (Stage_sum b c)
    (fun s s' => match s' with inl s' => hj_rel hab s s' | inr s' => hj_rel hac s s' end)
    _ _ _ _ _ _ _).
  - intros s [s'|s']; [apply (hj_to hab) | apply (hj_to hac)].
  - intros s [s'|s']; [apply (hj_pull hab) | apply (hj_pull hac)].
  - intros s [s'|s']; [apply (hj_to_eq hab) | apply (hj_to_eq hac)].
  - intros s [s'|s']; [apply (hj_pull_eq hab) | apply (hj_pull_eq hac)].
  - intros s [s'|s']; [apply (hj_pull_to hab) | apply (hj_pull_to hac)].
  - intros s [s'|s']; [apply (hj_to_pull hab) | apply (hj_to_pull hac)].
  - intros s [s'|s']; [apply (hj_irr hab) | apply (hj_irr hac)].
Defined.

Definition HJ_sup_L {T F c} (H : forall p, HJ (F p) c) : HJ (Stage_sup T F) c.
Proof.
  unshelve refine (Build_HJ (Stage_sup T F) c
    (fun s => hj_rel (H (projT1 s)) (projT2 s)) _ _ _ _ _ _ _).
  - intros [p s]; apply (hj_to (H p)).
  - intros [p s]; apply (hj_pull (H p)).
  - intros [p s]; apply (hj_to_eq (H p)).
  - intros [p s]; apply (hj_pull_eq (H p)).
  - intros [p s]; apply (hj_pull_to (H p)).
  - intros [p s]; apply (hj_to_pull (H p)).
  - intros [p s]; apply (hj_irr (H p)).
Defined.

Definition HJ_sup_R {a T' F'} (H : forall p', HJ a (F' p')) : HJ a (Stage_sup T' F').
Proof.
  unshelve refine (Build_HJ a (Stage_sup T' F')
    (fun s s' => hj_rel (H (projT1 s')) s (projT2 s')) _ _ _ _ _ _ _).
  - intros s [p' s']; apply (hj_to (H p')).
  - intros s [p' s']; apply (hj_pull (H p')).
  - intros s [p' s']; apply (hj_to_eq (H p')).
  - intros s [p' s']; apply (hj_pull_eq (H p')).
  - intros s [p' s']; apply (hj_pull_to (H p')).
  - intros s [p' s']; apply (hj_to_pull (H p')).
  - intros s [p' s']; apply (hj_irr (H p')).
Defined.

(* Restrictions along the injections.  With these, the hierarchy below can
   be built so that *every* way of peeling a stage -- on either side -- is
   definitional, which is what makes the inductions of Codes/IsoPER.v
   possible: the relation at a symbolic element of Sub alpha does not reduce,
   but after a case analysis on that element it does, and the peeled record
   is literally hj at the smaller stages. *)
Definition HJ_restrL {a b c} (H : HJ (Stage_sum a b) c) : HJ a c :=
  Build_HJ a c
    (fun s s' => hj_rel H (inl s) s')
    (fun s s' => hj_to H (inl s) s')
    (fun s s' => hj_pull H (inl s) s')
    (fun s s' => hj_to_eq H (inl s) s')
    (fun s s' => hj_pull_eq H (inl s) s')
    (fun s s' => hj_pull_to H (inl s) s')
    (fun s s' => hj_to_pull H (inl s) s')
    (fun s s' => hj_irr H (inl s) s').

Definition HJ_restrR {a b c} (H : HJ a (Stage_sum b c)) : HJ a b :=
  Build_HJ a b
    (fun s s' => hj_rel H s (inl s'))
    (fun s s' => hj_to H s (inl s'))
    (fun s s' => hj_pull H s (inl s'))
    (fun s s' => hj_to_eq H s (inl s'))
    (fun s s' => hj_pull_eq H s (inl s'))
    (fun s s' => hj_pull_to H s (inl s'))
    (fun s s' => hj_to_pull H s (inl s'))
    (fun s s' => hj_irr H s (inl s')).

Definition HJ_supL {T F c} (p : Pred T) (H : HJ (Stage_sup T F) c) : HJ (F p) c :=
  Build_HJ (F p) c
    (fun s s' => hj_rel H (existT _ p s) s')
    (fun s s' => hj_to H (existT _ p s) s')
    (fun s s' => hj_pull H (existT _ p s) s')
    (fun s s' => hj_to_eq H (existT _ p s) s')
    (fun s s' => hj_pull_eq H (existT _ p s) s')
    (fun s s' => hj_pull_to H (existT _ p s) s')
    (fun s s' => hj_to_pull H (existT _ p s) s')
    (fun s s' => hj_irr H (existT _ p s) s').

Definition HJ_supR {a T' F'} (p' : Pred T') (H : HJ a (Stage_sup T' F')) : HJ a (F' p') :=
  Build_HJ a (F' p')
    (fun s s' => hj_rel H s (existT _ p' s'))
    (fun s s' => hj_to H s (existT _ p' s'))
    (fun s s' => hj_pull H s (existT _ p' s'))
    (fun s s' => hj_to_eq H s (existT _ p' s'))
    (fun s s' => hj_pull_eq H s (existT _ p' s'))
    (fun s s' => hj_pull_to H s (existT _ p' s'))
    (fun s s' => hj_to_pull H s (existT _ p' s'))
    (fun s s' => hj_irr H s (existT _ p' s')).

Section Level.
  Context (Univ : nat -> etm -> Type)
          (UnivEq : forall m u, Univ m u -> forall u', Univ m u' -> Prop)
          (UnivOK : nat -> Prop).
  Context (UnivEq_sym : forall m u x u' x', UnivEq m u x u' x' -> UnivEq m u' x' u x)
          (UnivEq_trans : forall m u x u' x' u'' x'',
              UnivEq m u x u' x' -> UnivEq m u' x' u'' x'' -> UnivEq m u x u'' x'').

  Local Notation stage_ := (stage Univ UnivEq UnivOK).
  Local Notation Ust_ := (Ust Univ UnivEq UnivOK).
  Local Notation U_ := (U Univ UnivEq UnivOK).

  Definition sgood alpha : StGood (stage_ alpha) := stage_good Univ UnivEq UnivOK alpha.
  Definition ssym alpha : forall s, EqSym (stage_ alpha) s :=
    fun s => proj1 (eqs_PER Univ UnivEq UnivOK UnivEq_sym UnivEq_trans alpha s).
  Definition strans alpha : forall s, EqTrans (stage_ alpha) s :=
    fun s => proj2 (eqs_PER Univ UnivEq UnivOK UnivEq_sym UnivEq_trans alpha s).

  Definition HJ_nextS beta beta' (g : HJ (stage_ beta) (stage_ beta'))
    : HJ (Ust_ beta) (Ust_ beta') :=
    HJ_next (stage_ beta) (stage_ beta') Univ UnivEq UnivOK g
      (sgood beta) (sgood beta') (ssym beta) (strans beta) (ssym beta') (strans beta').

  (* The hierarchy of isomorphism records, by an outer recursion on the
     first stage and an inner one on the second, so that a stage is peeled on
     both sides at once.  At a pair of successors the four blocks are: node
     against node (one level up, HJ_nextS), node against the stage below
     (the inner call, restricted), the stage below against a node (the outer
     call at a successor, restricted), and the two stages below (the outer
     call).  Every peeling is therefore a projection of hj at strictly
     smaller stages, on the nose. *)
  Fixpoint hj (alpha : Ord) : forall alpha', HJ (stage_ alpha) (stage_ alpha') :=
    match alpha as a return forall alpha', HJ (stage_ a) (stage_ alpha') with
    | ozero => fun alpha' => HJ_emptyL _
    | osucc beta =>
        fix inner (alpha' : Ord)
          : HJ (Stage_sum (Ust_ beta) (stage_ beta)) (stage_ alpha') :=
          match alpha' as a'
            return HJ (Stage_sum (Ust_ beta) (stage_ beta)) (stage_ a') with
          | ozero => HJ_emptyR _
          | osucc beta' =>
              HJ_sum_L (HJ_sum_R (HJ_nextS beta beta' (hj beta beta'))
                                 (HJ_restrL (inner beta')))
                       (HJ_sum_R (HJ_restrR (hj beta (osucc beta')))
                                 (hj beta beta'))
          | osup T' f' =>
              HJ_sup_R (fun p' =>
                HJ_sum_L (HJ_sum_R (HJ_nextS beta (f' p') (hj beta (f' p')))
                                   (HJ_restrL (inner (f' p'))))
                         (HJ_sum_R (HJ_restrR (HJ_supR p' (hj beta (osup T' f'))))
                                   (hj beta (f' p'))))
          end
    | osup T f =>
        fix inner (alpha' : Ord)
          : HJ (Stage_sup T (fun p => Stage_sum (Ust_ (f p)) (stage_ (f p))))
               (stage_ alpha') :=
          match alpha' as a'
            return HJ (Stage_sup T (fun p => Stage_sum (Ust_ (f p)) (stage_ (f p))))
                      (stage_ a') with
          | ozero => HJ_emptyR _
          | osucc beta' =>
              HJ_sup_L (fun p =>
                HJ_sum_L (HJ_sum_R (HJ_nextS (f p) beta' (hj (f p) beta'))
                                   (HJ_restrL (HJ_supL p (inner beta'))))
                         (HJ_sum_R (HJ_restrR (hj (f p) (osucc beta')))
                                   (hj (f p) beta')))
          | osup T' f' =>
              HJ_sup_L (fun p => HJ_sup_R (fun p' =>
                HJ_sum_L (HJ_sum_R (HJ_nextS (f p) (f' p') (hj (f p) (f' p')))
                                   (HJ_restrL (HJ_supL p (inner (f' p')))))
                         (HJ_sum_R (HJ_restrR (HJ_supR p' (hj (f p) (osup T' f'))))
                                   (hj (f p) (f' p')))))
          end
    end.

  Definition hjU (beta beta' : Ord) : HJ (Ust_ beta) (Ust_ beta') :=
    HJ_nextS beta beta' (hj beta beta').

  (* The working interface: isomorphism of two codes at arbitrary nodes of
     one level, the transport along it, and its laws. *)
  Definition ciso {beta beta'} (c : U_ beta) (c' : U_ beta') : Prop :=
    hj_rel (hjU beta beta') c c'.

  Definition cto {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u
    : (Ust_ beta).(StEl) c u -> (Ust_ beta').(StEl) c' u := hj_to (hjU beta beta') c c' P u.

  Definition cpull {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u
    : (Ust_ beta').(StEl) c' u -> (Ust_ beta).(StEl) c u := hj_pull (hjU beta beta') c c' P u.

  (* The bridge from the code-level transport down to the refinement-level one.
     hjU is HJ_nextS, whose transport at a CODE is toRefine outright, so this is
     one projection and one match -- no part of the Brouwer tree is touched.
     That is what makes the componentwise laws above usable at a concrete pair
     of families: without it the conversion checker is asked to unfold hj at a
     tree built from rk, which does not terminate in practice. *)
  Lemma cto_refine {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u x :
    proj1_sig (cto c c' P u x)
    = toRefine (stage_ beta) (stage_ beta') Univ UnivOK (hj beta beta')
        (projT2 c) (projT2 c') P u (proj1_sig x).
  Proof. reflexivity. Qed.

  Lemma cto_eq {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u x u' x' :
    (Ust_ beta).(StEq) c u x u' x' ->
    (Ust_ beta').(StEq) c' u (cto c c' P u x) u' (cto c c' P u' x').
  Proof. apply (hj_to_eq (hjU beta beta')). Qed.

  Lemma cpull_eq {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u y u' y' :
    (Ust_ beta').(StEq) c' u y u' y' ->
    (Ust_ beta).(StEq) c u (cpull c c' P u y) u' (cpull c c' P u' y').
  Proof. apply (hj_pull_eq (hjU beta beta')). Qed.

  Lemma cpull_to {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u y :
    (Ust_ beta').(StEq) c' u (cto c c' P u (cpull c c' P u y)) u y.
  Proof. apply (hj_pull_to (hjU beta beta')). Qed.

  Lemma cto_pull {beta beta'} (c : U_ beta) (c' : U_ beta') (P : ciso c c') u x :
    (Ust_ beta).(StEq) c u (cpull c c' P u (cto c c' P u x)) u x.
  Proof. apply (hj_to_pull (hjU beta beta')). Qed.

  (* Irrelevance of the isomorphism proof: this is what lets the
     fundamental lemma satisfy the naturality square of isoRefine, and what
     makes the transport at a reflexivity witness the identity. *)
  Lemma cto_irr {beta beta'} (c : U_ beta) (c' : U_ beta') (P P' : ciso c c') u x :
    (Ust_ beta').(StEq) c' u (cto c c' P u x) u (cto c c' P' u x).
  Proof. apply (hj_irr (hjU beta beta')). Qed.
End Level.
