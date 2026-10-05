From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* "A type is a term of a universe", in this model.

   An element of the u_k-code's decoding is a coherent family of level-k codes
   -- exactly the semantic value of a type at level k -- and in v2 the
   identification is a CONSTRUCTOR: the level step of Codes/Levels.v is a sum
   that carries the level (dis)equality, so the family at the level the
   universe was added at is `inl (F, eq_refl)`.  v1 had to destruct
   `Nat.eq_dec k k` in every one of these lemmas, because its level step
   decided the level inside the TYPE and `Nat.eq_dec k k` does not reduce for
   a variable k.

   One round trip holds on the nose, `elFam (famEl F) = F`; the other holds up
   to the equality only, since an element carries a proof of `k = k` and two
   proofs of a Prop are not equal without proof irrelevance.  That costs
   nothing: functionality is up to the equality, never up to identity. *)

(* The semantic value of a type, read as an element of the universe. *)
Definition famEl {k u} (F : kUFam k u) : kElAt (univFam k) u := inl (F, eq_refl).

(* And back: the other summand is refuted by its own disequality. *)
Definition elFam {k u} (x : kElAt (univFam k) u) : kUFam k u.
Proof.
  cbn in x; destruct x as [[F e] | [y ne]]; [exact F | exfalso; exact (ne eq_refl)].
Defined.

Lemma elFam_famEl {k u} (F : kUFam k u) : elFam (famEl F) = F.
Proof. reflexivity. Qed.

(* The equality on the universe, in both directions: it is the layer-1
   equality of the realisers together with the equality of every pair of
   instances of the two families -- which is LUnivEq, spelled out. *)
Lemma uEq_of {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  eqty k u u' ->
  (forall v h pf v' h' pf', kceq (uf_c F v h pf) (uf_c F' v' h' pf')) ->
  kEqAt (univFam k) u (famEl F) (univFam k) u' (famEl F').
Proof.
  intros H1 H2; split; [exact (conj H1 H2) |].
  exact (tyeq_univ (euniv k) k (eval_whnf _ (whnf_univ k))).
Qed.

Lemma uEq_ty {k u u'} (x : kElAt (univFam k) u) (x' : kElAt (univFam k) u') :
  kEqAt (univFam k) u x (univFam k) u' x' -> eqty k u u'.
Proof.
  revert x x'; cbn; intros [[F e] | [y ne]] [[F' e'] | [y' ne']];
    try (intros H; exfalso; exact (match proj1 H with end));
    try (exfalso; exact (ne eq_refl)); try (exfalso; exact (ne' eq_refl)).
  intros H; exact (proj1 (proj1 H)).
Qed.

Lemma uEq_ceq {k u u'} (x : kElAt (univFam k) u) (x' : kElAt (univFam k) u') :
  kEqAt (univFam k) u x (univFam k) u' x' ->
  forall v h pf v' h' pf',
    kceq (uf_c (elFam x) v h pf) (uf_c (elFam x') v' h' pf').
Proof.
  revert x x'; cbn; intros [[F e] | [y ne]] [[F' e'] | [y' ne']];
    try (intros H; exfalso; exact (match proj1 H with end));
    try (exfalso; exact (ne eq_refl)); try (exfalso; exact (ne' eq_refl)).
  intros H; exact (proj2 (proj1 H)).
Qed.

(* and the canonical instances, which is the form the interpretation uses *)
Lemma uEq_at {k u u'} (x : kElAt (univFam k) u) (x' : kElAt (univFam k) u') :
  kEqAt (univFam k) u x (univFam k) u' x' -> kceq (kAt (elFam x)) (kAt (elFam x')).
Proof.
  intros H; apply (famCeq_of (elFam x) (elFam x') u (kAcc (elFam x)) (evalAg_refl u)
                     u' (kAcc (elFam x')) (evalAg_refl u')).
  apply uEq_ceq; exact H.
Qed.

Lemma uEq_famEl {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> kEqAt (univFam k) u (famEl F) (univFam k) u' (famEl F').
Proof.
  intros H; apply uEq_of; [exact (ceq_eqty F F' H) | apply famCeq_all; exact H].
Qed.
