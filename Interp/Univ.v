From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam.
From Stdlib Require Import Arith Lia.

(* "A type is a term of a universe", in this model.

   An element of the u_k-code's decoding is, by Codes/Levels.v's lU_spec, a
   coherent family of level-k codes -- that is, exactly the semantic value of
   a type at level k.  The identification is not definitional only because
   `lvl` selects the level with Nat.eq_dec, and `Nat.eq_dec k k` does not
   reduce for a variable k.  Destructing that one decision makes both sides
   reduce, so no transport along lU_spec is ever needed: the bridge below is
   built inside the branch, which is also what makes the round trip provable
   (an eq_rect along an opaque type equality would not compute).

   Only one round trip holds: elFam (famEl F) = F.  The other direction fails
   for the usual reason -- an element of the universe carries a proof that it
   is related to itself, and two proofs of a Prop are not equal without
   proof irrelevance.  This costs nothing, because functionality of the
   interpretation is up to isomorphism, never up to equality. *)

Definition uBridge (k : nat) (u : etm) :
  { f : kUFam k u -> kElAt (univFam k) u &
    { g : kElAt (univFam k) u -> kUFam k u | forall F, g (f F) = F } }.
Proof.
  unfold kElAt, kUst, kAt, univFam, uf_at, uf_c, Ust, Stage_next, kU, kUEq; cbn.
  unfold sU, sUEq; destruct (Nat.eq_dec k k) as [E | NE]; [| exfalso; exact (NE eq_refl)].
  refine (existT _
    (fun F => exist _ F (conj (uf_ty F) (fun v h pf v' h' pf' => uf_coh F v h pf v' h' pf')))
    (exist _ (fun x => proj1_sig x) _)).
  intros F; reflexivity.
Defined.

(* The semantic value of a type, read as an element of the universe. *)
Definition famEl {k u} (F : kUFam k u) : kElAt (univFam k) u := projT1 (uBridge k u) F.

(* And back. *)
Definition elFam {k u} (x : kElAt (univFam k) u) : kUFam k u :=
  proj1_sig (projT2 (uBridge k u)) x.

Lemma elFam_famEl {k u} (F : kUFam k u) : elFam (famEl F) = F.
Proof. exact (proj2_sig (projT2 (uBridge k u)) F). Qed.

(* The equality on the universe, in both directions.  It is the layer-1
   equality of the realisers together with the isomorphism of every pair of
   instances of the two families -- which is LUnivEq, spelled out. *)
Lemma uEq_of {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  eqty k u u' ->
  (forall v h pf v' h' pf', iso (uf_c F v h pf) (uf_c F' v' h' pf')) ->
  kEqAt (univFam k) u (famEl F) u' (famEl F').
Proof.
  unfold kEqAt, kUst, kAt, univFam, uf_at, uf_c, Ust, Stage_next, kUEq, famEl, uBridge; cbn.
  unfold sU, sUEq; destruct (Nat.eq_dec k k) as [E | NE]; [| exfalso; exact (NE eq_refl)].
  intros H1 H2; exact (conj H1 H2).
Qed.

Lemma uEq_ty {k u u'} (x : kElAt (univFam k) u) (x' : kElAt (univFam k) u') :
  kEqAt (univFam k) u x u' x' -> eqty k u u'.
Proof.
  unfold kEqAt, kUst, kAt, univFam, uf_at, uf_c, Ust, Stage_next, kUEq in *; cbn in *.
  revert x x'; unfold sU, sUEq;
    destruct (Nat.eq_dec k k) as [E | NE]; [| exfalso; exact (NE eq_refl)].
  intros x x' H; exact (proj1 H).
Qed.

Lemma uEq_iso {k u u'} (x : kElAt (univFam k) u) (x' : kElAt (univFam k) u') :
  kEqAt (univFam k) u x u' x' ->
  forall v h pf v' h' pf', iso (uf_c (elFam x) v h pf) (uf_c (elFam x') v' h' pf').
Proof.
  unfold kEqAt, kUst, kAt, univFam, uf_at, uf_c, Ust, Stage_next, kUEq, elFam, uBridge in *;
    cbn in *.
  revert x x'; unfold sU, sUEq;
    destruct (Nat.eq_dec k k) as [E | NE]; [| exfalso; exact (NE eq_refl)].
  intros x x' H; exact (proj2 H).
Qed.
