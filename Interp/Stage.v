From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes.
From Stdlib Require Import Arith Lia.

(* The stage bookkeeping.  A code for T lives at the node rk T h; its
   components sit at the nodes rk (pred p) for the component witnesses p of
   T, and placing one of those into Sub (rk T h) is a pair of constructor
   injections.  Everything below is proved by `reflexivity`: the placement
   changes neither the decoding, nor the equality, nor the shadow, nor the
   well-formedness.  That is what makes the blueprint's Lemma 8.2
   (cumulativity) unnecessary here.

   The accessibility proof has to be destructed first -- rk T h only unfolds
   to a sup once h is an Acc_intro -- which is why this section takes the
   Acc_intro's field rather than the proof.

   Against v1: `place_iso` and `place_idp` are replaced by `place_ceq` and
   `place_wf`, and the equality lemma is now HETEROGENEOUS -- two components
   placed at two different witnesses are compared by the equality of the codes
   themselves, at their own nodes.  v1 could only compare elements of one
   placed component and needed `iso` for the rest. *)

Section Stage.
  Context (k : nat) (T : etm) (fT : forall y, prec y T -> Acc prec y).

  Definition hT : Acc prec T := Acc_intro T fT.
  Definition accAt (p : Pred T) : Acc prec (pred p) := fT (pred p) (ex_intro _ p eq_refl).
  Definition nodeAt (p : Pred T) : Ord := rk (pred p) (accAt p).

  (* A component is placed as a CODE, not as a refinement: the families of
     Codes/Levels.v hand out codes, and `existT (projT1 c) (projT2 c)` is not
     convertible to `c`.  The shadow of the placed component is its own, NOT
     `pred p`: the codomain of a Pi-code is interpreted at the beta-reduct of
     B0 . u, and Refine only asks for the two to be layer-1 equal. *)
  Definition place (p : Pred T) (c : Code k (nodeAt p)) : kSub k (rk T hT) :=
    existT _ p (inr (inl c)).

  Lemma place_sh p c : kSh (place p c) = projT1 c.
  Proof. reflexivity. Qed.

  Lemma place_El p c u : kElS (place p c) u = kElC c u.
  Proof. reflexivity. Qed.

  Lemma place_cel p c u x p' c' u' x' :
    kcEl (place p c) u x (place p' c') u' x' = kcel c u x c' u' x'.
  Proof. reflexivity. Qed.

  Lemma place_ceq p c p' c' : kcU (place p c) (place p' c') = kceq c c'.
  Proof. reflexivity. Qed.

  Lemma place_wf p c : kwfS (place p c) = kwfc c.
  Proof. reflexivity. Qed.
End Stage.

(* Soundness of realisers at a level: the goodness of a realiser of a placed
   component is the premise that p_cod asks for. *)
Definition kgood (k : nat) (alpha : Ord) (s : kSub k alpha) u (x : kElS s u)
  : Good (kSh s) u :=
  sub_good (kU k) (kUEq k) (kOK k) (lsound (lvl k)) alpha s u x.

(* and the layer-1 relation of two related realisers, from Codes/Sound.v's
   pair induction *)
Definition krel (k : nat) (alpha : Ord) (s : kSub k alpha) u x (s' : kSub k alpha) u' x'
  (H : kcEl s u x s' u' x') : Rel (kSh s) u u' :=
  sub_rel (kU k) (kUEq k) (kOK k) (lsound (lvl k)) alpha alpha s u x s' u' x' H.

(* ------------------------------------------------------------------ *)
(* Where the components of a binder code live.                         *)
(* ------------------------------------------------------------------ *)

Section PiPlace.
  Context (k : nat) (T A0 B0 : etm) (fT : forall y, prec y T -> Acc prec y)
          (e : eval T (epi A0 B0)).

  Definition pdom : Pred T := p_dom A0 B0 e.
  Definition pcod (u : etm) (g : Good A0 u) : Pred T := p_cod A0 B0 u e g.

  Definition domNode : Ord := nodeAt T fT pdom.
  Definition codNode (u : etm) (g : Good A0 u) : Ord := nodeAt T fT (pcod u g).

  Lemma domNode_eq : domNode = rk A0 (fT A0 (ex_intro _ pdom eq_refl)).
  Proof. reflexivity. Qed.

  Lemma codNode_eq u g :
    codNode u g = rk (eapp B0 u) (fT (eapp B0 u) (ex_intro _ (pcod u g) eq_refl)).
  Proof. reflexivity. Qed.

  Definition placeDom (c : Code k domNode) : kSub k (rk T (hT T fT)) :=
    place k T fT pdom c.
  Definition placeCod u g (c : Code k (codNode u g)) : kSub k (rk T (hT T fT)) :=
    place k T fT (pcod u g) c.

  Lemma placeDom_sh c : kSh (placeDom c) = projT1 c.
  Proof. reflexivity. Qed.
  Lemma placeCod_sh u g c : kSh (placeCod u g c) = projT1 c.
  Proof. reflexivity. Qed.

  (* The goodness of an argument's realiser, which is exactly the premise the
     component witness p_cod requires.  The shadow of the domain code need
     only be layer-1 equal to A0. *)
  Definition argGood (c : Code k domNode) (eA : tyeq (projT1 c) A0)
    u (x : kElS (placeDom c) u) : Good A0 u :=
    Good_tyeq (projT1 c) A0 u eA (kgood k _ (placeDom c) u x).
End PiPlace.

Section SigPlace.
  Context (k : nat) (T A0 B0 : etm) (fT : forall y, prec y T -> Acc prec y)
          (e : eval T (esig A0 B0)).

  Definition sdom : Pred T := p_sdom A0 B0 e.
  Definition scod (u : etm) (g : Good A0 u) : Pred T := p_scod A0 B0 u e g.

  Definition sdomNode : Ord := nodeAt T fT sdom.
  Definition scodNode (u : etm) (g : Good A0 u) : Ord := nodeAt T fT (scod u g).

  Definition placeSDom (c : Code k sdomNode) : kSub k (rk T (hT T fT)) :=
    place k T fT sdom c.
  Definition placeSCod u g (c : Code k (scodNode u g)) : kSub k (rk T (hT T fT)) :=
    place k T fT (scod u g) c.

  Lemma placeSDom_sh c : kSh (placeSDom c) = projT1 c.
  Proof. reflexivity. Qed.
  Lemma placeSCod_sh u g c : kSh (placeSCod u g c) = projT1 c.
  Proof. reflexivity. Qed.

  Definition sargGood (c : Code k sdomNode) (eA : tyeq (projT1 c) A0)
    u (x : kElS (placeSDom c) u) : Good A0 u :=
    Good_tyeq (projT1 c) A0 u eA (kgood k _ (placeSDom c) u x).
End SigPlace.

(* W: the same two component witnesses, at the `ew` head.  New in v2. *)
Section WPlace.
  Context (k : nat) (T A0 B0 : etm) (fT : forall y, prec y T -> Acc prec y)
          (e : eval T (ew A0 B0)).

  Definition wdom : Pred T := p_wdom A0 B0 e.
  Definition wcod (u : etm) (g : Good A0 u) : Pred T := p_wcod A0 B0 u e g.

  Definition wdomNode : Ord := nodeAt T fT wdom.
  Definition wcodNode (u : etm) (g : Good A0 u) : Ord := nodeAt T fT (wcod u g).

  Definition placeWDom (c : Code k wdomNode) : kSub k (rk T (hT T fT)) :=
    place k T fT wdom c.
  Definition placeWCod u g (c : Code k (wcodNode u g)) : kSub k (rk T (hT T fT)) :=
    place k T fT (wcod u g) c.

  Lemma placeWDom_sh c : kSh (placeWDom c) = projT1 c.
  Proof. reflexivity. Qed.
  Lemma placeWCod_sh u g c : kSh (placeWCod u g c) = projT1 c.
  Proof. reflexivity. Qed.

  Definition wargGood (c : Code k wdomNode) (eA : tyeq (projT1 c) A0)
    u (x : kElS (placeWDom c) u) : Good A0 u :=
    Good_tyeq (projT1 c) A0 u eA (kgood k _ (placeWDom c) u x).
End WPlace.

(* The same across two NODES, which is what relating the branch indices of two
   different readings of one W type needs: `sub_rel` is heterogeneous in the
   ordinal already, and `krel` only instantiated it diagonally. *)
Definition krelX {k alpha alpha'} (s : kSub k alpha) u x (s' : kSub k alpha') u' x'
  (H : kcEl s u x s' u' x') : Rel (kSh s) u u' :=
  sub_rel (kU k) (kUEq k) (kOK k) (lsound (lvl k)) alpha alpha' s u x s' u' x' H.
