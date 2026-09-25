From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes.

(* The stage bookkeeping.  A code for T lives at the node rk T h; its
   components sit at the nodes rk (pred p) for the component witnesses p of
   T, and placing one of those into Sub (rk T h) is a pair of constructor
   injections.  Everything below is proved by `reflexivity`: the placement
   changes neither the decoding, nor the equality, nor the shadow, nor the
   isomorphism relation, nor the identity property.  That is what makes the
   blueprint's Lemma 8.2 (cumulativity) unnecessary here.

   The accessibility proof has to be destructed first -- rk T h only unfolds
   to a sup once h is an Acc_intro -- which is why this section takes the
   Acc_intro's field rather than the proof. *)

Section Stage.
  Context (k : nat) (T : etm) (fT : forall y, prec y T -> Acc prec y).

  Definition hT : Acc prec T := Acc_intro T fT.
  Definition accAt (p : Pred T) : Acc prec (pred p) := fT (pred p) (ex_intro _ p eq_refl).
  Definition nodeAt (p : Pred T) : Ord := rk (pred p) (accAt p).

  (* The shadow of a placed component is its own, NOT `pred p`: the codomain
     of a Pi-code is interpreted at the beta-reduct of B0 . u, and Refine only
     asks for the two to be layer-1 equal. *)
  (* A component is placed as a CODE, not as a refinement: the families of
     Codes/Levels.v hand out codes, and `existT (projT1 c) (projT2 c)` is not
     convertible to `c`.  The shadow of the placed component is its own, NOT
     `pred p`: the codomain of a Pi-code is interpreted at the beta-reduct of
     B0 . u, and Refine only asks for the two to be layer-1 equal. *)
  Definition place (p : Pred T) (c : Code k (nodeAt p)) : kSub k (rk T hT) :=
    existT _ p (inr (inl c)).

  Lemma place_sh p c : kSh (place p c) = projT1 c.
  Proof. reflexivity. Qed.

  Lemma place_El p c u : kElS (place p c) u = (kUst k (nodeAt p)).(StEl) c u.
  Proof. reflexivity. Qed.

  Lemma place_Eq p c u x u' x' :
    kEqS (place p c) u x u' x' = (kUst k (nodeAt p)).(StEq) c u x u' x'.
  Proof. reflexivity. Qed.

  (* The isomorphism relation at two placed components is the isomorphism of
     the codes themselves, at their own nodes. *)
  Lemma place_iso p c p' c' : kirel (place p c) (place p' c') = iso c c'.
  Proof. reflexivity. Qed.

  (* And likewise the identity property. *)
  Lemma place_idp p c : kidps k (rk T hT) (place p c) = LIdP c.
  Proof. reflexivity. Qed.
End Stage.

(* Soundness of realisers at a level, and the goodness of a realiser of a
   placed component -- the premise that p_cod asks for. *)
Definition kgood (k : nat) (alpha : Ord) (s : kSub k alpha) u (x : kElS s u) : Good (kSh s) u :=
  sub_good (kU k) (kUEq k) (kOK k) (lsound (lvl k)) alpha s u x.

Definition krel (k : nat) (alpha : Ord) (s : kSub k alpha) u x u' x'
  (H : kEqS s u x u' x') : Rel (kSh s) u u' :=
  sub_rel (kU k) (kUEq k) (kOK k) (lsound (lvl k)) alpha s u x u' x' H.

Section PiPlace.
  Context (k : nat) (T A0 B0 : etm) (fT : forall y, prec y T -> Acc prec y)
          (e : eval T (epi A0 B0)).

  Definition pdom : Pred T := p_dom A0 B0 e.
  Definition pcod (u : etm) (g : Good A0 u) : Pred T := p_cod A0 B0 u e g.

  (* The two nodes the components of a Pi-code live at. *)
  Definition domNode : Ord := nodeAt T fT pdom.
  Definition codNode (u : etm) (g : Good A0 u) : Ord := nodeAt T fT (pcod u g).

  Lemma domNode_eq : domNode = rk A0 (fT A0 (ex_intro _ pdom eq_refl)).
  Proof. reflexivity. Qed.

  Lemma codNode_eq u g : codNode u g = rk (eapp B0 u) (fT (eapp B0 u) (ex_intro _ (pcod u g) eq_refl)).
  Proof. reflexivity. Qed.

  Definition placeDom (c : Code k domNode) : kSub k (rk T (hT T fT)) :=
    place k T fT pdom c.

  Definition placeCod u g (c : Code k (codNode u g)) : kSub k (rk T (hT T fT)) :=
    place k T fT (pcod u g) c.

  Lemma placeDom_sh c : kSh (placeDom c) = projT1 c.
  Proof. reflexivity. Qed.

  Lemma placeCod_sh u g c : kSh (placeCod u g c) = projT1 c.
  Proof. reflexivity. Qed.

  (* The goodness of an argument's realiser, which is exactly the premise
     that the component witness p_cod requires -- blueprint fix (ii).  The
     shadow of the domain code need only be layer-1 equal to A0. *)
  Definition argGood (c : Code k domNode) (eA : tyeq (projT1 c) A0)
    u (x : kElS (placeDom c) u) : Good A0 u :=
    Good_tyeq (projT1 c) A0 u eA (kgood k _ (placeDom c) u x).
End PiPlace.

(* The same for Sigma: the same two component witnesses, at the esig head. *)
Section SigPlace.
  Context (k : nat) (T A0 B0 : etm) (fT : forall y, prec y T -> Acc prec y)
          (e : eval T (esig A0 B0)).

  Definition sdom : Pred T := p_sdom A0 B0 e.
  Definition scod (u : etm) (g : Good A0 u) : Pred T := p_scod A0 B0 u e g.

  (* The two nodes the components of a Sigma-code live at. *)
  Definition sdomNode : Ord := nodeAt T fT sdom.
  Definition scodNode (u : etm) (g : Good A0 u) : Ord := nodeAt T fT (scod u g).

  Lemma sdomNode_eq : sdomNode = rk A0 (fT A0 (ex_intro _ sdom eq_refl)).
  Proof. reflexivity. Qed.

  Lemma scodNode_eq u g : scodNode u g = rk (eapp B0 u) (fT (eapp B0 u) (ex_intro _ (scod u g) eq_refl)).
  Proof. reflexivity. Qed.

  Definition placeSDom (c : Code k sdomNode) : kSub k (rk T (hT T fT)) :=
    place k T fT sdom c.

  Definition placeSCod u g (c : Code k (scodNode u g)) : kSub k (rk T (hT T fT)) :=
    place k T fT (scod u g) c.

  Lemma placeSDom_sh c : kSh (placeSDom c) = projT1 c.
  Proof. reflexivity. Qed.

  Lemma placeSCod_sh u g c : kSh (placeSCod u g c) = projT1 c.
  Proof. reflexivity. Qed.

  (* The goodness of an argument's realiser, which is exactly the premise
     that the component witness p_scod requires -- blueprint fix (ii).  The
     shadow of the domain code need only be layer-1 equal to A0. *)
  Definition sargGood (c : Code k sdomNode) (eA : tyeq (projT1 c) A0)
    u (x : kElS (placeSDom c) u) : Good A0 u :=
    Good_tyeq (projT1 c) A0 u eA (kgood k _ (placeSDom c) u x).
End SigPlace.

