From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Univ
  Interp.Env.
From Stdlib Require Import Arith Lia.

(* Introducing and eliminating the semantic elements of the families with no
   components.  Each of these is a definitional unfolding of Codes/Def.v's El
   and eqEl at the corresponding clause: the goodness conjunct is supplied by
   the caller (it is the layer-1 fundamental lemma), and the self-relatedness
   that Stage_next bundles into the decoding is discharged on the spot.

   The pattern to notice: at Prf the equality does not mention the element at
   all, so any two elements of a Prf-family at the same realiser are related.
   That is proof irrelevance, and it is why the clauses of the interpretation
   at proof terms need no condition on the value. *)

(* ------------------------------------------------------------------ *)
(* Lemma 8.7 in the form the interpretation uses: the decoding of a    *)
(* family is closed under reduction and expansion of the realiser, and *)
(* the two realisers are related.                                      *)
(* ------------------------------------------------------------------ *)

Definition kexp (k : nat) (beta : Ord) : SExp (kUst k beta) :=
  sexpU (kU k) (kUEq k) (kOK k) (lexp (lvl k)) (ksym k) (ktrans k) beta.

Definition famRed {k u} (F : kUFam k u) w w1 (H : reds w w1) (x : kElAt F w)
  : kElAt F w1 := se_red (kexp k _) (kAt F) w w1 H x.

Definition famExp {k u} (F : kUFam k u) w w1 (H : reds w w1) (y : kElAt F w1)
  : kElAt F w := se_exp (kexp k _) (kAt F) w w1 H y.

Lemma famRed_rel {k u} (F : kUFam k u) w w1 (H : reds w w1) x :
  kEqAt F w x w1 (famRed F w w1 H x).
Proof. exact (se_red_rel (kexp k _) (kAt F) w w1 H x). Qed.

Lemma famExp_rel {k u} (F : kUFam k u) w w1 (H : reds w w1) y :
  kEqAt F w (famExp F w w1 H y) w1 y.
Proof. exact (se_exp_rel (kexp k _) (kAt F) w w1 H y). Qed.

(* ------------------------------------------------------------------ *)
(* Relatedness inside one family is heterogeneous relatedness with     *)
(* itself: the canonical self-transport is the identity.               *)
(* ------------------------------------------------------------------ *)

Lemma kRel_same {k u} (F : kUFam k u) w x w' x' :
  kEqAt F w x w' x' <-> kRel F F w x w' x'.
Proof.
  split.
  - intros H; exists (iso_self F); eapply kEqC_trans;
      [apply (uf_idp F u (kAcc F) (evalAg_refl u) (iso_self F) w x) | exact H].
  - intros H; pose proof (kRel_at F F (iso_self F) w x w' x' H) as H1.
    eapply kEqC_trans; [| exact H1].
    apply kEqC_sym, (uf_idp F u (kAcc F) (evalAg_refl u) (iso_self F) w x).
Qed.

(* ------------------------------------------------------------------ *)
(* N.                                                                  *)
(* ------------------------------------------------------------------ *)

Definition natElem {k} (u : etm) (j : nat) (e : NatAt j u) (g : Good enat u)
  : kElAt (natFam k) u := exist _ (existT _ j e, g) (conj eq_refl g).

Definition natIdx {k u} (x : kElAt (natFam k) u) : nat :=
  projT1 (Datatypes.fst (proj1_sig x)).

Definition natSpec {k u} (x : kElAt (natFam k) u) : NatAt (natIdx x) u :=
  projT2 (Datatypes.fst (proj1_sig x)).

Definition natGood {k u} (x : kElAt (natFam k) u) : Good enat u :=
  Datatypes.snd (proj1_sig x).

Lemma natEq_iff {k u u'} (x : kElAt (natFam k) u) (x' : kElAt (natFam k) u') :
  kEqAt (natFam k) u x u' x' <-> (natIdx x = natIdx x' /\ Rel enat u u').
Proof. split; intros H; exact H. Qed.

(* Any two elements at the same realiser agree: the index is determined by
   the realiser (NatAt_fun) and the goodness is irrelevant to the equality. *)
Lemma natEq_self {k u} (x x' : kElAt (natFam k) u) : kEqAt (natFam k) u x u x'.
Proof.
  apply natEq_iff; split;
    [exact (NatAt_fun _ _ u (natSpec x) (natSpec x')) | exact (natGood x)].
Qed.

(* ------------------------------------------------------------------ *)
(* Prop.                                                              *)
(* ------------------------------------------------------------------ *)

Definition propElem {k} (u : etm) (P : Prop) (g : Good eprop u)
  : kElAt (propFam k) u := exist _ (P, g) (conj (iff_refl P) g).

Definition propVal {k u} (x : kElAt (propFam k) u) : Prop :=
  Datatypes.fst (proj1_sig x).

Definition propGood {k u} (x : kElAt (propFam k) u) : Good eprop u :=
  Datatypes.snd (proj1_sig x).

Lemma propEq_iff {k u u'} (x : kElAt (propFam k) u) (x' : kElAt (propFam k) u') :
  kEqAt (propFam k) u x u' x' <-> ((propVal x <-> propVal x') /\ Rel eprop u u').
Proof. split; intros H; exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Prf: proof irrelevance.                                            *)
(* ------------------------------------------------------------------ *)

Definition prfElem {k p Hp H} (u : etm) (h : H) (g : Good (eprf p) u)
  : kElAt (prfFam k p Hp H) u := exist _ (h, g) g.

Definition prfVal {k p Hp H u} (x : kElAt (prfFam k p Hp H) u) : H :=
  Datatypes.fst (proj1_sig x).

Definition prfGood {k p Hp H u} (x : kElAt (prfFam k p Hp H) u) : Good (eprf p) u :=
  Datatypes.snd (proj1_sig x).

(* The equality at Prf does not look at the elements. *)
Lemma prfEq_iff {k p Hp H u u'} (x : kElAt (prfFam k p Hp H) u)
  (x' : kElAt (prfFam k p Hp H) u') :
  kEqAt (prfFam k p Hp H) u x u' x' <-> Rel (eprf p) u u'.
Proof. split; intros Hh; exact Hh. Qed.

Lemma prfEq_of {k p Hp H u u'} (x : kElAt (prfFam k p Hp H) u)
  (x' : kElAt (prfFam k p Hp H) u') :
  Rel (eprf p) u u' -> kEqAt (prfFam k p Hp H) u x u' x'.
Proof. apply prfEq_iff. Qed.

(* The layer-1 goodness of a realiser that carries a numeral, and the
   successor on semantic naturals. *)
Definition natGoodOf {j u} (e : NatAt j u) : Good enat u :=
  Rel_nat_intro enat u u gt_nat ev_nat (NatAt_NatPer j u u e e).

Definition natE {k u} (j : nat) (e : NatAt j u) : kElAt (natFam k) u :=
  natElem u j e (natGoodOf e).

Definition natSucc {k u} (x : kElAt (natFam k) u) : kElAt (natFam k) (esucc u) :=
  natE (S (natIdx x)) (NatAt_succ _ _ (natSpec x)).

Lemma natIdx_natE {k u} (j : nat) (e : NatAt j u) : natIdx (@natE k u j e) = j.
Proof. reflexivity. Qed.

(* Two semantic naturals are related as soon as their indices agree and their
   realisers are layer-1 related. *)
Lemma natE_eq {k u u'} (j : nat) (e : NatAt j u) (e' : NatAt j u') :
  kEqAt (natFam k) u (natE j e) u' (natE j e').
Proof.
  apply natEq_iff; split;
    [reflexivity | apply Rel_nat_intro; [apply gt_nat | apply ev_nat |]].
  exact (NatAt_NatPer j u u' e e').
Qed.

(* ------------------------------------------------------------------ *)
(* Moving a value to an isomorphic family and expanding its realiser:  *)
(* every computation rule of the interpretation is one of these.       *)
(* ------------------------------------------------------------------ *)

Definition moveTo {k u u'} (F : kUFam k u) (F' : kUFam k u') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) w0 (Hr : reds w0 w) : kElAt F' w0 :=
  famExp F' w0 w Hr (ctoK (kAt F) (kAt F') P w x).

Lemma moveTo_rel {k u u'} (F : kUFam k u) (F' : kUFam k u') (P : iso (kAt F) (kAt F'))
  w (x : kElAt F w) w0 (Hr : reds w0 w) :
  kRel F F' w x w0 (moveTo F F' P w x w0 Hr).
Proof.
  eapply hetC_eq_r; [apply hetC_to | apply kEqC_sym, famExp_rel].
Qed.
