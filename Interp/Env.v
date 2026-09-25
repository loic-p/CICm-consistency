From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Univ.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* 1.  The transport algebra at one level.                            *)
(*                                                                    *)
(* Codes/Iso.v and Codes/IsoPER.v with the five universe parameters   *)
(* fixed to the level-k ones, so that nothing downstream mentions      *)
(* them again.                                                        *)
(* ------------------------------------------------------------------ *)

Definition kElC {k beta} (c : Code k beta) (w : etm) : Type := (kUst k beta).(StEl) c w.
Definition kEqC {k beta} (c : Code k beta) w (x : kElC c w) w' (x' : kElC c w') : Prop :=
  (kUst k beta).(StEq) c w x w' x'.

Lemma kEqC_sym {k beta} (c : Code k beta) w x w' x' : kEqC c w x w' x' -> kEqC c w' x' w x.
Proof. apply (eqU_sym (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) beta c). Qed.

Lemma kEqC_trans {k beta} (c : Code k beta) w x w' x' w'' x'' :
  kEqC c w x w' x' -> kEqC c w' x' w'' x'' -> kEqC c w x w'' x''.
Proof. apply (eqU_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) beta c). Qed.

(* Every element of a decoding is self-related: the goodness is bundled into
   the decoding by Codes/Def.v's Stage_next. *)
Lemma kEqC_self {k beta} (c : Code k beta) w (x : kElC c w) : kEqC c w x w x.
Proof. exact (proj2_sig x). Qed.

Definition ctoK {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w
  (x : kElC c w) : kElC c' w :=
  cto (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) c c' P w x.

Definition cpullK {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w
  (y : kElC c' w) : kElC c w :=
  cpull (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k) c c' P w y.

Lemma iso_sym {k b b'} (c : Code k b) (c' : Code k b') : iso c c' -> iso c' c.
Proof. apply (ciso_sym (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma iso_trans {k b1 b2 b3} (c1 : Code k b1) (c2 : Code k b2) (c3 : Code k b3) :
  iso c1 c2 -> iso c2 c3 -> iso c1 c3.
Proof. apply (ciso_trans (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma ctoK_eq {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w x w' x' :
  kEqC c w x w' x' -> kEqC c' w (ctoK c c' P w x) w' (ctoK c c' P w' x').
Proof. apply (cto_eq (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma ctoK_irr {k b b'} (c : Code k b) (c' : Code k b') (P P' : iso c c') w x :
  kEqC c' w (ctoK c c' P w x) w (ctoK c c' P' w x).
Proof. apply (cto_irr (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma cpullK_to {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w y :
  kEqC c' w (ctoK c c' P w (cpullK c c' P w y)) w y.
Proof. apply (cpull_to (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma ctoK_pull {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w x :
  kEqC c w (cpullK c c' P w (ctoK c c' P w x)) w x.
Proof. apply (cto_pull (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma cpullK_eq {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w y w' y' :
  kEqC c' w y w' y' -> kEqC c w (cpullK c c' P w y) w' (cpullK c c' P w' y').
Proof. apply (cpull_eq (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma ctoK_sym {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') (Q : iso c' c) w y :
  kEqC c w (ctoK c' c Q w y) w (cpullK c c' P w y).
Proof. apply (cto_sym (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma ctoK_fun {k b1 b2 b3} (c1 : Code k b1) (c2 : Code k b2) (c3 : Code k b3)
  (P : iso c1 c2) (Q : iso c2 c3) (R : iso c1 c3) w x :
  kEqC c3 w (ctoK c1 c3 R w x) w (ctoK c2 c3 Q w (ctoK c1 c2 P w x)).
Proof. apply (cto_fun (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

(* ------------------------------------------------------------------ *)
(* 2.  Heterogeneous relatedness: elements of two isomorphic families *)
(* that transport onto each other.  By ctoK_irr the isomorphism proof *)
(* does not matter, so it is existentially quantified -- this is the   *)
(* relation the paper writes (u, x) ~ (u', x').                        *)
(* ------------------------------------------------------------------ *)

(* At the level of codes first: this is the algebra the interpretation
   reasons with, and it never needs a transport to be unfolded.  Everything
   in sight is a canonical transport between isomorphic codes, so composing
   and cancelling them is ctoK_fun and ctoK_irr, once. *)
Definition hetC {k b b'} (c : Code k b) (c' : Code k b')
  w (x : kElC c w) w' (x' : kElC c' w') : Prop :=
  exists P : iso c c', kEqC c' w (ctoK c c' P w x) w' x'.

Lemma hetC_at {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w x w' x' :
  hetC c c' w x w' x' -> kEqC c' w (ctoK c c' P w x) w' x'.
Proof. intros [Q H]; eapply kEqC_trans; [apply ctoK_irr | exact H]. Qed.

(* Transporting is the identity of this relation. *)
Lemma hetC_to {k b b'} (c : Code k b) (c' : Code k b') (P : iso c c') w x :
  hetC c c' w x w (ctoK c c' P w x).
Proof. exists P; apply kEqC_self. Qed.

Lemma hetC_eq_l {k b b'} (c : Code k b) (c' : Code k b') w x w1 x1 w' x' :
  kEqC c w x w1 x1 -> hetC c c' w1 x1 w' x' -> hetC c c' w x w' x'.
Proof.
  intros E [P H]; exists P; eapply kEqC_trans; [apply (ctoK_eq c c' P _ _ _ _ E) | exact H].
Qed.

Lemma hetC_eq_r {k b b'} (c : Code k b) (c' : Code k b') w x w1 x1 w' x' :
  hetC c c' w x w1 x1 -> kEqC c' w1 x1 w' x' -> hetC c c' w x w' x'.
Proof. intros [P H] E; exists P; eapply kEqC_trans; [exact H | exact E]. Qed.

Lemma hetC_sym {k b b'} (c : Code k b) (c' : Code k b') w x w' x' :
  hetC c c' w x w' x' -> hetC c' c w' x' w x.
Proof.
  intros [P HP]; exists (iso_sym _ _ P).
  eapply kEqC_trans; [apply (ctoK_sym c c' P) |].
  eapply kEqC_trans; [| apply (ctoK_pull c c' P)].
  apply kEqC_sym, cpullK_eq, HP.
Qed.

Lemma hetC_trans {k b1 b2 b3} (c1 : Code k b1) (c2 : Code k b2) (c3 : Code k b3)
  w1 x1 w2 x2 w3 x3 :
  hetC c1 c2 w1 x1 w2 x2 -> hetC c2 c3 w2 x2 w3 x3 -> hetC c1 c3 w1 x1 w3 x3.
Proof.
  intros [P HP] [Q HQ]; exists (iso_trans _ _ _ P Q).
  eapply kEqC_trans; [apply (ctoK_fun c1 c2 c3 P Q) |].
  eapply kEqC_trans; [apply (ctoK_eq c2 c3 Q _ _ _ _ HP) | exact HQ].
Qed.

(* Placement is transparent for the transport as well as for the decoding,
   the equality and the shadow (Interp/Stage.v): the canonical transport
   between two placed components IS the one between the codes. *)
Lemma place_to k T (fT : forall y, prec y T -> Acc prec y)
  p (c : Code k (nodeAt T fT p)) p' (c' : Code k (nodeAt T fT p'))
  (P : kirel (place k T fT p c) (place k T fT p' c')) v y :
  hj_to (khj k (rk T (hT T fT)) (rk T (hT T fT)))
        (place k T fT p c) (place k T fT p' c') P v y
  = ctoK c c' P v y.
Proof. reflexivity. Qed.

(* And the same between two DIFFERENT nodes, which is what a law about the
   transport at a structured code needs: the two readings of one syntactic type
   sit at the ranks of their own realisers. *)
Lemma place_to_het (k : nat) T (fT : forall y, prec y T -> Acc prec y)
  T' (fT' : forall y, prec y T' -> Acc prec y)
  p (c : Code k (nodeAt T fT p)) p' (c' : Code k (nodeAt T' fT' p'))
  (P : hj_rel (khj k (rk T (hT T fT)) (rk T' (hT T' fT')))
              (place k T fT p c) (place k T' fT' p' c')) v y :
  hj_to (khj k (rk T (hT T fT)) (rk T' (hT T' fT')))
        (place k T fT p c) (place k T' fT' p' c') P v y
  = ctoK c c' P v y.
Proof. reflexivity. Qed.

(* The pullback at two placed components is likewise the one between the codes. *)
Lemma place_pull_het (k : nat) T (fT : forall y, prec y T -> Acc prec y)
  T' (fT' : forall y, prec y T' -> Acc prec y)
  p (c : Code k (nodeAt T fT p)) p' (c' : Code k (nodeAt T' fT' p'))
  (P : hj_rel (khj k (rk T (hT T fT)) (rk T' (hT T' fT')))
              (place k T fT p c) (place k T' fT' p' c')) v y :
  hj_pull (khj k (rk T (hT T fT)) (rk T' (hT T' fT')))
          (place k T fT p c) (place k T' fT' p' c') P v y
  = cpullK c c' P v y.
Proof. reflexivity. Qed.

(* The pullback of a transported element IS the element.  Both sides are
   transports of y between the same pair of codes -- on the left along
   cpullK iA o ctoK co' o ctoK Q, on the right along ctoK co -- so ctoK_fun
   composes them, ctoK_irr identifies them, and cpullK_eq with ctoK_pull undoes
   the pullback.  Stated abstractly on purpose: at a Pi-code the transport
   applies the function at a PULLED BACK argument, and this is what reconciles
   that with the argument in hand. *)
Lemma pull_of_to {k bA bA' b b'} (cA : Code k bA) (cA' : Code k bA')
  (c : Code k b) (c' : Code k b')
  (iA : iso c c') (co : iso cA c) (co' : iso cA' c') (Q : iso cA cA') v y :
  kEqC c v (cpullK c c' iA v (ctoK cA' c' co' v (ctoK cA cA' Q v y)))
         v (ctoK cA c co v y).
Proof.
  eapply kEqC_trans; [ apply cpullK_eq | apply ctoK_pull ].
  eapply kEqC_trans;
    [ apply kEqC_sym; apply (ctoK_fun cA cA' c' Q co' (iso_trans cA cA' c' Q co'))
    |].
  eapply kEqC_trans;
    [ apply (ctoK_irr cA c' (iso_trans cA cA' c' Q co') (iso_trans cA c c' co iA))
    | apply (ctoK_fun cA c c' co iA (iso_trans cA c c' co iA)) ].
Qed.

(* And the same between two families, at their canonical codes: this is the
   relation the paper writes (u, x) ~ (u', x'). *)
Definition kRel {k u u'} (F : kUFam k u) (F' : kUFam k u')
  w (x : kElAt F w) w' (x' : kElAt F' w') : Prop := hetC (kAt F) (kAt F') w x w' x'.

Lemma kRel_at {k u u'} (F : kUFam k u) (F' : kUFam k u') (P : iso (kAt F) (kAt F'))
  w x w' x' : kRel F F' w x w' x' -> kEqC (kAt F') w (ctoK (kAt F) (kAt F') P w x) w' x'.
Proof. apply hetC_at. Qed.

(* A family is isomorphic to itself: uf_coh at the canonical instance. *)
Definition iso_self {k u} (F : kUFam k u) : iso (kAt F) (kAt F) :=
  uf_coh F u (kAcc F) (evalAg_refl u) u (kAcc F) (evalAg_refl u).

Lemma kRel_refl {k u} (F : kUFam k u) w (x : kElAt F w) : kRel F F w x w x.
Proof.
  exists (iso_self F).
  apply (uf_idp F u (kAcc F) (evalAg_refl u) (iso_self F) w x).
Qed.

Lemma kRel_sym {k u u'} (F : kUFam k u) (F' : kUFam k u') w x w' x' :
  kRel F F' w x w' x' -> kRel F' F w' x' w x.
Proof. apply hetC_sym. Qed.

Lemma kRel_trans {k u1 u2 u3} (F1 : kUFam k u1) (F2 : kUFam k u2) (F3 : kUFam k u3)
  w1 x1 w2 x2 w3 x3 :
  kRel F1 F2 w1 x1 w2 x2 -> kRel F2 F3 w2 x2 w3 x3 -> kRel F1 F3 w1 x1 w3 x3.
Proof. apply hetC_trans. Qed.

(* ------------------------------------------------------------------ *)
(* 3.  Layer-1 goodness of a semantic element (Lemma 8.4, packaged).  *)
(* ------------------------------------------------------------------ *)

Lemma kSh_good {k u} (F : kUFam k u) w (x : kElAt F w) : Good (sh (kAt F)) w.
Proof.
  exact (El_good (kstage k (rk u (kAcc F))) (kU k) (kUEq k) (kOK k) (lsound (lvl k))
           (projT2 (kAt F)) w (proj1_sig x)).
Qed.

Lemma kEl_good {k u} (F : kUFam k u) w (x : kElAt F w) : Good u w.
Proof.
  eapply Rel_cast; [apply (uf_sh F u (kAcc F) (evalAg_refl u)) | apply kSh_good, x].
Qed.

Lemma kFam_good_ty {k u} (F : kUFam k u) : Good_ty u.
Proof. exists k; apply (uf_ty F). Qed.

Lemma kRel_rel {k u u'} (F : kUFam k u) (F' : kUFam k u') w x w' x' :
  kRel F F' w x w' x' -> Rel u' w w'.
Proof.
  intros [P HP].
  eapply Rel_cast; [apply (uf_sh F' u' (kAcc F') (evalAg_refl u')) |].
  exact (eqEl_rel (kstage k (rk u' (kAcc F'))) (kU k) (kUEq k) (kOK k) (lsound (lvl k))
           (projT2 (kAt F')) w _ w' _ HP).
Qed.

(* ------------------------------------------------------------------ *)
(* 4.  Environments.                                                  *)
(*                                                                    *)
(* An entry is the semantic value of one variable together with the    *)
(* family its type is interpreted by; rsub reads off the substitution  *)
(* of realisers, and does so by a scons fold, so that extending the    *)
(* environment extends the substitution DEFINITIONALLY.                *)
(* ------------------------------------------------------------------ *)

Record Entry := {
  en_k : nat;
  en_S : etm;
  en_F : kUFam en_k en_S;
  en_u : etm;
  en_x : kElAt en_F en_u
}.

Definition Env := list Entry.

Fixpoint rsub (rho : Env) : nat -> etm :=
  match rho with
  | nil => var_etm
  | en :: rho0 => scons (en_u en) (rsub rho0)
  end.

(* The erasure of a term under an environment. *)
Definition ers (rho : Env) (t : tm) : etm := subst_etm (rsub rho) (er t).

Definition ext (rho : Env) {k S} (F : kUFam k S) (w : etm) (x : kElAt F w) : Env :=
  Build_Entry k S F w x :: rho.

Lemma rsub_ext rho {k S} (F : kUFam k S) w x :
  rsub (ext rho F w x) = scons w (rsub rho).
Proof. reflexivity. Qed.

Lemma ers_ext rho {k S} (F : kUFam k S) w x t :
  ers (ext rho F w x) t = subst_etm (scons w (rsub rho)) (er t).
Proof. reflexivity. Qed.

Lemma ers_var rho i : ers rho (var_tm i) = rsub rho i.
Proof. reflexivity. Qed.

(* Lemma 9.1, realiser half: substitution in the syntax is extension of the
   environment. *)
Lemma ers_sub1 rho t a {k S} (F : kUFam k S) x :
  ers rho (t [a..]) = ers (ext rho F (ers rho a) x) t.
Proof. unfold ers at 1; rewrite er_sub1; reflexivity. Qed.

Lemma ers_shift rho {k S} (F : kUFam k S) w x t :
  ers (ext rho F w x) (t ⟨↑⟩) = ers rho t.
Proof.
  unfold ers, ext; cbn; rewrite er_ren, sub_shift.
  apply ext_etm; intros y; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5.  Related environments.  The level is shared between two related  *)
(* entries, which is why this is an inductive rather than a            *)
(* conjunction: with the levels merely equal, every field would need   *)
(* transporting along that equality.                                   *)
(* ------------------------------------------------------------------ *)

(* The dependent content of an entry at a FIXED level.  Stating EntryRel's
   content as a relation between two such packages is what makes it
   invertible: the only equation left to transport along is one between
   natural numbers, where UIP is a theorem (Eqdep_dec, no axioms).  The
   inductive formulation that came before was not invertible -- `destruct`
   drops the level and `inversion` produces heterogeneous equations in the
   dependent fields F and x, which would need decidable equality of
   families. *)
Definition EnPack (k : nat) : Type :=
  { S : etm & { F : kUFam k S & { u : etm & kElAt F u } } }.

Definition enPack (en : Entry) : EnPack (en_k en) :=
  existT _ (en_S en) (existT _ (en_F en) (existT _ (en_u en) (en_x en))).

Definition relPack {k} (p q : EnPack k) : Prop :=
  kRel (projT1 (projT2 p)) (projT1 (projT2 q))
       (projT1 (projT2 (projT2 p))) (projT2 (projT2 (projT2 p)))
       (projT1 (projT2 (projT2 q))) (projT2 (projT2 (projT2 q))).

Definition EntryRel (a b : Entry) : Prop :=
  exists E : en_k a = en_k b,
    relPack (eq_rect (en_k a) EnPack (enPack a) (en_k b) E) (enPack b).

Definition UIP_nat {m n : nat} (E E' : m = n) : E = E' :=
  Eqdep_dec.UIP_dec Nat.eq_dec E E'.

(* The two halves of what the old inductive gave: the constructor, and the
   inversion that it could not support. *)
Lemma entry_rel k S (F : kUFam k S) w x S' (F' : kUFam k S') w' x' :
  kRel F F' w x w' x' ->
  EntryRel (Build_Entry k S F w x) (Build_Entry k S' F' w' x').
Proof. intros H; exists eq_refl; exact H. Qed.

Lemma EntryRel_at k S (F : kUFam k S) w x S' (F' : kUFam k S') w' x' :
  EntryRel (Build_Entry k S F w x) (Build_Entry k S' F' w' x') ->
  kRel F F' w x w' x'.
Proof.
  intros [E H]; rewrite (UIP_nat E eq_refl) in H; exact H.
Qed.

(* The level equation, for an entry not yet in constructor form.  A caller
   that needs the relation itself destructs the two entries first and then
   uses EntryRel_at. *)
Lemma EntryRel_k a b : EntryRel a b -> en_k a = en_k b.
Proof. intros [E _]; exact E. Qed.

Fixpoint EnvRel (rho rho' : Env) : Prop :=
  match rho, rho' with
  | nil, nil => True
  | en :: r, en' :: r' => EnvRel r r' /\ EntryRel en en'
  | _, _ => False
  end.

Lemma EntryRel_refl en : EntryRel en en.
Proof. destruct en; apply entry_rel; apply kRel_refl. Qed.

Lemma EntryRel_sym en en' : EntryRel en en' -> EntryRel en' en.
Proof.
  destruct en as [ka Sa Fa ua xa], en' as [kb Sb Fb ub xb].
  intros [E H]; cbn in E, H; destruct E; cbn in H.
  apply entry_rel; apply kRel_sym; exact H.
Qed.

(* Transitivity, which the inductive formulation could not support: composing
   two EntryRels needed injectivity of Build_Entry in a dependent field.  With
   the level equation isolated it is just kRel_trans. *)
Lemma EntryRel_trans a b c : EntryRel a b -> EntryRel b c -> EntryRel a c.
Proof.
  destruct a as [ka Sa Fa ua xa], b as [kb Sb Fb ub xb], c as [kc Sc Fc uc xc].
  intros [E1 H1] [E2 H2]; cbn in E1, E2, H1, H2; destruct E1; destruct E2;
    cbn in H1, H2.
  apply entry_rel; eapply kRel_trans; [exact H1 | exact H2].
Qed.

Lemma EnvRel_refl rho : EnvRel rho rho.
Proof.
  induction rho as [| en r IH]; cbn; [exact I | split; [exact IH | apply EntryRel_refl]].
Qed.

Lemma EnvRel_sym rho rho' : EnvRel rho rho' -> EnvRel rho' rho.
Proof.
  revert rho'; induction rho as [| en r IH]; intros [| en' r']; cbn; try tauto.
  intros [H1 H2]; split; [apply IH; exact H1 | apply EntryRel_sym; exact H2].
Qed.

Lemma EnvRel_ext rho rho' {k S} (F : kUFam k S) w x {S'} (F' : kUFam k S') w' x' :
  EnvRel rho rho' -> kRel F F' w x w' x' ->
  EnvRel (ext rho F w x) (ext rho' F' w' x').
Proof. intros H1 H2; split; [exact H1 | apply entry_rel; exact H2]. Qed.
