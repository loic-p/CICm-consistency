From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.Univ.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* 1.  The relation between elements of two families.                  *)
(*                                                                    *)
(* It bundles the equality of the two families' codes with the equality *)
(* of the elements, exactly as v1 bundled an isomorphism with a         *)
(* heterogeneous relatedness -- and for the same reason: transitivity   *)
(* of the element equality needs the code equality, and `EntryRel` must  *)
(* be transitive with no extra data.  What is gone is the TRANSPORT:     *)
(* v1's `hetC c c' w x w' x'` said: there is an iso P and x' is related  *)
(* to the transport of x along P.  Here the second component is the      *)
(* primitive heterogeneous equality.                                    *)
(* ------------------------------------------------------------------ *)

Definition kRel {k u u'} (F : kUFam k u) w (x : kElAt F w)
  (F' : kUFam k u') w' (x' : kElAt F' w') : Prop :=
  kceq (kAt F) (kAt F') /\ kEqAt F w x F' w' x'.

Definition kRel_ceq {k u u'} {F : kUFam k u} {w x} {F' : kUFam k u'} {w' x'}
  (H : kRel F w x F' w' x') : kceq (kAt F) (kAt F') := proj1 H.
Definition kRel_at {k u u'} {F : kUFam k u} {w x} {F' : kUFam k u'} {w' x'}
  (H : kRel F w x F' w' x') : kEqAt F w x F' w' x' := proj2 H.

Lemma kRel_refl {k u} (F : kUFam k u) w (x : kElAt F w) : kRel F w x F w x.
Proof. split; [exact (famAtSelf F) | exact (kEqAt_refl F w x)]. Qed.

Lemma kRel_sym {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kRel F w x F' w' x' -> kRel F' w' x' F w x.
Proof.
  intros [H1 H2]; split; [apply knsymU; exact H1 | apply kEqAt_sym; exact H2].
Qed.

Lemma kRel_trans {k u1 u2 u3} (F1 : kUFam k u1) w1 x1 (F2 : kUFam k u2) w2 x2
  (F3 : kUFam k u3) w3 x3 :
  kRel F1 w1 x1 F2 w2 x2 -> kRel F2 w2 x2 F3 w3 x3 -> kRel F1 w1 x1 F3 w3 x3.
Proof.
  intros [H1 H2] [H1' H2']; split.
  - exact (ktrU (kAt F1) (kAt F2) (kAt F3) (famAtWf F1) (famAtWf F2) (famAtWf F3) H1 H1').
  - eapply kEqAt_trans; [exact H1 | exact H2 | exact H2'].
Qed.

Lemma kRel_rel {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kRel F w x F' w' x' -> Rel u w w'.
Proof. intros H; exact (famEl_rel F w x F' w' x' (kRel_at H)). Qed.

Lemma kRel_ty {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kRel F w x F' w' x' -> eqty k u u'.
Proof. intros H; exact (ceq_eqty F F' (kRel_ceq H)). Qed.

Lemma kFam_good_ty {k u} (F : kUFam k u) : Good_ty u.
Proof. exists k; exact (uf_ty F). Qed.

Lemma kEl_good {k u} (F : kUFam k u) w (x : kElAt F w) : Good u w.
Proof. exact (famEl_good F w x). Qed.

(* ------------------------------------------------------------------ *)
(* 2.  Environments.                                                   *)
(*                                                                    *)
(* An entry is the semantic value of one variable together with the     *)
(* family its type is interpreted by; rsub reads off the substitution   *)
(* of realisers, and does so by a scons fold, so that extending the     *)
(* environment extends the substitution DEFINITIONALLY.                 *)
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
  | nil => sid
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
Proof.
  unfold ers at 1; rewrite er_subst1; unfold ers, ext; cbn.
  apply subst_sub1_etm.
Qed.

Lemma ers_shift rho {k S} (F : kUFam k S) w x t :
  ers (ext rho F w x) (t ⟨↑⟩) = ers rho t.
Proof.
  unfold ers, ext; cbn; rewrite er_ren; apply subst_cons_shift_etm.
Qed.

(* ------------------------------------------------------------------ *)
(* 3.  Related environments.  The level is shared between two related  *)
(* entries, which is why this is stated through a package at a FIXED    *)
(* level rather than as an inductive: with the levels merely equal,     *)
(* every field would need transporting along that equality, and         *)
(* `destruct` on the inductive dropped the level while `inversion`      *)
(* produced heterogeneous equations in the dependent fields.  Isolating  *)
(* the level equation leaves only an equation between natural numbers,   *)
(* where UIP is a theorem (Eqdep_dec, no axioms).                        *)
(* ------------------------------------------------------------------ *)

Definition EnPack (k : nat) : Type :=
  { S : etm & { F : kUFam k S & { u : etm & kElAt F u } } }.

Definition enPack (en : Entry) : EnPack (en_k en) :=
  existT _ (en_S en) (existT _ (en_F en) (existT _ (en_u en) (en_x en))).

Definition relPack {k} (p q : EnPack k) : Prop :=
  kRel (projT1 (projT2 p)) (projT1 (projT2 (projT2 p))) (projT2 (projT2 (projT2 p)))
       (projT1 (projT2 q)) (projT1 (projT2 (projT2 q))) (projT2 (projT2 (projT2 q))).

Definition EntryRel (a b : Entry) : Prop :=
  exists E : en_k a = en_k b,
    relPack (eq_rect (en_k a) EnPack (enPack a) (en_k b) E) (enPack b).

Definition UIP_nat {m n : nat} (E E' : m = n) : E = E' :=
  Eqdep_dec.UIP_dec Nat.eq_dec E E'.

(* the constructor, and the inversion an inductive could not support *)
Lemma entry_rel k S (F : kUFam k S) w x S' (F' : kUFam k S') w' x' :
  kRel F w x F' w' x' ->
  EntryRel (Build_Entry k S F w x) (Build_Entry k S' F' w' x').
Proof. intros H; exists eq_refl; exact H. Qed.

Lemma EntryRel_at k S (F : kUFam k S) w x S' (F' : kUFam k S') w' x' :
  EntryRel (Build_Entry k S F w x) (Build_Entry k S' F' w' x') ->
  kRel F w x F' w' x'.
Proof. intros [E H]; rewrite (UIP_nat E eq_refl) in H; exact H. Qed.

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

Lemma EnvRel_trans rho rho' rho'' :
  EnvRel rho rho' -> EnvRel rho' rho'' -> EnvRel rho rho''.
Proof.
  revert rho' rho''; induction rho as [| en r IH]; intros [| en' r'] [| en'' r''];
    cbn; try tauto.
  intros [H1 H2] [H1' H2']; split;
    [eapply IH; [exact H1 | exact H1'] | eapply EntryRel_trans; [exact H2 | exact H2']].
Qed.

Lemma EnvRel_ext rho rho' {k S} (F : kUFam k S) w x {S'} (F' : kUFam k S') w' x' :
  EnvRel rho rho' -> kRel F w x F' w' x' ->
  EnvRel (ext rho F w x) (ext rho' F' w' x').
Proof. intros H1 H2; split; [exact H1 | apply entry_rel; exact H2]. Qed.
