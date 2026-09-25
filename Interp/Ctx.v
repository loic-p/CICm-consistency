From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim Layer1.Fundamental.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build Interp.Fam Interp.PiFam
  Interp.Univ Interp.Env Interp.Elem Interp.PiEl Interp.Rec Interp.Def Interp.Inv.
From Stdlib Require Import Arith Lia.

Import UnscopedNotations.
Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* 1.  Environments that fit a context, and the bridge to layer 1.    *)
(*                                                                    *)
(* The bridge is what lets the layer-2 fundamental lemma call the      *)
(* layer-1 one: an environment's realisers ARE a layer-1 related pair  *)
(* of substitutions.  The proof needs the context's typing            *)
(* derivations, because moving the relation from the second entry's    *)
(* realiser to the first one's is exactly layer 1's type clause at the *)
(* context type -- which is why this is an induction on wfc.          *)
(* ------------------------------------------------------------------ *)

(* The entry's realiser need only be LAYER-1 EQUAL to the context type's, not
   syntactically equal.  Conversion forces this: a congruence at a binder --
   c_pi, c_sig, c_all, c_lam -- compares two types whose domains A and A' are
   only convertible, so one environment has to serve for both A :: G and
   A' :: G.  Nothing is lost: the two consumers are EnvOf_SubstRel, which casts
   its layer-1 relation along the equality anyway, and EnvITy (Interp/Fund.v),
   which carries the isomorphism to a genuine interpretation. *)
Fixpoint EnvOf (G : ctx) (rho : Env) : Prop :=
  match G, rho with
  | nil, nil => True
  | A :: G0, en :: rho0 => EnvOf G0 rho0 /\ tyeq (en_S en) (ers rho0 A)
  | _, _ => False
  end.

Lemma EnvOf_ext G rho A {k} (F : kUFam k (ers rho A)) w x :
  EnvOf G rho -> EnvOf (A :: G) (ext rho F w x).
Proof. intros H; split; [exact H | exists k; exact (uf_ty F)]. Qed.

Lemma EnvOf_ext_ty G rho (A : tm) k S (F : kUFam k S) w x :
  EnvOf G rho -> tyeq S (ers rho A) -> EnvOf (A :: G) (ext rho F w x).
Proof. intros H Hty; split; [exact H | exact Hty]. Qed.

Lemma EnvOf_SubstRel G (W : wfc G) : forall rho rho',
  EnvOf G rho -> EnvOf G rho' -> EnvRel rho rho' ->
  SubstRel G (rsub rho) (rsub rho').
Proof.
  induction W as [| G A k W IH dA IHd]; intros rho rho' HO HO' HR.
  - destruct rho; destruct rho'; exact I.
  - destruct rho as [| en rho0]; [destruct HO |].
    destruct rho' as [| en' rho0']; [destruct HO' |].
    destruct HO as [HO HS]; destruct HO' as [HO' HS'].
    destruct HR as [HR Hen].
    assert (Htail : SubstRel G (rsub rho0) (rsub rho0')) by (apply IH; assumption).
    split.
    + eapply SubstRel_ext; [| | exact Htail]; intros y; reflexivity.
    + rewrite (ext_etm (funcomp (rsub (en :: rho0)) shift) (rsub rho0)
                 (fun y => eq_refl) (er A)).
      destruct en as [k0 S0 F0 w0 x0]; destruct en' as [k0' S0' F0' w0' x0'].
      destruct Hen as [E Hrel]; cbn [en_k] in E; destruct E.
      unfold ers in HS, HS'; cbn in HS, HS' |- *.
      eapply Rel_cast;
        [apply eqty_sym, (fundamental_U _ _ _ dA (rsub rho0) (rsub rho0') Htail) |].
      destruct HS' as [n' HS'].
      eapply Rel_cast; [exact HS' |].
      exact (kRel_rel F0 F0' w0 x0 w0' x0' Hrel).
Qed.

(* ------------------------------------------------------------------ *)
(* 2.  Casting a family along an equality of realisers.               *)
(*                                                                    *)
(* Needed because erasure does not commute with substitution           *)
(* definitionally: the family of B[a..] and the family of B in the     *)
(* extended environment have realisers that are equal (ers_sub1) but   *)
(* not convertible, so the semantic substitution lemma has to move a   *)
(* family across that equality.  Everything is invariant under the     *)
(* cast, which is what makes it harmless.                             *)
(* ------------------------------------------------------------------ *)

Definition famCast {k w w'} (E : w = w') (F : kUFam k w) : kUFam k w' :=
  eq_rect w (kUFam k) F w' E.

Definition elCast {k w w'} (E : w = w') (F : kUFam k w) (u : etm) (x : kElAt F u)
  : kElAt (famCast E F) u.
Proof. destruct E; exact x. Defined.

Lemma famCast_iso {k w w'} (E : w = w') (F : kUFam k w) :
  iso (kAt F) (kAt (famCast E F)).
Proof. destruct E; apply iso_self. Qed.

Lemma famCast_rel {k w w'} (E : w = w') (F : kUFam k w) u (x : kElAt F u) :
  kRel F (famCast E F) u x u (elCast E F u x).
Proof. destruct E; apply kRel_refl. Qed.

Lemma famCast_refl {k w} (F : kUFam k w) : famCast eq_refl F = F.
Proof. reflexivity. Qed.
