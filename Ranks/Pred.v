From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def.

(* Component witnesses: an inductive family of *data* rather than a relation,
   so that Brouwer sups can be indexed by it (Remark 7.1 of the blueprint).
   Every index is a component by construction, no decision is involved.

   Deviation from the blueprint: there is no universe clause.  Universes are
   handled by an outer recursion on the level in Codes/, so ranks only have
   to bound the nesting of Pi and Sigma. *)
Inductive Pred (T : etm) : Type :=
| p_dom A0 B0 : eval T (epi A0 B0) -> Pred T
| p_cod A0 B0 u : eval T (epi A0 B0) -> Good A0 u -> Pred T
| p_sdom A0 B0 : eval T (esig A0 B0) -> Pred T
| p_scod A0 B0 u : eval T (esig A0 B0) -> Good A0 u -> Pred T.

Arguments p_dom {T}. Arguments p_cod {T}. Arguments p_sdom {T}. Arguments p_scod {T}.

Definition pred {T} (p : Pred T) : etm :=
  match p with
  | p_dom A0 _ _ => A0
  | p_cod _ B0 u _ _ => eapp B0 u
  | p_sdom A0 _ _ => A0
  | p_scod _ B0 u _ _ => eapp B0 u
  end.

Definition prec (C T : etm) : Prop := exists p : Pred T, pred p = C.

(* Predecessors only depend on the whnf: terms with a common reduct have
   witnesses in bijection.  This is what makes the rank of B0 . u and of its
   beta-reduct comparable in Codes/. *)
Definition Pred_red {T T'} (H : forall w, eval T w -> eval T' w) (p : Pred T) : Pred T' :=
  match p with
  | p_dom A0 B0 e => p_dom A0 B0 (H _ e)
  | p_cod A0 B0 u e g => p_cod A0 B0 u (H _ e) g
  | p_sdom A0 B0 e => p_sdom A0 B0 (H _ e)
  | p_scod A0 B0 u e g => p_scod A0 B0 u (H _ e) g
  end.

Lemma pred_Pred_red {T T'} (H : forall w, eval T w -> eval T' w) p :
  pred (Pred_red H p) = pred p.
Proof. destruct p; reflexivity. Qed.
