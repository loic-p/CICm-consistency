From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Ranks.Pred Ranks.Ord Ranks.Acc.

(* The rank: the one essential large elimination of Acc, written as a
   structural fixpoint on the accessibility proof.  Do not restate this
   definition: the stage bookkeeping in Interp/ relies on
   rk T (Acc_intro T f) = osup T (fun p => osucc (rk (pred p) _)) by
   computation. *)
Fixpoint rk (T : etm) (h : Acc prec T) {struct h} : Ord :=
  match h with
  | Acc_intro _ f => osup T (fun p => osucc (rk (pred p) (f (pred p) (ex_intro _ p eq_refl))))
  end.

Lemma rk_unfold T (h : Acc prec T) :
  rk T h = osup T (fun p => osucc (rk (pred p) (Acc_inv h (ex_intro _ p eq_refl)))).
Proof. destruct h; reflexivity. Qed.

(* Lemmas 7.6 and 7.8 in one: the rank is invariant, up to simulation, under
   the accessibility proof and under reduction of the term.  Type-valued, so
   it is a fixpoint on the proof rather than an induction. *)
Fixpoint rk_osim_eval T (h : Acc prec T) {struct h} :
  forall T' (HT : forall w, eval T w -> eval T' w) (h' : Acc prec T'),
    osim (rk T h) (rk T' h') :=
  match h as h0 return forall T' (HT : forall w, eval T w -> eval T' w) (h' : Acc prec T'),
                         osim (rk T h0) (rk T' h') with
  | Acc_intro _ f => fun T' HT h' =>
    match h' as h0' return osim (rk T (Acc_intro T f)) (rk T' h0') with
    | Acc_intro _ f' =>
      existT _ (Pred_red HT) (fun p =>
        rk_osim_eval (pred p) (f _ (ex_intro _ p eq_refl)) (pred (Pred_red HT p))
          (fun w e => eq_rect _ (fun x => eval x w) e _ (eq_sym (pred_Pred_red HT p)))
          (f' _ (ex_intro _ (Pred_red HT p) eq_refl)))
    end
  end.

Lemma rk_irrel T (h h' : Acc prec T) : osim (rk T h) (rk T h').
Proof. apply rk_osim_eval; auto. Qed.

Lemma rk_red T T' (H : reds T T') h h' : osim (rk T h) (rk T' h').
Proof. apply rk_osim_eval; intros; eapply eval_reds_inv; eauto. Qed.

Lemma rk_exp T T' (H : reds T T') h h' : osim (rk T' h') (rk T h).
Proof. apply rk_osim_eval; intros; eapply eval_reds; eauto. Qed.
