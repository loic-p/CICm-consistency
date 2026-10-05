From CICM Require Import Syntax.Ann Syntax.Erasure Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Layer1.BadTransp.
From Stdlib Require Import Arith Lia.

Open Scope list_scope.

(* A NOTE ON NAMES.  Both term algebras are loaded here, and each generates
   its own scons, sid and up_subst.  Syntax.Erased is imported LAST, so the
   bare names are the ERASED ones -- which is what every substitution in this
   file is -- and the annotated algebra is reached through its notations
   (t [s], t ⟨r⟩, .: , .. , .:s), which are bound to their own constants. *)

(* Theorem 6.7: the layer-1 fundamental lemma.

   Two departures from the blueprint's statement, both explained where they
   are used:

   - The conversion clause is stated in BOTH orders.  The blueprint's single
     clause is not closed under c_sym: swapping the two sides also swaps the
     two substitutions, and moving the relation back to the type at the
     first substitution would need eqty ((er A)[s]) ((er A)[s']), which the
     redundant premises of c_sym do not supply.  Stating both orders makes
     symmetry a projection and costs nothing anywhere else.

   - The type-level and Prop-level clauses are not part of the induction:
     they are corollaries of the term-level clause at the types Typek and
     Prop, by Rel_univ_elim and Rel_prop_elim.

   Eq is not part of the theory; see Layer1/BadTransp.v for why its
   transport rule makes this theorem false. *)

(* ------------------------------------------------------------------ *)
(* Substitution plumbing.  Erasure commutes with substitution         *)
(* (Erasure.er_subst); the erased algebra's own equations are proved   *)
(* in Syntax/Erased.v, which is where rasimpl is aimed at the erased   *)
(* signature, and this file only combines them.                       *)
(* ------------------------------------------------------------------ *)

(* A singleton substitution absorbed into an outer one. *)
Lemma sub_cons (t u : etm) (s : nat -> etm) :
  subst_etm s (subst_etm (scons u sid) t) = subst_etm (scons (subst_etm s u) s) t.
Proof. apply subst_sub1_etm. Qed.

(* A shift absorbed into an outer substitution. *)
Lemma sub_shift (t : etm) (s : nat -> etm) :
  subst_etm s (ren_etm ↑ t) = subst_etm (rscomp ↑ s) t.
Proof. apply subst_ren_etm. Qed.

(* Beta at an erased binder: this is what makes the codomain of an erased
   Pi behave like a family. *)
Lemma reds_lam_app (B : etm) (s : nat -> etm) (u : etm) :
  reds (eapp (subst_etm s (elam B)) u) (subst_etm (scons u s) B).
Proof.
  eapply reds_step; [apply red_beta |].
  rewrite subst_up_sub1_etm; apply reds_refl.
Qed.

(* The same for a term under TWO binders: natrec's step term erases to
   elam (elam .), and the two beta-steps that separate its body's realiser from
   eapp (eapp . m) u are what the erased recursor's computation rule leaves
   behind.  Layer 1 closes the gap by expansion, as it does for every other
   redex the erasure introduces. *)
Lemma reds_lam2_app (B : etm) (s : nat -> etm) (m u : etm) :
  reds (eapp (eapp (subst_etm s (elam (elam B))) m) u)
       (subst_etm (scons u (scons m s)) B).
Proof.
  eapply reds_trans; [apply reds_app, (reds_lam_app (elam B) s m) |].
  apply (reds_lam_app B (scons m s) u).
Qed.

(* And under THREE binders, which is what wrec's step needs: the label, the
   branching function, and the induction hypothesis. *)
Lemma reds_lam3_app (B : etm) (s : nat -> etm) (a f y : etm) :
  reds (eapp (eapp (eapp (subst_etm s (elam (elam (elam B)))) a) f) y)
       (subst_etm (scons y (scons f (scons a s))) B).
Proof.
  eapply reds_trans;
    [apply reds_app, reds_app, (reds_lam_app (elam (elam B)) s a) |].
  apply (reds_lam2_app B (scons a s) f y).
Qed.

(* A shifted term under an extended substitution. *)
Lemma sub_shift_up (t : etm) (s : nat -> etm) :
  subst_etm (up_etm s) (ren_etm ↑ t) = ren_etm ↑ (subst_etm s t).
Proof. apply subst_up_shift_etm. Qed.

(* ------------------------------------------------------------------ *)
(* Substitutions and renamings pushed through a constructor.  All of   *)
(* these are definitional; they are stated as lemmas only so that      *)
(* rewriting can aim at them without cbn also unfolding the erasure of *)
(* the components.                                                     *)
(* ------------------------------------------------------------------ *)

Lemma sub_lam (B : etm) (g : nat -> etm) :
  subst_etm g (elam B) = elam (subst_etm (up_etm g) B).
Proof. reflexivity. Qed.

Lemma sub_app (X Y : etm) (g : nat -> etm) :
  subst_etm g (eapp X Y) = eapp (subst_etm g X) (subst_etm g Y).
Proof. reflexivity. Qed.

Lemma sub_wrec (X Y : etm) (g : nat -> etm) :
  subst_etm g (ewrec X Y) = ewrec (subst_etm g X) (subst_etm g Y).
Proof. reflexivity. Qed.

Lemma sub_var0 (g : nat -> etm) : subst_etm (up_etm g) (var_etm 0) = var_etm 0.
Proof. reflexivity. Qed.

Lemma ren_lam (B : etm) (r : ren) :
  ren_etm r (elam B) = elam (ren_etm (up_ren r) B).
Proof. reflexivity. Qed.

Lemma er_pi_sub (k : nat) (A B : tm) (g : nat -> etm) :
  subst_etm g (er (pi k A B))
  = epi (subst_etm g (er A)) (elam (subst_etm (up_etm g) (er B))).
Proof. reflexivity. Qed.

Lemma er_w_sub (k : nat) (A B : tm) (g : nat -> etm) :
  subst_etm g (er (wt k A B))
  = ew (subst_etm g (er A)) (elam (subst_etm (up_etm g) (er B))).
Proof. reflexivity. Qed.

Lemma er_sup_sub (k : nat) (A B a f : tm) (g : nat -> etm) :
  subst_etm g (er (sup k A B a f))
  = esup (subst_etm g (er a)) (subst_etm g (er f)).
Proof. reflexivity. Qed.

Lemma er_wrec_sub (A B C s w : tm) (g : nat -> etm) :
  subst_etm g (er (wrec A B C s w))
  = ewrec (subst_etm g (elam (elam (elam (er s))))) (subst_etm g (er w)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Layer-1 type formation.  LR_pi, LR_sig and LR_w take the codomain   *)
(* PER as a function, so a bare "exists P" for each argument is not    *)
(* enough: the canonical choice Rel is used instead, which is          *)
(* legitimate because a type system determines its PER (Lemma 6.3).    *)
(* ------------------------------------------------------------------ *)

Lemma tau_Rel n T T' P : tau n T T' P -> P ≐ Rel T.
Proof.
  intros H a b; split.
  - intros HP; eapply Rel_intro; [eapply tau_refl_l; exact H | exact HP].
  - intros HR; eapply Rel_elim; [exact H | exact HR].
Qed.

Lemma eqty_tau n T T' : eqty n T T' -> tau n T T' (Rel T).
Proof. intros [P H]; eapply tau_ext; [exact H | apply (tau_Rel _ _ _ _ H)]. Qed.

Lemma eqty_nat n : eqty n enat enat.
Proof. exists NatPer; apply LR_nat; apply eval_whnf; left; apply v_nat. Qed.

Lemma eqty_prop n : eqty n eprop eprop.
Proof. exists PR; apply LR_prop; apply eval_whnf; left; apply v_prop. Qed.

Lemma eqty_prf n p p' : PR p p' -> eqty n (eprf p) (eprf p').
Proof.
  intros H; exists TruePer; eapply LR_prf;
    [apply eval_whnf; left; apply v_prf | apply eval_whnf; left; apply v_prf | exact H].
Qed.

Lemma eqty_univ m n : m < n -> eqty n (euniv m) (euniv m).
Proof.
  intros Hm; eexists; eapply LR_univ;
    [exact Hm | apply eval_whnf; left; apply v_univ | apply eval_whnf; left; apply v_univ].
Qed.

Lemma eqty_stuck n A A' : stuckv A -> stuckv A' -> eqty n A A'.
Proof. intros ? ?; exists NePer; apply tau_stuck; assumption. Qed.

Lemma eqty_pi n A B A' B' : eqty n A A' ->
  (forall u u', Rel A u u' -> eqty n (eapp B u) (eapp B' u')) ->
  eqty n (epi A B) (epi A' B').
Proof.
  intros HA HB; exists (PiPer (Rel A) (fun u _ => Rel (eapp B u))).
  eapply LR_pi; [apply eval_whnf; left; apply v_pi | apply eval_whnf; left; apply v_pi
    | apply eqty_tau; exact HA |].
  intros u u' Hu; apply eqty_tau; apply HB; exact Hu.
Qed.

Lemma eqty_sig n A B A' B' : eqty n A A' ->
  (forall u u', Rel A u u' -> eqty n (eapp B u) (eapp B' u')) ->
  eqty n (esig A B) (esig A' B').
Proof.
  intros HA HB; exists (SigPer (Rel A) (fun u _ => Rel (eapp B u))).
  eapply LR_sig; [apply eval_whnf; left; apply v_sig | apply eval_whnf; left; apply v_sig
    | apply eqty_tau; exact HA |].
  intros u u' Hu; apply eqty_tau; apply HB; exact Hu.
Qed.

(* W is formed exactly as Pi and Sigma are; the relation on trees is WPer of
   the domain PER and the codomain family, and the family is again taken to
   be the canonical Rel. *)
Lemma eqty_w n A B A' B' : eqty n A A' ->
  (forall u u', Rel A u u' -> eqty n (eapp B u) (eapp B' u')) ->
  eqty n (ew A B) (ew A' B').
Proof.
  intros HA HB; exists (WPer (Rel A) (fun u _ => Rel (eapp B u))).
  eapply LR_w; [apply eval_whnf; left; apply v_w | apply eval_whnf; left; apply v_w
    | apply eqty_tau; exact HA |].
  intros u u' Hu; apply eqty_tau; apply HB; exact Hu.
Qed.

(* Good_ty forms, for the intro lemmas of Layer1/Elim.v. *)
Lemma gt_nat : Good_ty enat.
Proof. exists 0; apply eqty_nat. Qed.

Lemma gt_prop : Good_ty eprop.
Proof. exists 0; apply eqty_prop. Qed.

Lemma gt_univ m : Good_ty (euniv m).
Proof. exists (S m); apply eqty_univ; auto. Qed.

Lemma gt_of n T : eqty n T T -> Good_ty T.
Proof. intros H; exists n; exact H. Qed.

Lemma Rel_cast n T T' a b : eqty n T T' -> Rel T a b -> Rel T' a b.
Proof. intros H; apply (Rel_resp n T T' H). Qed.

(* ------------------------------------------------------------------ *)
(* Related closed substitutions.                                      *)
(* ------------------------------------------------------------------ *)

Fixpoint SubstRel (G : ctx) (s s' : nat -> etm) : Prop :=
  match G with
  | nil => True
  | A :: G0 => SubstRel G0 (rscomp ↑ s) (rscomp ↑ s')
               /\ Rel (subst_etm (rscomp ↑ s) (er A)) (s 0) (s' 0)
  end.

Lemma SubstRel_ext G s1 s1' s2 s2' :
  (forall x, s1 x = s2 x) -> (forall x, s1' x = s2' x) ->
  SubstRel G s1 s1' -> SubstRel G s2 s2'.
Proof.
  revert s1 s1' s2 s2'; induction G as [|A G IH]; intros s1 s1' s2 s2' E E' H;
    [exact I |].
  destruct H as [H1 H2]; split.
  - eapply IH; [| | exact H1]; intros x; unfold rscomp; auto.
  - rewrite <- (E 0), <- (E' 0).
    rewrite (ext_etm (rscomp ↑ s2) (rscomp ↑ s1)
               (fun x => eq_sym (E (↑ x))) (er A)); exact H2.
Qed.

Lemma SubstRel_cons G A s s' u u' :
  SubstRel G s s' -> Rel (subst_etm s (er A)) u u' ->
  SubstRel (A :: G) (scons u s) (scons u' s').
Proof.
  intros HG Hu; split.
  - eapply SubstRel_ext; [| | exact HG]; intros x; reflexivity.
  - rewrite (ext_etm (rscomp ↑ (scons u s)) s (fun x => eq_refl) (er A)); exact Hu.
Qed.

Lemma SubstRel_lookup G s s' : SubstRel G s s' ->
  forall i A, lookup i G A -> Rel (subst_etm s (er A)) (s i) (s' i).
Proof.
  intros H i A Hl; revert s s' H;
    induction Hl as [G A | G i A B Hl IH]; intros s s' H.
  - destruct H as [_ H2]; rewrite er_ren, sub_shift; exact H2.
  - destruct H as [H1 _]; specialize (IH _ _ H1).
    rewrite er_ren, sub_shift; exact IH.
Qed.

Lemma SubstRel_refl G s s' : SubstRel G s s' -> SubstRel G s s.
Proof.
  revert s s'; induction G as [|A G IH]; intros s s' H; [exact I |].
  destruct H as [H1 H2]; split; [eapply IH; exact H1 |].
  eapply Rel_trans; [exact H2 | apply Rel_sym; exact H2].
Qed.

(* ------------------------------------------------------------------ *)
(* Erasure of the substitutions that the typing rules perform.        *)
(*                                                                    *)
(* All of them are instances of one lemma: the erasure of a            *)
(* substitution instance is determined POINTWISE, so the rule's        *)
(* substitution is matched against an erased one by computing it at    *)
(* each index.  With the annotated substitutions written in the        *)
(* algebra (.: and .:s) every index computes, and each instance below   *)
(* is `intros <cases>; reflexivity`.                                   *)
(* ------------------------------------------------------------------ *)

Lemma er_subst_ext (u : tm) (sg : nat -> tm) (t s : nat -> etm) :
  (forall i, subst_etm s (er (sg i)) = t i) ->
  subst_etm s (er (u [sg])) = subst_etm t (er u).
Proof.
  intros H.
  rewrite (er_subst u sg (fun i => er (sg i)) (fun i => eq_refl)).
  rewrite subst_subst_etm; apply ext_etm; exact H.
Qed.

Lemma er_sub1 (B u : tm) (s : nat -> etm) :
  subst_etm s (er (B [u..])) = subst_etm (scons (subst_etm s (er u)) s) (er B).
Proof. apply er_subst_ext; intros [|i]; reflexivity. Qed.

(* The same, under Prf: the erasure has to be pushed through the Prf head
   before the substitution can be rearranged. *)
Lemma er_sub1_prf (j : nat) (B u : tm) (s : nat -> etm) :
  subst_etm s (er (prf j (B [u..])))
  = eprf (subst_etm (scons (subst_etm s (er u)) s) (er B)).
Proof.
  change (subst_etm s (er (prf j (B [u..])))) with (eprf (subst_etm s (er (B [u..])))).
  rewrite er_sub1; reflexivity.
Qed.

Lemma er_nrec_succ (C : tm) (s : nat -> etm) (m y : etm) :
  subst_etm (scons y (scons m s)) (er (nrec_succ C))
  = subst_etm (scons (esucc m) s) (er C).
Proof. unfold nrec_succ; apply er_subst_ext; intros [|i]; reflexivity. Qed.

(* Erasure of a two-variable substitution, as er_sub1 is for one.  This is
   what the successor computation rule of natrec needs: it fills the step
   term's var 1 with the predecessor and var 0 with the recursive result. *)
Lemma er_sub2 (t a b : tm) (s : nat -> etm) :
  subst_etm s (er (t [ a .: b .. ]))
  = subst_etm (scons (subst_etm s (er a)) (scons (subst_etm s (er b)) s)) (er t).
Proof. apply er_subst_ext; intros [| [| i]]; reflexivity. Qed.

(* And of a three-variable one, for wrec's: the induction hypothesis, the
   branching function and the label. *)
Lemma er_sub3 (t a b c : tm) (s : nat -> etm) :
  subst_etm s (er (t [ a .: (b .: c ..) ]))
  = subst_etm (scons (subst_etm s (er a))
              (scons (subst_etm s (er b))
              (scons (subst_etm s (er c)) s))) (er t).
Proof. apply er_subst_ext; intros [| [| [| i]]]; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The three types wrec's step binds, erased.  This is the             *)
(* bureaucratic half of the W eliminator: the fundamental lemma's      *)
(* induction hypothesis for the step is a statement about an arbitrary *)
(* related substitution for the context                               *)
(*                                                                    *)
(*     wih n k A B C  ::  wbr k A B  ::  A  ::  Gamma,                 *)
(*                                                                    *)
(* so each of those three types has to be recognised, erased, as the   *)
(* type of the datum being substituted for it: a label, a branching    *)
(* function into the tree type, and a function from a branch to the    *)
(* motive at the subtree sitting there.                               *)
(* ------------------------------------------------------------------ *)

(* the branching function's type: a NON-dependent Pi from the fibre into the
   tree type, so its erased codomain is a shifted constant *)
Lemma er_wbr_sub (k : nat) (A B : tm) (g : nat -> etm) (a : etm) :
  subst_etm (scons a g) (er (wbr k A B))
  = epi (subst_etm (scons a g) (er B))
        (elam (ren_etm ↑ (subst_etm g (er (wt k A B))))).
Proof.
  unfold wbr; rewrite er_pi_sub, !er_ren, subst_up_cons_shift2_etm; reflexivity.
Qed.

(* the type of a sup's branching function is of the same shape *)
Lemma er_wsup_fun_sub (k : nat) (A B a : tm) (g : nat -> etm) :
  subst_etm g (er (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))
  = epi (subst_etm (scons (subst_etm g (er a)) g) (er B))
        (elam (ren_etm ↑ (subst_etm g (er (wt k A B))))).
Proof. rewrite er_pi_sub, er_sub1, er_ren, sub_shift_up; reflexivity. Qed.

(* the induction hypothesis's type.  Its codomain IS dependent -- the motive
   at the subtree -- so the lemma hands the codomain over together with the
   reduction that opens it, which is all Rel_pi_intro needs. *)
Lemma er_wih_cod (k : nat) (A B C : tm) (g : nat -> etm) (a f u : etm) :
  subst_etm (scons u (scons f (scons a g)))
    (er (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) (var_tm 1) (var_tm 0)
             .:s sh3 ]))
  = subst_etm (scons (eapp f u) g) (er C).
Proof. apply er_subst_ext; intros [|i]; reflexivity. Qed.

Lemma er_wih_sub (n k : nat) (A B C : tm) (g : nat -> etm) (a f : etm) :
  exists Y : etm,
    subst_etm (scons f (scons a g)) (er (wih n k A B C))
    = epi (subst_etm (scons a g) (er B)) (elam Y)
    /\ forall u, reds (eapp (elam Y) u) (subst_etm (scons (eapp f u) g) (er C)).
Proof.
  unfold wih; eexists; split.
  - rewrite er_pi_sub, er_ren, subst_cons_shift_etm; reflexivity.
  - intros u; rewrite <- (er_wih_cod k A B C g a f u).
    apply (reds_lam_app _ (scons f (scons a g)) u).
Qed.

(* the step's own type: the motive at the tree its label and branching
   function build *)
Lemma er_wsup_ty (k : nat) (A B C : tm) (g : nat -> etm) (a f y : etm) :
  subst_etm (scons y (scons f (scons a g))) (er (wsup_ty k A B C))
  = subst_etm (scons (esup a f) g) (er C).
Proof. unfold wsup_ty; apply er_subst_ext; intros [|i]; reflexivity. Qed.

(* the induction hypothesis the computation rule supplies: it is exactly the
   one the ERASED recursor's own computation rule builds, which is what makes
   c_wrec_sup an expansion on both sides and nothing more. *)
Lemma er_wih_val (n k : nat) (A B C s a f : tm) (g : nat -> etm) :
  subst_etm g (er (wih_val n k A B C s a f))
  = elam (ewrec (ren_etm ↑ (subst_etm g (elam (elam (elam (er s))))))
                (eapp (ren_etm ↑ (subst_etm g (er f))) (var_etm 0))).
Proof.
  unfold wih_val, wsub; cbn [er]; rewrite !er_ren.
  rewrite !sub_lam, sub_wrec, sub_app, !sub_lam, sub_var0, !ren_lam.
  rewrite subst_up3_shift_etm, sub_shift_up; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* natrec.  The blueprint's warning applies: the induction is on the   *)
(* PER of the scrutinee, never on a typing derivation.  With NatPer    *)
(* inductive there are exactly three cases, and the stuck one is what  *)
(* makes the recursor total on junk.                                   *)
(* ------------------------------------------------------------------ *)

Lemma reds_rec_zero z s a : eval a ezero -> reds (enatrec z s a) z.
Proof.
  intros [Hr _]; eapply reds_trans; [apply reds_rec, Hr |].
  eapply reds_step; [apply red_rec_z | apply reds_refl].
Qed.

Lemma reds_rec_succ z s a a0 : eval a (esucc a0) ->
  reds (enatrec z s a) (eapp (eapp s a0) (enatrec z s a0)).
Proof.
  intros [Hr _]; eapply reds_trans; [apply reds_rec, Hr |].
  eapply reds_step; [apply red_rec_s | apply reds_refl].
Qed.

Lemma stuckv_err : stuckv eerr.
Proof. exists eerr; split; [apply eval_whnf; right; apply st_err | apply st_err]. Qed.

Lemma Rel_refl_l T a b : Rel T a b -> Rel T a a.
Proof. intros H; eapply Rel_trans; [exact H | apply Rel_sym, H]. Qed.

(* The successor branch.  The step term carries its own two binders, so the
   induction hypothesis for it is a statement about its BODY at two extended
   substitutions; sem_step_body is that statement with the type of the body
   read off by er_nrec_succ, and sem_step puts it back into the applied form
   that the erased recursor's computation rule produces.  Nothing here opens a
   Pi-type any more -- the step has no type to open. *)
Lemma sem_step_body (G : ctx) (j : nat) (C t t' : tm) (g g' : nat -> etm)
  (HS : SubstRel G g g')
  (Hs : forall sigma sigma', SubstRel (C :: nat_ j :: G) sigma sigma' ->
          Rel (subst_etm sigma (er (nrec_succ C)))
              (subst_etm sigma (er t)) (subst_etm sigma' (er t'))) :
  forall m m', NatPer m m' -> forall y y',
    Rel (subst_etm (scons m g) (er C)) y y' ->
    Rel (subst_etm (scons (esucc m) g) (er C))
        (subst_etm (scons y (scons m g)) (er t))
        (subst_etm (scons y' (scons m' g')) (er t')).
Proof.
  intros m m' Hm y y' Hy.
  assert (Hm' : Rel enat m m')
    by (apply Rel_nat_intro;
        [apply gt_nat | apply eval_whnf; left; apply v_nat | exact Hm]).
  assert (H1 : SubstRel (nat_ j :: G) (scons m g) (scons m' g'))
    by (apply (SubstRel_cons G (nat_ j) g g' m m' HS); exact Hm').
  pose proof (Hs (scons y (scons m g)) (scons y' (scons m' g'))
                (SubstRel_cons (nat_ j :: G) C _ _ y y' H1 Hy)) as H2.
  rewrite er_nrec_succ in H2; exact H2.
Qed.

Lemma sem_step (G : ctx) (j : nat) (C t t' : tm) (g g' : nat -> etm)
  (HS : SubstRel G g g')
  (Hs : forall sigma sigma', SubstRel (C :: nat_ j :: G) sigma sigma' ->
          Rel (subst_etm sigma (er (nrec_succ C)))
              (subst_etm sigma (er t)) (subst_etm sigma' (er t'))) :
  forall m m', NatPer m m' -> forall y y',
    Rel (subst_etm (scons m g) (er C)) y y' ->
    Rel (subst_etm (scons (esucc m) g) (er C))
        (eapp (eapp (subst_etm g (elam (elam (er t)))) m) y)
        (eapp (eapp (subst_etm g' (elam (elam (er t')))) m') y').
Proof.
  intros m m' Hm y y' Hy.
  eapply Rel_exp; [apply reds_lam2_app | apply reds_lam2_app |].
  apply (sem_step_body G j C t t' g g' HS Hs); assumption.
Qed.

Lemma sem_natrec (C : tm) (sg : nat -> etm) (k : nat) (z z' sc sc' : etm)
  (HC : forall m m', NatPer m m' ->
        eqty k (subst_etm (scons m sg) (er C)) (subst_etm (scons m' sg) (er C)))
  (Hz : Rel (subst_etm (scons ezero sg) (er C)) z z')
  (Hs : forall m m', NatPer m m' -> forall y y',
        Rel (subst_etm (scons m sg) (er C)) y y' ->
        Rel (subst_etm (scons (esucc m) sg) (er C))
            (eapp (eapp sc m) y) (eapp (eapp sc' m') y')) :
  forall a b, NatPer a b ->
    Rel (subst_etm (scons a sg) (er C)) (enatrec z sc a) (enatrec z' sc' b).
Proof.
  intros a b H; induction H as [a b Ha Hb | a b a0 b0 Ha Hb Hab IH | a b Ha Hb].
  - eapply Rel_cast;
      [apply (HC ezero a (np_zero _ _ (eval_whnf _ (or_introl v_zero)) Ha)) |].
    eapply Rel_exp; [apply (reds_rec_zero _ _ _ Ha) | apply (reds_rec_zero _ _ _ Hb) | exact Hz].
  - eapply Rel_cast;
      [apply (HC (esucc a0) a (np_succ _ _ _ _ (eval_whnf _ (or_introl (v_succ _))) Ha
                                 (NatPer_trans _ _ _ Hab (NatPer_sym _ _ Hab)))) |].
    eapply Rel_exp;
      [apply (reds_rec_succ _ _ _ _ Ha) | apply (reds_rec_succ _ _ _ _ Hb) |].
    apply Hs; [exact Hab | exact IH].
  - apply Rel_stuck;
      [apply (gt_of k), (HC a a (np_stuck _ _ Ha Ha))
      | apply stuckv_rec; exact Ha | apply stuckv_rec; exact Hb].
Qed.

(* ------------------------------------------------------------------ *)
(* Small reduction facts used by the computation rules.               *)
(* ------------------------------------------------------------------ *)

Lemma reds_fst_pair t u : reds (efst (epair t u)) t.
Proof. eapply reds_step; [apply red_fst | apply reds_refl]. Qed.

Lemma reds_snd_pair t u : reds (esnd (epair t u)) u.
Proof. eapply reds_step; [apply red_snd | apply reds_refl]. Qed.

(* The eta-expansion of an erased function, applied. *)
Lemma reds_eta (f u : etm) :
  reds (eapp (elam (eapp (ren_etm ↑ f) (var_etm 0))) u) (eapp f u).
Proof.
  eapply reds_step; [apply red_beta |].
  rewrite sub_app, subst_sub1_shift_etm; apply reds_refl.
Qed.

Lemma sub_eta (f : etm) (g : nat -> etm) :
  subst_etm g (elam (eapp (ren_etm ↑ f) (var_etm 0)))
  = elam (eapp (ren_etm ↑ (subst_etm g f)) (var_etm 0)).
Proof. rewrite sub_lam, sub_app, sub_var0, sub_shift_up; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The semantic type formers, at a pair of substitutions.             *)
(* ------------------------------------------------------------------ *)

Lemma sem_pi_eq (A B A' B' : tm) (k m m' : nat) (s s' : nat -> etm)
  (HA : eqty k (subst_etm s (er A)) (subst_etm s' (er A')))
  (HB : forall u u', Rel (subst_etm s (er A)) u u' ->
        eqty k (subst_etm (scons u s) (er B)) (subst_etm (scons u' s') (er B'))) :
  eqty k (subst_etm s (er (pi m A B))) (subst_etm s' (er (pi m' A' B'))).
Proof.
  rewrite !er_pi_sub; apply eqty_pi; [exact HA |].
  intros u u' Hu; eapply eqty_exp;
    [apply (reds_lam_app (er B) s u) | apply (reds_lam_app (er B') s' u') | apply HB, Hu].
Qed.

Lemma sem_sig_eq (A B A' B' : tm) (k m m' : nat) (s s' : nat -> etm)
  (HA : eqty k (subst_etm s (er A)) (subst_etm s' (er A')))
  (HB : forall u u', Rel (subst_etm s (er A)) u u' ->
        eqty k (subst_etm (scons u s) (er B)) (subst_etm (scons u' s') (er B'))) :
  eqty k (subst_etm s (er (sig_ m A B))) (subst_etm s' (er (sig_ m' A' B'))).
Proof.
  cbn [er]; apply eqty_sig; [exact HA |].
  intros u u' Hu; eapply eqty_exp;
    [apply (reds_lam_app (er B) s u) | apply (reds_lam_app (er B') s' u') | apply HB, Hu].
Qed.

Lemma sem_w_eq (A B A' B' : tm) (k m m' : nat) (s s' : nat -> etm)
  (HA : eqty k (subst_etm s (er A)) (subst_etm s' (er A')))
  (HB : forall u u', Rel (subst_etm s (er A)) u u' ->
        eqty k (subst_etm (scons u s) (er B)) (subst_etm (scons u' s') (er B'))) :
  eqty k (subst_etm s (er (wt m A B))) (subst_etm s' (er (wt m' A' B'))).
Proof.
  rewrite !er_w_sub; apply eqty_w; [exact HA |].
  intros u u' Hu; eapply eqty_exp;
    [apply (reds_lam_app (er B) s u) | apply (reds_lam_app (er B') s' u') | apply HB, Hu].
Qed.

Lemma sem_lam (k : nat) (A B : tm) (t t' : etm) (s s' : nat -> etm)
  (HT : Good_ty (subst_etm s (er (pi k A B))))
  (H : forall u u', Rel (subst_etm s (er A)) u u' ->
       Rel (subst_etm (scons u s) (er B))
           (subst_etm (scons u s) t) (subst_etm (scons u' s') t')) :
  Rel (subst_etm s (er (pi k A B))) (subst_etm s (elam t)) (subst_etm s' (elam t')).
Proof.
  eapply Rel_pi_intro; [exact HT | apply eval_whnf; left; apply v_pi |].
  intros u u' Hu.
  eapply Rel_exp_ty; [apply (reds_lam_app (er B) s u) |].
  eapply Rel_exp; [apply (reds_lam_app t s u) | apply (reds_lam_app t' s' u') |].
  apply H, Hu.
Qed.

Lemma sem_app (k : nat) (A B : tm) (f g u u' : etm) (s : nat -> etm)
  (Hf : Rel (subst_etm s (er (pi k A B))) f g)
  (Hu : Rel (subst_etm s (er A)) u u') :
  Rel (subst_etm (scons u s) (er B)) (eapp f u) (eapp g u').
Proof.
  pose proof (Rel_pi_elim _ _ _ _ _ (eval_whnf _ (or_introl (v_pi _ _))) Hf _ _ Hu) as H.
  apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) s u)) in H; exact H.
Qed.

Lemma sem_pair (k : nat) (A B : tm) (t t' u u' : etm) (s : nat -> etm)
  (HT : Good_ty (subst_etm s (er (sig_ k A B))))
  (H1 : Rel (subst_etm s (er A)) t t')
  (H2 : Rel (subst_etm (scons t s) (er B)) u u') :
  Rel (subst_etm s (er (sig_ k A B))) (epair t u) (epair t' u').
Proof.
  assert (Hev : eval (subst_etm s (er (sig_ k A B)))
                     (esig (subst_etm s (er A)) (elam (subst_etm (up_etm s) (er B)))))
    by (apply eval_whnf; left; apply v_sig).
  assert (Hft : Rel (subst_etm s (er A)) (efst (epair t u)) t)
    by (eapply Rel_exp; [apply reds_fst_pair | apply reds_refl | apply (Rel_refl_l _ _ _ H1)]).
  eapply Rel_sig_intro; [exact HT | exact Hev | |].
  - eapply Rel_exp; [apply reds_fst_pair | apply reds_fst_pair | exact H1].
  - eapply Rel_exp_ty; [apply (reds_lam_app (er B) s (efst (epair t u))) |].
    destruct (Rel_sig_cod _ _ _ _ _ HT Hev Hft) as [n Hn].
    assert (Hn' : eqty n (subst_etm (scons (efst (epair t u)) s) (er B))
                         (subst_etm (scons t s) (er B)))
      by (eapply eqty_red; [exact Hn | apply (reds_lam_app (er B) s (efst (epair t u)))
                           | apply (reds_lam_app (er B) s t)]).
    eapply Rel_cast; [apply eqty_sym; exact Hn' |].
    eapply Rel_exp; [apply reds_snd_pair | apply reds_snd_pair | exact H2].
Qed.

(* ------------------------------------------------------------------ *)
(* Pi-shaped realisers.  Two shapes occur in the W rules: a branching  *)
(* function, whose codomain is the tree type and therefore a shifted   *)
(* constant, and an induction hypothesis, whose codomain is the motive *)
(* at the subtree and is handed over with the reduction that opens it. *)
(* ------------------------------------------------------------------ *)

Lemma reds_const_cod (T u : etm) : reds (eapp (elam (ren_etm ↑ T)) u) T.
Proof.
  eapply reds_step; [apply red_beta |].
  rewrite subst_sub1_shift_etm; apply reds_refl.
Qed.

Lemma eqty_cfun n (Bf T : etm) : eqty n Bf Bf -> eqty n T T ->
  eqty n (epi Bf (elam (ren_etm ↑ T))) (epi Bf (elam (ren_etm ↑ T))).
Proof.
  intros HB HT; apply eqty_pi; [exact HB |].
  intros u u' Hu; eapply eqty_exp;
    [apply reds_const_cod | apply reds_const_cod | exact HT].
Qed.

Lemma Rel_cfun_intro (Bf T f f' : etm) :
  Good_ty (epi Bf (elam (ren_etm ↑ T))) ->
  (forall u u', Rel Bf u u' -> Rel T (eapp f u) (eapp f' u')) ->
  Rel (epi Bf (elam (ren_etm ↑ T))) f f'.
Proof.
  intros HG Hf; eapply Rel_pi_intro; [exact HG | apply eval_whnf; left; apply v_pi |].
  intros u u' Hu; eapply Rel_exp_ty; [apply reds_const_cod | apply Hf, Hu].
Qed.

Lemma Rel_cfun_elim (Bf T f f' : etm) :
  Rel (epi Bf (elam (ren_etm ↑ T))) f f' ->
  forall u u', Rel Bf u u' -> Rel T (eapp f u) (eapp f' u').
Proof.
  intros Hf u u' Hu.
  pose proof (Rel_pi_elim _ _ _ _ _ (eval_whnf _ (or_introl (v_pi _ _))) Hf u u' Hu) as H.
  eapply Rel_red_ty; [apply reds_const_cod | exact H].
Qed.

Lemma eqty_dfun n (Bf Y : etm) (Cy : etm -> etm) :
  eqty n Bf Bf -> (forall u, reds (eapp (elam Y) u) (Cy u)) ->
  (forall u u', Rel Bf u u' -> eqty n (Cy u) (Cy u')) ->
  eqty n (epi Bf (elam Y)) (epi Bf (elam Y)).
Proof.
  intros HB HY HC; apply eqty_pi; [exact HB |].
  intros u u' Hu; eapply eqty_exp; [apply HY | apply HY | apply HC, Hu].
Qed.

Lemma Rel_dfun_intro (Bf Y : etm) (Cy : etm -> etm) (y y' : etm) :
  Good_ty (epi Bf (elam Y)) -> (forall u, reds (eapp (elam Y) u) (Cy u)) ->
  (forall u u', Rel Bf u u' -> Rel (Cy u) (eapp y u) (eapp y' u')) ->
  Rel (epi Bf (elam Y)) y y'.
Proof.
  intros HG HY Hy; eapply Rel_pi_intro; [exact HG | apply eval_whnf; left; apply v_pi |].
  intros u u' Hu; eapply Rel_exp_ty; [apply HY | apply Hy, Hu].
Qed.

(* ------------------------------------------------------------------ *)
(* W: the constructor, the step, and the recursor.                     *)
(* ------------------------------------------------------------------ *)

Lemma sem_sup (k : nat) (A B : tm) (a a' f f' : etm) (s : nat -> etm)
  (HT : Good_ty (subst_etm s (er (wt k A B))))
  (H1 : Rel (subst_etm s (er A)) a a')
  (H2 : forall u u', Rel (subst_etm (scons a s) (er B)) u u' ->
        Rel (subst_etm s (er (wt k A B))) (eapp f u) (eapp f' u')) :
  Rel (subst_etm s (er (wt k A B))) (esup a f) (esup a' f').
Proof.
  eapply Rel_w_intro;
    [exact HT
    | rewrite er_w_sub; apply eval_whnf; left; apply v_w
    | exact H1 |].
  intros u u' Hu; apply H2.
  eapply Rel_red_ty; [apply (reds_lam_app (er B) s a) | exact Hu].
Qed.

(* the branching function of a sup, whose type the rule states as a Pi *)
Lemma sem_wsup_fun (k : nat) (A B a : tm) (g : nat -> etm) (f f' : etm)
  (Hf : Rel (subst_etm g (er (pi k (B [a..]) ((wt k A B) ⟨↑⟩)))) f f') :
  forall u u', Rel (subst_etm (scons (subst_etm g (er a)) g) (er B)) u u' ->
    Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f' u').
Proof.
  rewrite er_wsup_fun_sub in Hf; apply (Rel_cfun_elim _ _ _ _ Hf).
Qed.

(* the two data the step's context binds, built from their semantic content *)
Lemma sem_wbr (k : nat) (A B : tm) (g : nat -> etm) (a f f' : etm)
  (HB : eqty k (subst_etm (scons a g) (er B)) (subst_etm (scons a g) (er B)))
  (HW : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B))))
  (Hf : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
        Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f' u')) :
  Rel (subst_etm (scons a g) (er (wbr k A B))) f f'.
Proof.
  rewrite er_wbr_sub; apply Rel_cfun_intro; [| exact Hf].
  apply (gt_of k), eqty_cfun; [exact HB | exact HW].
Qed.

Lemma sem_wih (n k : nat) (A B C : tm) (g : nat -> etm) (a f y y' : etm)
  (HB : eqty n (subst_etm (scons a g) (er B)) (subst_etm (scons a g) (er B)))
  (HC : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
        eqty n (subst_etm (scons (eapp f u) g) (er C))
               (subst_etm (scons (eapp f u') g) (er C)))
  (Hy : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
        Rel (subst_etm (scons (eapp f u) g) (er C)) (eapp y u) (eapp y' u')) :
  Rel (subst_etm (scons f (scons a g)) (er (wih n k A B C))) y y'.
Proof.
  destruct (er_wih_sub n k A B C g a f) as [Y [E HY]]; rewrite E.
  eapply (Rel_dfun_intro _ Y (fun u => subst_etm (scons (eapp f u) g) (er C)));
    [| exact HY | exact Hy].
  apply (gt_of n); eapply eqty_dfun; [exact HB | exact HY | exact HC].
Qed.

(* the step, at a related triple of arguments.  As at natrec the step carries
   its own binders, so the induction hypothesis is about its BODY; here the
   body's type is read off by er_wsup_ty. *)
Lemma sem_wstep_body (G : ctx) (n k : nat) (A B C s s' : tm) (g g' : nat -> etm)
  (HS : SubstRel G g g')
  (Hs : forall sigma sigma',
        SubstRel (wih n k A B C :: wbr k A B :: A :: G) sigma sigma' ->
        Rel (subst_etm sigma (er (wsup_ty k A B C)))
            (subst_etm sigma (er s)) (subst_etm sigma' (er s'))) :
  forall a a' f f' y y',
    Rel (subst_etm g (er A)) a a' ->
    Rel (subst_etm (scons a g) (er (wbr k A B))) f f' ->
    Rel (subst_etm (scons f (scons a g)) (er (wih n k A B C))) y y' ->
    Rel (subst_etm (scons (esup a f) g) (er C))
        (subst_etm (scons y (scons f (scons a g))) (er s))
        (subst_etm (scons y' (scons f' (scons a' g'))) (er s')).
Proof.
  intros a a' f f' y y' Ha Hf Hy.
  pose proof (Hs (scons y (scons f (scons a g))) (scons y' (scons f' (scons a' g')))
    (SubstRel_cons _ _ _ _ _ _
      (SubstRel_cons _ _ _ _ _ _ (SubstRel_cons _ _ _ _ _ _ HS Ha) Hf) Hy)) as H.
  rewrite er_wsup_ty in H; exact H.
Qed.

Lemma sem_wstep (G : ctx) (n k : nat) (A B C s s' : tm) (g g' : nat -> etm)
  (HS : SubstRel G g g')
  (Hs : forall sigma sigma',
        SubstRel (wih n k A B C :: wbr k A B :: A :: G) sigma sigma' ->
        Rel (subst_etm sigma (er (wsup_ty k A B C)))
            (subst_etm sigma (er s)) (subst_etm sigma' (er s'))) :
  forall a a' f f' y y',
    Rel (subst_etm g (er A)) a a' ->
    Rel (subst_etm (scons a g) (er (wbr k A B))) f f' ->
    Rel (subst_etm (scons f (scons a g)) (er (wih n k A B C))) y y' ->
    Rel (subst_etm (scons (esup a f) g) (er C))
        (eapp (eapp (eapp (subst_etm g (elam (elam (elam (er s))))) a) f) y)
        (eapp (eapp (eapp (subst_etm g' (elam (elam (elam (er s'))))) a') f') y').
Proof.
  intros a a' f f' y y' Ha Hf Hy.
  eapply Rel_exp; [apply reds_lam3_app | apply reds_lam3_app |].
  apply (sem_wstep_body G n k A B C s s' g g' HS Hs); assumption.
Qed.

(* the two reductions the erased recursor performs at a tree *)
Lemma reds_wrec_sup (S w a f : etm) : eval w (esup a f) ->
  reds (ewrec S w)
       (eapp (eapp (eapp S a) f)
             (elam (ewrec (ren_etm ↑ S) (eapp (ren_etm ↑ f) (var_etm 0))))).
Proof.
  intros [Hr _]; eapply reds_trans; [apply reds_wrec, Hr |].
  eapply reds_step; [apply red_wrec | apply reds_refl].
Qed.

Lemma reds_wih_beta (S f u : etm) :
  reds (eapp (elam (ewrec (ren_etm ↑ S) (eapp (ren_etm ↑ f) (var_etm 0)))) u)
       (ewrec S (eapp f u)).
Proof.
  eapply reds_step; [apply red_beta |].
  rewrite sub_wrec, sub_app, !subst_sub1_shift_etm; apply reds_refl.
Qed.

(* wrec.  As at natrec the induction is on the PER of the scrutinee -- here
   WPer, through the Rel-level principle Rel_w_elim -- and the stuck case is
   what makes the recursor total on junk.  The sup case is three reductions
   and a move of the motive from the scrutinee to its whnf. *)
Lemma sem_wrec (k m : nat) (A B C : tm) (g : nat -> etm) (S S' : etm)
  (HT : Good_ty (subst_etm g (er (wt k A B))))
  (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
        eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
  (Hstep : forall a a' f f' y y',
      Rel (subst_etm g (er A)) a a' ->
      (forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
         Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f' u')) ->
      (forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
         Rel (subst_etm (scons (eapp f u) g) (er C)) (eapp y u) (eapp y' u')) ->
      Rel (subst_etm (scons (esup a f) g) (er C))
          (eapp (eapp (eapp S a) f) y) (eapp (eapp (eapp S' a') f') y')) :
  forall w w', Rel (subst_etm g (er (wt k A B))) w w' ->
    Rel (subst_etm (scons w g) (er C)) (ewrec S w) (ewrec S' w').
Proof.
  apply (Rel_w_elim (subst_etm g (er (wt k A B)))
           (subst_etm g (er A)) (elam (subst_etm (up_etm g) (er B)))
           (fun x y => Rel (subst_etm (scons x g) (er C)) (ewrec S x) (ewrec S' y)));
    [ exact HT | rewrite er_w_sub; apply eval_whnf; left; apply v_w | |].
  - (* sup *)
    intros w w' a a' f f' Hw Hw' Hww Ha Hbr IH.
    assert (Hsup : Rel (subst_etm g (er (wt k A B))) (esup a f) w).
    { eapply Rel_exp; [apply reds_refl | apply (proj1 Hw) |].
      eapply Rel_red;
        [apply (proj1 Hw) | apply (proj1 Hw) | apply (Rel_refl_l _ _ _ Hww)]. }
    eapply Rel_cast; [apply HC; exact Hsup |].
    eapply Rel_exp;
      [apply (reds_wrec_sup _ _ _ _ Hw) | apply (reds_wrec_sup _ _ _ _ Hw') |].
    apply Hstep; [exact Ha | |].
    + intros u u' Hu; apply Hbr.
      eapply Rel_exp_ty; [apply (reds_lam_app (er B) g a) | exact Hu].
    + intros u u' Hu.
      eapply Rel_exp; [apply reds_wih_beta | apply reds_wih_beta |].
      apply IH; eapply Rel_exp_ty; [apply (reds_lam_app (er B) g a) | exact Hu].
  - (* stuck *)
    intros w w' Hww Hs Hs'.
    apply Rel_stuck;
      [apply (gt_of m), HC, (Rel_refl_l _ _ _ Hww)
      | apply stuckv_wrec; exact Hs | apply stuckv_wrec; exact Hs'].
Qed.

(* The step of sem_wrec, assembled from the fundamental lemma's induction
   hypothesis for the step term.  Everything here is the translation between
   the CONSUMED form the recursor hands out -- a label, a branch-indexed
   family of subtrees, and a branch-indexed family of recursive results --
   and the three TYPED data the step's context binds.  The levels are where
   the heterogeneous Pi earns its keep: the branching function's type sits at
   the annotation k, the induction hypothesis's at n, and the components come
   from j and m. *)
Lemma sem_wrec_step (G : ctx) (k j m n : nat) (A B C s s' : tm) (g g' : nat -> etm)
  (Hjk : j <= k) (Hjn : j <= n) (Hmn : m <= n)
  (HS : SubstRel G g g')
  (HBg : forall u u', Rel (subst_etm g (er A)) u u' ->
         eqty j (subst_etm (scons u g) (er B)) (subst_etm (scons u' g) (er B)))
  (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B))))
  (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
        eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
  (Hs : forall sigma sigma',
        SubstRel (wih n k A B C :: wbr k A B :: A :: G) sigma sigma' ->
        Rel (subst_etm sigma (er (wsup_ty k A B C)))
            (subst_etm sigma (er s)) (subst_etm sigma' (er s'))) :
  forall a a' f f' y y',
    Rel (subst_etm g (er A)) a a' ->
    (forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
       Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f' u')) ->
    (forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
       Rel (subst_etm (scons (eapp f u) g) (er C)) (eapp y u) (eapp y' u')) ->
    Rel (subst_etm (scons (esup a f) g) (er C))
        (eapp (eapp (eapp (subst_etm g (elam (elam (elam (er s))))) a) f) y)
        (eapp (eapp (eapp (subst_etm g' (elam (elam (elam (er s'))))) a') f') y').
Proof.
  intros a a' f f' y y' Ha Hf Hy.
  assert (HBa : eqty j (subst_etm (scons a g) (er B)) (subst_etm (scons a g) (er B)))
    by (apply HBg, (Rel_refl_l _ _ _ Ha)).
  (* the branches at a pair of related indices, on the SAME function: what the
     motive's functionality needs, and what the PER of the branches gives up
     only through symmetry and transitivity *)
  assert (Hff : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
                Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f u')).
  { intros u u' Hu; eapply Rel_trans; [apply (Hf u u' Hu) |].
    apply Rel_sym, (Hf u' u'), (Rel_refl_l _ _ _ (Rel_sym _ _ _ Hu)). }
  apply (sem_wstep G n k A B C s s' g g' HS Hs);
    [ exact Ha
    | apply (sem_wbr k A B g a f f');
        [ apply (eqty_cumul j k _ _ Hjk), HBa | exact HWk | exact Hf ]
    | apply (sem_wih n k A B C g a f y y');
        [ apply (eqty_cumul j n _ _ Hjn), HBa
        | intros u u' Hu; apply (eqty_cumul m n _ _ Hmn), HC, Hff, Hu
        | exact Hy ] ].
Qed.

(* c_wrec_sup's whole content: the step at the canonical triple the ERASED
   recursor's computation rule produces -- the label, the branching function,
   and the function sending a branch to the recursive result there.  Both
   directions of the conversion reduce to this one relation, the left-hand
   side by the recursor's computation rule and the right-hand side by the
   three beta-steps that open the step's binders. *)
Lemma sem_wrec_sup (G : ctx) (k j m n : nat) (A B C s : tm) (g g' : nat -> etm)
  (Hjk : j <= k) (Hjn : j <= n) (Hmn : m <= n)
  (HS : SubstRel G g g')
  (HBg : forall u u', Rel (subst_etm g (er A)) u u' ->
         eqty j (subst_etm (scons u g) (er B)) (subst_etm (scons u' g) (er B)))
  (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B))))
  (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
        eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
  (Hs : forall sigma sigma',
        SubstRel (wih n k A B C :: wbr k A B :: A :: G) sigma sigma' ->
        Rel (subst_etm sigma (er (wsup_ty k A B C)))
            (subst_etm sigma (er s)) (subst_etm sigma' (er s)))
  (a a' f f' : etm)
  (Ha : Rel (subst_etm g (er A)) a a')
  (Hf : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
        Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f' u')) :
  Rel (subst_etm (scons (esup a f) g) (er C))
      (subst_etm (scons (elam (ewrec (ren_etm ↑ (subst_etm g (elam (elam (elam (er s))))))
                                     (eapp (ren_etm ↑ f) (var_etm 0))))
                 (scons f (scons a g))) (er s))
      (subst_etm (scons (elam (ewrec (ren_etm ↑ (subst_etm g' (elam (elam (elam (er s))))))
                                     (eapp (ren_etm ↑ f') (var_etm 0))))
                 (scons f' (scons a' g'))) (er s)).
Proof.
  assert (HBa : eqty j (subst_etm (scons a g) (er B)) (subst_etm (scons a g) (er B)))
    by (apply HBg, (Rel_refl_l _ _ _ Ha)).
  assert (Hff : forall u u', Rel (subst_etm (scons a g) (er B)) u u' ->
                Rel (subst_etm g (er (wt k A B))) (eapp f u) (eapp f u')).
  { intros u u' Hu; eapply Rel_trans; [apply (Hf u u' Hu) |].
    apply Rel_sym, (Hf u' u'), (Rel_refl_l _ _ _ (Rel_sym _ _ _ Hu)). }
  apply (sem_wstep_body G n k A B C s s g g' HS Hs);
    [ exact Ha
    | apply (sem_wbr k A B g a f f');
        [ apply (eqty_cumul j k _ _ Hjk), HBa | exact HWk | exact Hf ] |].
  (* the induction hypothesis: one recursive call per branch, which is where
     sem_wrec is used INSIDE the computation rule *)
  apply (sem_wih n k A B C g a f);
    [ apply (eqty_cumul j n _ _ Hjn), HBa
    | intros u u' Hu; apply (eqty_cumul m n _ _ Hmn), HC, Hff, Hu |].
  intros u u' Hu.
  eapply Rel_exp; [apply reds_wih_beta | apply reds_wih_beta |].
  apply (sem_wrec k m A B C g _ _ (gt_of k _ HWk) HC
           (sem_wrec_step G k j m n A B C s s g g' Hjk Hjn Hmn HS HBg HWk HC Hs)).
  apply Hf, Hu.
Qed.

(* ------------------------------------------------------------------ *)
(* The two semantic judgements, and their type- and Prop-level        *)
(* projections (the other two clauses of Theorem 6.7).                *)
(* ------------------------------------------------------------------ *)

Definition SEl (G : ctx) (t A : tm) : Prop :=
  forall s s', SubstRel G s s' ->
    Rel (subst_etm s (er A)) (subst_etm s (er t)) (subst_etm s' (er t)).

Definition SCv (G : ctx) (t u A : tm) : Prop :=
  forall s s', SubstRel G s s' ->
    Rel (subst_etm s (er A)) (subst_etm s (er t)) (subst_etm s' (er u)) /\
    Rel (subst_etm s (er A)) (subst_etm s (er u)) (subst_etm s' (er t)).

Lemma SEl_U G A k : SEl G A (UU k) -> forall s s', SubstRel G s s' ->
  eqty k (subst_etm s (er A)) (subst_etm s' (er A)).
Proof.
  intros H s s' HS; eapply Rel_univ_elim;
    [apply eval_whnf; left; apply v_univ | apply H, HS].
Qed.

Lemma SEl_P G p j : SEl G p (prop j) -> forall s s', SubstRel G s s' ->
  PR (subst_etm s (er p)) (subst_etm s' (er p)).
Proof.
  intros H s s' HS; eapply Rel_prop_elim;
    [apply eval_whnf; left; apply v_prop | apply H, HS].
Qed.

Lemma SCv_U G A B k : SCv G A B (UU k) -> forall s s', SubstRel G s s' ->
  eqty k (subst_etm s (er A)) (subst_etm s' (er B)) /\
  eqty k (subst_etm s (er B)) (subst_etm s' (er A)).
Proof.
  intros H s s' HS; destruct (H s s' HS) as [H1 H2]; split;
    (eapply Rel_univ_elim; [apply eval_whnf; left; apply v_univ | eassumption]).
Qed.

Lemma SCv_P G p q j : SCv G p q (prop j) -> forall s s', SubstRel G s s' ->
  PR (subst_etm s (er p)) (subst_etm s' (er q)) /\
  PR (subst_etm s (er q)) (subst_etm s' (er p)).
Proof.
  intros H s s' HS; destruct (H s s' HS) as [H1 H2]; split;
    (eapply Rel_prop_elim; [apply eval_whnf; left; apply v_prop | eassumption]).
Qed.

(* Evaluation of whnfs, as one-liners: every clause below needs one. *)
Lemma ev_nat : eval enat enat.
Proof. apply eval_whnf; left; apply v_nat. Qed.
Lemma ev_prop : eval eprop eprop.
Proof. apply eval_whnf; left; apply v_prop. Qed.
Lemma ev_false : eval efalse efalse.
Proof. apply eval_whnf; left; apply v_false. Qed.
Lemma ev_zero : eval ezero ezero.
Proof. apply eval_whnf; left; apply v_zero. Qed.
Lemma ev_univ m : eval (euniv m) (euniv m).
Proof. apply eval_whnf; left; apply v_univ. Qed.
Lemma ev_succ X : eval (esucc X) (esucc X).
Proof. apply eval_whnf; left; apply v_succ. Qed.
Lemma ev_prf X : eval (eprf X) (eprf X).
Proof. apply eval_whnf; left; apply v_prf. Qed.
Lemma ev_pi X Y : eval (epi X Y) (epi X Y).
Proof. apply eval_whnf; left; apply v_pi. Qed.
Lemma ev_sig X Y : eval (esig X Y) (esig X Y).
Proof. apply eval_whnf; left; apply v_sig. Qed.
Lemma ev_w X Y : eval (ew X Y) (ew X Y).
Proof. apply eval_whnf; left; apply v_w. Qed.
Lemma ev_sup X Y : eval (esup X Y) (esup X Y).
Proof. apply eval_whnf; left; apply v_sup. Qed.
Lemma ev_all X Y : eval (eall X Y) (eall X Y).
Proof. apply eval_whnf; left; apply v_all. Qed.
Lemma ev_eqty X Y Z : eval (eeqty X Y Z) (eeqty X Y Z).
Proof. apply eval_whnf; left; apply v_eqty. Qed.

(* The erasure of an eta-expansion, pushed under a substitution. *)
Lemma er_eta (k : nat) (A B f : tm) (g : nat -> etm) :
  subst_etm g (er (lam k A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))))
  = elam (eapp (ren_etm ↑ (subst_etm g (er f))) (var_etm 0)).
Proof. cbn [er]; rewrite er_ren, sub_lam, sub_app, sub_var0, sub_shift_up; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Theorem 6.7.  Induction on the three judgements at once; the       *)
(* motive for context well-formedness is trivial, because every use   *)
(* of a variable goes through SubstRel_lookup instead.                *)
(* ------------------------------------------------------------------ *)

Scheme wfc_mind := Minimality for wfc Sort Prop
  with ty_mind := Minimality for ty Sort Prop
  with cv_mind := Minimality for cv Sort Prop.

Combined Scheme wty_mind from wfc_mind, ty_mind, cv_mind.

Theorem fundamental :
  (forall G, wfc G -> True) /\
  (forall G t A, ty G t A -> SEl G t A) /\
  (forall G t u A, cv G t u A -> SCv G t u A).
Proof.
  apply wty_mind.
  (* --- wfc --- *)
  - exact I.
  - intros; exact I.
  (* --- t_var --- *)
  - intros G i A _ _ Hl g g' HS. exact (SubstRel_lookup G g g' HS i A Hl).
  (* --- t_conv --- *)
  - intros G t A B k _ IHt _ IHA _ IHB _ IHc g g' HS.
    eapply Rel_cast;
      [apply (proj1 (SCv_U _ _ _ _ IHc g g (SubstRel_refl _ _ _ HS))) | apply IHt, HS].
  (* --- t_univ --- *)
  - intros G k j Hjk _ _ g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ | apply eqty_univ; lia].
  (* --- t_up --- *)
  - intros G j A _ IHA g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
    apply (eqty_cumul j (S j)); [lia | apply (SEl_U _ _ _ IHA _ _ HS)].
  (* --- t_up_tm: the lift is invisible on realisers, so the term's value and
         its type's value are literally those of t and A --- *)
  - intros G j A t _ IHA _ IHt g g' HS. apply IHt, HS.
  (* --- t_pi --- *)
  - intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
    apply sem_pi_eq;
      [ apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HS) |].
    intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
    apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu).
  (* --- t_lam --- *)
  - intros G k i j A B t Hik Hjk _ IHA _ IHB _ IHt g g' HS.
    apply sem_lam.
    + apply (gt_of k), sem_pi_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hu).
    + intros u u' Hu; apply IHt, (SubstRel_cons _ _ _ _ _ _ HS Hu).
  (* --- t_app --- *)
  - intros G k i j A B f u Hik Hjk _ IHA _ IHB _ IHf _ IHu g g' HS.
    rewrite er_sub1; apply (sem_app k A B); [apply IHf, HS | apply IHu, HS].
  (* --- t_sig --- *)
  - intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
    apply sem_sig_eq;
      [ apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HS) |].
    intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
    apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu).
  (* --- t_pair --- *)
  - intros G k i j A B t u Hik Hjk _ IHA _ IHB _ IHt _ IHu g g' HS.
    apply (sem_pair k A B).
    + apply (gt_of k), sem_sig_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros v v' Hv; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hv).
    + apply IHt, HS.
    + pose proof (IHu g g' HS) as H; rewrite er_sub1 in H; exact H.
  (* --- t_fst --- *)
  - intros G k i j A B p Hik Hjk _ IHA _ IHB _ IHp g g' HS.
    exact (proj1 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) (IHp g g' HS))).
  (* --- t_snd --- *)
  - intros G k i j A B p Hik Hjk _ IHA _ IHB _ IHp g g' HS.
    rewrite er_sub1.
    pose proof (proj2 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) (IHp g g' HS))) as H.
    apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) g _)) in H; exact H.
  (* --- t_w --- *)
  - intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
    apply sem_w_eq;
      [ apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HS) |].
    intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
    apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu).
  (* --- t_sup: the label is related in A and the branching function is a
         function into the tree type, which is exactly what WPer asks for --- *)
  - intros G k i j A B a f Hik Hjk _ IHA _ IHB _ IHa _ IHf g g' HS.
    assert (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B)))).
    { apply sem_w_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hu). }
    rewrite !er_sup_sub.
    apply (sem_sup k A B); [apply (gt_of k), HWk | apply IHa, HS |].
    apply (sem_wsup_fun k A B a g), IHf, HS.
  (* --- t_wrec: the induction is on the PER of the scrutinee (sem_wrec), and
         the step is assembled by sem_wrec_step --- *)
  - intros G k i j m n A B C s w Hik Hjk Hjn Hmn _ _ IHA _ IHB _ IHC _ _ _ _ _ IHs
      _ IHw g g' HS.
    pose proof (SubstRel_refl _ _ _ HS) as HSr.
    assert (HBg : forall u u', Rel (subst_etm g (er A)) u u' ->
                  eqty j (subst_etm (scons u g) (er B)) (subst_etm (scons u' g) (er B)))
      by (intros u u' Hu; apply (SEl_U _ _ _ IHB),
            (SubstRel_cons _ _ _ _ _ _ HSr Hu)).
    assert (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B)))).
    { apply sem_w_eq;
        [apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HSr) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), HBg, Hu. }
    assert (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
                 eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
      by (intros x y Hxy; apply (SEl_U _ _ _ IHC),
            (SubstRel_cons _ _ _ _ _ _ HSr Hxy)).
    rewrite er_sub1, !er_wrec_sub.
    apply (sem_wrec k m A B C g _ _ (gt_of k _ HWk) HC
             (sem_wrec_step G k j m n A B C s s g g' Hjk Hjn Hmn HS HBg HWk HC IHs)).
    apply IHw, HS.
  (* --- t_nat --- *)
  - intros G k _ _ g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ | apply eqty_nat].
  (* --- t_zero --- *)
  - intros G k _ _ g g' HS.
    apply Rel_nat_intro; [apply gt_nat | apply ev_nat | apply np_zero; apply ev_zero].
  (* --- t_succ --- *)
  - intros G k n _ IHn g g' HS.
    apply Rel_nat_intro; [apply gt_nat | apply ev_nat |].
    eapply np_succ; [apply ev_succ | apply ev_succ |].
    eapply Rel_nat_elim; [apply ev_nat | apply IHn, HS].
  (* --- t_natrec --- *)
  - intros G C z sc n k j _ IHC _ IHz _ IHs _ IHn g g' HS.
    assert (HCe : forall m m', NatPer m m' ->
              eqty k (subst_etm (scons m g) (er C)) (subst_etm (scons m' g) (er C))).
    { intros m m' Hm; apply (SEl_U _ _ _ IHC).
      apply (SubstRel_cons _ (nat_ j) _ _ _ _ (SubstRel_refl _ _ _ HS)).
      apply Rel_nat_intro; [apply gt_nat | apply ev_nat | exact Hm]. }
    rewrite er_sub1.
    apply (sem_natrec C g k _ _ _ _ HCe).
    + pose proof (IHz g g' HS) as H; rewrite er_sub1 in H; exact H.
    + apply (sem_step G j C sc sc g g' HS IHs).
    + eapply Rel_nat_elim; [apply ev_nat | apply IHn, HS].
  (* --- t_prop --- *)
  - intros G k _ _ g g' HS.
    eapply Rel_univ_intro; [apply gt_univ | apply ev_univ | apply eqty_prop].
  (* --- t_prf --- *)
  - intros G k j p Hjk _ IHp g g' HS.
    eapply Rel_univ_intro;
      [apply gt_univ | apply ev_univ | apply eqty_prf, (SEl_P _ _ _ IHp _ _ HS)].
  (* --- t_all --- *)
  - intros G A p j k _ IHA _ IHp g g' HS.
    apply Rel_prop_intro; [apply gt_prop | apply ev_prop |].
    eapply PR_all; apply ev_all.
  (* --- t_all_intro --- *)
  - intros G A p t j k _ IHA _ IHp _ IHt g g' HS.
    eapply Rel_prf_intro; [| apply ev_prf].
    apply (gt_of 0), eqty_prf; eapply PR_all; apply ev_all.
  (* --- t_all_elim --- *)
  - intros G A p f u j k _ IHA _ IHp _ IHf _ IHu g g' HS.
    rewrite er_sub1_prf.
    eapply Rel_prf_intro; [| apply ev_prf].
    apply (gt_of 0), eqty_prf.
    apply (SEl_P _ _ _ IHp), (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS)).
    apply (Rel_refl_l _ _ _ (IHu g g' HS)).
  (* --- t_false --- *)
  - intros G k _ _ g g' HS.
    apply Rel_prop_intro; [apply gt_prop | apply ev_prop | apply PR_false; apply ev_false].
  (* --- t_absurd --- *)
  - intros G T e k j _ IHT _ IHe g g' HS.
    apply Rel_stuck;
      [apply (gt_of k), (SEl_U _ _ _ IHT _ _ (SubstRel_refl _ _ _ HS))
      | apply stuckv_err | apply stuckv_err].
  (* --- c_refl --- *)
  - intros G t A _ IHt g g' HS. split; apply IHt, HS.
  (* --- c_sym --- *)
  - intros G t u A _ IH g g' HS.
    destruct (IH g g' HS) as [H1 H2]; split; [exact H2 | exact H1].
  (* --- c_trans --- *)
  - intros G t u v A _ IH1 _ IH2 g g' HS.
    destruct (IH1 g g (SubstRel_refl _ _ _ HS)) as [A1 _].
    destruct (IH1 g g' HS) as [_ B2].
    destruct (IH2 g g (SubstRel_refl _ _ _ HS)) as [_ C2].
    destruct (IH2 g g' HS) as [D1 _].
    split; [eapply Rel_trans; [exact A1 | exact D1]
           | eapply Rel_trans; [exact C2 | exact B2]].
  (* --- c_conv --- *)
  - intros G t u A B k _ IHc _ IHA _ IHB _ IHAB g g' HS.
    destruct (IHc g g' HS) as [H1 H2].
    pose proof (proj1 (SCv_U _ _ _ _ IHAB g g (SubstRel_refl _ _ _ HS))) as E.
    split; eapply Rel_cast; [exact E | exact H1 | exact E | exact H2].
  (* --- c_prf_irr --- *)
  - intros G j p e e' _ IHp _ _ _ _ g g' HS.
    assert (HG : Good_ty (subst_etm g (er (prf j p))))
      by (apply (gt_of 0), eqty_prf, (SEl_P _ _ _ IHp _ _ (SubstRel_refl _ _ _ HS))).
    split; eapply Rel_prf_intro; [exact HG | apply ev_prf | exact HG | apply ev_prf].
  (* --- c_up --- *)
  - intros G j A A' _ IHA _ IHA' _ IHc g g' HS.
    destruct (SCv_U _ _ _ _ IHc g g' HS) as [E1 E2]; split.
    + eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
      apply (eqty_cumul j (S j)); [lia | exact E1].
    + eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |].
      apply (eqty_cumul j (S j)); [lia | exact E2].
  (* --- c_up_tm --- *)
  - intros G j A t t' _ IHA _ IHt _ IHt' _ IHc g g' HS. exact (IHc g g' HS).
  (* --- the six lift computations: the two sides have the SAME erasure, so
         each is the formation case of the corresponding former, one level up,
         twice --- *)
  - (* c_up_univ *) intros G k j Hjk _ _ g g' HS.
    split; (eapply Rel_univ_intro;
            [apply gt_univ | apply ev_univ | apply eqty_univ; lia]).
  - (* c_up_nat *) intros G k _ _ g g' HS.
    split; (eapply Rel_univ_intro;
            [apply gt_univ | apply ev_univ | apply eqty_nat]).
  - (* c_up_prop *) intros G k _ _ g g' HS.
    split; (eapply Rel_univ_intro;
            [apply gt_univ | apply ev_univ | apply eqty_prop]).
  - (* c_up_prf *) intros G k j p Hjk _ IHp g g' HS.
    split; (eapply Rel_univ_intro;
            [apply gt_univ | apply ev_univ
            | apply eqty_prf, (SEl_P _ _ _ IHp _ _ HS)]).
  - (* c_up_pi *) intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    assert (HA : eqty (S k) (subst_etm g (er A)) (subst_etm g' (er A))) by
      (apply (eqty_cumul i (S k) _ _ (le_S _ _ Hik)), (SEl_U _ _ _ IHA _ _ HS)).
    assert (HB : forall u u', Rel (subst_etm g (er A)) u u' ->
                 eqty (S k) (subst_etm (scons u g) (er B))
                            (subst_etm (scons u' g') (er B))) by
      (intros u u' Hu; apply (eqty_cumul j (S k) _ _ (le_S _ _ Hjk));
       apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu)).
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + exact (sem_pi_eq A B A B (S k) k (S k) g g' HA HB).
    + exact (sem_pi_eq A B A B (S k) (S k) k g g' HA HB).
  - (* c_up_sig *) intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    assert (HA : eqty (S k) (subst_etm g (er A)) (subst_etm g' (er A))) by
      (apply (eqty_cumul i (S k) _ _ (le_S _ _ Hik)), (SEl_U _ _ _ IHA _ _ HS)).
    assert (HB : forall u u', Rel (subst_etm g (er A)) u u' ->
                 eqty (S k) (subst_etm (scons u g) (er B))
                            (subst_etm (scons u' g') (er B))) by
      (intros u u' Hu; apply (eqty_cumul j (S k) _ _ (le_S _ _ Hjk));
       apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu)).
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + exact (sem_sig_eq A B A B (S k) k (S k) g g' HA HB).
    + exact (sem_sig_eq A B A B (S k) (S k) k g g' HA HB).
  - (* c_up_w *) intros G k i j A B Hik Hjk _ IHA _ IHB g g' HS.
    assert (HA : eqty (S k) (subst_etm g (er A)) (subst_etm g' (er A))) by
      (apply (eqty_cumul i (S k) _ _ (le_S _ _ Hik)), (SEl_U _ _ _ IHA _ _ HS)).
    assert (HB : forall u u', Rel (subst_etm g (er A)) u u' ->
                 eqty (S k) (subst_etm (scons u g) (er B))
                            (subst_etm (scons u' g') (er B))) by
      (intros u u' Hu; apply (eqty_cumul j (S k) _ _ (le_S _ _ Hjk));
       apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HS Hu)).
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + exact (sem_w_eq A B A B (S k) k (S k) g g' HA HB).
    + exact (sem_w_eq A B A B (S k) (S k) k g g' HA HB).
  (* --- c_pi --- *)
  - intros G k i j A A' B B' Hik Hjk _ IHA _ IHB _ IHA' _ IHB' _ IHcA _ IHcB g g' HS.
    destruct (SCv_U _ _ _ _ IHcA g g' HS) as [EA1 EA2].
    destruct (SCv_U _ _ _ _ IHcA g g (SubstRel_refl _ _ _ HS)) as [_ EAr2].
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + apply sem_pi_eq; [apply (eqty_cumul i k _ _ Hik), EA1 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj1 (SCv_U _ _ _ _ IHcB _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu))).
    + apply sem_pi_eq; [apply (eqty_cumul i k _ _ Hik), EA2 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj2 (SCv_U _ _ _ _ IHcB _ _
        (SubstRel_cons _ _ _ _ _ _ HS (Rel_cast _ _ _ _ _ EAr2 Hu)))).
  (* --- c_lam --- *)
  - intros G k i j A A' B B' t t' Hik Hjk _ IHA _ IHB _ IHA' _ IHB' _ IHcA _ IHcB _ IHt _ IHt'
      _ IHct g g' HS.
    assert (HT : Good_ty (subst_etm g (er (pi k A B)))).
    { apply (gt_of k), sem_pi_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hu). }
    split; (apply sem_lam; [exact HT |]).
    + intros u u' Hu; apply (proj1 (IHct _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu))).
    + intros u u' Hu; apply (proj2 (IHct _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu))).
  (* --- c_app --- *)
  - intros G k i j A B f f' u u' Hik Hjk _ IHA _ IHB _ IHf _ IHf' _ IHcf _ IHu _ IHu' _ IHcu
      g g' HS.
    destruct (IHcf g g' HS) as [Hf1 Hf2].
    destruct (IHcu g g' HS) as [Hu1 Hu2].
    destruct (IHcu g g (SubstRel_refl _ _ _ HS)) as [_ Hur2].
    rewrite er_sub1; split.
    + apply (sem_app k A B); [exact Hf1 | exact Hu1].
    + eapply Rel_cast;
        [apply (SEl_U _ _ _ IHB _ _
           (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hur2)) |].
      apply (sem_app k A B); [exact Hf2 | exact Hu2].
  (* --- c_beta --- *)
  - intros G k i j A B t u Hik Hjk _ IHA _ IHB _ IHt _ IHu g g' HS.
    pose proof (IHt _ _ (SubstRel_cons _ _ _ _ _ _ HS (IHu g g' HS))) as H.
    rewrite !er_sub1; split.
    + eapply Rel_exp; [apply (reds_lam_app (er t) g _) | apply reds_refl | exact H].
    + eapply Rel_exp; [apply reds_refl | apply (reds_lam_app (er t) g' _) | exact H].
  (* --- c_eta --- *)
  - intros G k i j A B f Hik Hjk _ IHA _ IHB _ IHf g g' HS.
    assert (HT : Good_ty (subst_etm g (er (pi k A B)))).
    { apply (gt_of k), sem_pi_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hu). }
    split; rewrite er_eta; (eapply Rel_pi_intro; [exact HT | apply ev_pi |]);
      intros u u' Hu;
      (eapply Rel_exp_ty; [apply (reds_lam_app (er B) g u) |]).
    + eapply Rel_exp; [apply reds_eta | apply reds_refl |].
      apply (sem_app k A B); [apply IHf, HS | exact Hu].
    + eapply Rel_exp; [apply reds_refl | apply reds_eta |].
      apply (sem_app k A B); [apply IHf, HS | exact Hu].
  (* --- c_sig --- *)
  - intros G k i j A A' B B' Hik Hjk _ IHA _ IHB _ IHA' _ IHB' _ IHcA _ IHcB g g' HS.
    destruct (SCv_U _ _ _ _ IHcA g g' HS) as [EA1 EA2].
    destruct (SCv_U _ _ _ _ IHcA g g (SubstRel_refl _ _ _ HS)) as [_ EAr2].
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + apply sem_sig_eq; [apply (eqty_cumul i k _ _ Hik), EA1 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj1 (SCv_U _ _ _ _ IHcB _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu))).
    + apply sem_sig_eq; [apply (eqty_cumul i k _ _ Hik), EA2 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj2 (SCv_U _ _ _ _ IHcB _ _
        (SubstRel_cons _ _ _ _ _ _ HS (Rel_cast _ _ _ _ _ EAr2 Hu)))).
  (* --- c_pair --- *)
  - intros G k i j A B t t' u u' Hik Hjk _ IHA _ IHB _ IHt _ IHt' _ IHct _ IHu _ IHu' _ IHcu
      g g' HS.
    assert (HT : Good_ty (subst_etm g (er (sig_ k A B)))).
    { apply (gt_of k), sem_sig_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros v v' Hv; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hv). }
    destruct (IHct g g' HS) as [Ht1 Ht2].
    destruct (IHct g g (SubstRel_refl _ _ _ HS)) as [Htr1 _].
    destruct (IHcu g g' HS) as [Hu1 Hu2].
    rewrite er_sub1 in Hu1, Hu2.
    split.
    + apply (sem_pair k A B); [exact HT | exact Ht1 | exact Hu1].
    + apply (sem_pair k A B); [exact HT | exact Ht2 |].
      eapply Rel_cast;
        [apply (SEl_U _ _ _ IHB _ _
           (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Htr1)) | exact Hu2].
  (* --- c_fst --- *)
  - intros G k i j A B p p' Hik Hjk _ IHA _ IHB _ IHp _ IHp' _ IHcp g g' HS.
    destruct (IHcp g g' HS) as [H1 H2]; split.
    + exact (proj1 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) H1)).
    + exact (proj1 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) H2)).
  (* --- c_snd --- *)
  - intros G k i j A B p p' Hik Hjk _ IHA _ IHB _ IHp _ IHp' _ IHcp g g' HS.
    destruct (IHcp g g' HS) as [H1 H2].
    destruct (IHcp g g (SubstRel_refl _ _ _ HS)) as [_ Hr2].
    rewrite er_sub1; split.
    + pose proof (proj2 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) H1)) as H.
      apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) g _)) in H; exact H.
    + pose proof (proj2 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) H2)) as H.
      apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) g _)) in H.
      eapply Rel_cast; [| exact H].
      apply (SEl_U _ _ _ IHB _ _ (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS)
        (proj1 (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) Hr2)))).
  (* --- c_fst_beta --- *)
  - intros G k i j A B t u Hik Hjk _ IHA _ IHB _ IHt _ IHu g g' HS; split.
    + eapply Rel_exp; [apply reds_fst_pair | apply reds_refl | apply IHt, HS].
    + eapply Rel_exp; [apply reds_refl | apply reds_fst_pair | apply IHt, HS].
  (* --- c_snd_beta --- *)
  - intros G k i j A B t u Hik Hjk _ IHA _ IHB _ IHt _ IHu g g' HS.
    pose proof (IHu g g' HS) as H; split.
    + eapply Rel_exp; [apply reds_snd_pair | apply reds_refl | exact H].
    + eapply Rel_exp; [apply reds_refl | apply reds_snd_pair | exact H].
  (* --- c_surj --- *)
  - intros G k i j A B p Hik Hjk _ IHA _ IHB _ IHp g g' HS.
    assert (HT : Good_ty (subst_etm g (er (sig_ k A B)))).
    { apply (gt_of k), sem_sig_eq;
        [apply (eqty_cumul i k _ _ Hik),
           (SEl_U _ _ _ IHA _ _ (SubstRel_refl _ _ _ HS)) |].
      intros v v' Hv; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS) Hv). }
    pose proof (Rel_sig_elim _ _ _ _ _ (ev_sig _ _) (IHp g g' HS)) as [Hf1 Hs1].
    pose proof (Rel_sig_elim _ _ _ _ _ (ev_sig _ _)
                  (IHp g g (SubstRel_refl _ _ _ HS))) as [Hfr _].
    split.
    + eapply Rel_sig_intro; [exact HT | apply ev_sig | |].
      * eapply Rel_exp; [apply reds_fst_pair | apply reds_refl | exact Hf1].
      * eapply Rel_exp_ty; [apply (reds_lam_app (er B) g _) |].
        eapply Rel_cast;
          [apply (SEl_U _ _ _ IHB _ _ (SubstRel_cons _ _ _ _ _ _ (SubstRel_refl _ _ _ HS)
             (Rel_exp _ _ _ _ _ (reds_refl _) (reds_fst_pair _ _) Hfr))) |].
        eapply Rel_exp_ty; [apply reds_refl |].
        apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) g _)) in Hs1.
        eapply Rel_exp; [apply reds_snd_pair | apply reds_refl | exact Hs1].
    + eapply Rel_sig_intro; [exact HT | apply ev_sig | |].
      * eapply Rel_exp; [apply reds_refl | apply reds_fst_pair | exact Hf1].
      * apply (Rel_red_ty _ _ _ _ (reds_lam_app (er B) g _)) in Hs1.
        eapply Rel_exp_ty; [apply (reds_lam_app (er B) g _) |].
        eapply Rel_exp; [apply reds_refl | apply reds_snd_pair | exact Hs1].
  (* --- c_w --- *)
  - intros G k i j A A' B B' Hik Hjk _ IHA _ IHB _ IHA' _ IHB' _ IHcA _ IHcB g g' HS.
    destruct (SCv_U _ _ _ _ IHcA g g' HS) as [EA1 EA2].
    destruct (SCv_U _ _ _ _ IHcA g g (SubstRel_refl _ _ _ HS)) as [_ EAr2].
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + apply sem_w_eq; [apply (eqty_cumul i k _ _ Hik), EA1 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj1 (SCv_U _ _ _ _ IHcB _ _ (SubstRel_cons _ _ _ _ _ _ HS Hu))).
    + apply sem_w_eq; [apply (eqty_cumul i k _ _ Hik), EA2 |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk).
      apply (proj2 (SCv_U _ _ _ _ IHcB _ _
        (SubstRel_cons _ _ _ _ _ _ HS (Rel_cast _ _ _ _ _ EAr2 Hu)))).
  (* --- c_sup.  In the second direction the branching functions are compared
         at the fibre over the PRIMED label, so the fibre itself has to be
         moved along the labels' conversion first. --- *)
  - intros G k i j A B a a' f f' Hik Hjk _ IHA _ IHB _ IHa _ IHa' _ IHca _ IHf _ IHf' _ IHcf
      g g' HS.
    pose proof (SubstRel_refl _ _ _ HS) as HSr.
    assert (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B)))).
    { apply sem_w_eq; [apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HSr) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), (SEl_U _ _ _ IHB),
        (SubstRel_cons _ _ _ _ _ _ HSr Hu). }
    destruct (IHca g g' HS) as [Ha1 Ha2].
    destruct (IHca g g HSr) as [_ Har2].
    destruct (IHcf g g' HS) as [Hf1 Hf2].
    assert (Eaa : eqty j (subst_etm (scons (subst_etm g (er a')) g) (er B))
                         (subst_etm (scons (subst_etm g (er a)) g) (er B)))
      by (apply (SEl_U _ _ _ IHB), (SubstRel_cons _ _ _ _ _ _ HSr Har2)).
    rewrite !er_sup_sub; split.
    + apply (sem_sup k A B);
        [apply (gt_of k), HWk | exact Ha1 | apply (sem_wsup_fun k A B a g), Hf1].
    + apply (sem_sup k A B); [apply (gt_of k), HWk | exact Ha2 |].
      intros u u' Hu.
      apply (sem_wsup_fun k A B a g _ _ Hf2).
      eapply Rel_cast; [exact Eaa | exact Hu].
  (* --- c_wrec --- *)
  - intros G k i j m n A B C C' s s' w w' Hik Hjk Hjn Hmn _ _ IHA _ IHB _ IHC
      _ IHC' _ IHcC _ _ _ _ _ IHs _ IHs' _ IHcs _ IHw _ IHw' _ IHcw g g' HS.
    pose proof (SubstRel_refl _ _ _ HS) as HSr.
    assert (HBg : forall u u', Rel (subst_etm g (er A)) u u' ->
                  eqty j (subst_etm (scons u g) (er B)) (subst_etm (scons u' g) (er B)))
      by (intros u u' Hu; apply (SEl_U _ _ _ IHB),
            (SubstRel_cons _ _ _ _ _ _ HSr Hu)).
    assert (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B)))).
    { apply sem_w_eq;
        [apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HSr) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), HBg, Hu. }
    assert (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
                 eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
      by (intros x y Hxy; apply (SEl_U _ _ _ IHC),
            (SubstRel_cons _ _ _ _ _ _ HSr Hxy)).
    destruct (IHcw g g' HS) as [Hw1 Hw2].
    destruct (IHcw g g HSr) as [_ Hwr2].
    rewrite er_sub1, !er_wrec_sub; split.
    + apply (sem_wrec k m A B C g _ _ (gt_of k _ HWk) HC
               (sem_wrec_step G k j m n A B C s s' g g' Hjk Hjn Hmn HS HBg HWk HC
                  (fun si si' H => proj1 (IHcs si si' H)))).
      exact Hw1.
    + eapply Rel_cast; [apply HC; exact Hwr2 |].
      apply (sem_wrec k m A B C g _ _ (gt_of k _ HWk) HC
               (sem_wrec_step G k j m n A B C s' s g g' Hjk Hjn Hmn HS HBg HWk HC
                  (fun si si' H => proj2 (IHcs si si' H)))).
      exact Hw2.
  (* --- c_wrec_sup: both directions are the same relation, reached on one
         side by the erased recursor's computation rule and on the other by
         the three beta-steps that open the step's binders. --- *)
  - intros G k i j m n A B C s a f Hik Hjk Hjn Hmn _ _ IHA _ IHB _ IHC _ _ _ _ _ IHs
      _ IHa _ IHf g g' HS.
    pose proof (SubstRel_refl _ _ _ HS) as HSr.
    assert (HBg : forall u u', Rel (subst_etm g (er A)) u u' ->
                  eqty j (subst_etm (scons u g) (er B)) (subst_etm (scons u' g) (er B)))
      by (intros u u' Hu; apply (SEl_U _ _ _ IHB),
            (SubstRel_cons _ _ _ _ _ _ HSr Hu)).
    assert (HWk : eqty k (subst_etm g (er (wt k A B))) (subst_etm g (er (wt k A B)))).
    { apply sem_w_eq;
        [apply (eqty_cumul i k _ _ Hik), (SEl_U _ _ _ IHA _ _ HSr) |].
      intros u u' Hu; apply (eqty_cumul j k _ _ Hjk), HBg, Hu. }
    assert (HC : forall x y, Rel (subst_etm g (er (wt k A B))) x y ->
                 eqty m (subst_etm (scons x g) (er C)) (subst_etm (scons y g) (er C)))
      by (intros x y Hxy; apply (SEl_U _ _ _ IHC),
            (SubstRel_cons _ _ _ _ _ _ HSr Hxy)).
    pose proof (sem_wrec_sup G k j m n A B C s g g' Hjk Hjn Hmn HS HBg HWk HC IHs
                  _ _ _ _ (IHa g g' HS)
                  (sem_wsup_fun k A B a g _ _ (IHf g g' HS))) as Hbody.
    rewrite er_sub1, !er_wrec_sub, !er_sup_sub, !er_sub3, !er_wih_val; split.
    + eapply Rel_exp;
        [ eapply reds_trans;
            [apply (reds_wrec_sup _ _ _ _ (ev_sup _ _)) | apply reds_lam3_app]
        | apply reds_refl | exact Hbody ].
    + eapply Rel_exp;
        [ apply reds_refl
        | eapply reds_trans;
            [apply (reds_wrec_sup _ _ _ _ (ev_sup _ _)) | apply reds_lam3_app]
        | exact Hbody ].
  (* --- c_succ --- *)
  - intros G k n n' _ IHn _ IHn' _ IHcn g g' HS.
    destruct (IHcn g g' HS) as [H1 H2].
    split; (apply Rel_nat_intro; [apply gt_nat | apply ev_nat |]);
      (eapply np_succ; [apply ev_succ | apply ev_succ |]).
    + eapply Rel_nat_elim; [apply ev_nat | exact H1].
    + eapply Rel_nat_elim; [apply ev_nat | exact H2].
  (* --- c_natrec --- *)
  - intros G C C' z z' sc sc' n n' k j _ IHC _ IHC' _ IHcC _ IHz _ IHz' _ IHcz
      _ IHs _ IHs' _ IHcs _ IHn _ IHn' _ IHcn g g' HS.
    assert (HCe : forall m m', NatPer m m' ->
              eqty k (subst_etm (scons m g) (er C)) (subst_etm (scons m' g) (er C))).
    { intros m m' Hm; apply (SEl_U _ _ _ IHC).
      apply (SubstRel_cons _ (nat_ j) _ _ _ _ (SubstRel_refl _ _ _ HS)).
      apply Rel_nat_intro; [apply gt_nat | apply ev_nat | exact Hm]. }
    destruct (IHcz g g' HS) as [Hz1 Hz2]; rewrite er_sub1 in Hz1, Hz2.
    destruct (IHcn g g' HS) as [Hn1 Hn2].
    destruct (IHcn g g (SubstRel_refl _ _ _ HS)) as [_ Hnr2].
    rewrite er_sub1; split.
    + apply (sem_natrec C g k _ _ _ _ HCe Hz1
               (sem_step G j C sc sc' g g' HS
                  (fun si si' H => proj1 (IHcs si si' H)))).
      eapply Rel_nat_elim; [apply ev_nat | exact Hn1].
    + eapply Rel_cast;
        [apply HCe; (eapply Rel_nat_elim; [apply ev_nat | exact Hnr2]) |].
      apply (sem_natrec C g k _ _ _ _ HCe Hz2
               (sem_step G j C sc' sc g g' HS
                  (fun si si' H => proj2 (IHcs si si' H)))).
      eapply Rel_nat_elim; [apply ev_nat | exact Hn2].
  (* --- c_rec_zero --- *)
  - intros G C z sc k j _ IHC _ IHz _ IHs g g' HS.
    pose proof (IHz g g' HS) as H; rewrite er_sub1 in H; rewrite er_sub1; split.
    + eapply Rel_exp; [apply (reds_rec_zero _ _ _ ev_zero) | apply reds_refl | exact H].
    + eapply Rel_exp; [apply reds_refl | apply (reds_rec_zero _ _ _ ev_zero) | exact H].
  (* --- c_rec_succ --- *)
  - intros G C z sc n k j _ IHC _ IHz _ IHs _ IHn g g' HS.
    assert (HCe : forall m m', NatPer m m' ->
              eqty k (subst_etm (scons m g) (er C)) (subst_etm (scons m' g) (er C))).
    { intros m m' Hm; apply (SEl_U _ _ _ IHC).
      apply (SubstRel_cons _ (nat_ j) _ _ _ _ (SubstRel_refl _ _ _ HS)).
      apply Rel_nat_intro; [apply gt_nat | apply ev_nat | exact Hm]. }
    pose proof (IHz g g' HS) as Hz; rewrite er_sub1 in Hz.
    pose proof (sem_step G j C sc sc g g' HS IHs) as Hst.
    pose proof (sem_step_body G j C sc sc g g' HS IHs) as Hbody.
    pose proof (Rel_nat_elim _ _ _ ev_nat (IHn g g' HS)) as Hn.
    pose proof (sem_natrec C g k _ _ _ _ HCe Hz Hst _ _ Hn) as Hrec.
    rewrite er_sub1, !er_sub2; split.
    + eapply Rel_exp;
        [eapply reds_trans;
           [apply (reds_rec_succ _ _ _ _ (ev_succ _)) | apply reds_lam2_app]
        | apply reds_refl |].
      exact (Hbody _ _ Hn _ _ Hrec).
    + eapply Rel_exp;
        [apply reds_refl
        | eapply reds_trans;
            [apply (reds_rec_succ _ _ _ _ (ev_succ _)) | apply reds_lam2_app] |].
      exact (Hbody _ _ Hn _ _ Hrec).
  (* --- c_prf --- *)
  - intros G k j p p' Hjk _ IHp _ IHp' _ IHcp g g' HS.
    destruct (SCv_P _ _ _ _ IHcp g g' HS) as [E1 E2].
    split; (eapply Rel_univ_intro; [apply gt_univ | apply ev_univ |]).
    + apply eqty_prf, E1.
    + apply eqty_prf, E2.
  (* --- c_all --- *)
  - intros G A A' p p' j k _ IHA _ IHp _ IHA' _ IHp' _ IHcA _ IHcp g g' HS.
    split; (apply Rel_prop_intro; [apply gt_prop | apply ev_prop |]);
      (eapply PR_all; apply ev_all).
Qed.

(* ------------------------------------------------------------------ *)
(* The three clauses of Theorem 6.7 as stated, and the closed case.   *)
(* ------------------------------------------------------------------ *)

Corollary fundamental_ty G t A : ty G t A -> SEl G t A.
Proof. apply fundamental. Qed.

Corollary fundamental_cv G t u A : cv G t u A -> SCv G t u A.
Proof. apply fundamental. Qed.

Corollary fundamental_U G A k : ty G A (UU k) ->
  forall g g', SubstRel G g g' -> eqty k (subst_etm g (er A)) (subst_etm g' (er A)).
Proof. intros H; apply (SEl_U _ _ _ (fundamental_ty _ _ _ H)). Qed.

Corollary fundamental_P G p j : ty G p (prop j) ->
  forall g g', SubstRel G g g' -> PR (subst_etm g (er p)) (subst_etm g' (er p)).
Proof. intros H; apply (SEl_P _ _ _ (fundamental_ty _ _ _ H)). Qed.

Corollary fundamental_cv_U G A B k : cv G A B (UU k) ->
  forall g g', SubstRel G g g' -> eqty k (subst_etm g (er A)) (subst_etm g' (er B)).
Proof. intros H g g' HS; apply (proj1 (SCv_U _ _ _ _ (fundamental_cv _ _ _ _ H) g g' HS)). Qed.

(* The closed case, which is what the code hierarchy consumes: the erasure
   of a closed type is a layer-1 type, and the erasure of a closed term is
   one of its realisers. *)
Lemma SubstRel_nil : SubstRel nil var_etm var_etm.
Proof. exact I. Qed.

Corollary closed_eqty A k : ty nil A (UU k) -> eqty k (er A) (er A).
Proof.
  intros H; pose proof (fundamental_U _ _ _ H var_etm var_etm SubstRel_nil) as E.
  rewrite !subst_etm_id in E; exact E.
Qed.

Corollary closed_Good_ty A k : ty nil A (UU k) -> Good_ty (er A).
Proof. intros H; exists k; apply closed_eqty, H. Qed.

Corollary closed_Good t A : ty nil t A -> Good (er A) (er t).
Proof.
  intros H; pose proof (fundamental_ty _ _ _ H var_etm var_etm SubstRel_nil) as E.
  rewrite !subst_etm_id in E; exact E.
Qed.

(* Closing the loop with Layer1/BadTransp.v: that file derives, from
   Eq-formation and transport alone, a closed type whose erasure is not a
   layer-1 type.  The corollary above says every closed type's erasure is
   one.  So the two rules are not merely unproved here -- adding them to
   Typing/Rules.v would make this theorem false, which is why Eq is absent
   from the formalised theory rather than present in a weakened form. *)
Corollary Eq_with_transport_inadmissible :
  (forall G A t u k, ty G A (UU k) -> ty G t A -> ty G u A ->
     ty G (Ann.eqty A t u) (prop 0)) ->
  (forall G A B t u e b k j,
     ty G A (UU k) -> ty (A :: G) B (UU j) ->
     ty G t A -> ty G u A -> ty G e (prf 0 (Ann.eqty A t u)) -> ty G b (B [t..]) ->
     ty G (transp A B t u e b) (B [u..])) -> False.
Proof.
  intros HE HL; apply (large_transp_refutes_layer1 HE HL).
  intros A k H; apply (closed_Good_ty A k H).
Qed.
