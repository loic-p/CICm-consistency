From CICM Require Import Syntax.Erased.

(* Weak head reduction on erased terms: contractions plus head congruences
   for the eliminators.  Nothing reduces under a binder, and eerr has no
   rule, so eerr-headed eliminations are irreducible. *)
Inductive red : etm -> etm -> Prop :=
| red_beta t u : red (eapp (elam t) u) (subst_etm (esub1 u) t)
| red_fst t u : red (efst (epair t u)) t
| red_snd t u : red (esnd (epair t u)) u
| red_rec_z z s : red (enatrec z s ezero) z
| red_rec_s z s n : red (enatrec z s (esucc n)) (eapp (eapp s n) (enatrec z s n))
(* W: the step is applied to the label, to the branching function, and to the
   induction hypothesis -- the function sending a branch to the recursive
   result on that subtree.  That last argument is the only contractum in the
   calculus that builds a binder. *)
| red_wrec s a f :
    red (ewrec s (esup a f))
        (eapp (eapp (eapp s a) f)
              (elam (ewrec (ren_etm ↑ s) (eapp (ren_etm ↑ f) (var_etm 0)))))
| red_app t t' u : red t t' -> red (eapp t u) (eapp t' u)
| red_fst_c t t' : red t t' -> red (efst t) (efst t')
| red_snd_c t t' : red t t' -> red (esnd t) (esnd t')
| red_rec_c z s n n' : red n n' -> red (enatrec z s n) (enatrec z s n')
| red_wrec_c s w w' : red w w' -> red (ewrec s w) (ewrec s w').

Inductive reds : etm -> etm -> Prop :=
| reds_refl t : reds t t
| reds_step t t' u : red t t' -> reds t' u -> reds t u.

(* Values: terms headed by a constructor or a type former. *)
Inductive value : etm -> Prop :=
| v_lam t : value (elam t)
| v_pair t u : value (epair t u)
| v_zero : value ezero
| v_succ t : value (esucc t)
| v_nat : value enat
| v_pi A B : value (epi A B)
| v_sig A B : value (esig A B)
| v_w A B : value (ew A B)
| v_sup a f : value (esup a f)
| v_univ m : value (euniv m)
| v_prop : value eprop
| v_prf p : value (eprf p)
| v_all A p : value (eall A p)
| v_false : value efalse
| v_star : value estar
| v_eqty A t u : value (eeqty A t u).

(* Stuck terms: eerr under a stack of eliminators. *)
Inductive stuck : etm -> Prop :=
| st_err : stuck eerr
| st_app t u : stuck t -> stuck (eapp t u)
| st_fst t : stuck t -> stuck (efst t)
| st_snd t : stuck t -> stuck (esnd t)
| st_rec z s n : stuck n -> stuck (enatrec z s n)
| st_wrec s w : stuck w -> stuck (ewrec s w).

Definition whnf t := value t \/ stuck t.

Definition eval t w := reds t w /\ whnf w.

Definition num : nat -> etm := fix num k := match k with 0 => ezero | S k => esucc (num k) end.

Lemma reds_trans t u v : reds t u -> reds u v -> reds t v.
Proof. induction 1; eauto using reds. Qed.

Lemma reds_app t t' u : reds t t' -> reds (eapp t u) (eapp t' u).
Proof. induction 1; eauto using reds, red. Qed.

Lemma reds_fst t t' : reds t t' -> reds (efst t) (efst t').
Proof. induction 1; eauto using reds, red. Qed.

Lemma reds_snd t t' : reds t t' -> reds (esnd t) (esnd t').
Proof. induction 1; eauto using reds, red. Qed.

Lemma reds_rec z s n n' : reds n n' -> reds (enatrec z s n) (enatrec z s n').
Proof. induction 1; eauto using reds, red. Qed.

Lemma reds_wrec s w w' : reds w w' -> reds (ewrec s w) (ewrec s w').
Proof. induction 1; eauto using reds, red. Qed.
