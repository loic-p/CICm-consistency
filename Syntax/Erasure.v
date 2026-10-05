(** Erasure |-| : tm -> etm.  Proof terms go to their subject or to estar,
    absurd goes to eerr (the only source of stuck terms), the lifts are
    transparent, and binders of type formers become explicit elam so that
    codomains are functions on the erased side.  The LEVEL ANNOTATIONS all
    erase away: a former and its lift have the same realiser, which is what
    makes every `up`-conversion invisible at layer 1. *)

From CICM Require Import Syntax.Erased Syntax.Ann.

Fixpoint er (t : tm) : etm :=
  match t with
  | var_tm i => var_etm i
  | lam k A B t => elam (er t)
  | plam A t => elam (er t)
  | app A B t u => eapp (er t) (er u)
  | papp t u => eapp (er t) (er u)
  | pair k A B t u => epair (er t) (er u)
  | fst A B t => efst (er t)
  | snd A B t => esnd (er t)
  | pi k A B => epi (er A) (elam (er B))
  | sig_ k A B => esig (er A) (elam (er B))
  (* W: the branching type becomes a function, as at Pi and Sigma, and the
     recursor's step -- three binders here, none there -- becomes a curried
     function of the label, the branching function and the induction
     hypothesis, which is the shape red_wrec consumes. *)
  | wt k A B => ew (er A) (elam (er B))
  | sup k A B a f => esup (er a) (er f)
  | wrec A B C s w => ewrec (elam (elam (elam (er s)))) (er w)
  | nat_ k => enat
  | zero k => ezero
  | succ t => esucc (er t)
  | natrec C z s n => enatrec (er z) (elam (elam (er s))) (er n)
  | univ k j => euniv j
  | up j A => er A
  | uptm A t => er t
  | prop k => eprop
  | prf k p => eprf (er p)
  | all j A p => eall (er A) (elam (er p))
  | false_ k => efalse
  | absurd T e => eerr
  | eqty A t u => eeqty (er A) (er t) (er u)
  | refl A a => estar
  | transp A B t u e b => er b
  end.

(* RENAMINGS ARE SHARED between the two algebras -- both are nat -> nat, and
   `up_ren` is Sulfur's, not a generated constant -- so erasure commutes with
   renaming with no compatibility lemma at all.  Under Autosubst2 this needed
   one lemma per binder depth (upRen_tm_tm versus upRen_etm_etm). *)
Lemma er_ren r t : er (t ⟨r⟩) = ren_etm r (er t).
Proof.
  revert r; induction t; intros r; cbn; unfold ren_etm in *; repeat f_equal; auto.
Qed.

(* Substitutions are NOT shared: a tm-substitution is nat -> tm and an
   etm-substitution is nat -> etm, so the two `up_subst`s have to be matched.
   Stating the match as a CLOSURE PROPERTY rather than an equation makes it
   iterate on its own, which is what natrec's two binders and wrec's three
   need -- under Autosubst2 this was one lemma per depth. *)
Lemma er_up_subst s t :
  (forall i, er (s i) = t i) -> forall i, er (up_subst s i) = up_etm t i.
Proof.
  intros H [| i]; unfold up_etm, up_subst, Erased.up_subst; cbn; [reflexivity |].
  unfold rscomp, srcomp; cbn; rewrite er_ren, H; reflexivity.
Qed.

Lemma er_subst : forall u s t, (forall i, er (s i) = t i) ->
  er (u [s]) = subst_etm t (er u).
Proof.
  induction u; intros s t H; cbn; unfold subst_etm in *; repeat f_equal;
    eauto using er_up_subst.
Qed.

Lemma er_subst1 t u :
  er (t [u..]) = subst_etm (Erased.scons (er u) Erased.sid) (er t).
Proof. apply er_subst; intros [| i]; reflexivity. Qed.
