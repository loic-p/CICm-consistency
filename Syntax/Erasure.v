From CICM Require Import core unscoped Syntax.

Import UnscopedNotations.

(* Erasure |-| : tm -> etm.  Proof terms go to their subject or to estar,
   absurd goes to eerr (the only source of stuck terms), up is transparent,
   and binders of type formers become explicit elam so that codomains are
   functions on the erased side.  The LEVEL ANNOTATIONS all erase away: a
   former and its lift have the same realiser, which is what makes every
   `up`-conversion invisible at layer 1. *)
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
  | nat_ k => enat
  | zero k => ezero
  | succ t => esucc (er t)
  (* The step term has two binders in the annotated syntax and none in the
     erased one: it erases to a function of the scrutinee's predecessor and of
     the recursive result, which is exactly the shape red_rec_s consumes.  So
     the erased calculus is unchanged by the binder form of natrec, and the two
     beta-steps that separate the body's realiser from eapp (eapp . m) w are
     closed by expansion (reds_lam2_app). *)
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

Lemma er_up_ren xi :
  forall x, upRen_tm_tm xi x = upRen_etm_etm xi x.
Proof. intros []; reflexivity. Qed.

(* natrec's step term sits under TWO binders, so the two calculi's `up` have to
   be matched twice. *)
Lemma er_up_ren2 xi :
  forall x, upRen_tm_tm (upRen_tm_tm xi) x = upRen_etm_etm (upRen_etm_etm xi) x.
Proof. intros [| []]; reflexivity. Qed.

Lemma er_ren xi t : er (ren_tm xi t) = ren_etm xi (er t).
Proof.
  revert xi; induction t; intros xi; cbn; f_equal; auto;
    rewrite ?IHt2, ?IHt, ?IHt3;
    try apply extRen_etm; intros; try apply er_up_ren; auto.
  all: apply er_up_ren2.
Qed.

Lemma er_up_subst sigma :
  forall x, er (up_tm_tm sigma x) = up_etm_etm (sigma >> er) x.
Proof.
  intros []; cbn; [reflexivity|].
  unfold funcomp; apply er_ren.
Qed.

Lemma er_up_subst2 sigma :
  forall x, er (up_tm_tm (up_tm_tm sigma) x) = up_etm_etm (up_etm_etm (sigma >> er)) x.
Proof.
  intros [| []]; cbn; try reflexivity.
  unfold funcomp; cbn; rewrite !er_ren; reflexivity.
Qed.

(* Lemma 3.1: erasure commutes with substitution.  The substitution on the
   erased side is the annotated one composed with erasure. *)
Lemma er_subst sigma t : er (subst_tm sigma t) = subst_etm (sigma >> er) (er t).
Proof.
  revert sigma; induction t; intros sigma; cbn; f_equal; auto;
    rewrite ?IHt2, ?IHt, ?IHt3;
    try apply ext_etm; intros; try apply er_up_subst; auto.
  (* pi, sig_ and all sit under one elam, natrec's step under two. *)
  all: repeat apply congr_elam; apply ext_etm; intros;
       first [apply er_up_subst | apply er_up_subst2].
Qed.

Lemma er_subst1 t u : er (t[u..]) = (er t)[(er u)..].
Proof.
  rewrite er_subst; apply ext_etm; intros []; reflexivity.
Qed.
