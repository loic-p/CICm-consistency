From CICM Require Import core unscoped.
From Stdlib Require Import Setoid Morphisms Relation_Definitions.
Module Core.

Inductive etm : Type :=
  | var_etm : nat -> etm
  | elam : etm -> etm
  | eapp : etm -> etm -> etm
  | epair : etm -> etm -> etm
  | efst : etm -> etm
  | esnd : etm -> etm
  | epi : etm -> etm -> etm
  | esig : etm -> etm -> etm
  | enat : etm
  | ezero : etm
  | esucc : etm -> etm
  | enatrec : etm -> etm -> etm -> etm
  | euniv : nat -> etm
  | eprop : etm
  | eprf : etm -> etm
  | eall : etm -> etm -> etm
  | efalse : etm
  | estar : etm
  | eerr : etm
  | eeqty : etm -> etm -> etm -> etm.

Lemma congr_elam {s0 : etm} {t0 : etm} (H0 : s0 = t0) : elam s0 = elam t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => elam x) H0)).
Qed.

Lemma congr_eapp {s0 : etm} {s1 : etm} {t0 : etm} {t1 : etm} (H0 : s0 = t0)
  (H1 : s1 = t1) : eapp s0 s1 = eapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => eapp x s1) H0))
         (ap (fun x => eapp t0 x) H1)).
Qed.

Lemma congr_epair {s0 : etm} {s1 : etm} {t0 : etm} {t1 : etm} (H0 : s0 = t0)
  (H1 : s1 = t1) : epair s0 s1 = epair t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => epair x s1) H0))
         (ap (fun x => epair t0 x) H1)).
Qed.

Lemma congr_efst {s0 : etm} {t0 : etm} (H0 : s0 = t0) : efst s0 = efst t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => efst x) H0)).
Qed.

Lemma congr_esnd {s0 : etm} {t0 : etm} (H0 : s0 = t0) : esnd s0 = esnd t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => esnd x) H0)).
Qed.

Lemma congr_epi {s0 : etm} {s1 : etm} {t0 : etm} {t1 : etm} (H0 : s0 = t0)
  (H1 : s1 = t1) : epi s0 s1 = epi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => epi x s1) H0))
         (ap (fun x => epi t0 x) H1)).
Qed.

Lemma congr_esig {s0 : etm} {s1 : etm} {t0 : etm} {t1 : etm} (H0 : s0 = t0)
  (H1 : s1 = t1) : esig s0 s1 = esig t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => esig x s1) H0))
         (ap (fun x => esig t0 x) H1)).
Qed.

Lemma congr_enat : enat = enat.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ezero : ezero = ezero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_esucc {s0 : etm} {t0 : etm} (H0 : s0 = t0) : esucc s0 = esucc t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => esucc x) H0)).
Qed.

Lemma congr_enatrec {s0 : etm} {s1 : etm} {s2 : etm} {t0 : etm} {t1 : etm}
  {t2 : etm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  enatrec s0 s1 s2 = enatrec t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => enatrec x s1 s2) H0))
            (ap (fun x => enatrec t0 x s2) H1))
         (ap (fun x => enatrec t0 t1 x) H2)).
Qed.

Lemma congr_euniv {s0 : nat} {t0 : nat} (H0 : s0 = t0) : euniv s0 = euniv t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => euniv x) H0)).
Qed.

Lemma congr_eprop : eprop = eprop.
Proof.
exact (eq_refl).
Qed.

Lemma congr_eprf {s0 : etm} {t0 : etm} (H0 : s0 = t0) : eprf s0 = eprf t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => eprf x) H0)).
Qed.

Lemma congr_eall {s0 : etm} {s1 : etm} {t0 : etm} {t1 : etm} (H0 : s0 = t0)
  (H1 : s1 = t1) : eall s0 s1 = eall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => eall x s1) H0))
         (ap (fun x => eall t0 x) H1)).
Qed.

Lemma congr_efalse : efalse = efalse.
Proof.
exact (eq_refl).
Qed.

Lemma congr_estar : estar = estar.
Proof.
exact (eq_refl).
Qed.

Lemma congr_eerr : eerr = eerr.
Proof.
exact (eq_refl).
Qed.

Lemma congr_eeqty {s0 : etm} {s1 : etm} {s2 : etm} {t0 : etm} {t1 : etm}
  {t2 : etm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  eeqty s0 s1 s2 = eeqty t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => eeqty x s1 s2) H0))
            (ap (fun x => eeqty t0 x s2) H1))
         (ap (fun x => eeqty t0 t1 x) H2)).
Qed.

Lemma upRen_etm_etm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_etm (xi_etm : nat -> nat) (s : etm) {struct s} : etm :=
  match s with
  | var_etm s0 => var_etm (xi_etm s0)
  | elam s0 => elam (ren_etm (upRen_etm_etm xi_etm) s0)
  | eapp s0 s1 => eapp (ren_etm xi_etm s0) (ren_etm xi_etm s1)
  | epair s0 s1 => epair (ren_etm xi_etm s0) (ren_etm xi_etm s1)
  | efst s0 => efst (ren_etm xi_etm s0)
  | esnd s0 => esnd (ren_etm xi_etm s0)
  | epi s0 s1 => epi (ren_etm xi_etm s0) (ren_etm xi_etm s1)
  | esig s0 s1 => esig (ren_etm xi_etm s0) (ren_etm xi_etm s1)
  | enat => enat
  | ezero => ezero
  | esucc s0 => esucc (ren_etm xi_etm s0)
  | enatrec s0 s1 s2 =>
      enatrec (ren_etm xi_etm s0) (ren_etm xi_etm s1) (ren_etm xi_etm s2)
  | euniv s0 => euniv s0
  | eprop => eprop
  | eprf s0 => eprf (ren_etm xi_etm s0)
  | eall s0 s1 => eall (ren_etm xi_etm s0) (ren_etm xi_etm s1)
  | efalse => efalse
  | estar => estar
  | eerr => eerr
  | eeqty s0 s1 s2 =>
      eeqty (ren_etm xi_etm s0) (ren_etm xi_etm s1) (ren_etm xi_etm s2)
  end.

Lemma up_etm_etm (sigma : nat -> etm) : nat -> etm.
Proof.
exact (scons (var_etm var_zero) (funcomp (ren_etm shift) sigma)).
Defined.

Fixpoint subst_etm (sigma_etm : nat -> etm) (s : etm) {struct s} : etm :=
  match s with
  | var_etm s0 => sigma_etm s0
  | elam s0 => elam (subst_etm (up_etm_etm sigma_etm) s0)
  | eapp s0 s1 => eapp (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
  | epair s0 s1 => epair (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
  | efst s0 => efst (subst_etm sigma_etm s0)
  | esnd s0 => esnd (subst_etm sigma_etm s0)
  | epi s0 s1 => epi (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
  | esig s0 s1 => esig (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
  | enat => enat
  | ezero => ezero
  | esucc s0 => esucc (subst_etm sigma_etm s0)
  | enatrec s0 s1 s2 =>
      enatrec (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
        (subst_etm sigma_etm s2)
  | euniv s0 => euniv s0
  | eprop => eprop
  | eprf s0 => eprf (subst_etm sigma_etm s0)
  | eall s0 s1 => eall (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
  | efalse => efalse
  | estar => estar
  | eerr => eerr
  | eeqty s0 s1 s2 =>
      eeqty (subst_etm sigma_etm s0) (subst_etm sigma_etm s1)
        (subst_etm sigma_etm s2)
  end.

Lemma upId_etm_etm (sigma : nat -> etm) (Eq : forall x, sigma x = var_etm x)
  : forall x, up_etm_etm sigma x = var_etm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_etm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_etm (sigma_etm : nat -> etm)
(Eq_etm : forall x, sigma_etm x = var_etm x) (s : etm) {struct s} :
subst_etm sigma_etm s = s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (idSubst_etm (up_etm_etm sigma_etm) (upId_etm_etm _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1)
  | efst s0 => congr_efst (idSubst_etm sigma_etm Eq_etm s0)
  | esnd s0 => congr_esnd (idSubst_etm sigma_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (idSubst_etm sigma_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1) (idSubst_etm sigma_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 => congr_eprf (idSubst_etm sigma_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (idSubst_etm sigma_etm Eq_etm s0)
        (idSubst_etm sigma_etm Eq_etm s1) (idSubst_etm sigma_etm Eq_etm s2)
  end.

Lemma upExtRen_etm_etm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_etm_etm xi x = upRen_etm_etm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_etm (xi_etm : nat -> nat) (zeta_etm : nat -> nat)
(Eq_etm : forall x, xi_etm x = zeta_etm x) (s : etm) {struct s} :
ren_etm xi_etm s = ren_etm zeta_etm s :=
  match s with
  | var_etm s0 => ap (var_etm) (Eq_etm s0)
  | elam s0 =>
      congr_elam
        (extRen_etm (upRen_etm_etm xi_etm) (upRen_etm_etm zeta_etm)
           (upExtRen_etm_etm _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
  | efst s0 => congr_efst (extRen_etm xi_etm zeta_etm Eq_etm s0)
  | esnd s0 => congr_esnd (extRen_etm xi_etm zeta_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (extRen_etm xi_etm zeta_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
        (extRen_etm xi_etm zeta_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 => congr_eprf (extRen_etm xi_etm zeta_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (extRen_etm xi_etm zeta_etm Eq_etm s0)
        (extRen_etm xi_etm zeta_etm Eq_etm s1)
        (extRen_etm xi_etm zeta_etm Eq_etm s2)
  end.

Lemma upExt_etm_etm (sigma : nat -> etm) (tau : nat -> etm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_etm_etm sigma x = up_etm_etm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_etm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_etm (sigma_etm : nat -> etm) (tau_etm : nat -> etm)
(Eq_etm : forall x, sigma_etm x = tau_etm x) (s : etm) {struct s} :
subst_etm sigma_etm s = subst_etm tau_etm s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (ext_etm (up_etm_etm sigma_etm) (up_etm_etm tau_etm)
           (upExt_etm_etm _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
  | efst s0 => congr_efst (ext_etm sigma_etm tau_etm Eq_etm s0)
  | esnd s0 => congr_esnd (ext_etm sigma_etm tau_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (ext_etm sigma_etm tau_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
        (ext_etm sigma_etm tau_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 => congr_eprf (ext_etm sigma_etm tau_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (ext_etm sigma_etm tau_etm Eq_etm s0)
        (ext_etm sigma_etm tau_etm Eq_etm s1)
        (ext_etm sigma_etm tau_etm Eq_etm s2)
  end.

Lemma up_ren_ren_etm_etm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_etm_etm zeta) (upRen_etm_etm xi) x = upRen_etm_etm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_etm (xi_etm : nat -> nat) (zeta_etm : nat -> nat)
(rho_etm : nat -> nat)
(Eq_etm : forall x, funcomp zeta_etm xi_etm x = rho_etm x) (s : etm) {struct
 s} :
ren_etm zeta_etm (ren_etm xi_etm s) = ren_etm rho_etm s :=
  match s with
  | var_etm s0 => ap (var_etm) (Eq_etm s0)
  | elam s0 =>
      congr_elam
        (compRenRen_etm (upRen_etm_etm xi_etm) (upRen_etm_etm zeta_etm)
           (upRen_etm_etm rho_etm) (up_ren_ren _ _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
  | efst s0 => congr_efst (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
  | esnd s0 => congr_esnd (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 => congr_eprf (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s0)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s1)
        (compRenRen_etm xi_etm zeta_etm rho_etm Eq_etm s2)
  end.

Lemma up_ren_subst_etm_etm (xi : nat -> nat) (tau : nat -> etm)
  (theta : nat -> etm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_etm_etm tau) (upRen_etm_etm xi) x = up_etm_etm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_etm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_etm (xi_etm : nat -> nat) (tau_etm : nat -> etm)
(theta_etm : nat -> etm)
(Eq_etm : forall x, funcomp tau_etm xi_etm x = theta_etm x) (s : etm) {struct
 s} :
subst_etm tau_etm (ren_etm xi_etm s) = subst_etm theta_etm s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (compRenSubst_etm (upRen_etm_etm xi_etm) (up_etm_etm tau_etm)
           (up_etm_etm theta_etm) (up_ren_subst_etm_etm _ _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
  | efst s0 =>
      congr_efst (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
  | esnd s0 =>
      congr_esnd (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 =>
      congr_eprf (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s0)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s1)
        (compRenSubst_etm xi_etm tau_etm theta_etm Eq_etm s2)
  end.

Lemma up_subst_ren_etm_etm (sigma : nat -> etm) (zeta_etm : nat -> nat)
  (theta : nat -> etm)
  (Eq : forall x, funcomp (ren_etm zeta_etm) sigma x = theta x) :
  forall x,
  funcomp (ren_etm (upRen_etm_etm zeta_etm)) (up_etm_etm sigma) x =
  up_etm_etm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_etm shift (upRen_etm_etm zeta_etm)
                (funcomp shift zeta_etm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_etm zeta_etm shift (funcomp shift zeta_etm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_etm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_etm (sigma_etm : nat -> etm) (zeta_etm : nat -> nat)
(theta_etm : nat -> etm)
(Eq_etm : forall x, funcomp (ren_etm zeta_etm) sigma_etm x = theta_etm x)
(s : etm) {struct s} :
ren_etm zeta_etm (subst_etm sigma_etm s) = subst_etm theta_etm s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (compSubstRen_etm (up_etm_etm sigma_etm) (upRen_etm_etm zeta_etm)
           (up_etm_etm theta_etm) (up_subst_ren_etm_etm _ _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
  | efst s0 =>
      congr_efst (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
  | esnd s0 =>
      congr_esnd (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 =>
      congr_eprf (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s0)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s1)
        (compSubstRen_etm sigma_etm zeta_etm theta_etm Eq_etm s2)
  end.

Lemma up_subst_subst_etm_etm (sigma : nat -> etm) (tau_etm : nat -> etm)
  (theta : nat -> etm)
  (Eq : forall x, funcomp (subst_etm tau_etm) sigma x = theta x) :
  forall x,
  funcomp (subst_etm (up_etm_etm tau_etm)) (up_etm_etm sigma) x =
  up_etm_etm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_etm shift (up_etm_etm tau_etm)
                (funcomp (up_etm_etm tau_etm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_etm tau_etm shift
                      (funcomp (ren_etm shift) tau_etm) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_etm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_etm (sigma_etm : nat -> etm) (tau_etm : nat -> etm)
(theta_etm : nat -> etm)
(Eq_etm : forall x, funcomp (subst_etm tau_etm) sigma_etm x = theta_etm x)
(s : etm) {struct s} :
subst_etm tau_etm (subst_etm sigma_etm s) = subst_etm theta_etm s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (compSubstSubst_etm (up_etm_etm sigma_etm) (up_etm_etm tau_etm)
           (up_etm_etm theta_etm) (up_subst_subst_etm_etm _ _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
  | efst s0 =>
      congr_efst (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
  | esnd s0 =>
      congr_esnd (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 =>
      congr_esucc (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 =>
      congr_eprf (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s0)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s1)
        (compSubstSubst_etm sigma_etm tau_etm theta_etm Eq_etm s2)
  end.

Lemma renRen_etm (xi_etm : nat -> nat) (zeta_etm : nat -> nat) (s : etm) :
  ren_etm zeta_etm (ren_etm xi_etm s) = ren_etm (funcomp zeta_etm xi_etm) s.
Proof.
exact (compRenRen_etm xi_etm zeta_etm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_etm_pointwise (xi_etm : nat -> nat) (zeta_etm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_etm zeta_etm) (ren_etm xi_etm))
    (ren_etm (funcomp zeta_etm xi_etm)).
Proof.
exact (fun s => compRenRen_etm xi_etm zeta_etm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_etm (xi_etm : nat -> nat) (tau_etm : nat -> etm) (s : etm) :
  subst_etm tau_etm (ren_etm xi_etm s) = subst_etm (funcomp tau_etm xi_etm) s.
Proof.
exact (compRenSubst_etm xi_etm tau_etm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_etm_pointwise (xi_etm : nat -> nat) (tau_etm : nat -> etm) :
  pointwise_relation _ eq (funcomp (subst_etm tau_etm) (ren_etm xi_etm))
    (subst_etm (funcomp tau_etm xi_etm)).
Proof.
exact (fun s => compRenSubst_etm xi_etm tau_etm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_etm (sigma_etm : nat -> etm) (zeta_etm : nat -> nat) (s : etm)
  :
  ren_etm zeta_etm (subst_etm sigma_etm s) =
  subst_etm (funcomp (ren_etm zeta_etm) sigma_etm) s.
Proof.
exact (compSubstRen_etm sigma_etm zeta_etm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_etm_pointwise (sigma_etm : nat -> etm) (zeta_etm : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_etm zeta_etm) (subst_etm sigma_etm))
    (subst_etm (funcomp (ren_etm zeta_etm) sigma_etm)).
Proof.
exact (fun s => compSubstRen_etm sigma_etm zeta_etm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_etm (sigma_etm : nat -> etm) (tau_etm : nat -> etm)
  (s : etm) :
  subst_etm tau_etm (subst_etm sigma_etm s) =
  subst_etm (funcomp (subst_etm tau_etm) sigma_etm) s.
Proof.
exact (compSubstSubst_etm sigma_etm tau_etm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_etm_pointwise (sigma_etm : nat -> etm)
  (tau_etm : nat -> etm) :
  pointwise_relation _ eq (funcomp (subst_etm tau_etm) (subst_etm sigma_etm))
    (subst_etm (funcomp (subst_etm tau_etm) sigma_etm)).
Proof.
exact (fun s => compSubstSubst_etm sigma_etm tau_etm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_etm_etm (xi : nat -> nat) (sigma : nat -> etm)
  (Eq : forall x, funcomp (var_etm) xi x = sigma x) :
  forall x, funcomp (var_etm) (upRen_etm_etm xi) x = up_etm_etm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_etm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_etm (xi_etm : nat -> nat) (sigma_etm : nat -> etm)
(Eq_etm : forall x, funcomp (var_etm) xi_etm x = sigma_etm x) (s : etm)
{struct s} : ren_etm xi_etm s = subst_etm sigma_etm s :=
  match s with
  | var_etm s0 => Eq_etm s0
  | elam s0 =>
      congr_elam
        (rinst_inst_etm (upRen_etm_etm xi_etm) (up_etm_etm sigma_etm)
           (rinstInst_up_etm_etm _ _ Eq_etm) s0)
  | eapp s0 s1 =>
      congr_eapp (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
  | epair s0 s1 =>
      congr_epair (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
  | efst s0 => congr_efst (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
  | esnd s0 => congr_esnd (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
  | epi s0 s1 =>
      congr_epi (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
  | esig s0 s1 =>
      congr_esig (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
  | enat => congr_enat
  | ezero => congr_ezero
  | esucc s0 => congr_esucc (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
  | enatrec s0 s1 s2 =>
      congr_enatrec (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s2)
  | euniv s0 => congr_euniv (eq_refl s0)
  | eprop => congr_eprop
  | eprf s0 => congr_eprf (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
  | eall s0 s1 =>
      congr_eall (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
  | efalse => congr_efalse
  | estar => congr_estar
  | eerr => congr_eerr
  | eeqty s0 s1 s2 =>
      congr_eeqty (rinst_inst_etm xi_etm sigma_etm Eq_etm s0)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s1)
        (rinst_inst_etm xi_etm sigma_etm Eq_etm s2)
  end.

Lemma rinstInst'_etm (xi_etm : nat -> nat) (s : etm) :
  ren_etm xi_etm s = subst_etm (funcomp (var_etm) xi_etm) s.
Proof.
exact (rinst_inst_etm xi_etm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_etm_pointwise (xi_etm : nat -> nat) :
  pointwise_relation _ eq (ren_etm xi_etm)
    (subst_etm (funcomp (var_etm) xi_etm)).
Proof.
exact (fun s => rinst_inst_etm xi_etm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_etm (s : etm) : subst_etm (var_etm) s = s.
Proof.
exact (idSubst_etm (var_etm) (fun n => eq_refl) s).
Qed.

Lemma instId'_etm_pointwise :
  pointwise_relation _ eq (subst_etm (var_etm)) id.
Proof.
exact (fun s => idSubst_etm (var_etm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_etm (s : etm) : ren_etm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_etm s) (rinstInst'_etm id s)).
Qed.

Lemma rinstId'_etm_pointwise : pointwise_relation _ eq (@ren_etm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_etm s) (rinstInst'_etm id s)).
Qed.

Lemma varL'_etm (sigma_etm : nat -> etm) (x : nat) :
  subst_etm sigma_etm (var_etm x) = sigma_etm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_etm_pointwise (sigma_etm : nat -> etm) :
  pointwise_relation _ eq (funcomp (subst_etm sigma_etm) (var_etm)) sigma_etm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_etm (xi_etm : nat -> nat) (x : nat) :
  ren_etm xi_etm (var_etm x) = var_etm (xi_etm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_etm_pointwise (xi_etm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_etm xi_etm) (var_etm))
    (funcomp (var_etm) xi_etm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive tm : Type :=
  | var_tm : nat -> tm
  | lam : tm -> tm -> tm -> tm
  | plam : tm -> tm -> tm
  | app : tm -> tm -> tm -> tm -> tm
  | papp : tm -> tm -> tm
  | pair : tm -> tm -> tm -> tm -> tm
  | fst : tm -> tm -> tm -> tm
  | snd : tm -> tm -> tm -> tm
  | pi : tm -> tm -> tm
  | sig_ : tm -> tm -> tm
  | nat_ : tm
  | zero : tm
  | succ : tm -> tm
  | natrec : tm -> tm -> tm -> tm -> tm
  | univ : nat -> tm
  | up : tm -> tm -> tm
  | uptm : tm -> tm -> tm
  | prop : tm
  | prf : tm -> tm
  | all : tm -> tm -> tm
  | false_ : tm
  | absurd : tm -> tm -> tm
  | eqty : tm -> tm -> tm -> tm
  | refl : tm -> tm -> tm
  | transp : tm -> tm -> tm -> tm -> tm -> tm -> tm.

Lemma congr_lam {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : lam s0 s1 s2 = lam t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => lam x s1 s2) H0))
            (ap (fun x => lam t0 x s2) H1))
         (ap (fun x => lam t0 t1 x) H2)).
Qed.

Lemma congr_plam {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : plam s0 s1 = plam t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => plam x s1) H0))
         (ap (fun x => plam t0 x) H1)).
Qed.

Lemma congr_app {s0 : tm} {s1 : tm} {s2 : tm} {s3 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : app s0 s1 s2 s3 = app t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => app x s1 s2 s3) H0))
               (ap (fun x => app t0 x s2 s3) H1))
            (ap (fun x => app t0 t1 x s3) H2))
         (ap (fun x => app t0 t1 t2 x) H3)).
Qed.

Lemma congr_papp {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : papp s0 s1 = papp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => papp x s1) H0))
         (ap (fun x => papp t0 x) H1)).
Qed.

Lemma congr_pair {s0 : tm} {s1 : tm} {s2 : tm} {s3 : tm} {t0 : tm} {t1 : tm}
  {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : pair s0 s1 s2 s3 = pair t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => pair x s1 s2 s3) H0))
               (ap (fun x => pair t0 x s2 s3) H1))
            (ap (fun x => pair t0 t1 x s3) H2))
         (ap (fun x => pair t0 t1 t2 x) H3)).
Qed.

Lemma congr_fst {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : fst s0 s1 s2 = fst t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => fst x s1 s2) H0))
            (ap (fun x => fst t0 x s2) H1))
         (ap (fun x => fst t0 t1 x) H2)).
Qed.

Lemma congr_snd {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) : snd s0 s1 s2 = snd t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => snd x s1 s2) H0))
            (ap (fun x => snd t0 x s2) H1))
         (ap (fun x => snd t0 t1 x) H2)).
Qed.

Lemma congr_pi {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : pi s0 s1 = pi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pi x s1) H0))
         (ap (fun x => pi t0 x) H1)).
Qed.

Lemma congr_sig_ {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : sig_ s0 s1 = sig_ t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => sig_ x s1) H0))
         (ap (fun x => sig_ t0 x) H1)).
Qed.

Lemma congr_nat_ : nat_ = nat_.
Proof.
exact (eq_refl).
Qed.

Lemma congr_zero : zero = zero.
Proof.
exact (eq_refl).
Qed.

Lemma congr_succ {s0 : tm} {t0 : tm} (H0 : s0 = t0) : succ s0 = succ t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => succ x) H0)).
Qed.

Lemma congr_natrec {s0 : tm} {s1 : tm} {s2 : tm} {s3 : tm} {t0 : tm}
  {t1 : tm} {t2 : tm} {t3 : tm} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : natrec s0 s1 s2 s3 = natrec t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => natrec x s1 s2 s3) H0))
               (ap (fun x => natrec t0 x s2 s3) H1))
            (ap (fun x => natrec t0 t1 x s3) H2))
         (ap (fun x => natrec t0 t1 t2 x) H3)).
Qed.

Lemma congr_univ {s0 : nat} {t0 : nat} (H0 : s0 = t0) : univ s0 = univ t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => univ x) H0)).
Qed.

Lemma congr_up {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : up s0 s1 = up t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => up x s1) H0))
         (ap (fun x => up t0 x) H1)).
Qed.

Lemma congr_uptm {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : uptm s0 s1 = uptm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => uptm x s1) H0))
         (ap (fun x => uptm t0 x) H1)).
Qed.

Lemma congr_prop : prop = prop.
Proof.
exact (eq_refl).
Qed.

Lemma congr_prf {s0 : tm} {t0 : tm} (H0 : s0 = t0) : prf s0 = prf t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => prf x) H0)).
Qed.

Lemma congr_all {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : all s0 s1 = all t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => all x s1) H0))
         (ap (fun x => all t0 x) H1)).
Qed.

Lemma congr_false_ : false_ = false_.
Proof.
exact (eq_refl).
Qed.

Lemma congr_absurd {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : absurd s0 s1 = absurd t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => absurd x s1) H0))
         (ap (fun x => absurd t0 x) H1)).
Qed.

Lemma congr_eqty {s0 : tm} {s1 : tm} {s2 : tm} {t0 : tm} {t1 : tm} {t2 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  eqty s0 s1 s2 = eqty t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => eqty x s1 s2) H0))
            (ap (fun x => eqty t0 x s2) H1))
         (ap (fun x => eqty t0 t1 x) H2)).
Qed.

Lemma congr_refl {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : refl s0 s1 = refl t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => refl x s1) H0))
         (ap (fun x => refl t0 x) H1)).
Qed.

Lemma congr_transp {s0 : tm} {s1 : tm} {s2 : tm} {s3 : tm} {s4 : tm}
  {s5 : tm} {t0 : tm} {t1 : tm} {t2 : tm} {t3 : tm} {t4 : tm} {t5 : tm}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) (H4 : s4 = t4)
  (H5 : s5 = t5) : transp s0 s1 s2 s3 s4 s5 = transp t0 t1 t2 t3 t4 t5.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans
                  (eq_trans
                     (eq_trans eq_refl
                        (ap (fun x => transp x s1 s2 s3 s4 s5) H0))
                     (ap (fun x => transp t0 x s2 s3 s4 s5) H1))
                  (ap (fun x => transp t0 t1 x s3 s4 s5) H2))
               (ap (fun x => transp t0 t1 t2 x s4 s5) H3))
            (ap (fun x => transp t0 t1 t2 t3 x s5) H4))
         (ap (fun x => transp t0 t1 t2 t3 t4 x) H5)).
Qed.

Lemma upRen_tm_tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_tm : nat -> nat) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => var_tm (xi_tm s0)
  | lam s0 s1 s2 =>
      lam (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
        (ren_tm (upRen_tm_tm xi_tm) s2)
  | plam s0 s1 => plam (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | app s0 s1 s2 s3 =>
      app (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1) (ren_tm xi_tm s2)
        (ren_tm xi_tm s3)
  | papp s0 s1 => papp (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | pair s0 s1 s2 s3 =>
      pair (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
        (ren_tm xi_tm s2) (ren_tm xi_tm s3)
  | fst s0 s1 s2 =>
      fst (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1) (ren_tm xi_tm s2)
  | snd s0 s1 s2 =>
      snd (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1) (ren_tm xi_tm s2)
  | pi s0 s1 => pi (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | sig_ s0 s1 => sig_ (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | nat_ => nat_
  | zero => zero
  | succ s0 => succ (ren_tm xi_tm s0)
  | natrec s0 s1 s2 s3 =>
      natrec (ren_tm (upRen_tm_tm xi_tm) s0) (ren_tm xi_tm s1)
        (ren_tm (upRen_tm_tm (upRen_tm_tm xi_tm)) s2) (ren_tm xi_tm s3)
  | univ s0 => univ s0
  | up s0 s1 => up (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | uptm s0 s1 => uptm (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | prop => prop
  | prf s0 => prf (ren_tm xi_tm s0)
  | all s0 s1 => all (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
  | false_ => false_
  | absurd s0 s1 => absurd (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | eqty s0 s1 s2 =>
      eqty (ren_tm xi_tm s0) (ren_tm xi_tm s1) (ren_tm xi_tm s2)
  | refl s0 s1 => refl (ren_tm xi_tm s0) (ren_tm xi_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      transp (ren_tm xi_tm s0) (ren_tm (upRen_tm_tm xi_tm) s1)
        (ren_tm xi_tm s2) (ren_tm xi_tm s3) (ren_tm xi_tm s4)
        (ren_tm xi_tm s5)
  end.

Lemma up_tm_tm (sigma : nat -> tm) : nat -> tm.
Proof.
exact (scons (var_tm var_zero) (funcomp (ren_tm shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_tm : nat -> tm) (s : tm) {struct s} : tm :=
  match s with
  | var_tm s0 => sigma_tm s0
  | lam s0 s1 s2 =>
      lam (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm (up_tm_tm sigma_tm) s2)
  | plam s0 s1 =>
      plam (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | app s0 s1 s2 s3 =>
      app (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm sigma_tm s2) (subst_tm sigma_tm s3)
  | papp s0 s1 => papp (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | pair s0 s1 s2 s3 =>
      pair (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm sigma_tm s2) (subst_tm sigma_tm s3)
  | fst s0 s1 s2 =>
      fst (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm sigma_tm s2)
  | snd s0 s1 s2 =>
      snd (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm sigma_tm s2)
  | pi s0 s1 => pi (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | sig_ s0 s1 =>
      sig_ (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | nat_ => nat_
  | zero => zero
  | succ s0 => succ (subst_tm sigma_tm s0)
  | natrec s0 s1 s2 s3 =>
      natrec (subst_tm (up_tm_tm sigma_tm) s0) (subst_tm sigma_tm s1)
        (subst_tm (up_tm_tm (up_tm_tm sigma_tm)) s2) (subst_tm sigma_tm s3)
  | univ s0 => univ s0
  | up s0 s1 => up (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | uptm s0 s1 => uptm (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | prop => prop
  | prf s0 => prf (subst_tm sigma_tm s0)
  | all s0 s1 => all (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
  | false_ => false_
  | absurd s0 s1 => absurd (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | eqty s0 s1 s2 =>
      eqty (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
        (subst_tm sigma_tm s2)
  | refl s0 s1 => refl (subst_tm sigma_tm s0) (subst_tm sigma_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      transp (subst_tm sigma_tm s0) (subst_tm (up_tm_tm sigma_tm) s1)
        (subst_tm sigma_tm s2) (subst_tm sigma_tm s3) (subst_tm sigma_tm s4)
        (subst_tm sigma_tm s5)
  end.

Lemma upId_tm_tm (sigma : nat -> tm) (Eq : forall x, sigma x = var_tm x) :
  forall x, up_tm_tm sigma x = var_tm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = var_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm sigma_tm Eq_tm s2) (idSubst_tm sigma_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm sigma_tm Eq_tm s2) (idSubst_tm sigma_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm sigma_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (idSubst_tm sigma_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s0)
        (idSubst_tm sigma_tm Eq_tm s1)
        (idSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s2)
        (idSubst_tm sigma_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (idSubst_tm sigma_tm Eq_tm s0) (idSubst_tm sigma_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (idSubst_tm sigma_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1) (idSubst_tm sigma_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm sigma_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (idSubst_tm sigma_tm Eq_tm s0)
        (idSubst_tm (up_tm_tm sigma_tm) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm sigma_tm Eq_tm s2) (idSubst_tm sigma_tm Eq_tm s3)
        (idSubst_tm sigma_tm Eq_tm s4) (idSubst_tm sigma_tm Eq_tm s5)
  end.

Lemma upExtRen_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm) {struct s} :
ren_tm xi_tm s = ren_tm zeta_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | lam s0 s1 s2 =>
      congr_lam (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2) (extRen_tm xi_tm zeta_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2) (extRen_tm xi_tm zeta_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
        (extRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s2)
        (extRen_tm xi_tm zeta_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (extRen_tm xi_tm zeta_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1) (extRen_tm xi_tm zeta_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm xi_tm zeta_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (extRen_tm xi_tm zeta_tm Eq_tm s0)
        (extRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm xi_tm zeta_tm Eq_tm s2) (extRen_tm xi_tm zeta_tm Eq_tm s3)
        (extRen_tm xi_tm zeta_tm Eq_tm s4) (extRen_tm xi_tm zeta_tm Eq_tm s5)
  end.

Lemma upExt_tm_tm (sigma : nat -> tm) (tau : nat -> tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm) {struct s} :
subst_tm sigma_tm s = subst_tm tau_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s2)
  | plam s0 s1 =>
      congr_plam (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | app s0 s1 s2 s3 =>
      congr_app (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2) (ext_tm sigma_tm tau_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2) (ext_tm sigma_tm tau_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | sig_ s0 s1 =>
      congr_sig_ (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (ext_tm sigma_tm tau_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
        (ext_tm (up_tm_tm (up_tm_tm sigma_tm)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s2)
        (ext_tm sigma_tm tau_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (ext_tm sigma_tm tau_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1) (ext_tm sigma_tm tau_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm sigma_tm tau_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (ext_tm sigma_tm tau_tm Eq_tm s0)
        (ext_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm) (upExt_tm_tm _ _ Eq_tm)
           s1)
        (ext_tm sigma_tm tau_tm Eq_tm s2) (ext_tm sigma_tm tau_tm Eq_tm s3)
        (ext_tm sigma_tm tau_tm Eq_tm s4) (ext_tm sigma_tm tau_tm Eq_tm s5)
  end.

Lemma up_ren_ren_tm_tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat)
(rho_tm : nat -> nat) (Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x)
(s : tm) {struct s} : ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm rho_tm s :=
  match s with
  | var_tm s0 => ap (var_tm) (Eq_tm s0)
  | lam s0 s1 s2 =>
      congr_lam (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_tm (upRen_tm_tm rho_tm))
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s0)
        (compRenRen_tm (upRen_tm_tm xi_tm) (upRen_tm_tm zeta_tm)
           (upRen_tm_tm rho_tm) (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s2)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s3)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s4)
        (compRenRen_tm xi_tm zeta_tm rho_tm Eq_tm s5)
  end.

Lemma up_ren_subst_tm_tm (xi : nat -> nat) (tau : nat -> tm)
  (theta : nat -> tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm) {struct s} :
subst_tm tau_tm (ren_tm xi_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s0)
        (compRenSubst_tm (upRen_tm_tm xi_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s2)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s3)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s4)
        (compRenSubst_tm xi_tm tau_tm theta_tm Eq_tm s5)
  end.

Lemma up_subst_ren_tm_tm (sigma : nat -> tm) (zeta_tm : nat -> nat)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (ren_tm zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_tm zeta_tm)) (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_tm shift (upRen_tm_tm zeta_tm)
                (funcomp shift zeta_tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_tm shift (funcomp shift zeta_tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (ren_tm zeta_tm) sigma_tm x = theta_tm x) 
(s : tm) {struct s} :
ren_tm zeta_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 =>
      congr_succ (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_tm (upRen_tm_tm zeta_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_tm _ _ _ (up_subst_ren_tm_tm _ _ _ Eq_tm)) s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s0)
        (compSubstRen_tm (up_tm_tm sigma_tm) (upRen_tm_tm zeta_tm)
           (up_tm_tm theta_tm) (up_subst_ren_tm_tm _ _ _ Eq_tm) s1)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s2)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s3)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s4)
        (compSubstRen_tm sigma_tm zeta_tm theta_tm Eq_tm s5)
  end.

Lemma up_subst_subst_tm_tm (sigma : nat -> tm) (tau_tm : nat -> tm)
  (theta : nat -> tm)
  (Eq : forall x, funcomp (subst_tm tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_tm tau_tm)) (up_tm_tm sigma) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_tm shift (up_tm_tm tau_tm)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_tm shift
                      (funcomp (ren_tm shift) tau_tm) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm)
(theta_tm : nat -> tm)
(Eq_tm : forall x, funcomp (subst_tm tau_tm) sigma_tm x = theta_tm x)
(s : tm) {struct s} :
subst_tm tau_tm (subst_tm sigma_tm s) = subst_tm theta_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 =>
      congr_succ (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_tm (up_tm_tm tau_tm)) (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_tm _ _ _ (up_subst_subst_tm_tm _ _ _ Eq_tm)) s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s0)
        (compSubstSubst_tm (up_tm_tm sigma_tm) (up_tm_tm tau_tm)
           (up_tm_tm theta_tm) (up_subst_subst_tm_tm _ _ _ Eq_tm) s1)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s2)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s3)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s4)
        (compSubstSubst_tm sigma_tm tau_tm theta_tm Eq_tm s5)
  end.

Lemma renRen_tm (xi_tm : nat -> nat) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (ren_tm xi_tm s) = ren_tm (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_tm : nat -> nat) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (ren_tm xi_tm))
    (ren_tm (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s => compRenRen_tm xi_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_tm : nat -> nat) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (ren_tm xi_tm s) = subst_tm (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_tm : nat -> nat) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (ren_tm xi_tm))
    (subst_tm (funcomp tau_tm xi_tm)).
Proof.
exact (fun s => compRenSubst_tm xi_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) (s : tm) :
  ren_tm zeta_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (ren_tm zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_tm : nat -> tm) (zeta_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm zeta_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (ren_tm zeta_tm) sigma_tm)).
Proof.
exact (fun s => compSubstRen_tm sigma_tm zeta_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_tm : nat -> tm) (tau_tm : nat -> tm) (s : tm) :
  subst_tm tau_tm (subst_tm sigma_tm s) =
  subst_tm (funcomp (subst_tm tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_tm : nat -> tm) (tau_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm tau_tm) (subst_tm sigma_tm))
    (subst_tm (funcomp (subst_tm tau_tm) sigma_tm)).
Proof.
exact (fun s => compSubstSubst_tm sigma_tm tau_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_tm_tm (xi : nat -> nat) (sigma : nat -> tm)
  (Eq : forall x, funcomp (var_tm) xi x = sigma x) :
  forall x, funcomp (var_tm) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_tm : nat -> nat) (sigma_tm : nat -> tm)
(Eq_tm : forall x, funcomp (var_tm) xi_tm x = sigma_tm x) (s : tm) {struct s}
   :
ren_tm xi_tm s = subst_tm sigma_tm s :=
  match s with
  | var_tm s0 => Eq_tm s0
  | lam s0 s1 s2 =>
      congr_lam (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s2)
  | plam s0 s1 =>
      congr_plam (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | app s0 s1 s2 s3 =>
      congr_app (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
  | papp s0 s1 =>
      congr_papp (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | pair s0 s1 s2 s3 =>
      congr_pair (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
  | fst s0 s1 s2 =>
      congr_fst (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | snd s0 s1 s2 =>
      congr_snd (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | pi s0 s1 =>
      congr_pi (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | sig_ s0 s1 =>
      congr_sig_ (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | nat_ => congr_nat_
  | zero => congr_zero
  | succ s0 => congr_succ (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | natrec s0 s1 s2 s3 =>
      congr_natrec
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
  | univ s0 => congr_univ (eq_refl s0)
  | up s0 s1 =>
      congr_up (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | uptm s0 s1 =>
      congr_uptm (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | prop => congr_prop
  | prf s0 => congr_prf (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
  | all s0 s1 =>
      congr_all (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | false_ => congr_false_
  | absurd s0 s1 =>
      congr_absurd (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | eqty s0 s1 s2 =>
      congr_eqty (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
  | refl s0 s1 =>
      congr_refl (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s1)
  | transp s0 s1 s2 s3 s4 s5 =>
      congr_transp (rinst_inst_tm xi_tm sigma_tm Eq_tm s0)
        (rinst_inst_tm (upRen_tm_tm xi_tm) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s2)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s3)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s4)
        (rinst_inst_tm xi_tm sigma_tm Eq_tm s5)
  end.

Lemma rinstInst'_tm (xi_tm : nat -> nat) (s : tm) :
  ren_tm xi_tm s = subst_tm (funcomp (var_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_tm) (subst_tm (funcomp (var_tm) xi_tm)).
Proof.
exact (fun s => rinst_inst_tm xi_tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_tm) s = s.
Proof.
exact (idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise : pointwise_relation _ eq (subst_tm (var_tm)) id.
Proof.
exact (fun s => idSubst_tm (var_tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id s)).
Qed.

Lemma varL'_tm (sigma_tm : nat -> tm) (x : nat) :
  subst_tm sigma_tm (var_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise (sigma_tm : nat -> tm) :
  pointwise_relation _ eq (funcomp (subst_tm sigma_tm) (var_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm (xi_tm : nat -> nat) (x : nat) :
  ren_tm xi_tm (var_tm x) = var_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise (xi_tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_tm xi_tm) (var_tm))
    (funcomp (var_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_etm X Y :=
    up_etm : X -> Y.

#[global] Instance Subst_tm : (Subst1 _ _ _) := @subst_tm.

#[global] Instance Up_tm_tm : (Up_tm _ _) := @up_tm_tm.

#[global] Instance Ren_tm : (Ren1 _ _ _) := @ren_tm.

#[global] Instance VarInstance_tm : (Var _ _) := @var_tm.

#[global] Instance Subst_etm : (Subst1 _ _ _) := @subst_etm.

#[global] Instance Up_etm_etm : (Up_etm _ _) := @up_etm_etm.

#[global] Instance Ren_etm : (Ren1 _ _ _) := @ren_etm.

#[global]
Instance VarInstance_etm : (Var _ _) := @var_etm.

Notation "s [ sigma_tm ]" := (subst_tm sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "s ⟨ xi_tm ⟩" := (ren_tm xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.

Notation "s [ sigma_etm ]" := (subst_etm sigma_etm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__etm" := up_etm (only printing)  : subst_scope.

Notation "↑__etm" := up_etm_etm (only printing)  : subst_scope.

Notation "s ⟨ xi_etm ⟩" := (ren_etm xi_etm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_etm ( at level 1, only printing)  : subst_scope.

Notation "x '__etm'" := (@ids _ _ VarInstance_etm x)
( at level 5, format "x __etm", only printing)  : subst_scope.

Notation "x '__etm'" := (var_etm x) ( at level 5, format "x __etm")  :
subst_scope.

#[global]
Instance subst_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_tm s = subst_tm g_tm t')
         (ext_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => ext_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_tm s = ren_tm g_tm t')
         (extRen_tm f_tm g_tm Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_tm)).
Proof.
exact (fun f_tm g_tm Eq_tm s => extRen_tm f_tm g_tm Eq_tm s).
Qed.

#[global]
Instance subst_etm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_etm)).
Proof.
exact (fun f_etm g_etm Eq_etm s t Eq_st =>
       eq_ind s (fun t' => subst_etm f_etm s = subst_etm g_etm t')
         (ext_etm f_etm g_etm Eq_etm s) t Eq_st).
Qed.

#[global]
Instance subst_etm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_etm)).
Proof.
exact (fun f_etm g_etm Eq_etm s => ext_etm f_etm g_etm Eq_etm s).
Qed.

#[global]
Instance ren_etm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_etm)).
Proof.
exact (fun f_etm g_etm Eq_etm s t Eq_st =>
       eq_ind s (fun t' => ren_etm f_etm s = ren_etm g_etm t')
         (extRen_etm f_etm g_etm Eq_etm s) t Eq_st).
Qed.

#[global]
Instance ren_etm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_etm)).
Proof.
exact (fun f_etm g_etm Eq_etm s => extRen_etm f_etm g_etm Eq_etm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_etm, Var, ids, Ren_etm, Ren1, ren1,
                      Up_etm_etm, Up_etm, up_etm, Subst_etm, Subst1, subst1,
                      VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, Up_tm_tm,
                      Up_tm, up_tm, Subst_tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_etm, Var, ids,
                                            Ren_etm, Ren1, ren1, Up_etm_etm,
                                            Up_etm, up_etm, Subst_etm,
                                            Subst1, subst1, VarInstance_tm,
                                            Var, ids, Ren_tm, Ren1, ren1,
                                            Up_tm_tm, Up_tm, up_tm, Subst_tm,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite substSubst_etm_pointwise
                 | progress setoid_rewrite substSubst_etm
                 | progress setoid_rewrite substRen_etm_pointwise
                 | progress setoid_rewrite substRen_etm
                 | progress setoid_rewrite renSubst_etm_pointwise
                 | progress setoid_rewrite renSubst_etm
                 | progress setoid_rewrite renRen'_etm_pointwise
                 | progress setoid_rewrite renRen_etm
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress setoid_rewrite varLRen'_etm_pointwise
                 | progress setoid_rewrite varLRen'_etm
                 | progress setoid_rewrite varL'_etm_pointwise
                 | progress setoid_rewrite varL'_etm
                 | progress setoid_rewrite rinstId'_etm_pointwise
                 | progress setoid_rewrite rinstId'_etm
                 | progress setoid_rewrite instId'_etm_pointwise
                 | progress setoid_rewrite instId'_etm
                 | progress
                    unfold up_tm_tm, upRen_tm_tm, up_etm_etm, upRen_etm_etm,
                     up_ren
                 | progress cbn[subst_tm ren_tm subst_etm ren_etm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_etm, Var, ids, Ren_etm, Ren1, ren1,
                  Up_etm_etm, Up_etm, up_etm, Subst_etm, Subst1, subst1,
                  VarInstance_tm, Var, ids, Ren_tm, Ren1, ren1, Up_tm_tm,
                  Up_tm, up_tm, Subst_tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm;
                  try setoid_rewrite rinstInst'_etm_pointwise;
                  try setoid_rewrite rinstInst'_etm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm;
                  try setoid_rewrite_left rinstInst'_etm_pointwise;
                  try setoid_rewrite_left rinstInst'_etm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

#[global] Hint Opaque subst_etm: rewrite.

#[global] Hint Opaque ren_etm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

