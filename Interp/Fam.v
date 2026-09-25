From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER Codes.Levels.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build.
From Stdlib Require Import Arith Lia.

(* The semantic value of a type is an element of the decoding of the universe
   it lives in, that is, a coherent family of codes -- a UFam.  This file
   builds one for each type former.  A family constructor is exactly what the
   fundamental lemma will return for a type, so these are the clauses of the
   interpretation, stripped of the syntax. *)

Definition kUFam (k : nat) (u : etm) : Type := UFam (lvl k) k u.

Definition kAcc {k u} (F : kUFam k u) : Acc prec u := uf_acc F.
Definition kAt {k u} (F : kUFam k u) : Code k (rk u (kAcc F)) := uf_at F.
Definition kElAt {k u} (F : kUFam k u) (w : etm) : Type :=
  (kUst k (rk u (kAcc F))).(StEl) (kAt F) w.
Definition kEqAt {k u} (F : kUFam k u) w (x : kElAt F w) w' (x' : kElAt F w') : Prop :=
  (kUst k (rk u (kAcc F))).(StEq) (kAt F) w x w' x'.

(* Transporting an element between two instances of one family: the family's
   own coherence, transported by Codes/Iso.v. *)
Definition famTo {k u} (F : kUFam k u) v h pf w
  (x : (kUst k (rk v h)).(StEl) (uf_c F v h pf) w) : kElAt F w :=
  cto (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
      (uf_c F v h pf) (kAt F) (uf_coh F v h pf u (kAcc F) (evalAg_refl u)) w x.

Definition famFrom {k u} (F : kUFam k u) v h pf w (x : kElAt F w)
  : (kUst k (rk v h)).(StEl) (uf_c F v h pf) w :=
  cto (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
      (kAt F) (uf_c F v h pf) (uf_coh F u (kAcc F) (evalAg_refl u) v h pf) w x.

(* ------------------------------------------------------------------ *)
(* Layer-1 facts each constructor needs of its shadow. *)

Lemma eqty_nat k v v' : eval v enat -> eval v' enat -> eqty k v v'.
Proof. intros H H'; exists NatPer; apply LR_nat; assumption. Qed.

Lemma eqty_prop k v v' : eval v eprop -> eval v' eprop -> eqty k v v'.
Proof. intros H H'; exists PR; apply LR_prop; assumption. Qed.

Lemma eqty_prf k v v' p p' : eval v (eprf p) -> eval v' (eprf p') -> PR p p' -> eqty k v v'.
Proof. intros H H' HP; exists TruePer; eapply LR_prf; eassumption. Qed.

Lemma eqty_univ k m v v' : m < k -> eval v (euniv m) -> eval v' (euniv m) -> eqty k v v'.
Proof.
  intros Hm H H'; exists (fun C C' => exists P, below k m C C' P); apply LR_univ; assumption.
Qed.

Lemma eqty_ne k v v' N N' : eval v N -> eval v' N' -> stuck N -> stuck N' -> eqty k v v'.
Proof. intros; exists NePer; eapply LR_ne; eassumption. Qed.

Definition whnf_nat : whnf enat := or_introl v_nat.
Definition whnf_prop : whnf eprop := or_introl v_prop.
Definition whnf_prf p : whnf (eprf p) := or_introl (v_prf p).
Definition whnf_univ m : whnf (euniv m) := or_introl (v_univ m).
Definition whnf_pi A B : whnf (epi A B) := or_introl (v_pi A B).
Definition whnf_sig A B : whnf (esig A B) := or_introl (v_sig A B).

(* ------------------------------------------------------------------ *)
(* The families for the formers with no components. *)

Definition natFam (k : nat) : kUFam k enat.
Proof.
  unshelve refine (Build_UFam (lvl k) k enat
    (fun v h pf => mkCode (mkNat k (rk v h) v (pf enat (eval_whnf enat whnf_nat)))) _ _ _ _).
  - apply eqty_nat; apply eval_whnf; exact whnf_nat.
  - intros v h pf; apply eqty_nat; [apply pf; apply eval_whnf; exact whnf_nat
                                   | apply eval_whnf; exact whnf_nat].
  - intros v h pf v' h' pf'.
    exists k; apply eqty_nat; apply pf || apply pf'; apply eval_whnf; exact whnf_nat.
  - intros v h pf; apply (kIdP_of k (rk v h)); exact I.
Defined.

Definition propFam (k : nat) : kUFam k eprop.
Proof.
  unshelve refine (Build_UFam (lvl k) k eprop
    (fun v h pf => mkCode (mkProp k (rk v h) v (pf eprop (eval_whnf eprop whnf_prop)))) _ _ _ _).
  - apply eqty_prop; apply eval_whnf; exact whnf_prop.
  - intros v h pf; apply eqty_prop; [apply pf; apply eval_whnf; exact whnf_prop
                                    | apply eval_whnf; exact whnf_prop].
  - intros v h pf v' h' pf'.
    exists k; apply eqty_prop; apply pf || apply pf'; apply eval_whnf; exact whnf_prop.
  - intros v h pf; apply (kIdP_of k (rk v h)); exact I.
Defined.

Definition prfFam (k : nat) (p : etm) (Hp : PR p p) (H : Prop) : kUFam k (eprf p).
Proof.
  unshelve refine (Build_UFam (lvl k) k (eprf p)
    (fun v h pf => mkCode (mkPrf k (rk v h) v p (pf (eprf p) (eval_whnf _ (whnf_prf p))) H))
    _ _ _ _).
  - eapply eqty_prf; [apply eval_whnf; exact (whnf_prf p)
                     | apply eval_whnf; exact (whnf_prf p) | exact Hp].
  - intros v h pf; eapply eqty_prf;
      [apply pf; apply eval_whnf; exact (whnf_prf p)
      | apply eval_whnf; exact (whnf_prf p) | exact Hp].
  - intros v h pf v' h' pf'; split; [| split; auto].
    exists k; eapply eqty_prf;
      [apply pf; apply eval_whnf; exact (whnf_prf p)
      | apply pf'; apply eval_whnf; exact (whnf_prf p) | exact Hp].
  - intros v h pf; apply (kIdP_of k (rk v h)); exact I.
Defined.

Definition univFam (k : nat) : kUFam (S k) (euniv k).
Proof.
  unshelve refine (Build_UFam (lvl (S k)) (S k) (euniv k)
    (fun v h pf => mkCode (mkUniv (S k) (rk v h) v k (kOK_of (S k) k (Nat.lt_succ_diag_r k))
                             (pf (euniv k) (eval_whnf _ (whnf_univ k))))) _ _ _ _).
  - eapply eqty_univ; [apply Nat.lt_succ_diag_r | apply eval_whnf; exact (whnf_univ k)
                      | apply eval_whnf; exact (whnf_univ k)].
  - intros v h pf; eapply eqty_univ;
      [apply Nat.lt_succ_diag_r | apply pf; apply eval_whnf; exact (whnf_univ k)
      | apply eval_whnf; exact (whnf_univ k)].
  - intros v h pf v' h' pf'; split; [| reflexivity].
    exists (S k); eapply eqty_univ;
      [apply Nat.lt_succ_diag_r | apply pf; apply eval_whnf; exact (whnf_univ k)
      | apply pf'; apply eval_whnf; exact (whnf_univ k)].
  - intros v h pf; apply (kIdP_of (S k) (rk v h)); exact I.
Defined.

Definition neFam (k : nat) (N : etm) (sN : stuck N) : kUFam k N.
Proof.
  unshelve refine (Build_UFam (lvl k) k N
    (fun v h pf => mkCode (mkNe k (rk v h) v N (pf N (eval_whnf N (or_intror sN))) sN))
    _ _ _ _).
  - eapply eqty_ne; [apply eval_whnf; exact (or_intror sN)
                    | apply eval_whnf; exact (or_intror sN) | exact sN | exact sN].
  - intros v h pf; eapply eqty_ne;
      [apply pf; apply eval_whnf; exact (or_intror sN)
      | apply eval_whnf; exact (or_intror sN) | exact sN | exact sN].
  - intros v h pf v' h' pf'.
    exists k; eapply eqty_ne;
      [apply pf; apply eval_whnf; exact (or_intror sN)
      | apply pf'; apply eval_whnf; exact (or_intror sN) | exact sN | exact sN].
  - intros v h pf; apply (kIdP_of k (rk v h)); exact I.
Defined.

(* Moving elements between instances of a family respects the equality, and
   turns a heterogeneous relatedness between two instances into one between
   the canonical images.  Both are functoriality of the canonical transport. *)
Lemma famTo_eq {k u0} (F : kUFam k u0) v h pf w x w' x' :
  (kUst k (rk v h)).(StEq) (uf_c F v h pf) w x w' x' ->
  kEqAt F w (famTo F v h pf w x) w' (famTo F v h pf w' x').
Proof. apply (cto_eq (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)). Qed.

Lemma famTo_het {k u0} (F : kUFam k u0) v1 h1 pf1 v2 h2 pf2 w x w' y
  (P : iso (uf_c F v1 h1 pf1) (uf_c F v2 h2 pf2))
  (HP : (kUst k (rk v2 h2)).(StEq) (uf_c F v2 h2 pf2) w
          (cto (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
             (uf_c F v1 h1 pf1) (uf_c F v2 h2 pf2) P w x) w' y) :
  kEqAt F w (famTo F v1 h1 pf1 w x) w' (famTo F v2 h2 pf2 w' y).
Proof.
  pose proof (proj2 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
                       (osucc (rk u0 (kAcc F))) (inl (kAt F)))) as Ht.
  unfold EqTrans in Ht.
  eapply Ht.
  - apply (cto_fun (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
             (uf_c F v1 h1 pf1) (uf_c F v2 h2 pf2) (kAt F)
             P (uf_coh F v2 h2 pf2 u0 (kAcc F) (evalAg_refl u0))
             (uf_coh F v1 h1 pf1 u0 (kAcc F) (evalAg_refl u0))).
  - apply (cto_eq (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)); exact HP.
Qed.

Lemma kEqAt_sym {k u0} (F : kUFam k u0) w x w' x' :
  kEqAt F w x w' x' -> kEqAt F w' x' w x.
Proof.
  apply (proj1 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
                  (osucc (rk u0 (kAcc F))) (inl (kAt F)))).
Qed.

Lemma kEqAt_trans {k u0} (F : kUFam k u0) w x w' x' w'' x'' :
  kEqAt F w x w' x' -> kEqAt F w' x' w'' x'' -> kEqAt F w x w'' x''.
Proof.
  apply (proj2 (eqs_PER (kU k) (kUEq k) (kOK k) (ksym k) (ktrans k)
                  (osucc (rk u0 (kAcc F))) (inl (kAt F)))).
Qed.

(* Two isomorphic families have layer-1 equal realisers.  This is the only way
   the interpretation ever gets a layer-1 equation out of an isomorphism, and
   it is what functionality needs to feed its own induction hypotheses. *)
Lemma iso_ty {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  iso (kAt F) (kAt F') -> tyeq u u'.
Proof.
  intros H.
  eapply tyeq_trans;
    [ apply tyeq_sym;
      exact (ex_intro _ k (uf_sh F u (kAcc F) (evalAg_refl u))) |].
  eapply tyeq_trans;
    [ exact (iso_sh _ _ H)
    | exact (ex_intro _ k (uf_sh F' u' (kAcc F') (evalAg_refl u'))) ].
Qed.
