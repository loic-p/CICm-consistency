From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Typing.Rules.
From Stdlib Require Import Arith.

Import UnscopedNotations.
Open Scope list_scope.

(* ================================================================== *)
(* TEST 3: the impredicative encodings of conjunction and disjunction.  *)
(*                                                                    *)
(* `prop` is impredicative and is itself a type of `univ 0`, so `all prop p` *)
(* is again a proposition and the Church encodings go through verbatim:    *)
(*                                                                    *)
(*   conj A B := forall C : Prop. (A -> B -> C) -> C                     *)
(*   disj A B := forall C : Prop. (A -> C) -> (B -> C) -> C              *)
(*                                                                    *)
(* An implication between propositions is the impredicative quantifier     *)
(* over the TYPE of proofs of its premise: `A -> B` is `all (prf A) B`,     *)
(* with B under the new binder.  Proof terms are built from `plam` and      *)
(* `papp`, the forall-introduction and -elimination of the calculus.        *)
(*                                                                    *)
(* Everything is written with explicit de Bruijn indices (no `t ⟨↑⟩` in any  *)
(* definition), so the two beta steps of `conj A B` are pure computation:   *)
(* no substitution lemma is needed anywhere.                               *)
(* ================================================================== *)

(* ---- variables ---- *)

Lemma lk1 G A B : lookup 1 (B :: A :: G) ((A ⟨↑⟩) ⟨↑⟩).
Proof. exact (lookup_S (A :: G) 0 (A ⟨↑⟩) B (lookup_O G A)). Qed.

Lemma lk2 G A B C : lookup 2 (C :: B :: A :: G) (((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof. exact (lookup_S (B :: A :: G) 1 ((A ⟨↑⟩) ⟨↑⟩) C (lk1 G A B)). Qed.

Lemma lk3 G A B C D : lookup 3 (D :: C :: B :: A :: G) ((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof. exact (lookup_S (C :: B :: A :: G) 2 (((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) D (lk2 G A B C)). Qed.

Lemma lk4 G A B C D E :
  lookup 4 (E :: D :: C :: B :: A :: G) (((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof.
  exact (lookup_S (D :: C :: B :: A :: G) 3 ((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) E
           (lk3 G A B C D)).
Qed.

Lemma lk5 G A B C D E F :
  lookup 5 (F :: E :: D :: C :: B :: A :: G) ((((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof.
  exact (lookup_S (E :: D :: C :: B :: A :: G) 4 (((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) F
           (lk4 G A B C D E)).
Qed.

Lemma lk6 G A B C D E F H :
  lookup 6 (H :: F :: E :: D :: C :: B :: A :: G)
    (((((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof.
  exact (lookup_S (F :: E :: D :: C :: B :: A :: G) 5
           ((((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) H (lk5 G A B C D E F)).
Qed.

Lemma lk7 G A B C D E F H I :
  lookup 7 (I :: H :: F :: E :: D :: C :: B :: A :: G)
    ((((((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩).
Proof.
  exact (lookup_S (H :: F :: E :: D :: C :: B :: A :: G) 6
           (((((((A ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) ⟨↑⟩) I (lk6 G A B C D E F H)).
Qed.

Lemma lkS1 G A i (H : lookup i G prop) : lookup (S i) (A :: G) prop.
Proof. exact (lookup_S G i prop A H). Qed.

Ltac lk :=
  first [ exact (lookup_O _ _) | exact (lk1 _ _ _) | exact (lk2 _ _ _ _)
        | exact (lk3 _ _ _ _ _) | exact (lk4 _ _ _ _ _ _)
        | exact (lk5 _ _ _ _ _ _ _) | exact (lk6 _ _ _ _ _ _ _ _)
        | exact (lk7 _ _ _ _ _ _ _ _ _)
        | (repeat apply lkS1); eassumption ].

(* Context well-formedness and the typing of an encoded proposition are both
   syntax-directed.  Every branch fires on a CONCRETE head, so nothing loops. *)
Ltac tystep0 :=
  match goal with
  | |- wfc nil => exact w_nil
  | |- wfc (_ :: _) => eapply w_cons
  | |- ty _ prop _ => apply t_prop
  | |- ty _ (prf _) _ => apply t_prf
  | |- ty _ (all _ _) _ => eapply t_all
  | |- ty _ (pi _ _) _ => eapply t_pi
  | |- ty _ (lam _ _ _) _ => eapply t_lam
  | |- ty _ (var_tm _) _ => eapply t_var; [ | lk ]
  | _ => eassumption
  end.

Ltac tyauto0 := repeat tystep0.

(* ---- the encodings ---- *)

(* conj A B = forall C : Prop. (A -> B -> C) -> C.
   In the body the indices are C=0, B=1, A=2; under the extra binders of
   `A -> B -> _` they shift, which is why the three `var 2`s below are, in
   order, A, B and C. *)
Definition conj_inner_body : tm :=
  all prop
    (all (prf (all (prf (var_tm 2)) (all (prf (var_tm 2)) (var_tm 2))))
       (var_tm 1)).

Definition conj_inner : tm := lam prop prop conj_inner_body.
Definition conj : tm := lam prop (pi prop prop) conj_inner.

(* disj A B = forall C : Prop. (A -> C) -> (B -> C) -> C *)
Definition disj_inner_body : tm :=
  all prop
    (all (prf (all (prf (var_tm 2)) (var_tm 1)))
       (all (prf (all (prf (var_tm 2)) (var_tm 2))) (var_tm 2))).

Definition disj_inner : tm := lam prop prop disj_inner_body.
Definition disj : tm := lam prop (pi prop prop) disj_inner.

Definition conjAt (a b : tm) : tm :=
  app prop prop (app prop (pi prop prop) conj a) b.

Definition disjAt (a b : tm) : tm :=
  app prop prop (app prop (pi prop prop) disj a) b.

(* after the FIRST beta step (A := var i): A has crossed two binders *)
Definition conj_mid_body (i : nat) : tm :=
  all prop
    (all (prf (all (prf (var_tm (S (S i))))
                 (all (prf (var_tm 2)) (var_tm 2))))
       (var_tm 1)).

Definition conj_mid (i : nat) : tm := lam prop prop (conj_mid_body i).

Definition disj_mid_body (i : nat) : tm :=
  all prop
    (all (prf (all (prf (var_tm (S (S i)))) (var_tm 1)))
       (all (prf (all (prf (var_tm 2)) (var_tm 2))) (var_tm 2))).

Definition disj_mid (i : nat) : tm := lam prop prop (disj_mid_body i).

(* after BOTH beta steps: A has crossed one binder, B two *)
Definition conj_v (i j : nat) : tm :=
  all prop
    (all (prf (all (prf (var_tm (S i)))
                 (all (prf (var_tm (S (S j)))) (var_tm 2))))
       (var_tm 1)).

Definition disj_v (i j : nat) : tm :=
  all prop
    (all (prf (all (prf (var_tm (S i))) (var_tm 1)))
       (all (prf (all (prf (var_tm (S (S j)))) (var_tm 2))) (var_tm 2))).

(* ---- the two connectives are well typed ---- *)

Theorem ty_conj G (W : wfc G) : ty G conj (pi prop (pi prop prop)).
Proof. unfold conj, conj_inner, conj_inner_body; tyauto0. Qed.

Theorem ty_disj G (W : wfc G) : ty G disj (pi prop (pi prop prop)).
Proof. unfold disj, disj_inner, disj_inner_body; tyauto0. Qed.

Lemma ty_pipp G (W : wfc G) : ty G (pi prop prop) (univ 0).
Proof. tyauto0. Qed.

Theorem ty_conjAt G (W : wfc G) a b (da : ty G a prop) (db : ty G b prop) :
  ty G (conjAt a b) prop.
Proof.
  unfold conjAt.
  refine (t_app G prop prop _ b 0 (t_prop G W)
            (t_prop _ (w_cons G prop 0 W (t_prop G W))) _ db).
  exact (t_app G prop (pi prop prop) conj a 0 (t_prop G W)
           (ty_pipp _ (w_cons G prop 0 W (t_prop G W))) (ty_conj G W) da).
Qed.

Theorem ty_disjAt G (W : wfc G) a b (da : ty G a prop) (db : ty G b prop) :
  ty G (disjAt a b) prop.
Proof.
  unfold disjAt.
  refine (t_app G prop prop _ b 0 (t_prop G W)
            (t_prop _ (w_cons G prop 0 W (t_prop G W))) _ db).
  exact (t_app G prop (pi prop prop) disj a 0 (t_prop G W)
           (ty_pipp _ (w_cons G prop 0 W (t_prop G W))) (ty_disj G W) da).
Qed.

Ltac tystep :=
  match goal with
  | |- ty _ (conjAt _ _) _ => apply ty_conjAt
  | |- ty _ (disjAt _ _) _ => apply ty_disjAt
  | |- ty _ (plam _ _) _ => refine (t_all_intro _ _ _ _ 0 _ _ _)
  | |- ty _ (conj_v _ _) _ => unfold conj_v
  | |- ty _ (disj_v _ _) _ => unfold disj_v
  | _ => tystep0
  end.

Ltac tyauto := repeat tystep.

(* ---- the two beta steps ---- *)

Theorem cv_conjAt G (W : wfc G) i j
  (Li : lookup i G prop) (Lj : lookup j G prop) :
  cv G (conjAt (var_tm i) (var_tm j)) (conj_v i j) prop.
Proof.
  pose proof (w_cons G prop 0 W (t_prop G W)) as W1.
  pose proof (t_var G i prop W Li) as di.
  pose proof (t_var G j prop W Lj) as dj.
  assert (dinner : ty (prop :: G) conj_inner (pi prop prop))
    by (unfold conj_inner, conj_inner_body; tyauto0).
  assert (dmid : ty G (conj_mid i) (pi prop prop))
    by (unfold conj_mid, conj_mid_body; tyauto0).
  assert (dmidb : ty (prop :: G) (conj_mid_body i) prop)
    by (unfold conj_mid_body; tyauto0).
  unfold conjAt.
  eapply c_trans.
  - refine (c_app G prop prop (app prop (pi prop prop) conj (var_tm i))
              (conj_mid i) (var_tm j) (var_tm j) 0 (t_prop G W) (t_prop _ W1)
              _ dmid _ dj dj (c_refl G (var_tm j) prop dj)).
    + exact (t_app G prop (pi prop prop) conj (var_tm i) 0 (t_prop G W)
               (ty_pipp _ W1) (ty_conj G W) di).
    + exact (c_beta G prop (pi prop prop) conj_inner (var_tm i) 0 (t_prop G W)
               (ty_pipp _ W1) dinner di).
  - exact (c_beta G prop prop (conj_mid_body i) (var_tm j) 0 (t_prop G W)
             (t_prop _ W1) dmidb dj).
Qed.

Theorem cv_disjAt G (W : wfc G) i j
  (Li : lookup i G prop) (Lj : lookup j G prop) :
  cv G (disjAt (var_tm i) (var_tm j)) (disj_v i j) prop.
Proof.
  pose proof (w_cons G prop 0 W (t_prop G W)) as W1.
  pose proof (t_var G i prop W Li) as di.
  pose proof (t_var G j prop W Lj) as dj.
  assert (dinner : ty (prop :: G) disj_inner (pi prop prop))
    by (unfold disj_inner, disj_inner_body; tyauto0).
  assert (dmid : ty G (disj_mid i) (pi prop prop))
    by (unfold disj_mid, disj_mid_body; tyauto0).
  assert (dmidb : ty (prop :: G) (disj_mid_body i) prop)
    by (unfold disj_mid_body; tyauto0).
  unfold disjAt.
  eapply c_trans.
  - refine (c_app G prop prop (app prop (pi prop prop) disj (var_tm i))
              (disj_mid i) (var_tm j) (var_tm j) 0 (t_prop G W) (t_prop _ W1)
              _ dmid _ dj dj (c_refl G (var_tm j) prop dj)).
    + exact (t_app G prop (pi prop prop) disj (var_tm i) 0 (t_prop G W)
               (ty_pipp _ W1) (ty_disj G W) di).
    + exact (c_beta G prop (pi prop prop) disj_inner (var_tm i) 0 (t_prop G W)
               (ty_pipp _ W1) dinner di).
  - exact (c_beta G prop prop (disj_mid_body i) (var_tm j) 0 (t_prop G W)
             (t_prop _ W1) dmidb dj).
Qed.

Ltac intro_step := refine (t_all_intro _ _ _ _ 0 _ _ _); [tyauto | tyauto |].

(* ================================================================== *)
(* THE INTRODUCTION RULES                                              *)
(* ================================================================== *)

(* forall A B : Prop. A -> B -> conj A B *)
Definition conj_intro_prop : tm :=
  all prop (all prop
    (all (prf (var_tm 1)) (all (prf (var_tm 1)) (conjAt (var_tm 3) (var_tm 2))))).

Definition conj_intro_tm : tm :=
  plam prop (plam prop (plam (prf (var_tm 1)) (plam (prf (var_tm 1))
    (plam prop
       (plam (prf (all (prf (var_tm 4)) (all (prf (var_tm 4)) (var_tm 2))))
          (papp (papp (var_tm 0) (var_tm 3)) (var_tm 2))))))).

Theorem ty_conj_intro G (W : wfc G) : ty G conj_intro_tm (prf conj_intro_prop).
Proof.
  unfold conj_intro_tm, conj_intro_prop.
  intro_step. intro_step. intro_step. intro_step.
  (* prf B :: prf A :: prop :: prop :: G, at prf (conj A B) *)
  refine (t_conv _ _ (prf (conj_v 3 2)) (prf (conjAt (var_tm 3) (var_tm 2))) 0
            _ _ _ _); [| tyauto | tyauto |].
  - unfold conj_v.
    intro_step. intro_step.
    (* ... |- papp (papp f a) b : prf C *)
    refine (t_all_elim _ (prf (var_tm 4)) (var_tm 2) (papp (var_tm 0) (var_tm 3))
              (var_tm 2) 0 _ _ _ _); [tyauto | tyauto | | tyauto].
    refine (t_all_elim _ (prf (var_tm 5)) (all (prf (var_tm 5)) (var_tm 3))
              (var_tm 0) (var_tm 3) 0 _ _ _ _); [tyauto | tyauto | tyauto | tyauto].
  - refine (c_prf _ (conj_v 3 2) (conjAt (var_tm 3) (var_tm 2)) _ _ _);
      [tyauto | tyauto |].
    apply c_sym; apply cv_conjAt; [tyauto | lk | lk].
Qed.

(* forall A B : Prop. A -> disj A B *)
Definition disj_intro1_prop : tm :=
  all prop (all prop (all (prf (var_tm 1)) (disjAt (var_tm 2) (var_tm 1)))).

Definition disj_intro1_tm : tm :=
  plam prop (plam prop (plam (prf (var_tm 1))
    (plam prop
       (plam (prf (all (prf (var_tm 3)) (var_tm 1)))
          (plam (prf (all (prf (var_tm 3)) (var_tm 2)))
             (papp (var_tm 1) (var_tm 3))))))).

Theorem ty_disj_intro1 G (W : wfc G) : ty G disj_intro1_tm (prf disj_intro1_prop).
Proof.
  unfold disj_intro1_tm, disj_intro1_prop.
  intro_step. intro_step. intro_step.
  refine (t_conv _ _ (prf (disj_v 2 1)) (prf (disjAt (var_tm 2) (var_tm 1))) 0
            _ _ _ _); [| tyauto | tyauto |].
  - unfold disj_v.
    intro_step. intro_step. intro_step.
    refine (t_all_elim _ (prf (var_tm 5)) (var_tm 3) (var_tm 1) (var_tm 3) 0
              _ _ _ _); [tyauto | tyauto | tyauto | tyauto].
  - refine (c_prf _ (disj_v 2 1) (disjAt (var_tm 2) (var_tm 1)) _ _ _);
      [tyauto | tyauto |].
    apply c_sym; apply cv_disjAt; [tyauto | lk | lk].
Qed.

(* forall A B : Prop. B -> disj A B *)
Definition disj_intro2_prop : tm :=
  all prop (all prop (all (prf (var_tm 0)) (disjAt (var_tm 2) (var_tm 1)))).

Definition disj_intro2_tm : tm :=
  plam prop (plam prop (plam (prf (var_tm 0))
    (plam prop
       (plam (prf (all (prf (var_tm 3)) (var_tm 1)))
          (plam (prf (all (prf (var_tm 3)) (var_tm 2)))
             (papp (var_tm 0) (var_tm 3))))))).

Theorem ty_disj_intro2 G (W : wfc G) : ty G disj_intro2_tm (prf disj_intro2_prop).
Proof.
  unfold disj_intro2_tm, disj_intro2_prop.
  intro_step. intro_step. intro_step.
  refine (t_conv _ _ (prf (disj_v 2 1)) (prf (disjAt (var_tm 2) (var_tm 1))) 0
            _ _ _ _); [| tyauto | tyauto |].
  - unfold disj_v.
    intro_step. intro_step. intro_step.
    refine (t_all_elim _ (prf (var_tm 4)) (var_tm 3) (var_tm 0) (var_tm 3) 0
              _ _ _ _); [tyauto | tyauto | tyauto | tyauto].
  - refine (c_prf _ (disj_v 2 1) (disjAt (var_tm 2) (var_tm 1)) _ _ _);
      [tyauto | tyauto |].
    apply c_sym; apply cv_disjAt; [tyauto | lk | lk].
Qed.

(* ================================================================== *)
(* THE ELIMINATION RULES                                               *)
(* ================================================================== *)

(* the two projections use the encoded pair at C := A and C := B *)
Definition kfst : tm := plam (prf (var_tm 2)) (plam (prf (var_tm 2)) (var_tm 1)).
Definition ksnd : tm := plam (prf (var_tm 2)) (plam (prf (var_tm 2)) (var_tm 0)).

(* forall A B : Prop. conj A B -> A *)
Definition conj_elim1_prop : tm :=
  all prop (all prop (all (prf (conjAt (var_tm 1) (var_tm 0))) (var_tm 2))).

Definition conj_elim1_tm : tm :=
  plam prop (plam prop (plam (prf (conjAt (var_tm 1) (var_tm 0)))
    (papp (papp (var_tm 0) (var_tm 2)) kfst))).

Theorem ty_conj_elim1 G (W : wfc G) : ty G conj_elim1_tm (prf conj_elim1_prop).
Proof.
  unfold conj_elim1_tm, conj_elim1_prop.
  intro_step. intro_step. intro_step.
  (* prf (conj A B) :: prop :: prop :: G  |-  papp (papp h A) kfst : prf A *)
  refine (t_all_elim _
            (prf (all (prf (var_tm 2)) (all (prf (var_tm 2)) (var_tm 4))))
            (var_tm 3) (papp (var_tm 0) (var_tm 2)) kfst 0 _ _ _ _);
    [tyauto | tyauto | | unfold kfst; tyauto].
  refine (t_all_elim _ prop
            (all (prf (all (prf (var_tm 3)) (all (prf (var_tm 3)) (var_tm 2))))
               (var_tm 1))
            (var_tm 0) (var_tm 2) 0 _ _ _ _); [tyauto | tyauto | | tyauto].
  (* the hypothesis, read through the two beta steps *)
  refine (t_conv _ (var_tm 0) (prf (conjAt (var_tm 2) (var_tm 1)))
            (prf (conj_v 2 1)) 0 _ _ _ _); [tyauto | tyauto | tyauto |].
  refine (c_prf _ (conjAt (var_tm 2) (var_tm 1)) (conj_v 2 1) _ _ _);
    [tyauto | tyauto |].
  apply cv_conjAt; [tyauto | lk | lk].
Qed.

(* forall A B : Prop. conj A B -> B *)
Definition conj_elim2_prop : tm :=
  all prop (all prop (all (prf (conjAt (var_tm 1) (var_tm 0))) (var_tm 1))).

Definition conj_elim2_tm : tm :=
  plam prop (plam prop (plam (prf (conjAt (var_tm 1) (var_tm 0)))
    (papp (papp (var_tm 0) (var_tm 1)) ksnd))).

Theorem ty_conj_elim2 G (W : wfc G) : ty G conj_elim2_tm (prf conj_elim2_prop).
Proof.
  unfold conj_elim2_tm, conj_elim2_prop.
  intro_step. intro_step. intro_step.
  refine (t_all_elim _
            (prf (all (prf (var_tm 2)) (all (prf (var_tm 2)) (var_tm 3))))
            (var_tm 2) (papp (var_tm 0) (var_tm 1)) ksnd 0 _ _ _ _);
    [tyauto | tyauto | | unfold ksnd; tyauto].
  refine (t_all_elim _ prop
            (all (prf (all (prf (var_tm 3)) (all (prf (var_tm 3)) (var_tm 2))))
               (var_tm 1))
            (var_tm 0) (var_tm 1) 0 _ _ _ _); [tyauto | tyauto | | tyauto].
  refine (t_conv _ (var_tm 0) (prf (conjAt (var_tm 2) (var_tm 1)))
            (prf (conj_v 2 1)) 0 _ _ _ _); [tyauto | tyauto | tyauto |].
  refine (c_prf _ (conjAt (var_tm 2) (var_tm 1)) (conj_v 2 1) _ _ _);
    [tyauto | tyauto |].
  apply cv_conjAt; [tyauto | lk | lk].
Qed.

(* forall A B C : Prop. (A -> C) -> (B -> C) -> disj A B -> C *)
Definition disj_elim_prop : tm :=
  all prop (all prop (all prop
    (all (prf (all (prf (var_tm 2)) (var_tm 1)))
       (all (prf (all (prf (var_tm 2)) (var_tm 2)))
          (all (prf (disjAt (var_tm 4) (var_tm 3))) (var_tm 3)))))).

Definition disj_elim_tm : tm :=
  plam prop (plam prop (plam prop
    (plam (prf (all (prf (var_tm 2)) (var_tm 1)))
       (plam (prf (all (prf (var_tm 2)) (var_tm 2)))
          (plam (prf (disjAt (var_tm 4) (var_tm 3)))
             (papp (papp (papp (var_tm 0) (var_tm 3)) (var_tm 2)) (var_tm 1))))))).

Theorem ty_disj_elim G (W : wfc G) : ty G disj_elim_tm (prf disj_elim_prop).
Proof.
  unfold disj_elim_tm, disj_elim_prop.
  intro_step. intro_step. intro_step. intro_step. intro_step. intro_step.
  (* h : disj A B, f : A -> C, g : B -> C  |-  h C f g : prf C *)
  refine (t_all_elim _ (prf (all (prf (var_tm 4)) (var_tm 4))) (var_tm 4)
            (papp (papp (var_tm 0) (var_tm 3)) (var_tm 2)) (var_tm 1) 0
            _ _ _ _); [tyauto | tyauto | | tyauto].
  refine (t_all_elim _ (prf (all (prf (var_tm 5)) (var_tm 4)))
            (all (prf (all (prf (var_tm 5)) (var_tm 5))) (var_tm 5))
            (papp (var_tm 0) (var_tm 3)) (var_tm 2) 0 _ _ _ _);
    [tyauto | tyauto | | tyauto].
  refine (t_all_elim _ prop
            (all (prf (all (prf (var_tm 6)) (var_tm 1)))
               (all (prf (all (prf (var_tm 6)) (var_tm 2))) (var_tm 2)))
            (var_tm 0) (var_tm 3) 0 _ _ _ _); [tyauto | tyauto | | tyauto].
  refine (t_conv _ (var_tm 0) (prf (disjAt (var_tm 5) (var_tm 4)))
            (prf (disj_v 5 4)) 0 _ _ _ _); [tyauto | tyauto | tyauto |].
  refine (c_prf _ (disjAt (var_tm 5) (var_tm 4)) (disj_v 5 4) _ _ _);
    [tyauto | tyauto |].
  apply cv_disjAt; [tyauto | lk | lk].
Qed.

(* ================================================================== *)
(* All of it in the empty context: six closed proof terms.              *)
(* ================================================================== *)

Corollary conj_is_a_connective : ty nil conj (pi prop (pi prop prop)).
Proof. exact (ty_conj nil w_nil). Qed.

Corollary disj_is_a_connective : ty nil disj (pi prop (pi prop prop)).
Proof. exact (ty_disj nil w_nil). Qed.

Corollary closed_conj_intro : ty nil conj_intro_tm (prf conj_intro_prop).
Proof. exact (ty_conj_intro nil w_nil). Qed.

Corollary closed_conj_elim1 : ty nil conj_elim1_tm (prf conj_elim1_prop).
Proof. exact (ty_conj_elim1 nil w_nil). Qed.

Corollary closed_conj_elim2 : ty nil conj_elim2_tm (prf conj_elim2_prop).
Proof. exact (ty_conj_elim2 nil w_nil). Qed.

Corollary closed_disj_intro1 : ty nil disj_intro1_tm (prf disj_intro1_prop).
Proof. exact (ty_disj_intro1 nil w_nil). Qed.

Corollary closed_disj_intro2 : ty nil disj_intro2_tm (prf disj_intro2_prop).
Proof. exact (ty_disj_intro2 nil w_nil). Qed.

Corollary closed_disj_elim : ty nil disj_elim_tm (prf disj_elim_prop).
Proof. exact (ty_disj_elim nil w_nil). Qed.
