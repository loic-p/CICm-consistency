From CICM Require Import Syntax.Ann.
From CICM Require Import Typing.Rules.
From Stdlib Require Import Arith.

Open Scope list_scope.

(* ================================================================== *)
(* TEST 4: ACZEL SETS.                                                 *)
(*                                                                    *)
(* A set is a TYPE of indices together with a family of sets indexed   *)
(* by it -- Aczel's V, which is the W type                             *)
(*                                                                    *)
(*     V  :=  W (A : U_0). A                                           *)
(*                                                                    *)
(* the label type being the universe itself and the branching type at  *)
(* a label A being A.  This is the construction the HETEROGENEOUS      *)
(* levels of v2 were needed for, and it is worth spelling out why: the *)
(* label type U_0 lives at level 1 and the branching type A at level   *)
(* 0, so with W (or Pi) homogeneous in its components, as in v1, V     *)
(* cannot be formed at all.  Each of the three formers below uses the  *)
(* heterogeneity again -- `pi 1 A V` from a level-0 domain to a        *)
(* level-1 codomain, and the motive of each recursion.                 *)
(*                                                                    *)
(* Everything is closed object-language syntax: the constructions and  *)
(* their typing derivations, with no appeal to the model.              *)
(* ================================================================== *)

Lemma le01 : 0 <= 1. Proof. apply Nat.le_0_l. Qed.

(* ------------------------------------------------------------------ *)
(* V, and the constructor of sets                                      *)
(* ------------------------------------------------------------------ *)

Definition V : tm := wt 1 (UU 0) (var_tm 0).

Lemma ty_U G (W : wfc G) : ty G (UU 0) (UU 1).
Proof. exact (t_univ G 1 0 (le_n 1) W). Qed.

Lemma wfc_U G (W : wfc G) : wfc (UU 0 :: G).
Proof. exact (w_cons G (UU 0) 1 W (ty_U G W)). Qed.

(* the branching type of V: the label itself *)
Lemma ty_br G (W : wfc G) : ty (UU 0 :: G) (var_tm 0) (UU 0).
Proof. exact (t_var (UU 0 :: G) 0 (UU 0) (wfc_U G W) (lookup_O G (UU 0))). Qed.

Lemma ty_V G (W : wfc G) : ty G V (UU 1).
Proof.
  exact (t_w G 1 1 0 (UU 0) (var_tm 0) (le_n 1) le01 (ty_U G W) (ty_br G W)).
Qed.

Lemma wfc_V G (W : wfc G) : wfc (V :: G).
Proof. exact (w_cons G V 1 W (ty_V G W)). Qed.

(* `aset A f` is the set whose elements are the f a for a : A *)
Definition aset (A f : tm) : tm := sup 1 (UU 0) (var_tm 0) A f.

Lemma ty_aset G (W : wfc G) A f
  (dA : ty G A (UU 0)) (df : ty G f (pi 1 A V)) : ty G (aset A f) V.
Proof.
  exact (t_sup G 1 1 0 (UU 0) (var_tm 0) A f (le_n 1) le01
           (ty_U G W) (ty_br G W) dA df).
Qed.

(* a family of sets indexed by A, as a function A -> V: the domain sits at
   level 0 and the codomain at level 1, so this Pi is heterogeneous too *)
Lemma ty_fam G (W : wfc G) A t (dA : ty G A (UU 0))
  (dt : ty (A :: G) t V) : ty G (lam 1 A V t) (pi 1 A V).
Proof.
  exact (t_lam G 1 0 1 A V t le01 (le_n 1) dA
           (ty_V _ (w_cons G A 0 W dA)) dt).
Qed.

(* ------------------------------------------------------------------ *)
(* The empty set                                                       *)
(* ------------------------------------------------------------------ *)

Definition Bot : tm := prf 0 (false_ 0).

Lemma ty_Bot G (W : wfc G) : ty G Bot (UU 0).
Proof. exact (t_prf G 0 0 (false_ 0) (le_n 0) (t_false G 0 W)). Qed.

Definition emptyset : tm := aset Bot (lam 1 Bot V (absurd V (var_tm 0))).

Lemma ty_emptyset G (W : wfc G) : ty G emptyset V.
Proof.
  pose proof (w_cons G Bot 0 W (ty_Bot G W)) as WB.
  refine (ty_aset G W Bot _ (ty_Bot G W) _).
  refine (ty_fam G W Bot _ (ty_Bot G W) _).
  exact (t_absurd _ V (var_tm 0) 1 0 (ty_V _ WB)
           (t_var _ 0 Bot WB (lookup_O G Bot))).
Qed.

(* ------------------------------------------------------------------ *)
(* Singleton, pairing, and the set of natural numbers                  *)
(* ------------------------------------------------------------------ *)

(* {x}: indexed by N with the constant family.  Any inhabited index type
   would do -- as a SET, {x, x, x, ...} IS {x} -- and N is the one the
   calculus hands us with no further work. *)
Definition singleton (x : tm) : tm :=
  aset (nat_ 0) (lam 1 (nat_ 0) V (x ⟨↑⟩)).

Lemma ty_singleton G (W : wfc G) x
  (dx : ty (nat_ 0 :: G) (x ⟨↑⟩) V) : ty G (singleton x) V.
Proof. exact (ty_aset G W _ _ (t_nat G 0 W) (ty_fam G W _ _ (t_nat G 0 W) dx)). Qed.

(* {x, y}: indexed by N again, with 0 |-> x and every successor |-> y.
   This is the LARGE ELIMINATION of N in miniature -- the motive V is a type,
   not a proposition -- which is what lets a finite family be written down at
   all without a finite index type. *)
Definition pairing (x y : tm) : tm :=
  aset (nat_ 0)
       (lam 1 (nat_ 0) V (natrec V (x ⟨↑⟩) (y ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) (var_tm 0))).

Lemma ty_pairing G (W : wfc G) x y
  (dx : ty (nat_ 0 :: G) (x ⟨↑⟩) V)
  (dy : ty (V :: nat_ 0 :: nat_ 0 :: G) (y ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) V) :
  ty G (pairing x y) V.
Proof.
  pose proof (w_cons G (nat_ 0) 0 W (t_nat G 0 W)) as W1.
  refine (ty_aset G W _ _ (t_nat G 0 W) (ty_fam G W _ _ (t_nat G 0 W) _)).
  refine (t_natrec (nat_ 0 :: G) V (x ⟨↑⟩) (y ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) (var_tm 0) 1 0
            (ty_V _ (w_cons _ (nat_ 0) 0 W1 (t_nat _ 0 W1))) dx dy _).
  exact (t_var _ 0 (nat_ 0) W1 (lookup_O G (nat_ 0))).
Qed.

(* The set of natural numbers, Zermelo style: 0 is the empty set and n+1 is
   {n}.  (Von Neumann's n+1 = n u {n} needs a binary union, i.e. a sum type
   in the index position; see the union below for what that would take.) *)
Definition zerm : tm := natrec V emptyset (singleton (var_tm 0)) (var_tm 0).

Definition omega : tm := aset (nat_ 0) (lam 1 (nat_ 0) V zerm).

Lemma ty_zerm G (W : wfc G) : ty (nat_ 0 :: G) zerm V.
Proof.
  pose proof (w_cons G (nat_ 0) 0 W (t_nat G 0 W)) as W1.
  pose proof (w_cons _ (nat_ 0) 0 W1 (t_nat _ 0 W1)) as W2.
  refine (t_natrec (nat_ 0 :: G) V emptyset (singleton (var_tm 0)) (var_tm 0) 1 0
            (ty_V _ W2) (ty_emptyset _ W1) _ _).
  - (* the step: the singleton of the recursive result *)
    pose proof (w_cons _ V 1 W2 (ty_V _ W2)) as W3.
    refine (ty_singleton _ W3 _ _).
    exact (t_var _ 1 V (w_cons _ (nat_ 0) 0 W3 (t_nat _ 0 W3))
             (lookup_S _ 0 (V ⟨↑⟩) (nat_ 0) (lookup_O _ V))).
  - exact (t_var _ 0 (nat_ 0) W1 (lookup_O G (nat_ 0))).
Qed.

Lemma ty_omega G (W : wfc G) : ty G omega V.
Proof.
  exact (ty_aset G W _ _ (t_nat G 0 W)
           (ty_fam G W _ _ (t_nat G 0 W) (ty_zerm G W))).
Qed.

(* all three are closed sets *)
Definition closed_emptyset : ty nil emptyset V := ty_emptyset nil w_nil.
Definition closed_omega : ty nil omega V := ty_omega nil w_nil.

(* ------------------------------------------------------------------ *)
(* Bisimulation, by a double recursion into Prop                       *)
(* ------------------------------------------------------------------ *)

(* Extensional equality of Aczel sets is bisimulation:

     bisim (sup A f) (sup B g)  =  (forall a:A. exists b:B. bisim (f a) (g b))
                                /\ (forall b:B. exists a:A. bisim (f a) (g b))

   which is a recursion on the first argument -- with motive V -> Prop, so the
   step's induction hypothesis is exactly `fun a => bisim (f a)` -- inside
   which a second recursion inspects the shape of the second argument and
   ignores its own induction hypothesis.  Both motives are Pi types with
   components at different levels (V at 1, Prop at 0), which is again the
   heterogeneity.

   /\ and exists are the impredicative encodings; they are written out at
   concrete de Bruijn indices, parameterised by the number `d` of binders
   they sit under, so that no renaming appears anywhere. *)

(* In the step of the inner recursion the context is

     IHy :: g :: B :: y :: IH :: f :: A :: x :: Gamma
      0      1    2    3    4     5    6    7

   with IH : Pi (a : A). V -> Prop and g : B -> V. *)

(* `IH a (g b)`, with a and b the two innermost bound variables *)
Definition bis_app (d a b : nat) : tm :=
  app V (prop 0)
      (app (var_tm (9 + d)) (pi 1 V (prop 0)) (var_tm (7 + d)) (var_tm a))
      (app (var_tm (5 + d)) V (var_tm (4 + d)) (var_tm b)).

(* forall a : A. exists b : B. IH a (g b) *)
Definition bis_half1 (d : nat) : tm :=
  all 0 (var_tm (6 + d))
    (all 0 (prop 0)
       (all 0 (prf 0 (all 0 (var_tm (4 + d))
                        (all 0 (prf 0 (bis_app d 2 0)) (var_tm 2))))
          (var_tm 1))).

(* forall b : B. exists a : A. IH a (g b) *)
Definition bis_half2 (d : nat) : tm :=
  all 0 (var_tm (2 + d))
    (all 0 (prop 0)
       (all 0 (prf 0 (all 0 (var_tm (8 + d))
                        (all 0 (prf 0 (bis_app d 0 2)) (var_tm 2))))
          (var_tm 1))).

(* their conjunction, again impredicatively *)
Definition bis_step2 : tm :=
  all 0 (prop 0)
    (all 0 (prf 0 (all 0 (prf 0 (bis_half1 1))
                     (all 0 (prf 0 (bis_half2 2)) (var_tm 2))))
       (var_tm 1)).

(* the inner recursion, on the second set *)
Definition bis_inner : tm :=
  wrec (UU 0) (var_tm 0) (prop 0) bis_step2 (var_tm 0).

(* the outer step: a function of the second set *)
Definition bis_step : tm := lam 1 V (prop 0) bis_inner.

Definition bisim : tm :=
  lam 1 V (pi 1 V (prop 0))
    (wrec (UU 0) (var_tm 0) (pi 1 V (prop 0)) bis_step (var_tm 0)).

(* ---- the pieces of the two step contexts ---- *)

(* Looking a variable up.  `lookup_S`'s conclusion carries a renaming, so
   unifying it against a goal whose type is given would have to INVERT that
   renaming; routing the shift through an equality instead lets the type be
   computed forwards and checked by conversion at the end. *)
Lemma lk_step G i A B (H : lookup i G A) T : T = A ⟨↑⟩ -> lookup (S i) (B :: G) T.
Proof. intros ->; apply lookup_S; exact H. Qed.

Ltac lkgo := first [ exact (lookup_O _ _) | (eapply lk_step; [ lkgo | reflexivity ]) ].
Ltac tv := eapply t_var; [ assumption | lkgo ].

Lemma ty_pVP G (W : wfc G) : ty G (pi 1 V (prop 0)) (UU 1).
Proof.
  exact (t_pi G 1 1 0 V (prop 0) (le_n 1) le01 (ty_V G W)
           (t_prop _ 0 (wfc_V G W))).
Qed.

(* `wbr 1 (UU 0) (var 0)` is `pi 1 (var 0) V`: the branching function *)
Lemma ty_wbrV G (W : wfc G) : ty (UU 0 :: G) (pi 1 (var_tm 0) V) (UU 1).
Proof.
  pose proof (wfc_U G W) as WU.
  exact (t_pi _ 1 0 1 (var_tm 0) V le01 (le_n 1) (ty_br G W)
           (ty_V _ (w_cons _ (var_tm 0) 0 WU (ty_br G W)))).
Qed.

Lemma wfc_br G (W : wfc G) : wfc (pi 1 (var_tm 0) V :: UU 0 :: G).
Proof. exact (w_cons _ _ 1 (wfc_U G W) (ty_wbrV G W)). Qed.

Lemma ty_lab G (W : wfc G) :
  ty (pi 1 (var_tm 0) V :: UU 0 :: G) (var_tm 1) (UU 0).
Proof. pose proof (wfc_br G W) as WB; tv. Qed.

(* `wih n 1 (UU 0) (var 0) C` is `pi n (var 1) C` for a closed motive C *)
(* at a closed motive C of level 1 *)
Lemma ty_wihC G (W : wfc G) C (dC : forall D, wfc D -> ty D C (UU 1)) :
  ty (pi 1 (var_tm 0) V :: UU 0 :: G) (pi 1 (var_tm 1) C) (UU 1).
Proof.
  pose proof (wfc_br G W) as WB.
  exact (t_pi _ 1 0 1 (var_tm 1) C le01 (le_n 1) (ty_lab G W)
           (dC _ (w_cons _ (var_tm 1) 0 WB (ty_lab G W)))).
Qed.

Lemma ty_wihV G (W : wfc G) :
  ty (pi 1 (var_tm 0) V :: UU 0 :: G) (pi 1 (var_tm 1) (pi 1 V (prop 0))) (UU 1).
Proof. exact (ty_wihC G W _ ty_pVP). Qed.

Lemma ty_wihP G (W : wfc G) :
  ty (pi 1 (var_tm 0) V :: UU 0 :: G) (pi 0 (var_tm 1) (prop 0)) (UU 0).
Proof.
  pose proof (wfc_br G W) as WB.
  exact (t_pi _ 0 0 0 (var_tm 1) (prop 0) (le_n 0) (le_n 0) (ty_lab G W)
           (t_prop _ 0 (w_cons _ (var_tm 1) 0 WB (ty_lab G W)))).
Qed.

(* ---- the derivation ---- *)

(* Deriving it bottom-up matters: the rules are in the REDUNDANT style, so
   every leaf asks for the well-formedness of its context, and a tactic that
   rebuilds those contexts re-derives the whole proposition once per leaf --
   528 copies of the same goal, in the first attempt at this file.  Each
   context is therefore built once and passed along, and each variable's type
   is passed as a lookup. *)

Ltac lkS h := exact (lk_step _ _ _ _ h _ eq_refl).
Ltac lkS2 h := exact (lk_step _ _ _ _ (lk_step _ _ _ _ h _ eq_refl) _ eq_refl).
Ltac lkS3 h :=
  exact (lk_step _ _ _ _ (lk_step _ _ _ _ (lk_step _ _ _ _ h _ eq_refl) _ eq_refl)
           _ eq_refl).

(* `IH a (g b)` : Prop *)
Lemma ty_bis_app E (WE : wfc E) d a b
  (hA  : lookup (9 + d) E (UU 0))
  (hIH : lookup (7 + d) E (pi 1 (var_tm (9 + d)) (pi 1 V (prop 0))))
  (hB  : lookup (5 + d) E (UU 0))
  (hg  : lookup (4 + d) E (pi 1 (var_tm (5 + d)) V))
  (ha  : lookup a E (var_tm (9 + d)))
  (hb  : lookup b E (var_tm (5 + d))) :
  ty E (bis_app d a b) (prop 0).
Proof.
  assert (dA : ty E (var_tm (9 + d)) (UU 0)) by exact (t_var E _ _ WE hA).
  assert (dB : ty E (var_tm (5 + d)) (UU 0)) by exact (t_var E _ _ WE hB).
  refine (t_app E 1 1 0 V (prop 0) _ _ (le_n 1) le01 (ty_V E WE)
            (t_prop _ 0 (wfc_V E WE)) _ _).
  - (* IH a : V -> Prop *)
    refine (t_app E 1 0 1 (var_tm (9 + d)) (pi 1 V (prop 0)) _ _ le01 (le_n 1)
              dA (ty_pVP _ (w_cons E _ 0 WE dA)) _ _).
    + exact (t_var E _ _ WE hIH).
    + exact (t_var E _ _ WE ha).
  - (* g b : V *)
    refine (t_app E 1 0 1 (var_tm (5 + d)) V _ _ le01 (le_n 1)
              dB (ty_V _ (w_cons E _ 0 WE dB)) _ _).
    + exact (t_var E _ _ WE hg).
    + exact (t_var E _ _ WE hb).
Qed.

(* the two halves.  D is the context the half sits in, d the number of
   binders between it and the step's own context; the four lookups are the
   label types A and B, the induction hypothesis, and the branching function
   of the second set. *)
Section Halves.
  Context (D : ctx) (WD : wfc D) (d : nat)
          (hA  : lookup (6 + d) D (UU 0))
          (hB  : lookup (2 + d) D (UU 0))
          (hIH : lookup (4 + d) D (pi 1 (var_tm (6 + d)) (pi 1 V (prop 0))))
          (hg  : lookup (1 + d) D (pi 1 (var_tm (2 + d)) V)).

  Lemma ty_half1 : ty D (bis_half1 d) (prop 0).
  Proof.
    assert (dA : ty D (var_tm (6 + d)) (UU 0)) by exact (t_var D _ _ WD hA).
    (* a : A *)
    pose proof (w_cons D _ 0 WD dA) as W1.
    (* C : Prop *)
    pose proof (w_cons _ (prop 0) 0 W1 (t_prop _ 0 W1)) as W2.
    assert (dB : ty (prop 0 :: var_tm (6 + d) :: D) (var_tm (4 + d)) (UU 0))
      by (refine (t_var _ _ _ W2 _); lkS2 hB).
    (* b : B *)
    pose proof (w_cons _ _ 0 W2 dB) as W3.
    (* the body of the existential *)
    assert (dQ : ty (var_tm (4 + d) :: prop 0 :: var_tm (6 + d) :: D)
                    (bis_app d 2 0) (prop 0)).
    { refine (ty_bis_app _ W3 d 2 0 _ _ _ _ _ _).
      - lkS3 hA.
      - lkS3 hIH.
      - lkS3 hB.
      - lkS3 hg.
      - lkS2 (lookup_O D (var_tm (6 + d))).
      - exact (lookup_O _ (var_tm (4 + d))). }
    pose proof (t_prf _ 0 0 _ (le_n 0) dQ) as dPQ.
    pose proof (w_cons _ _ 0 W3 dPQ) as W4.
    unfold bis_half1.
    refine (t_all D (var_tm (6 + d)) _ 0 0 dA _).
    refine (t_all _ (prop 0) _ 0 0 (t_prop _ 0 W1) _).
    refine (t_all _ (prf 0 _) (var_tm 1) 0 0 _ _).
    - refine (t_prf _ 0 0 _ (le_n 0) _).
      refine (t_all _ (var_tm (4 + d)) _ 0 0 dB _).
      refine (t_all _ (prf 0 _) (var_tm 2) 0 0 dPQ _).
      refine (t_var _ _ _ W4 _); lkS2 (lookup_O (var_tm (6 + d) :: D) (prop 0)).
    - refine (t_var _ _ _ _ _);
        [ apply (w_cons _ _ 0 W2); refine (t_prf _ 0 0 _ (le_n 0) _)
        | lkS (lookup_O (var_tm (6 + d) :: D) (prop 0)) ].
      refine (t_all _ (var_tm (4 + d)) _ 0 0 dB _).
      refine (t_all _ (prf 0 _) (var_tm 2) 0 0 dPQ _).
      refine (t_var _ _ _ W4 _); lkS2 (lookup_O (var_tm (6 + d) :: D) (prop 0)).
  Qed.

  Lemma ty_half2 : ty D (bis_half2 d) (prop 0).
  Proof.
    assert (dB : ty D (var_tm (2 + d)) (UU 0)) by exact (t_var D _ _ WD hB).
    (* b : B *)
    pose proof (w_cons D _ 0 WD dB) as W1.
    (* C : Prop *)
    pose proof (w_cons _ (prop 0) 0 W1 (t_prop _ 0 W1)) as W2.
    assert (dA : ty (prop 0 :: var_tm (2 + d) :: D) (var_tm (8 + d)) (UU 0))
      by (refine (t_var _ _ _ W2 _); lkS2 hA).
    (* a : A *)
    pose proof (w_cons _ _ 0 W2 dA) as W3.
    assert (dQ : ty (var_tm (8 + d) :: prop 0 :: var_tm (2 + d) :: D)
                    (bis_app d 0 2) (prop 0)).
    { refine (ty_bis_app _ W3 d 0 2 _ _ _ _ _ _).
      - lkS3 hA.
      - lkS3 hIH.
      - lkS3 hB.
      - lkS3 hg.
      - exact (lookup_O _ (var_tm (8 + d))).
      - lkS2 (lookup_O D (var_tm (2 + d))). }
    pose proof (t_prf _ 0 0 _ (le_n 0) dQ) as dPQ.
    pose proof (w_cons _ _ 0 W3 dPQ) as W4.
    unfold bis_half2.
    refine (t_all D (var_tm (2 + d)) _ 0 0 dB _).
    refine (t_all _ (prop 0) _ 0 0 (t_prop _ 0 W1) _).
    refine (t_all _ (prf 0 _) (var_tm 1) 0 0 _ _).
    - refine (t_prf _ 0 0 _ (le_n 0) _).
      refine (t_all _ (var_tm (8 + d)) _ 0 0 dA _).
      refine (t_all _ (prf 0 _) (var_tm 2) 0 0 dPQ _).
      refine (t_var _ _ _ W4 _); lkS2 (lookup_O (var_tm (2 + d) :: D) (prop 0)).
    - refine (t_var _ _ _ _ _);
        [ apply (w_cons _ _ 0 W2); refine (t_prf _ 0 0 _ (le_n 0) _)
        | lkS (lookup_O (var_tm (2 + d) :: D) (prop 0)) ].
      refine (t_all _ (var_tm (8 + d)) _ 0 0 dA _).
      refine (t_all _ (prf 0 _) (var_tm 2) 0 0 dPQ _).
      refine (t_var _ _ _ W4 _); lkS2 (lookup_O (var_tm (2 + d) :: D) (prop 0)).
  Qed.
End Halves.

(* the two step contexts, with wbr and wih computed out *)
Definition Souter (G : ctx) : ctx :=
  pi 1 (var_tm 1) (pi 1 V (prop 0)) :: pi 1 (var_tm 0) V :: UU 0 :: V :: G.

Definition Sinner (G : ctx) : ctx :=
  pi 0 (var_tm 1) (prop 0) :: pi 1 (var_tm 0) V :: UU 0 :: V :: Souter G.

Theorem ty_bisim G (W : wfc G) : ty G bisim (pi 1 V (pi 1 V (prop 0))).
Proof.
  pose proof (wfc_V G W) as WV.
  refine (t_lam G 1 1 1 V (pi 1 V (prop 0)) _ (le_n 1) (le_n 1)
            (ty_V G W) (ty_pVP _ WV) _).
  (* the outer recursion, on the first set, at the motive V -> Prop *)
  refine (t_wrec (V :: G) 1 1 0 1 1 (UU 0) (var_tm 0) (pi 1 V (prop 0))
            bis_step (var_tm 0) (le_n 1) le01 le01 (le_n 1) eq_refl
            (ty_U _ WV) (ty_br _ WV) (ty_pVP _ (wfc_V _ WV))
            (ty_wbrV _ WV) (ty_wihV _ WV) _
            (t_var _ 0 V WV (lookup_O G V))).
  (* its step is a function of the second set *)
  pose proof (wfc_br _ WV) as WB.
  pose proof (w_cons _ _ 1 WB (ty_wihV _ WV)) as WS.
  refine (t_lam _ 1 1 0 V (prop 0) _ (le_n 1) le01
            (ty_V _ WS) (t_prop _ 0 (wfc_V _ WS)) _).
  (* the inner recursion, on the second set, at the motive Prop *)
  pose proof (wfc_V _ WS) as WSV.
  refine (t_wrec _ 1 1 0 0 0 (UU 0) (var_tm 0) (prop 0) bis_step2 (var_tm 0)
            (le_n 1) le01 (le_n 0) (le_n 0) eq_refl
            (ty_U _ WSV) (ty_br _ WSV) (t_prop _ 0 (wfc_V _ WSV))
            (ty_wbrV _ WSV) (ty_wihP _ WSV) _
            (t_var _ 0 V WSV (lookup_O _ V))).
  (* the inner step: the conjunction of the two halves *)
  pose proof (wfc_br _ WSV) as WB2.
  pose proof (w_cons _ _ 0 WB2 (ty_wihP _ WSV)) as WS2.
  pose proof (w_cons _ (prop 0) 0 WS2 (t_prop _ 0 WS2)) as W3.
  assert (dH1 : ty (prop 0 :: Sinner G) (bis_half1 1) (prop 0)).
  { refine (ty_half1 _ W3 1 _ _ _ _).
    - lkgo.
    - lkgo.
    - lkgo.
    - lkgo. }
  pose proof (t_prf _ 0 0 _ (le_n 0) dH1) as dP1.
  pose proof (w_cons _ _ 0 W3 dP1) as W4.
  assert (dH2 : ty (prf 0 (bis_half1 1) :: prop 0 :: Sinner G)
                   (bis_half2 2) (prop 0)).
  { refine (ty_half2 _ W4 2 _ _ _ _).
    - lkgo.
    - lkgo.
    - lkgo.
    - lkgo. }
  pose proof (t_prf _ 0 0 _ (le_n 0) dH2) as dP2.
  pose proof (w_cons _ _ 0 W4 dP2) as W5.
  unfold bis_step2.
  refine (t_all _ (prop 0) _ 0 0 (t_prop _ 0 WS2) _).
  refine (t_all _ (prf 0 _) (var_tm 1) 0 0 _ _).
  - (* the hypothesis of the conjunction *)
    refine (t_prf _ 0 0 _ (le_n 0) _).
    refine (t_all _ (prf 0 (bis_half1 1)) _ 0 0 dP1 _).
    refine (t_all _ (prf 0 (bis_half2 2)) (var_tm 2) 0 0 dP2 _).
    refine (t_var _ _ _ W5 _); lkgo.
  - (* its conclusion, the bound propositional variable *)
    refine (t_var _ _ _ _ _).
    + apply (w_cons _ _ 0 W3); refine (t_prf _ 0 0 _ (le_n 0) _).
      refine (t_all _ (prf 0 (bis_half1 1)) _ 0 0 dP1 _).
      refine (t_all _ (prf 0 (bis_half2 2)) (var_tm 2) 0 0 dP2 _).
      refine (t_var _ _ _ W5 _); lkgo.
    + lkgo.
Qed.

(* bisimulation is a closed function V -> V -> Prop *)
Definition closed_bisim : ty nil bisim (pi 1 V (pi 1 V (prop 0))) :=
  ty_bisim nil w_nil.

(* ------------------------------------------------------------------ *)
(* Union                                                               *)
(* ------------------------------------------------------------------ *)

(* The union of a set needs to take a set APART again, which for a W type
   means a recursion.  Doing it in one step -- returning the label type and
   the branching function as a PAIR -- makes the two projections definitional:
   `elt s` lands in `idx s -> V` on the nose, where separate recursions for
   the two would have made that an equality to be transported along. *)
Definition Shape : tm := sig_ 1 (UU 0) (pi 1 (var_tm 0) V).

Definition shape : tm :=
  lam 1 V Shape
    (wrec (UU 0) (var_tm 0) Shape
       (pair 1 (UU 0) (pi 1 (var_tm 0) V) (var_tm 2) (var_tm 1))
       (var_tm 0)).

Definition idx (s : tm) : tm :=
  fst (UU 0) (pi 1 (var_tm 0) V) (app V Shape shape s).

Definition elt (s : tm) : tm :=
  snd (UU 0) (pi 1 (var_tm 0) V) (app V Shape shape s).

Lemma ty_Shape G (W : wfc G) : ty G Shape (UU 1).
Proof.
  refine (t_sig G 1 1 1 (UU 0) (pi 1 (var_tm 0) V) (le_n 1) (le_n 1)
            (ty_U G W) _).
  exact (ty_wbrV G W).
Qed.

Lemma ty_shape G (W : wfc G) : ty G shape (pi 1 V Shape).
Proof.
  pose proof (wfc_V G W) as WV.
  refine (t_lam G 1 1 1 V Shape _ (le_n 1) (le_n 1) (ty_V G W) (ty_Shape _ WV) _).
  refine (t_wrec (V :: G) 1 1 0 1 1 (UU 0) (var_tm 0) Shape _ (var_tm 0)
            (le_n 1) le01 le01 (le_n 1) eq_refl
            (ty_U _ WV) (ty_br _ WV) (ty_Shape _ (wfc_V _ WV))
            (ty_wbrV _ WV) (ty_wihC _ WV Shape ty_Shape) _
            (t_var _ 0 V WV (lookup_O G V))).
  (* the step: the label and the branching function, paired *)
  pose proof (wfc_br _ WV) as WB.
  pose proof (w_cons _ _ 1 WB (ty_wihC _ WV Shape ty_Shape)) as WS.
  refine (t_pair _ 1 1 1 (UU 0) (pi 1 (var_tm 0) V) (var_tm 2) (var_tm 1)
            (le_n 1) (le_n 1) (ty_U _ WS) _ _ _).
  - exact (ty_wbrV _ WS).
  - refine (t_var _ _ _ WS _); lkgo.
  - refine (t_var _ _ _ WS _); lkgo.
Qed.

Lemma ty_shape_at G (W : wfc G) s (ds : ty G s V) :
  ty G (app V Shape shape s) Shape.
Proof.
  exact (t_app G 1 1 1 V Shape shape s (le_n 1) (le_n 1) (ty_V G W)
           (ty_Shape _ (wfc_V G W)) (ty_shape G W) ds).
Qed.

Lemma ty_idx G (W : wfc G) s (ds : ty G s V) : ty G (idx s) (UU 0).
Proof.
  exact (t_fst G 1 1 1 (UU 0) (pi 1 (var_tm 0) V) _ (le_n 1) (le_n 1)
           (ty_U G W) (ty_wbrV G W) (ty_shape_at G W s ds)).
Qed.

Lemma ty_elt G (W : wfc G) s (ds : ty G s V) :
  ty G (elt s) (pi 1 (idx s) V).
Proof.
  exact (t_snd G 1 1 1 (UU 0) (pi 1 (var_tm 0) V) _ (le_n 1) (le_n 1)
           (ty_U G W) (ty_wbrV G W) (ty_shape_at G W s ds)).
Qed.

(* The union of s = sup A f: indexed by the pairs (a, i) with a : A and i an
   index of the set f a, and sending such a pair to the i-th element of f a.
   Note the index type is a Sigma at level 0 while the recursion's motive is V
   at level 1 -- the two levels never have to meet. *)
Definition usig : tm :=
  sig_ 0 (var_tm 2) (idx (app (var_tm 3) V (var_tm 2) (var_tm 0))).

Definition ufst : tm :=
  fst (var_tm 3) (idx (app (var_tm 4) V (var_tm 3) (var_tm 0))) (var_tm 0).

Definition usnd : tm :=
  snd (var_tm 3) (idx (app (var_tm 4) V (var_tm 3) (var_tm 0))) (var_tm 0).

Definition union : tm :=
  lam 1 V V
    (wrec (UU 0) (var_tm 0) V
       (aset usig
          (lam 1 usig V
             (app (idx (app (var_tm 3) V (var_tm 2) ufst)) V
                  (elt (app (var_tm 3) V (var_tm 2) ufst)) usnd)))
       (var_tm 0)).

(* the step context of a recursion on V at a closed motive of level 1 *)
Definition Sun (G : ctx) : ctx :=
  pi 1 (var_tm 1) V :: pi 1 (var_tm 0) V :: UU 0 :: V :: G.

(* applying a branching function to an index *)
Definition ty_app_f D (WD : wfc D) n u
  (hA : ty D (var_tm (S n)) (UU 0))
  (hf : ty D (var_tm n) (pi 1 (var_tm (S n)) V))
  (hu : ty D u (var_tm (S n))) :
  ty D (app (var_tm (S n)) V (var_tm n) u) V :=
  t_app D 1 0 1 (var_tm (S n)) V (var_tm n) u le01 (le_n 1) hA
    (ty_V _ (w_cons D _ 0 WD hA)) hf hu.

Theorem ty_union G (W : wfc G) : ty G union (pi 1 V V).
Proof.
  pose proof (wfc_V G W) as WV.
  refine (t_lam G 1 1 1 V V _ (le_n 1) (le_n 1) (ty_V G W) (ty_V _ WV) _).
  refine (t_wrec (V :: G) 1 1 0 1 1 (UU 0) (var_tm 0) V _ (var_tm 0)
            (le_n 1) le01 le01 (le_n 1) eq_refl
            (ty_U _ WV) (ty_br _ WV) (ty_V _ (wfc_V _ WV))
            (ty_wbrV _ WV) (ty_wihC _ WV V ty_V) _
            (t_var _ 0 V WV (lookup_O G V))).
  pose proof (wfc_br _ WV) as WB.
  pose proof (w_cons _ _ 1 WB (ty_wihC _ WV V ty_V)) as WS.
  (* in the step context: the label A is var 2 and the branching function var 1 *)
  assert (dA : ty (Sun G) (var_tm 2) (UU 0)) by (refine (t_var _ _ _ WS _); lkgo).
  pose proof (w_cons _ _ 0 WS dA) as WA.
  assert (dfa : ty (var_tm 2 :: Sun G) (app (var_tm 3) V (var_tm 2) (var_tm 0)) V).
  { refine (ty_app_f _ WA 2 (var_tm 0) _ _ _);
      refine (t_var _ _ _ WA _); lkgo. }
  assert (dsig : ty (Sun G) usig (UU 0)).
  { exact (t_sig _ 0 0 0 (var_tm 2) _ (le_n 0) (le_n 0) dA (ty_idx _ WA _ dfa)). }
  pose proof (w_cons _ _ 0 WS dsig) as WSig.
  refine (ty_aset _ WS usig _ dsig (ty_fam _ WS usig _ dsig _)).
  (* the body, in  usig :: (step context) *)
  assert (dA1 : ty (usig :: Sun G) (var_tm 3) (UU 0))
    by (refine (t_var _ _ _ WSig _); lkgo).
  pose proof (w_cons _ _ 0 WSig dA1) as WA1.
  assert (dcod : ty (var_tm 3 :: usig :: Sun G)
                    (idx (app (var_tm 4) V (var_tm 3) (var_tm 0))) (UU 0)).
  { refine (ty_idx _ WA1 _ (ty_app_f _ WA1 3 (var_tm 0) _ _ _));
      refine (t_var _ _ _ WA1 _); lkgo. }
  assert (dp : ty (usig :: Sun G) (var_tm 0)
                  (sig_ 0 (var_tm 3) (idx (app (var_tm 4) V (var_tm 3) (var_tm 0)))))
    by (refine (t_var _ _ _ WSig _); lkgo).
  assert (dufst : ty (usig :: Sun G) ufst (var_tm 3))
    by exact (t_fst _ 0 0 0 (var_tm 3) _ (var_tm 0) (le_n 0) (le_n 0)
                dA1 dcod dp).
  assert (dfu : ty (usig :: Sun G) (app (var_tm 3) V (var_tm 2) ufst) V).
  { refine (ty_app_f _ WSig 2 ufst dA1 _ dufst).
    refine (t_var _ _ _ WSig _); lkgo. }
  (* and the element it picks out *)
  refine (t_app _ 1 0 1 (idx (app (var_tm 3) V (var_tm 2) ufst)) V _ usnd
            le01 (le_n 1) (ty_idx _ WSig _ dfu)
            (ty_V _ (w_cons _ _ 0 WSig (ty_idx _ WSig _ dfu)))
            (ty_elt _ WSig _ dfu) _).
  exact (t_snd _ 0 0 0 (var_tm 3) _ (var_tm 0) (le_n 0) (le_n 0) dA1 dcod dp).
Qed.

Definition closed_union : ty nil union (pi 1 V V) := ty_union nil w_nil.

(* ------------------------------------------------------------------ *)
(* Closed instances                                                    *)
(* ------------------------------------------------------------------ *)

(* {0, omega} *)
Definition two_elt : tm := pairing emptyset omega.

Lemma ty_two_elt G (W : wfc G) : ty G two_elt V.
Proof.
  pose proof (w_cons G (nat_ 0) 0 W (t_nat G 0 W)) as W1.
  pose proof (w_cons _ (nat_ 0) 0 W1 (t_nat _ 0 W1)) as W2.
  pose proof (w_cons _ V 1 W2 (ty_V _ W2)) as W3.
  exact (ty_pairing G W emptyset omega (ty_emptyset _ W1) (ty_omega _ W3)).
Qed.

Definition closed_two_elt : ty nil two_elt V := ty_two_elt nil w_nil.

(* and its union, which is omega itself up to bisimulation *)
Definition closed_union_two : ty nil (app V V union two_elt) V :=
  t_app nil 1 1 1 V V union two_elt (le_n 1) (le_n 1) (ty_V nil w_nil)
    (ty_V _ (wfc_V nil w_nil)) (ty_union nil w_nil) closed_two_elt.
