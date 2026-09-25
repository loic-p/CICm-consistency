From CICM Require Import core unscoped Syntax Erasure.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Typing.Rules.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.

Import UnscopedNotations.
Open Scope list_scope.
Open Scope subst_scope.

(* WHY THERE IS NO Eq IN Typing/Rules.v.

   The paper's CIC^- has Eq : Prop with transport,

     G |- A : Typek   G, x:A |- B : Typej   G |- e : Prf (Eq A t u)
     G |- b : B[t/x]  ==>  G |- transp A B t u e b : B[u/x],

   and the layer-1 fundamental lemma (paper Lemma 3.4) discharges it with
   "erasures are *, or the subject, and the Prf-PER is transparent, so these
   cases are immediate".  That step is a gap, and it cannot be patched: the
   erasure of a transport IS its subject, so layer 1 has to keep the same
   realiser |b| while its type moves from |B[t/x]| to |B[u/x]|, and a
   transparent Prf-PER gives it no way to know that |t| and |u| are related
   in |A| -- nor, indeed, to tell transp b from b at all.

   This file makes the failure concrete.  Assuming only Eq-formation and the
   transport rule (everything else is the theory as formalised), there is a
   closed, conversion-free derivation of

       |- Tbad : Type0

   with Good_ty (er Tbad) absurd: a false equation Type0 -> Type0 = Type0 is
   assumed in the context, and the identity function is transported across
   it into Type0, so the codomain of Tbad has a lambda where a type former
   is required.  Tbad therefore has no layer-1 shadow, hence no rank, hence
   no code, and it is not in the decoding of any universe (UnivSound.us_ty
   demands eqty m u u of every element of Univ m).  Both fundamental lemmas
   are false, not merely unproved.

   Why nothing local rescues it:

   - Erasing transports to a stuck term would satisfy layer 1 (stuck terms
     inhabit every PER) but not layer 2: code decodings deliberately exclude
     stuck realisers, which is what buys canonicity.  absurd gets away with
     err only because its case is vacuous -- the decoding of the Prf-code at
     False has no elements at all.
   - Adding an erased eliminator that reduces only at a reflexivity witness
     does not help either: the Prf-PER is transparent, so an environment may
     realise a proof variable by the reflexivity witness even when the
     equation is false, and the eliminator fires.
   - Making layer 1 truth-aware at Eq -- reading the PER of Prf (Eq A t u)
     as transparent-if-Rel-A-t-u and empty otherwise -- is circular: Prop is
     impredicative, so Prf (Eq (u_n) t u) : Type0 would need tau (n+1),
     while LR n only has the levels below n.  That circularity is precisely
     what the two layers exist to break.

   Restricting the motive to Prop does make the rule sound -- the realiser
   of b then only has to stay in the transparent PER of Prf (B[u/x]), which
   it does for free -- but that is a different, weaker theory, with no large
   elimination for Eq.  So Eq is left out entirely until the model can carry
   the intended rule.  (In the POPL'23 model this one descends from, the
   question does not arise: transport computes there by recursion on the head
   constructors of the types, and propositions are definitionally
   proof-irrelevant, so transports of proofs never need to compute.)

   Contrast absurd, whose erasure err is *stuck* and hence in every PER:
   that is exactly why ex falso costs layer 1 nothing, and why it stays. *)

(* eqty (univ 1) (Type0 -> Type0) Type0 : a false equation between types. *)
Definition EqT : tm := Core.eqty (univ 1) (pi (univ 0) (univ 0)) (univ 0).
Definition PT : tm := prf EqT.

(* In context [PT], transport the identity function on Type0 along the
   variable proof, from the type (Type0 -> Type0) to the type Type0. *)
Definition Cod : tm :=
  transp (univ 1) (var_tm 0) (pi (univ 0) (univ 0)) (univ 0)
         (var_tm 0) (lam (univ 0) (univ 0) (var_tm 0)).

Definition Tbad : tm := pi PT Cod.

(* ------------------------------------------------------------------ *)
(* 1.  Under the large rule, Tbad is a well-formed closed type, with  *)
(*     no use of conversion.                                          *)
(* ------------------------------------------------------------------ *)

Section LargeTransp.

(* The two absent rules, as hypotheses: all this file assumes. *)
Hypothesis t_eq : forall G A t u k,
  ty G A (univ k) -> ty G t A -> ty G u A -> ty G (Core.eqty A t u) prop.

Hypothesis t_transp_large : forall G A B t u e b k j,
  ty G A (univ k) -> ty (A :: G) B (univ j) ->
  ty G t A -> ty G u A -> ty G e (prf (Core.eqty A t u)) -> ty G b (B [t..]) ->
  ty G (transp A B t u e b) (B [u..]).

Lemma wf_nil : wfc nil.
Proof. exact w_nil. Qed.

Lemma ty_EqT : ty nil EqT prop.
Proof.
  apply (t_eq nil (univ 1) _ _ 2).
  - apply t_univ, wf_nil.
  - apply (t_pi nil (univ 0) (univ 0) 1); apply t_univ;
      [apply wf_nil | apply (w_cons nil (univ 0) 1); [apply wf_nil | apply t_univ, wf_nil]].
  - apply t_univ, wf_nil.
Qed.

Lemma ty_PT : ty nil PT (univ 0).
Proof. apply t_prf, ty_EqT. Qed.

Lemma wf_PT : wfc (PT :: nil).
Proof. apply (w_cons nil PT 0); [apply wf_nil | apply ty_PT]. Qed.

Lemma ty_Cod : ty (PT :: nil) Cod (univ 0).
Proof.
  apply (t_transp_large (PT :: nil) (univ 1) (var_tm 0) _ _ _ _ 2 1).
  - apply t_univ, wf_PT.
  - apply t_var; [apply (w_cons _ (univ 1) 2); [apply wf_PT | apply t_univ, wf_PT]
                 | apply lookup_O].
  - apply (t_pi _ (univ 0) (univ 0) 1); apply t_univ;
      [apply wf_PT | apply (w_cons _ (univ 0) 1); [apply wf_PT | apply t_univ, wf_PT]].
  - apply t_univ, wf_PT.
  - apply t_var; [apply wf_PT | apply lookup_O].
  - apply (t_lam _ (univ 0) (univ 0) _ 1).
    + apply t_univ, wf_PT.
    + apply t_univ, (w_cons _ (univ 0) 1); [apply wf_PT | apply t_univ, wf_PT].
    + apply t_var; [apply (w_cons _ (univ 0) 1); [apply wf_PT | apply t_univ, wf_PT]
                   | apply lookup_O].
Qed.

Theorem ty_Tbad : ty nil Tbad (univ 0).
Proof. apply (t_pi nil PT Cod 0); [apply ty_PT | apply ty_Cod]. Qed.

End LargeTransp.

(* ------------------------------------------------------------------ *)
(* 2.  Its erasure is not a layer-1 type.                             *)
(* ------------------------------------------------------------------ *)

Definition D : etm := eprf (er EqT).
Definition B0 : etm := elam (elam (var_etm 0)).

Lemma er_Tbad : er Tbad = epi D B0.
Proof. reflexivity. Qed.

Lemma eval_Tbad : eval (er Tbad) (epi D B0).
Proof. rewrite er_Tbad; apply eval_whnf; left; apply v_pi. Qed.

(* The codomain applied to any argument reduces to the identity lambda. *)
Lemma B0_app u : reds (eapp B0 u) (elam (var_etm 0)).
Proof.
  eapply reds_step; [apply red_beta | apply reds_refl].
Qed.

Theorem Tbad_not_good : Good_ty (er Tbad) -> False.
Proof.
  intros HG.
  (* the domain prf (...) is good, and its PER relates everything *)
  assert (HD : Good_ty D) by (eapply Rel_pi_dom; [exact HG | apply eval_Tbad]).
  assert (Hst : Rel D estar estar)
    by (eapply Rel_prf_intro; [exact HD | apply eval_whnf; left; apply v_prf]).
  (* so the codomain at estar is a layer-1 type ... *)
  destruct (Rel_pi_cod _ _ _ estar estar HG eval_Tbad Hst) as [n Hn].
  (* ... but it reduces to a lambda, which no layer-1 type does *)
  eapply eqty_lam_absurd, (eqty_red n _ _ _ _ Hn); apply B0_app.
Qed.

(* Putting the two halves together: the large rule refutes the type-level
   half of the layer-1 fundamental lemma (blueprint Theorem 6.7), which is
   the half every later layer consumes. *)
Corollary large_transp_refutes_layer1 :
  (forall G A t u k, ty G A (univ k) -> ty G t A -> ty G u A ->
     ty G (Core.eqty A t u) prop) ->
  (forall G A B t u e b k j,
     ty G A (univ k) -> ty (A :: G) B (univ j) ->
     ty G t A -> ty G u A -> ty G e (prf (Core.eqty A t u)) -> ty G b (B [t..]) ->
     ty G (transp A B t u e b) (B [u..])) ->
  ~ (forall A k, ty nil A (univ k) -> Good_ty (er A)).
Proof. intros HE HL H; apply Tbad_not_good, (H Tbad 0 (ty_Tbad HE HL)). Qed.
