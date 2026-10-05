From CICM Require Import Syntax.Ann Syntax.Erasure.
From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str Codes.Sound
  Codes.Expand Codes.Refl Codes.Levels Codes.Lift.
From CICM Require Import Interp.Codes Interp.Stage Interp.Build.
From Stdlib Require Import Arith Lia.

(* The semantic value of a type is an element of the decoding of the universe
   it lives in, that is, a coherent family of codes -- a UFam.  This file
   builds one for each former with no components, and gives the interface for
   moving elements between a family's instances.

   Two differences from v1.  A UFam's fifth field is now `uf_wf`, the
   well-formedness of every code in the family, where v1 carried `uf_idp`, the
   identity law of the transport those codes used to carry.  And the equality
   of elements, `kEqAt`, relates elements of TWO families -- v1's was
   homogeneous, so comparing two families' elements needed an isomorphism and
   a transport along it; here it is the canonical equality and nothing else. *)

Definition kUFam (k : nat) (u : etm) : Type := UFam (lvl k) k u.

Definition kAcc {k u} (F : kUFam k u) : Acc prec u := uf_acc F.
Definition kAt {k u} (F : kUFam k u) : Code k (rk u (kAcc F)) := uf_at F.
Definition kElAt {k u} (F : kUFam k u) (w : etm) : Type := kElC (kAt F) w.

(* HETEROGENEOUS: elements of two families at two realisers *)
Definition kEqAt {k u u'} (F : kUFam k u) w (x : kElAt F w)
  (F' : kUFam k u') w' (x' : kElAt F' w') : Prop := kcel (kAt F) w x (kAt F') w' x'.

Definition famWf {k u} (F : kUFam k u) v h pf : wfn (uf_c F v h pf) := uf_wf F v h pf.
Definition famAtWf {k u} (F : kUFam k u) : kwfc (kAt F) := uf_wf F u (kAcc F) (evalAg_refl u).

(* the self-equality of a well-formed code is its second conjunct *)
Definition famAtSelf {k u} (F : kUFam k u) : kceq (kAt F) (kAt F) := proj2 (famAtWf F).

(* Moving an element between two instances of one family: the family's own
   coherence, and the coercion of Codes/Str.v. *)
Definition famTo {k u} (F : kUFam k u) v h pf w
  (x : kElC (uf_c F v h pf) w) : kElAt F w :=
  kto (uf_c F v h pf) (kAt F) (famWf F v h pf) (famAtWf F)
    (uf_coh F v h pf u (kAcc F) (evalAg_refl u)) w x.

Definition famFrom {k u} (F : kUFam k u) v h pf w (x : kElAt F w)
  : kElC (uf_c F v h pf) w :=
  kto (kAt F) (uf_c F v h pf) (famAtWf F) (famWf F v h pf)
    (uf_coh F u (kAcc F) (evalAg_refl u) v h pf) w x.

(* and it is related to what it came from, which is all that is ever needed *)
Lemma famTo_coh {k u} (F : kUFam k u) v h pf w x :
  kcel (uf_c F v h pf) w x (kAt F) w (famTo F v h pf w x).
Proof. apply kto_coh. Qed.

Lemma famFrom_coh {k u} (F : kUFam k u) v h pf w x :
  kcel (kAt F) w x (uf_c F v h pf) w (famFrom F v h pf w x).
Proof. apply kto_coh. Qed.

(* ------------------------------------------------------------------ *)
(* Layer-1 facts each constructor needs of its shadow.                 *)
(* ------------------------------------------------------------------ *)

Lemma eqty_nat k v v' : eval v enat -> eval v' enat -> eqty k v v'.
Proof. intros H H'; exists NatPer; apply LR_nat; assumption. Qed.

Lemma eqty_prop k v v' : eval v eprop -> eval v' eprop -> eqty k v v'.
Proof. intros H H'; exists PR; apply LR_prop; assumption. Qed.

Lemma eqty_prf k v v' p p' : eval v (eprf p) -> eval v' (eprf p') -> PR p p' ->
  eqty k v v'.
Proof. intros H H' HP; exists TruePer; eapply LR_prf; eassumption. Qed.

Lemma eqty_univ k m v v' : m < k -> eval v (euniv m) -> eval v' (euniv m) ->
  eqty k v v'.
Proof.
  intros Hm H H'; exists (fun C C' => exists P, below k m C C' P);
    apply LR_univ; assumption.
Qed.

Definition whnf_nat : whnf enat := or_introl v_nat.
Definition whnf_prop : whnf eprop := or_introl v_prop.
Definition whnf_prf p : whnf (eprf p) := or_introl (v_prf p).
Definition whnf_univ m : whnf (euniv m) := or_introl (v_univ m).
Definition whnf_pi A B : whnf (epi A B) := or_introl (v_pi A B).
Definition whnf_sig A B : whnf (esig A B) := or_introl (v_sig A B).
Definition whnf_w A B : whnf (ew A B) := or_introl (v_w A B).

(* ------------------------------------------------------------------ *)
(* The families for the formers with no components.  There is no        *)
(* neutral one: v2 has no r_ne (DESIGN.md sec. 4).                      *)
(* ------------------------------------------------------------------ *)

Definition natFam (k : nat) : kUFam k enat.
Proof.
  unshelve refine (Build_UFam (lvl k) k enat
    (fun v h pf => mkCode (mkNat k (rk v h) v (pf enat (eval_whnf enat whnf_nat))))
    _ _ _ _).
  - apply eqty_nat; apply eval_whnf; exact whnf_nat.
  - intros v h pf; apply eqty_nat; [apply pf; apply eval_whnf; exact whnf_nat
                                   | apply eval_whnf; exact whnf_nat].
  - intros v h pf; exact (mkNat_wf k (rk v h) v _).
  - intros v h pf v' h' pf'.
    exists k; apply eqty_nat; [apply pf | apply pf']; apply eval_whnf; exact whnf_nat.
Defined.

Definition propFam (k : nat) : kUFam k eprop.
Proof.
  unshelve refine (Build_UFam (lvl k) k eprop
    (fun v h pf => mkCode (mkProp k (rk v h) v (pf eprop (eval_whnf eprop whnf_prop))))
    _ _ _ _).
  - apply eqty_prop; apply eval_whnf; exact whnf_prop.
  - intros v h pf; apply eqty_prop; [apply pf; apply eval_whnf; exact whnf_prop
                                    | apply eval_whnf; exact whnf_prop].
  - intros v h pf; exact (mkProp_wf k (rk v h) v _).
  - intros v h pf v' h' pf'.
    exists k; apply eqty_prop; [apply pf | apply pf']; apply eval_whnf; exact whnf_prop.
Defined.

Definition prfFam (k : nat) (p : etm) (Hp : PR p p) (H : Prop) : kUFam k (eprf p).
Proof.
  unshelve refine (Build_UFam (lvl k) k (eprf p)
    (fun v h pf => mkCode (mkPrf k (rk v h) v p
                             (pf (eprf p) (eval_whnf _ (whnf_prf p))) H)) _ _ _ _).
  - eapply eqty_prf; [apply eval_whnf; exact (whnf_prf p)
                     | apply eval_whnf; exact (whnf_prf p) | exact Hp].
  - intros v h pf; eapply eqty_prf;
      [apply pf; apply eval_whnf; exact (whnf_prf p)
      | apply eval_whnf; exact (whnf_prf p) | exact Hp].
  - intros v h pf; exact (mkPrf_wf k (rk v h) v p _ H Hp).
  - intros v h pf v' h' pf'; split; [| split; exact (fun h0 => h0)].
    exists k; eapply eqty_prf;
      [apply pf; apply eval_whnf; exact (whnf_prf p)
      | apply pf'; apply eval_whnf; exact (whnf_prf p) | exact Hp].
Defined.

Definition univFam (k : nat) : kUFam (S k) (euniv k).
Proof.
  unshelve refine (Build_UFam (lvl (S k)) (S k) (euniv k)
    (fun v h pf => mkCode (mkUniv (S k) (rk v h) v k
                             (kOK_of (S k) k (Nat.lt_succ_diag_r k))
                             (pf (euniv k) (eval_whnf _ (whnf_univ k))))) _ _ _ _).
  - eapply eqty_univ; [apply Nat.lt_succ_diag_r | apply eval_whnf; exact (whnf_univ k)
                      | apply eval_whnf; exact (whnf_univ k)].
  - intros v h pf; eapply eqty_univ;
      [apply Nat.lt_succ_diag_r | apply pf; apply eval_whnf; exact (whnf_univ k)
      | apply eval_whnf; exact (whnf_univ k)].
  - intros v h pf; exact (mkUniv_wf (S k) (rk v h) v k _ _).
  - intros v h pf v' h' pf'; split; [| reflexivity].
    exists (S k); eapply eqty_univ;
      [apply Nat.lt_succ_diag_r | apply pf; apply eval_whnf; exact (whnf_univ k)
      | apply pf'; apply eval_whnf; exact (whnf_univ k)].
Defined.

(* ------------------------------------------------------------------ *)
(* The equality of elements of families.                               *)
(*                                                                    *)
(* v1 had `famTo_het` here -- a composite of two canonical transports    *)
(* reconciled by `hj_irr` -- because its equality could not compare      *)
(* elements of two codes.  In v2 every statement below is the coercion's *)
(* own `xto_eq`, or symmetry and transitivity of the equality.           *)
(* ------------------------------------------------------------------ *)

Lemma kEqAt_refl {k u} (F : kUFam k u) w x : kEqAt F w x F w x.
Proof. exact (kcrefl (kAt F) (famAtWf F) w x). Qed.

Lemma kEqAt_sym {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kEqAt F w x F' w' x' -> kEqAt F' w' x' F w x.
Proof. apply knsym. Qed.

Lemma kEqAt_trans {k u u' u''} (F : kUFam k u) w x (F' : kUFam k u') w' x'
  (F'' : kUFam k u'') w'' x'' :
  kceq (kAt F) (kAt F') -> kEqAt F w x F' w' x' -> kEqAt F' w' x' F'' w'' x'' ->
  kEqAt F w x F'' w'' x''.
Proof.
  intros Hc H H'.
  exact (ktrE (kAt F) (kAt F') (kAt F'') w x w' x' w'' x''
           (famAtWf F) (famAtWf F') (famAtWf F'') Hc H H').
Qed.

(* Moving an element to the canonical instance respects the equality.  The
   code equality of the two instances is a hypothesis, because two DIFFERENT
   families' instances are equal only when the families are. *)
Lemma famTo_eqX {k u u'} (F : kUFam k u) v h pf w x (F' : kUFam k u') v' h' pf' w' x' :
  kceq (uf_c F v h pf) (uf_c F' v' h' pf') ->
  kcel (uf_c F v h pf) w x (uf_c F' v' h' pf') w' x' ->
  kEqAt F w (famTo F v h pf w x) F' w' (famTo F' v' h' pf' w' x').
Proof.
  intros Hc H.
  assert (e1 : kceq (kAt F) (uf_c F v h pf))
    by exact (uf_coh F u (kAcc F) (evalAg_refl u) v h pf).
  eapply ktrE;
    [ exact (famAtWf F) | exact (famWf F v h pf) | exact (famAtWf F') | exact e1
    | apply knsym; apply famTo_coh |].
  eapply ktrE;
    [ exact (famWf F v h pf) | exact (famWf F' v' h' pf') | exact (famAtWf F')
    | exact Hc | exact H | apply famTo_coh ].
Qed.

(* the same family: its own coherence supplies the code equality *)
Lemma famTo_eq {k u} (F : kUFam k u) v h pf w x v' h' pf' w' x' :
  kcel (uf_c F v h pf) w x (uf_c F v' h' pf') w' x' ->
  kEqAt F w (famTo F v h pf w x) F w' (famTo F v' h' pf' w' x').
Proof. apply famTo_eqX; exact (uf_coh F v h pf v' h' pf'). Qed.

(* and the instances of two families are all equal as soon as the canonical
   ones are: compose the two coherences with the equality *)
Lemma famCeq_all {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') ->
  forall v h pf v' h' pf', kceq (uf_c F v h pf) (uf_c F' v' h' pf').
Proof.
  intros H v h pf v' h' pf'.
  eapply ktrU;
    [ exact (famWf F v h pf) | exact (famAtWf F) | exact (famWf F' v' h' pf')
    | exact (uf_coh F v h pf u (kAcc F) (evalAg_refl u)) |].
  eapply ktrU;
    [ exact (famAtWf F) | exact (famAtWf F') | exact (famWf F' v' h' pf')
    | exact H | exact (uf_coh F' u' (kAcc F') (evalAg_refl u') v' h' pf') ].
Qed.

(* Two equal families have layer-1 equal realisers.  This is the only way the
   interpretation gets a layer-1 equation out of an equality of codes, and it
   is what functionality needs to feed its own induction hypotheses. *)
Lemma ceq_ty {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> tyeq u u'.
Proof.
  intros H.
  eapply tyeq_trans;
    [ apply tyeq_sym; exact (ex_intro _ k (uf_sh F u (kAcc F) (evalAg_refl u))) |].
  eapply tyeq_trans;
    [ exact (U_tyeq (kU k) (kUEq k) (kOK k) (kAt F) (kAt F') H)
    | exact (ex_intro _ k (uf_sh F' u' (kAcc F') (evalAg_refl u'))) ].
Qed.

(* the realiser of a family is a layer-1 type, and its elements are good *)
Lemma fam_ty {k u} (F : kUFam k u) : eqty k u u.
Proof. exact (uf_ty F). Qed.

Lemma famEl_good {k u} (F : kUFam k u) w (x : kElAt F w) : Good u w.
Proof.
  eapply Good_tyeq;
    [ exact (ex_intro _ k (uf_sh F u (kAcc F) (evalAg_refl u)))
    | exact (U_good (kU k) (kUEq k) (kOK k) (lsound (lvl k)) _ (kAt F) w x) ].
Qed.

Lemma famEl_rel {k u u'} (F : kUFam k u) w x (F' : kUFam k u') w' x' :
  kEqAt F w x F' w' x' -> Rel u w w'.
Proof.
  intros H.
  eapply Rel_tyeq;
    [ exact (ex_intro _ k (uf_sh F u (kAcc F) (evalAg_refl u)))
    | exact (U_rel (kU k) (kUEq k) (kOK k) (lsound (lvl k)) (kAt F) (kAt F') w x w' x' H) ].
Qed.

(* and conversely: an equality of any two instances gives the equality of the
   canonical ones, which is how the lift's equality lemma lands *)
Lemma famCeq_of {k u u'} (F : kUFam k u) (F' : kUFam k u') v h pf v' h' pf' :
  kceq (uf_c F v h pf) (uf_c F' v' h' pf') -> kceq (kAt F) (kAt F').
Proof.
  intros H.
  eapply ktrU;
    [ exact (famAtWf F) | exact (famWf F v h pf) | exact (famAtWf F')
    | exact (uf_coh F u (kAcc F) (evalAg_refl u) v h pf) |].
  eapply ktrU;
    [ exact (famWf F v h pf) | exact (famWf F' v' h' pf') | exact (famAtWf F')
    | exact H | exact (uf_coh F' v' h' pf' u' (kAcc F') (evalAg_refl u')) ].
Qed.

(* and at the family's own level, which is what the universe's equality asks
   for: layer-1 cumulativity is restricted back to level k by `eqty_restrict`,
   using that both realisers are level-k types. *)
Lemma ceq_eqty {k u u'} (F : kUFam k u) (F' : kUFam k u') :
  kceq (kAt F) (kAt F') -> eqty k u u'.
Proof.
  intros H; destruct (ceq_ty F F' H) as [n Hn].
  exact (eqty_restrict k n u u' Hn (uf_ty F) (uf_ty F')).
Qed.

(* the backwards move respects the equality too: compose the two coherences
   with the given relation *)
Lemma famFrom_eq {k u} (F : kUFam k u) v h pf w x w' x' :
  kEqAt F w x F w' x' ->
  kcel (uf_c F v h pf) w (famFrom F v h pf w x)
       (uf_c F v h pf) w' (famFrom F v h pf w' x').
Proof.
  intros H.
  assert (e : kceq (uf_c F v h pf) (kAt F))
    by exact (uf_coh F v h pf u (kAcc F) (evalAg_refl u)).
  eapply ktrE;
    [ exact (famWf F v h pf) | exact (famAtWf F) | exact (famWf F v h pf)
    | exact e | apply knsym; exact (famFrom_coh F v h pf w x) |].
  eapply ktrE;
    [ exact (famAtWf F) | exact (famAtWf F) | exact (famWf F v h pf)
    | exact (famAtSelf F) | exact H | exact (famFrom_coh F v h pf w' x') ].
Qed.

(* the same between two families, given their equality: this is what the
   heterogeneous application law needs of its argument *)
Lemma famFrom_eqX {k u u'} (F : kUFam k u) v h pf w x
  (F' : kUFam k u') v' h' pf' w' x' :
  kceq (kAt F) (kAt F') -> kEqAt F w x F' w' x' ->
  kcel (uf_c F v h pf) w (famFrom F v h pf w x)
       (uf_c F' v' h' pf') w' (famFrom F' v' h' pf' w' x').
Proof.
  intros He H.
  eapply ktrE;
    [ exact (famWf F v h pf) | exact (famAtWf F) | exact (famWf F' v' h' pf')
    | exact (uf_coh F v h pf u (kAcc F) (evalAg_refl u))
    | apply knsym; exact (famFrom_coh F v h pf w x) |].
  eapply ktrE;
    [ exact (famAtWf F) | exact (famAtWf F') | exact (famWf F' v' h' pf')
    | exact He | exact H | exact (famFrom_coh F' v' h' pf' w' x') ].
Qed.

(* The round trip through an instance of a family is the identity, up to the
   family's own equality: the element is related to its image both ways, and
   the two relations compose. *)
Lemma famTo_famFrom {k u} (F : kUFam k u) v h pf w (y : kElAt F w) :
  kEqAt F w (famTo F v h pf w (famFrom F v h pf w y)) F w y.
Proof.
  apply kEqAt_sym.
  eapply ktrE;
    [ exact (famAtWf F) | exact (famWf F v h pf) | exact (famAtWf F)
    | exact (uf_coh F u (kAcc F) (evalAg_refl u) v h pf)
    | exact (famFrom_coh F v h pf w y)
    | exact (famTo_coh F v h pf w (famFrom F v h pf w y)) ].
Qed.

(* The other round trip through an instance: from the instance's own point of
   view this time. *)
Lemma famFrom_famTo {k u} (F : kUFam k u) v h pf w (z : kElC (uf_c F v h pf) w) :
  kcel (uf_c F v h pf) w (famFrom F v h pf w (famTo F v h pf w z))
       (uf_c F v h pf) w z.
Proof.
  assert (e : kceq (uf_c F v h pf) (kAt F))
    by exact (uf_coh F v h pf u (kAcc F) (evalAg_refl u)).
  eapply ktrE;
    [ exact (famWf F v h pf) | exact (famAtWf F) | exact (famWf F v h pf)
    | exact e
    | apply knsym; exact (famFrom_coh F v h pf w (famTo F v h pf w z))
    | apply knsym; exact (famTo_coh F v h pf w z) ].
Qed.
