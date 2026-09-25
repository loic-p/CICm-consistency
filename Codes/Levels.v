From CICM Require Import core unscoped Syntax.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Sound Codes.EqPER Codes.Expand Codes.Iso
  Codes.WF Codes.IsoPER.
From Stdlib Require Import Arith Lia.

(* The outer recursion on the object level.  Everything the code hierarchy
   needs of its universe parameter is bundled into one record, which is then
   built by recursion on the level; the level-n codes are the codes over the
   record for level n, and the universe u_n is decoded by them.  This is what
   keeps the hierarchy at one fixed metatheoretic universe for every object
   level, which is the whole point of the exercise: `lU` is a field of type
   `nat -> etm -> Type`, so `U (lU L) ... : Type` at the same level, and the
   record for level n+1 is built from it without escalation.

   The universe decoding carries `LIso c c` -- self-isomorphism of the code.
   It is free for the codes the interpretation builds (their coherence data
   IS the canonical transport), and it is what makes the equality on the
   universe reflexive, which the expansion closure of the decoding needs. *)

Record Lvl := {
  lU : nat -> etm -> Type;
  lUEq : forall m u, lU m u -> forall u', lU m u' -> Prop;
  lOK : nat -> Prop;
  lsym : forall m u x u' x', lUEq m u x u' x' -> lUEq m u' x' u x;
  ltrans : forall m u x u' x' u'' x'',
      lUEq m u x u' x' -> lUEq m u' x' u'' x'' -> lUEq m u x u'' x'';
  lsound : UnivSound lU lUEq lOK;
  lexp : UnivExp lU lUEq
}.

Definition LCode (L : Lvl) (beta : Ord) : Type := U L.(lU) L.(lUEq) L.(lOK) beta.
Definition LSh {L beta} (c : LCode L beta) : etm := projT1 c.
Definition LIso {L b b'} (c : LCode L b) (c' : LCode L b') : Prop :=
  ciso L.(lU) L.(lUEq) L.(lOK) L.(lsym) L.(ltrans) c c'.

(* v agrees with u: every whnf of u is one of v.  This direction is the one
   that is usable, because the realiser u of a type is its erasure, which is
   already a whnf -- so the agreement yields `eval v <that whnf>` outright,
   which is what every code constructor asks for. *)
Definition evalAg (v u : etm) : Prop := forall w, eval u w -> eval v w.

Lemma evalAg_refl u : evalAg u u.
Proof. intros w H; exact H. Qed.

Lemma evalAg_red v u u1 : reds u u1 -> evalAg v u1 -> evalAg v u.
Proof. intros H P w Hu; apply P; eapply eval_reds_inv; [exact H | exact Hu]. Qed.

Lemma evalAg_exp v u u1 : reds u u1 -> evalAg v u -> evalAg v u1.
Proof. intros H P w Hu1; apply P; eapply eval_reds; [exact H | exact Hu1]. Qed.

Definition LIdP {L beta} (c : LCode L beta) : Prop :=
  IdP (Ust L.(lU) L.(lUEq) L.(lOK) beta)
      (hjU L.(lU) L.(lUEq) L.(lOK) L.(lsym) L.(ltrans) beta beta) c.

(* The decoding of the universe u_n at the realiser u: not one code, but the
   whole coherent FAMILY of codes for u, indexed by a term agreeing with u
   and by an accessibility proof of that term.  This is exactly what the
   fundamental lemma produces, and it buys two things that would otherwise
   each need a lift along a simulation of Brouwer trees: a type variable's
   code can be read off at whatever node the surrounding code requires, and
   the decoding is closed under reduction and expansion of the realiser on
   the nose.  `LIso c c` and `LIdP c` are carried because they are free for
   the codes the interpretation builds and are what the equality's
   reflexivity and the Pi-code's identity law need. *)
Record UFam (L : Lvl) (n : nat) (u : etm) : Type := {
  uf_c : forall v (h : Acc prec v), evalAg v u -> LCode L (rk v h);
  uf_ty : eqty n u u;
  uf_sh : forall v h pf, eqty n (LSh (uf_c v h pf)) u;
  uf_coh : forall v h pf v' h' pf', LIso (uf_c v h pf) (uf_c v' h' pf');
  uf_idp : forall v h pf, LIdP (uf_c v h pf)
}.
Arguments uf_c {L n u}. Arguments uf_ty {L n u}. Arguments uf_sh {L n u}.
Arguments uf_coh {L n u}. Arguments uf_idp {L n u}.

Definition LUniv (L : Lvl) (n : nat) (u : etm) : Type := UFam L n u.

(* One instance of the family always exists: the realiser is a good type, so
   it is accessible. *)
Definition uf_acc {L n u} (x : UFam L n u) : Acc prec u :=
  Good_ty_acc u (ex_intro _ n (uf_ty x)).
Definition uf_at {L n u} (x : UFam L n u) : LCode L (rk u (uf_acc x)) :=
  uf_c x u (uf_acc x) (evalAg_refl u).

Definition LUnivEq (L : Lvl) (n : nat) u (x : UFam L n u) u' (x' : UFam L n u') : Prop :=
  eqty n u u' /\
  (forall v h pf v' h' pf', LIso (uf_c x v h pf) (uf_c x' v' h' pf')).

Lemma univ_good_ty n m T : m < n -> eval T (euniv m) -> Good_ty T.
Proof.
  intros Hm He; exists n; exists (fun C C' => exists P, below n m C C' P).
  apply LR_univ; assumption.
Qed.

(* Level 0: no universes at all. *)
Definition eU : nat -> etm -> Type := fun _ _ => Empty_set.
Definition eUEq : forall m u, eU m u -> forall u', eU m u' -> Prop :=
  fun m u x => match x with end.

Definition lvl0 : Lvl :=
  Build_Lvl eU eUEq (fun _ => False)
    (fun m u x => match x with end)
    (fun m u x => match x with end)
    (Build_UnivSound eU eUEq (fun _ => False)
       (fun m u x => match x with end)
       (fun m u x => match x with end)
       (fun m T H _ => match H with end))
    (Build_UnivExp eU eUEq
       (fun m u u1 H x => match x with end)
       (fun m u u1 H y => match y with end)
       (fun m u u1 H x => match x with end)
       (fun m u u1 H y => match y with end)).

Section Step.
  Context (n : nat) (L : Lvl).

  Definition sU (m : nat) (u : etm) : Type :=
    match Nat.eq_dec m n with
    | left _ => LUniv L n u
    | right _ => L.(lU) m u
    end.

  Definition sUEq (m : nat) : forall u, sU m u -> forall u', sU m u' -> Prop.
  Proof.
    unfold sU; destruct (Nat.eq_dec m n) as [E | NE].
    - exact (fun u x u' x' => LUnivEq L n u x u' x').
    - exact (fun u x u' x' => L.(lUEq) m u x u' x').
  Defined.

  Definition sU_red (m : nat) (u u1 : etm) (H : reds u u1) : sU m u -> sU m u1.
  Proof.
    unfold sU; destruct (Nat.eq_dec m n) as [E | NE].
    - intros F.
      refine (Build_UFam L n u1 (fun v h pf => uf_c F v h (evalAg_red v u u1 H pf)) _ _ _ _).
      + eapply eqty_red; [apply (uf_ty F) | exact H | exact H].
      + intros v h pf; eapply eqty_red; [apply (uf_sh F) | apply reds_refl | exact H].
      + intros; apply uf_coh.
      + intros; apply uf_idp.
    - exact (ue_red L.(lexp) m u u1 H).
  Defined.

  Definition sU_exp (m : nat) (u u1 : etm) (H : reds u u1) : sU m u1 -> sU m u.
  Proof.
    unfold sU; destruct (Nat.eq_dec m n) as [E | NE].
    - intros F.
      refine (Build_UFam L n u (fun v h pf => uf_c F v h (evalAg_exp v u u1 H pf)) _ _ _ _).
      + eapply eqty_exp; [exact H | exact H | apply (uf_ty F)].
      + intros v h pf; eapply eqty_exp; [apply reds_refl | exact H | apply (uf_sh F)].
      + intros; apply uf_coh.
      + intros; apply uf_idp.
    - exact (ue_exp L.(lexp) m u u1 H).
  Defined.

  Definition lvl_step : Lvl.
  Proof.
    refine (Build_Lvl sU sUEq (fun m => m < S n) _ _ _ _).
    - (* lsym *)
      intros m; unfold sUEq, sU; destruct (Nat.eq_dec m n) as [E | NE]; cbn.
      + intros u x u' x' [H1 H2]; split; [apply eqty_sym; exact H1 |].
        intros v h pf v' h' pf'; unfold LIso in *.
        apply (ciso_sym L.(lU) L.(lUEq) L.(lOK) L.(lsym) L.(ltrans)).
        exact (H2 v' h' pf' v h pf).
      + apply L.(lsym).
    - (* ltrans *)
      intros m; unfold sUEq, sU; destruct (Nat.eq_dec m n) as [E | NE]; cbn.
      + intros u x u' x' u'' x'' [H1 H2] [H1' H2']; split;
          [eapply eqty_trans; eassumption |].
        intros v h pf v'' h'' pf''; unfold LIso in *.
        eapply (ciso_trans L.(lU) L.(lUEq) L.(lOK) L.(lsym) L.(ltrans));
          [ exact (H2 v h pf u' (uf_acc x') (evalAg_refl u'))
          | exact (H2' u' (uf_acc x') (evalAg_refl u') v'' h'' pf'') ].
      + apply L.(ltrans).
    - (* lsound *)
      constructor.
      + intros m u; unfold sUEq, sU; destruct (Nat.eq_dec m n) as [E | NE]; cbn.
        * subst m. intros F; exact (uf_ty F).
        * apply (us_ty _ _ _ L.(lsound)).
      + intros m u x u' x'; unfold sUEq, sU in *;
          revert x x'; destruct (Nat.eq_dec m n) as [E | NE]; cbn.
        * subst m; intros x x' [H1 _]; exact H1.
        * intros x x'; apply (us_eq _ _ _ L.(lsound)).
      + intros m T Hm He; eapply univ_good_ty; [exact Hm | exact He].
    - (* lexp *)
      unshelve refine (Build_UnivExp _ _ sU_red sU_exp _ _).
      + intros m u u1 H; unfold sUEq, sU, sU_red;
          destruct (Nat.eq_dec m n) as [E | NE]; cbn.
        * intros F; split;
            [ eapply eqty_red; [apply (uf_ty F) | apply reds_refl | exact H]
            | intros v h pf v' h' pf';
              exact (uf_coh F v h pf v' h' (evalAg_red v' u u1 H pf')) ].
        * apply (ue_red_rel L.(lexp)).
      + intros m u u1 H; unfold sUEq, sU, sU_exp;
          destruct (Nat.eq_dec m n) as [E | NE]; cbn.
        * intros F; split;
            [ eapply eqty_exp; [exact H | apply reds_refl | apply (uf_ty F)]
            | intros v h pf v' h' pf';
              exact (uf_coh F v h (evalAg_exp v u u1 H pf) v' h' pf') ].
        * apply (ue_exp_rel L.(lexp)).
  Defined.
End Step.

Fixpoint lvl (n : nat) : Lvl :=
  match n with
  | 0 => lvl0
  | S k => lvl_step k (lvl k)
  end.

(* What the decoding of the universe u_m is, at any level above m: the
   coherent family of level-m codes.  Needed because the level hierarchy is
   truncated per level, so `lU (lvl k) m u` only reaches `UFam (lvl m) m u`
   after k - m steps through the `Nat.eq_dec` matches. *)
Lemma lU_spec : forall k m u, m < k -> lU (lvl k) m u = UFam (lvl m) m u.
Proof.
  induction k as [| j IH]; intros m u Hm; [inversion Hm |].
  cbn; unfold sU; destruct (Nat.eq_dec m j) as [E | NE].
  - subst m; reflexivity.
  - apply IH; lia.
Qed.

(* The codes of level n, their shadows and their isomorphism. *)
Definition Code (n : nat) (beta : Ord) : Type := LCode (lvl n) beta.
Definition sh {n beta} (c : Code n beta) : etm := LSh c.
Definition iso {n b b'} (c : Code n b) (c' : Code n b') : Prop := LIso c c'.

(* The shadows of isomorphic codes are layer-1 equal. *)
Lemma LIso_sh {L b b'} (c : LCode L b) (c' : LCode L b') :
  LIso c c' -> tyeq (LSh c) (LSh c').
Proof. apply isoRefine_sh. Qed.

Lemma iso_sh {n b b'} (c : Code n b) (c' : Code n b') : iso c c' -> tyeq (sh c) (sh c').
Proof. apply LIso_sh. Qed.
