From CICM Require Import Syntax.Erased.
From CICM Require Import Reduction.Def Reduction.Stuck Reduction.Determinism.
From CICM Require Import Layer1.Per Layer1.Def Layer1.Bundle Layer1.Elim.
From CICM Require Import Ranks.Pred Ranks.Ord Ranks.Acc Ranks.Rank.
From CICM Require Import Codes.Def Codes.Eq Codes.WF Codes.Sym Codes.Str
  Codes.Sound Codes.Expand.
From Stdlib Require Import Arith Lia.

(* The outer recursion on the object level.  Everything the code hierarchy
   needs of its universe parameter is bundled into one record, which is then
   built by recursion on the level; the level-n codes are the codes over the
   record for level n, and the universe u_n is decoded by them.  This is what
   keeps the hierarchy at one fixed metatheoretic universe for every object
   level, which is the whole point of the exercise: `lU` is a field of type
   `nat -> etm -> Type`, so the codes over it live at the same universe, and
   the record for level n+1 is built from it without escalation.

   Differences from v1.  The parameter's equality is heterogeneous in the
   LEVEL as well as in the realiser, so the step has to decide two levels
   rather than one, but nothing ever transports along an equality of levels.
   And `UFam` carries well-formedness where v1 carried `IdP`, plus the
   coherence of the family; v1's `uf_idp` -- the identity law of the carried
   transport -- is gone with the transports. *)

Record Lvl := {
  lU : nat -> etm -> Type;
  lUEq : forall m u, lU m u -> forall m' u', lU m' u' -> Prop;
  lOK : nat -> Prop;
  lrefl : forall m u x, lUEq m u x m u x;
  lsym : forall m u x m' u' x', lUEq m u x m' u' x' -> lUEq m' u' x' m u x;
  ltrans : forall m u x m' u' x' m'' u'' x'',
      lUEq m u x m' u' x' -> lUEq m' u' x' m'' u'' x'' -> lUEq m u x m'' u'' x'';
  lsound : UnivSound lU lUEq lOK;
  lexp : UnivExp lU lUEq
}.

(* the code hierarchy over a level record *)
Definition LSub (L : Lvl) (alpha : Ord) : Type := Sub (lU L) (lOK L) alpha.
Definition LCode (L : Lvl) (beta : Ord) : Type := U (lU L) (lOK L) beta.
Definition LSh {L beta} (c : LCode L beta) : etm := projT1 c.
Definition Lceq {L b b'} (c : LCode L b) (c' : LCode L b') : Prop :=
  ceq (lU L) (lUEq L) (lOK L) c c'.
Definition Lwfc {L b} (c : LCode L b) : Prop := wfc (lU L) (lUEq L) (lOK L) c.

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

(* The decoding of the universe u_n at the realiser u: not one code, but the
   whole coherent FAMILY of codes for u, indexed by a term agreeing with u and
   by an accessibility proof of that term.  This is exactly what the
   fundamental lemma produces, and it buys two things that would otherwise
   each need a lift along a simulation of Brouwer trees: a type variable's code
   can be read off at whatever node the surrounding code requires, and the
   decoding is closed under reduction and expansion of the realiser on the
   nose.  Well-formedness and the coherence of the family are carried because
   they are free for the codes the interpretation builds. *)
Record UFam (L : Lvl) (n : nat) (u : etm) : Type := {
  uf_c : forall v (h : Acc prec v), evalAg v u -> LCode L (rk v h);
  uf_ty : eqty n u u;
  uf_sh : forall v h pf, eqty n (LSh (uf_c v h pf)) u;
  uf_wf : forall v h pf, Lwfc (uf_c v h pf);
  uf_coh : forall v h pf v' h' pf', Lceq (uf_c v h pf) (uf_c v' h' pf')
}.
Arguments uf_c {L n u}. Arguments uf_ty {L n u}. Arguments uf_sh {L n u}.
Arguments uf_wf {L n u}. Arguments uf_coh {L n u}.

Definition LUniv (L : Lvl) (n : nat) (u : etm) : Type := UFam L n u.

(* One instance of the family always exists: the realiser is a good type, so
   it is accessible. *)
Definition uf_acc {L n u} (x : UFam L n u) : Acc prec u :=
  Good_ty_acc u (ex_intro _ n (uf_ty x)).
Definition uf_at {L n u} (x : UFam L n u) : LCode L (rk u (uf_acc x)) :=
  uf_c x u (uf_acc x) (evalAg_refl u).

Definition LUnivEq (L : Lvl) (n : nat) u (x : UFam L n u) u' (x' : UFam L n u') : Prop :=
  eqty n u u' /\ (forall v h pf v' h' pf', Lceq (uf_c x v h pf) (uf_c x' v' h' pf')).

Lemma univ_good_ty n m T : m < n -> eval T (euniv m) -> Good_ty T.
Proof.
  intros Hm He; exists n; exists (fun C C' => exists P, below n m C C' P).
  apply LR_univ; assumption.
Qed.

(* Level 0: no universes at all. *)
Definition eU : nat -> etm -> Type := fun _ _ => Empty_set.
Definition eUEq : forall m u, eU m u -> forall m' u', eU m' u' -> Prop :=
  fun m u x => match x with end.

Definition lvl0 : Lvl :=
  Build_Lvl eU eUEq (fun _ => False)
    (fun m u x => match x with end)
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

(* The parameter for level n+1: the new level's families, or one of the old
   levels' elements, each carrying the level (dis)equality that put it there.
   v1 decided `Nat.eq_dec m n` inside the TYPE, which made the equality a
   double decision and the level lift a transport along an opaque proof of
   type equality; with the sum every match is on a constructor, and the lift's
   universe clause becomes a constructor injection. *)
Definition sU (m : nat) (u : etm) : Type :=
  ((LUniv L n u * (m = n)) + (lU L m u * (m <> n)))%type.

Definition sUEq (m : nat) (u : etm) (x : sU m u) (m' : nat) (u' : etm) (x' : sU m' u')
  : Prop :=
  match x, x' with
  | inl (F, _), inl (F', _) => LUnivEq L n u F u' F'
  | inr (y, _), inr (y', _) => lUEq L m u y m' u' y'
  | _, _ => False
  end.

Definition sU_red (m : nat) (u u1 : etm) (H : reds u u1) (x : sU m u) : sU m u1 :=
  match x with
  | inl (F, e) =>
      inl (Build_UFam L n u1 (fun v h pf => uf_c F v h (evalAg_red v u u1 H pf))
             (eqty_red n u u u1 u1 (uf_ty F) H H)
             (fun v h pf => eqty_red n _ _ _ _ (uf_sh F v h _) (reds_refl _) H)
             (fun v h pf => uf_wf F v h _)
             (fun v h pf v' h' pf' => uf_coh F v h _ v' h' _), e)
  | inr (y, ne) => inr (ue_red (lexp L) m u u1 H y, ne)
  end.

Definition sU_exp (m : nat) (u u1 : etm) (H : reds u u1) (x : sU m u1) : sU m u :=
  match x with
  | inl (F, e) =>
      inl (Build_UFam L n u (fun v h pf => uf_c F v h (evalAg_exp v u u1 H pf))
             (eqty_exp n u u u1 u1 H H (uf_ty F))
             (fun v h pf => eqty_exp n _ _ _ _ (reds_refl _) H (uf_sh F v h _))
             (fun v h pf => uf_wf F v h _)
             (fun v h pf v' h' pf' => uf_coh F v h _ v' h' _), e)
  | inr (y, ne) => inr (ue_exp (lexp L) m u u1 H y, ne)
  end.

Definition lvl_step : Lvl.
Proof.
  refine (Build_Lvl sU sUEq (fun m => m < S n) _ _ _ _ _).
  - (* lrefl *)
    intros m u [[F e] | [y ne]]; cbn.
    + split; [apply (uf_ty F) | intros; apply uf_coh].
    + apply (lrefl L).
  - (* lsym *)
    intros m u [[F e] | [y ne]] m' u' [[F' e'] | [y' ne']]; cbn;
      try (exact (fun h => match h with end)).
    + intros [H1 H2]; split; [apply eqty_sym; exact H1 |].
      intros v h pf v' h' pf'.
      apply (nsymU (lU L) (lUEq L) (lOK L) (lsym L)).
      exact (H2 v' h' pf' v h pf).
    + apply (lsym L).
  - (* ltrans *)
    intros m u [[F e] | [y ne]] m' u' [[F' e'] | [y' ne']] m'' u'' [[F'' e''] | [y'' ne'']];
      cbn; try (exact (fun h => match h with end));
      try (exact (fun _ h => match h with end)).
    + intros [H1 H2] [H1' H2']; split; [eapply eqty_trans; eassumption |].
      intros v h pf v'' h'' pf''.
      eapply (xtrU (lU L) (lUEq L) (lOK L) (lrefl L) (lsym L) (ltrans L));
        [ exact (uf_wf F v h pf)
        | exact (uf_wf F' u' (uf_acc F') (evalAg_refl u'))
        | exact (uf_wf F'' v'' h'' pf'')
        | exact (H2 v h pf u' (uf_acc F') (evalAg_refl u'))
        | exact (H2' u' (uf_acc F') (evalAg_refl u') v'' h'' pf'') ].
    + apply (ltrans L).
  - (* lsound *)
    constructor.
    + intros m u [[F e] | [y ne]];
        [ rewrite e; exact (uf_ty F) | apply (us_ty (lsound L)); exact y ].
    + intros m u [[F e] | [y ne]] m' u' [[F' e'] | [y' ne']]; cbn;
        try (exact (fun h => match h with end)).
      * intros [H1 _]; rewrite e; exact H1.
      * apply (us_eq (lsound L)).
    + intros m T Hm He; eapply univ_good_ty; [exact Hm | exact He].
  - (* lexp *)
    unshelve refine (Build_UnivExp _ _ sU_red sU_exp _ _).
    + intros m u u1 H [[F e] | [y ne]]; cbn.
      * split; [eapply eqty_red; [apply (uf_ty F) | apply reds_refl | exact H]
               | intros v h pf v' h' pf';
                 exact (uf_coh F v h pf v' h' (evalAg_red v' u u1 H pf')) ].
      * apply (ue_red_rel (lexp L)).
    + intros m u u1 H [[F e] | [y ne]]; cbn.
      * split; [eapply eqty_exp; [exact H | apply reds_refl | apply (uf_ty F)]
               | intros v h pf v' h' pf';
                 exact (uf_coh F v h (evalAg_exp v u u1 H pf) v' h' pf') ].
      * apply (ue_exp_rel (lexp L)).
Defined.
End Step.

Fixpoint lvl (n : nat) : Lvl :=
  match n with
  | 0 => lvl0
  | S k => lvl_step k (lvl k)
  end.

(* The decoding of the universe u_m at a level above m: the injection is a
   constructor, so it computes -- where v1 had to transport along `lU_spec`, an
   equality of TYPES proved by induction on the level and therefore opaque.
   This is what makes the universe clause of the level lift trivial. *)
Definition lU_up (k m : nat) (u : etm) (H : m <> k) (x : lU (lvl k) m u)
  : lU (lvl (S k)) m u := inr (x, H).

Lemma lU_up_eq (k m : nat) u (H : m <> k) x u' (H' : m <> k) x' :
  lUEq (lvl k) m u x m u' x' <-> lUEq (lvl (S k)) m u (lU_up k m u H x) m u' (lU_up k m u' H' x').
Proof. cbn; split; exact (fun h => h). Qed.

(* The codes of level n, their shadows, their equality and their
   well-formedness. *)
Definition Code (n : nat) (beta : Ord) : Type := LCode (lvl n) beta.
Definition sh {n beta} (c : Code n beta) : etm := LSh c.
Definition ceqn {n b b'} (c : Code n b) (c' : Code n b') : Prop := Lceq c c'.
Definition wfn {n b} (c : Code n b) : Prop := Lwfc c.

Lemma ceqn_sh {n b b'} (c : Code n b) (c' : Code n b') : ceqn c c' -> tyeq (sh c) (sh c').
Proof. apply (U_tyeq (lU (lvl n)) (lUEq (lvl n)) (lOK (lvl n))). Qed.
