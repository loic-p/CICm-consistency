From CICM Require Import core unscoped Syntax.

Import UnscopedNotations.
Open Scope list_scope.
Open Scope subst_scope.


(* The rules of CIC^-, in the redundant style.  The three judgements are
   Type-valued, not Prop-valued: the fundamental lemma computes semantic
   data -- codes and their elements -- by recursion on a derivation, and a
   Prop-valued inductive admits no such elimination.

   The rules in the redundant style: every rule carries, as extra
   premises, the formation judgements of every type it mentions.  This costs
   nothing to state and buys the whole of Typing/Inversion.v, and -- as the
   blueprint's Proposition 5.1 observes -- it is what makes stability under
   weakening and substitution unnecessary: neither fundamental lemma ever
   transports a derivation into another context, and the presuppositions
   that usually force weakening are supplied by the redundant premises.

   On `up`.  The signature's `up` takes two arguments; we read `up (univ k) A`
   as the explicit embedding of the type A from Typek into Typek+1, with the
   source universe recorded so that the rule is syntax-directed (the
   blueprint writes it with one argument and an implicit level).  Erasure
   sends it to the erasure of its second argument, so the embedding is
   transparent on realisers, and the interpretation will send it to the same
   code.  `up` is ALSO the term-level lift (t_up_tm): the embedding of terms
   is explicit rather than silent, which is what makes typing unique.

   On unicity of typing.  The syntax is deliberately explicit enough that a
   term determines its type up to conversion, and in particular determines
   every universe level: the forall-lambda and forall-application are their own
   formers (plam, papp), and the term-level lift is written.  Levels then come
   off the syntax -- `nat_`, `prop`, `prf p` at Type0, `univ k` and
   `up (univ k) A` at Typek+1, Pi and Sigma at their components' level -- which
   is what the interpretation needs when it has to compare two readings of the
   same type.  Proving it post hoc about a theory with silent lifts is not an
   option: reaching `ty G A (univ k)` through t_conv would need
   `univ k /= univ k'` for k /= k', which is a consequence of the model being
   built.

   On Eq.  CIC^- as described in the paper has Eq : Prop with transport, and
   the syntax still carries eqty/refl/transp (it is generated), but there are
   NO RULES for them here: equality is deliberately outside the formalised
   theory.

   The reason is in Layer1/BadTransp.v, which derives False from the
   transport rule alone.  The erasure of a transport is its subject, so
   layer 1 has to keep one realiser while its type moves from B[t/x] to
   B[u/x]; being truth-agnostic, it cannot tell a true equation from a false
   one, and it cannot tell transp b from b.  In the POPL'23 model that this
   one is based on the question does not arise: transport there computes by
   recursion on the head constructors of the types, and propositions are
   definitionally proof-irrelevant, so transports of proofs never need to
   compute.  Restricting the motive to Prop does make the rule sound, but it
   weakens the theory (no large elimination for Eq) rather than modelling the
   intended one, so Eq waits for a model that can carry it. *)

Definition ctx := list tm.

(* The type of variable i in Gamma, with the de Bruijn shifts applied. *)
Inductive lookup : nat -> ctx -> tm -> Prop :=
| lookup_O G A : lookup 0 (A :: G) (A ⟨↑⟩)
| lookup_S G i A B : lookup i G A -> lookup (S i) (B :: G) (A ⟨↑⟩).

(* The motive of natrec at a successor: C is in context (nat_ :: Gamma), and
   nrec_succ C is C[succ (var 1)] in context (C :: nat_ :: Gamma).  That is the
   type of the STEP TERM, which carries its own two binders -- var 1 for the
   scrutinee's predecessor, var 0 for the recursive result.

   There is deliberately no `nrec_step C = pi nat_ (pi C (nrec_succ C))`.  A
   function of that type is formed by t_pi, which is homogeneous in the level,
   so it would need `ty G nat_ (univ k)` at the motive's level k -- and t_nat
   gives only univ 0.  Every route to `ty G s (nrec_step C)` (t_lam, t_var
   through wfc, t_conv, t_app, t_fst, t_absurd, t_natrec) in turn requires
   nrec_step C to be formed at some universe, so with the function form the
   rule was derivable only for k = 0 and large elimination above Type0 was
   unreachable.  The binder form needs no type for the step at all. *)
Definition nrec_succ (C : tm) : tm :=
  C [ succ (var_tm 1) .: (fun i => var_tm (S (S i))) ].

Reserved Notation "'⊢' G" (at level 80).
Reserved Notation "G '⊢' t ':' A" (at level 80, t at next level).
Reserved Notation "G '⊢' t '≡' u ':' A" (at level 80, t at next level, u at next level).

Inductive wfc : ctx -> Type :=
| w_nil : wfc nil
| w_cons G A k : wfc G -> ty G A (univ k) -> wfc (A :: G)

with ty : ctx -> tm -> tm -> Type :=
(* structural *)
| t_var G i A : wfc G -> lookup i G A -> ty G (var_tm i) A
| t_conv G t A B k : ty G t A -> ty G A (univ k) -> ty G B (univ k) ->
    cv G A B (univ k) -> ty G t B

(* universes *)
| t_univ G k : wfc G -> ty G (univ k) (univ (S k))
(* The annotation on a lift records THE UNIVERSE THE SUBJECT'S TYPE LIVES IN,
   which for the type lift is the successor of the lifted type's own level (and
   coincides with the result type) and for the term lift is the level of the
   term's type.  The two used to disagree -- t_up annotated with the subject's
   own universe -- and the interpretation of RAW syntax was then ambiguous in
   the level: Layer1/Elim.v's Rel_prf_intro relates every realiser at a Prf
   type, so i_proof reads any subject as a proof at level 0, i_up_tm lifts that
   to level 1, while i_ty after ity_up gives level 2 for the same term.  With
   the annotations uniform both readings of `up (univ j) X` sit at level S j and
   the level is read off the annotation. *)
| t_up G A k : ty G A (univ k) -> ty G (up (univ (S k)) A) (univ (S k))
(* The lift on TERMS is explicit: `up` doubles as its own term former, so a
   term of A does not silently also have type up (univ k) A.  The two
   transparency rules that used to say it did (t_up_in / t_up_out) made typing
   non-unique -- t : A and t : up (univ k) A for the same t -- and unicity of
   typing, universe levels included, is what lets the level of a forall-domain
   be read off the syntax.  Nothing is lost: the lift is still there, small
   types still appear in large ones, and erasure still sends `up A t` to the
   erasure of t, so the lift is invisible on realisers. *)
| t_up_tm G A t k : ty G A (univ k) -> ty G t A ->
    ty G (uptm A t) (up (univ (S k)) A)

(* Pi *)
| t_pi G A B k : ty G A (univ k) -> ty (A :: G) B (univ k) -> ty G (pi A B) (univ k)
| t_lam G A B t k : ty G A (univ k) -> ty (A :: G) B (univ k) -> ty (A :: G) t B ->
    ty G (lam A B t) (pi A B)
| t_app G A B f u k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G f (pi A B) -> ty G u A -> ty G (app A B f u) (B [u..])

(* Sigma *)
| t_sig G A B k : ty G A (univ k) -> ty (A :: G) B (univ k) -> ty G (sig_ A B) (univ k)
| t_pair G A B t u k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G t A -> ty G u (B [t..]) -> ty G (pair A B t u) (sig_ A B)
| t_fst G A B p k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G p (sig_ A B) -> ty G (fst A B p) A
| t_snd G A B p k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G p (sig_ A B) -> ty G (snd A B p) (B [(fst A B p)..])

(* N and its large elimination *)
| t_nat G : wfc G -> ty G nat_ (univ 0)
| t_zero G : wfc G -> ty G zero nat_
| t_succ G n : ty G n nat_ -> ty G (succ n) nat_
| t_natrec G C z s n k :
    ty (nat_ :: G) C (univ k) ->
    ty G z (C [zero..]) -> ty (C :: nat_ :: G) s (nrec_succ C) -> ty G n nat_ ->
    ty G (natrec C z s n) (C [n..])

(* Prop, Prf, impredicative forall, bottom *)
| t_prop G : wfc G -> ty G prop (univ 0)
| t_prf G p : ty G p prop -> ty G (prf p) (univ 0)
| t_all G A p k : ty G A (univ k) -> ty (A :: G) p prop -> ty G (all A p) prop
(* The forall-lambda and forall-application are their OWN formers, plam and
   papp, not lam and app: with one lambda, `lam A t` inhabits both
   pi A (prf p) and prf (all A p), so neither the type nor the universe level
   is determined by the term.  They erase exactly as lam and app do
   (Syntax/Erasure.v), so this costs nothing on realisers, and their conversion
   rules are subsumed by c_prf_irr, every papp and plam living at a Prf type. *)
| t_all_intro G A p t k : ty G A (univ k) -> ty (A :: G) p prop ->
    ty (A :: G) t (prf p) -> ty G (plam A t) (prf (all A p))
| t_all_elim G A p f u k : ty G A (univ k) -> ty (A :: G) p prop ->
    ty G f (prf (all A p)) -> ty G u A -> ty G (papp f u) (prf (p [u..]))
| t_false G : wfc G -> ty G false_ prop
| t_absurd G T e k : ty G T (univ k) -> ty G e (prf false_) -> ty G (absurd T e) T

(* NO Eq.  See the note on Eq at the top of the file. *)

with cv : ctx -> tm -> tm -> tm -> Type :=
(* equivalence, conversion of the type, proof irrelevance *)
| c_refl G t A : ty G t A -> cv G t t A
| c_sym G t u A : cv G t u A -> cv G u t A
| c_trans G t u v A : cv G t u A -> cv G u v A -> cv G t v A
| c_conv G t u A B k : cv G t u A -> ty G A (univ k) -> ty G B (univ k) ->
    cv G A B (univ k) -> cv G t u B
| c_prf_irr G p e e' : ty G p prop -> ty G e (prf p) -> ty G e' (prf p) -> cv G e e' (prf p)

(* universes *)
| c_up G A A' k : ty G A (univ k) -> ty G A' (univ k) -> cv G A A' (univ k) ->
    cv G (up (univ (S k)) A) (up (univ (S k)) A') (univ (S k))
| c_up_tm G A t t' k : ty G A (univ k) -> ty G t A -> ty G t' A -> cv G t t' A ->
    cv G (uptm A t) (uptm A t') (up (univ (S k)) A)

(* Pi *)
| c_pi G A A' B B' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G A' (univ k) -> ty (A' :: G) B' (univ k) ->
    cv G A A' (univ k) -> cv (A :: G) B B' (univ k) -> cv G (pi A B) (pi A' B') (univ k)
(* The lambda congruence, in the same shape as c_pi: the PRIMED premises live
   in the PRIMED context.  It used to keep the codomain B and the body t' in
   the A-context while annotating the subject with A', and then the semantics
   of `lam A' B t'` could not be given: interpreting B and t' asks for an
   environment extended by A''s family, whose realiser is `ers rho A'`, and
   that is not an environment for A :: G.  Modulo context conversion -- which
   is admissible -- the two rules prove the same conversions. *)
| c_lam G A A' B B' t t' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G A' (univ k) -> ty (A' :: G) B' (univ k) ->
    cv G A A' (univ k) -> cv (A :: G) B B' (univ k) ->
    ty (A :: G) t B -> ty (A' :: G) t' B' -> cv (A :: G) t t' B ->
    cv G (lam A B t) (lam A' B' t') (pi A B)
| c_app G A B f f' u u' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G f (pi A B) -> ty G f' (pi A B) -> cv G f f' (pi A B) ->
    ty G u A -> ty G u' A -> cv G u u' A ->
    cv G (app A B f u) (app A B f' u') (B [u..])
| c_beta G A B t u k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty (A :: G) t B -> ty G u A ->
    cv G (app A B (lam A B t) u) (t [u..]) (B [u..])
| c_eta G A B f k : ty G A (univ k) -> ty (A :: G) B (univ k) -> ty G f (pi A B) ->
    cv G (lam A B (app (A ⟨↑⟩) (B ⟨upRen_tm_tm shift⟩) (f ⟨↑⟩) (var_tm 0))) f (pi A B)

(* Sigma *)
| c_sig G A A' B B' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G A' (univ k) -> ty (A' :: G) B' (univ k) ->
    cv G A A' (univ k) -> cv (A :: G) B B' (univ k) -> cv G (sig_ A B) (sig_ A' B') (univ k)
| c_pair G A B t t' u u' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G t A -> ty G t' A -> cv G t t' A ->
    ty G u (B [t..]) -> ty G u' (B [t..]) -> cv G u u' (B [t..]) ->
    cv G (pair A B t u) (pair A B t' u') (sig_ A B)
| c_fst G A B p p' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G p (sig_ A B) -> ty G p' (sig_ A B) -> cv G p p' (sig_ A B) ->
    cv G (fst A B p) (fst A B p') A
| c_snd G A B p p' k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G p (sig_ A B) -> ty G p' (sig_ A B) -> cv G p p' (sig_ A B) ->
    cv G (snd A B p) (snd A B p') (B [(fst A B p)..])
| c_fst_beta G A B t u k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G t A -> ty G u (B [t..]) -> cv G (fst A B (pair A B t u)) t A
| c_snd_beta G A B t u k : ty G A (univ k) -> ty (A :: G) B (univ k) ->
    ty G t A -> ty G u (B [t..]) -> cv G (snd A B (pair A B t u)) u (B [t..])
| c_surj G A B p k : ty G A (univ k) -> ty (A :: G) B (univ k) -> ty G p (sig_ A B) ->
    cv G (pair A B (fst A B p) (snd A B p)) p (sig_ A B)

(* N *)
| c_succ G n n' : ty G n nat_ -> ty G n' nat_ -> cv G n n' nat_ ->
    cv G (succ n) (succ n') nat_
| c_natrec G C C' z z' s s' n n' k :
    ty (nat_ :: G) C (univ k) -> ty (nat_ :: G) C' (univ k) -> cv (nat_ :: G) C C' (univ k) ->
    ty G z (C [zero..]) -> ty G z' (C [zero..]) -> cv G z z' (C [zero..]) ->
    ty (C :: nat_ :: G) s (nrec_succ C) -> ty (C :: nat_ :: G) s' (nrec_succ C) ->
    cv (C :: nat_ :: G) s s' (nrec_succ C) ->
    ty G n nat_ -> ty G n' nat_ -> cv G n n' nat_ ->
    cv G (natrec C z s n) (natrec C' z' s' n') (C [n..])
| c_rec_zero G C z s k :
    ty (nat_ :: G) C (univ k) -> ty G z (C [zero..]) ->
    ty (C :: nat_ :: G) s (nrec_succ C) ->
    cv G (natrec C z s zero) z (C [zero..])
(* The step's two variables are filled in one substitution: var 1 by the
   predecessor, var 0 by the recursive result. *)
| c_rec_succ G C z s n k :
    ty (nat_ :: G) C (univ k) -> ty G z (C [zero..]) ->
    ty (C :: nat_ :: G) s (nrec_succ C) ->
    ty G n nat_ ->
    cv G (natrec C z s (succ n)) (s [ (natrec C z s n) .: n .. ]) (C [(succ n)..])

(* Prop *)
| c_prf G p p' : ty G p prop -> ty G p' prop -> cv G p p' prop ->
    cv G (prf p) (prf p') (univ 0)
| c_all G A A' p p' k : ty G A (univ k) -> ty (A :: G) p prop ->
    ty G A' (univ k) -> ty (A' :: G) p' prop ->
    cv G A A' (univ k) -> cv (A :: G) p p' prop -> cv G (all A p) (all A' p') prop

where "'⊢' G" := (wfc G)
  and "G '⊢' t ':' A" := (ty G t A)
  and "G '⊢' t '≡' u ':' A" := (cv G t u A).

(* ------------------------------------------------------------------ *)
(* Regression: large elimination above Type0.                          *)
(*                                                                    *)
(* With the step term a FUNCTION of type nrec_step C = pi nat_ (pi C   *)
(* (nrec_succ C)), this judgement was underivable for every k > 0, so  *)
(* t_natrec was usable only at a Type0 motive: forming that type needs  *)
(* t_pi, which is homogeneous in the level, hence `ty G nat_ (univ k)`, *)
(* and t_nat gives only univ 0 -- and every other route to the step's   *)
(* type (t_var through wfc, t_conv, t_app, t_fst, t_absurd, t_natrec)   *)
(* in turn asks for that type to be formed at some universe.  With the  *)
(* step carrying its own two binders there is no such type to form, and *)
(* the motive's level is free.  Here it is 4.                          *)
(* ------------------------------------------------------------------ *)

Definition wfc_nat : wfc (nat_ :: nil) := w_cons nil nat_ 0 w_nil (t_nat nil w_nil).

Definition wfc_u3 : wfc (univ 3 :: nat_ :: nil) :=
  w_cons (nat_ :: nil) (univ 3) 4 wfc_nat (t_univ (nat_ :: nil) 3 wfc_nat).

Definition natrec_at_4
  : ty nil (natrec (univ 3) (univ 2) (var_tm 0) zero) (univ 3) :=
  t_natrec nil (univ 3) (univ 2) (var_tm 0) zero 4
    (t_univ (nat_ :: nil) 3 wfc_nat)
    (t_univ nil 2 w_nil)
    (t_var (univ 3 :: nat_ :: nil) 0 (univ 3) wfc_u3
       (lookup_O (nat_ :: nil) (univ 3)))
    (t_zero nil w_nil).
