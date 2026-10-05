From CICM Require Import Syntax.Ann.

Open Scope list_scope.


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
   off the syntax -- every former carries the level it lives at -- which
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

   There is deliberately no `nrec_step C = pi nat_ (pi C (nrec_succ C))`.  In
   v1 that was forced: t_pi was HOMOGENEOUS in the level, so the step's type
   would have needed `nat_` at the motive's level, and large elimination above
   Type0 was unreachable.  With t_pi heterogeneous (v2) the function form is
   derivable again, and the binder form is kept for a different reason: a step
   written as a function HAS A TYPE, and the interpretation of
   `natrec C z s n` would have to match it -- including the level annotations
   on its Pis, which are not part of the subject.  With binders there is no
   type to match: the interpretation extends the environment by families it
   has already built.  The same argument keeps wrec's step binder-shaped. *)
Definition nrec_succ (C : tm) : tm :=
  C [ succ (var_tm 1) .:s (rcomp ↑ ↑) ].

(* ------------------------------------------------------------------ *)
(* W: the three types the step's binders range over.                   *)
(*                                                                    *)
(* With the tree type W := wt k A B over Gamma, the step of            *)
(* `wrec A B C s w` is typed in the context                            *)
(*                                                                    *)
(*     wih n k A B C  ::  wbr k A B  ::  A  ::  Gamma                  *)
(*         (var 0)          (var 1)     (var 2)                        *)
(*                                                                    *)
(* -- the induction hypothesis, the branching function and the label.  *)
(* `n` is the level of the induction hypothesis's Pi, whose domain sits *)
(* at B's level and whose codomain sits at the motive's: exactly the    *)
(* heterogeneity t_pi now allows, and the only place in the calculus    *)
(* that needs it.                                                      *)
(* ------------------------------------------------------------------ *)

(* the three shifts of the step's three binders, in the RENAMING algebra.
   Written as a raw lambda, `fun i => S (S (S i))`, rasimpl cannot push a
   composition through it, and every equation about the step becomes
   intractable; in the algebra they are routine. *)
Definition sh3 : ren := rcomp ↑ (rcomp ↑ ↑).

(* the branching function of a tree with label (var 0), in context A :: Gamma *)
Definition wbr (k : nat) (A B : tm) : tm :=
  pi k B ((wt k A B) ⟨↑⟩ ⟨↑⟩).

(* the induction hypothesis, in context (wbr k A B :: A :: Gamma): a function
   taking a branch (var 0) to the motive at the subtree the branching
   function (var 1) puts there. *)
Definition wih (n k : nat) (A B C : tm) : tm :=
  pi n (B ⟨↑⟩)
     (C [ app (B ⟨↑⟩ ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩ ⟨↑⟩ ⟨↑⟩) (var_tm 1) (var_tm 0)
          .:s sh3 ]).

(* the step's own type, in context (wih .. :: wbr .. :: A :: Gamma): the
   motive at the tree built from the label (var 2) and the branching
   function (var 1). *)
Definition wsup_ty (k : nat) (A B C : tm) : tm :=
  C [ sup k (A ⟨sh3⟩) (B ⟨up_ren sh3⟩) (var_tm 2) (var_tm 1)
      .:s sh3 ].

(* The subtree at branch (var 0), in context (B[a] :: Gamma), and the
   induction hypothesis the computation rule supplies: the function sending a
   branch to the recursive result on that subtree. *)
Definition wsub (k : nat) (A B a f : tm) : tm :=
  app ((B [a..]) ⟨↑⟩) ((wt k A B) ⟨↑⟩ ⟨↑⟩) (f ⟨↑⟩) (var_tm 0).

Definition wih_val (n k : nat) (A B C s a f : tm) : tm :=
  lam n (B [a..])
      (C [ wsub k A B a f .:s ↑ ])
      (wrec (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (C ⟨up_ren ↑⟩)
            (s ⟨up_ren (up_ren (up_ren ↑))⟩)
            (wsub k A B a f)).

Reserved Notation "'⊢' G" (at level 80).
Reserved Notation "G '⊢' t ':' A" (at level 80, t at next level).
Reserved Notation "G '⊢' t '≡' u ':' A" (at level 80, t at next level, u at next level).

(* LEVEL ANNOTATIONS.  Every type former carries the level it lives at and its
   components sit at any level below, so the universe lift is one step on the
   annotation (the c_up_* rules below) and computes on every closed type
   expression.  `univ k j` is the universe of the level-j types, living at
   level k, so the universe where the level-k types live is `univ (S k) k`;
   that is what UU abbreviates. *)
Notation UU k := (univ (S k) k).

Inductive wfc : ctx -> Type :=
| w_nil : wfc nil
| w_cons G A k : wfc G -> ty G A (UU k) -> wfc (A :: G)

with ty : ctx -> tm -> tm -> Type :=
(* structural *)
| t_var G i A : wfc G -> lookup i G A -> ty G (var_tm i) A
| t_conv G t A B k : ty G t A -> ty G A (UU k) -> ty G B (UU k) ->
    cv G A B (UU k) -> ty G t B

(* universes *)
| t_univ G k j : j < k -> wfc G -> ty G (univ k j) (UU k)
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
| t_up G j A : ty G A (UU j) -> ty G (up j A) (UU (S j))
(* The lift on TERMS is explicit: `up` doubles as its own term former, so a
   term of A does not silently also have type up (univ k) A.  The two
   transparency rules that used to say it did (t_up_in / t_up_out) made typing
   non-unique -- t : A and t : up (univ k) A for the same t -- and unicity of
   typing, universe levels included, is what lets the level of a forall-domain
   be read off the syntax.  Nothing is lost: the lift is still there, small
   types still appear in large ones, and erasure still sends `up A t` to the
   erasure of t, so the lift is invisible on realisers. *)
| t_up_tm G j A t : ty G A (UU j) -> ty G t A -> ty G (uptm A t) (up j A)

(* Pi *)
| t_pi G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G (pi k A B) (UU k)
| t_lam G k i j A B t : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty (A :: G) t B -> ty G (lam k A B t) (pi k A B)
| t_app G k i j A B f u : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G f (pi k A B) -> ty G u A -> ty G (app A B f u) (B [u..])

(* Sigma *)
| t_sig G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G (sig_ k A B) (UU k)
| t_pair G k i j A B t u : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G t A -> ty G u (B [t..]) -> ty G (pair k A B t u) (sig_ k A B)
| t_fst G k i j A B p : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G p (sig_ k A B) -> ty G (fst A B p) A
| t_snd G k i j A B p : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G p (sig_ k A B) -> ty G (snd A B p) (B [(fst A B p)..])

(* W: the same shape as Sigma -- the label type A and the branching type B at
   independent levels below the annotation -- and the same discipline for the
   eliminator as natrec: the step carries its own binders, here three, for the
   label, the branching function and the induction hypothesis.  A tree's
   branching function is typed AT THE ANNOTATION'S LEVEL, which a
   heterogeneous Pi allows outright: its domain B[a] sits at j and its
   codomain, the tree type itself, at k. *)
| t_w G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G (wt k A B) (UU k)
| t_sup G k i j A B a f : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G a A -> ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ->
    ty G (sup k A B a f) (wt k A B)
(* The induction hypothesis's level `n` is PINNED to the least level that
   accommodates its domain (the branching type, at j) and its codomain (the
   motive at the subtree, at m).  Without the pin `wrec` would be the one
   eliminator whose premises mention a level its subject does not record, and
   the interpretation -- which has only the term to go by -- could not
   determine the level of the step's third context entry; two readings of one
   `wrec` could then put that entry at different levels, which `EnvRel`
   cannot relate at all (see Interp/Fund.v).  Nothing is lost: the step is
   typed in the same context up to that annotation. *)
| t_wrec G k i j m n A B C s w : i <= k -> j <= k -> j <= n -> m <= n ->
    n = Nat.max j m ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty (wt k A B :: G) C (UU m) ->
    (* the step's context, in the redundant style: the rule MENTIONS these two
       types, so it carries their formation judgements.  Without them the
       admissibility of renaming is not provable -- its induction hypothesis
       for the step needs this context to be well formed, and building it
       would need weakening of A and B and a substitution instance of the
       motive, i.e. the very theorems being proved. *)
    ty (A :: G) (wbr k A B) (UU k) ->
    ty (wbr k A B :: A :: G) (wih n k A B C) (UU n) ->
    ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C) ->
    ty G w (wt k A B) ->
    ty G (wrec A B C s w) (C [w..])

(* N and its large elimination *)
| t_nat G k : wfc G -> ty G (nat_ k) (UU k)
| t_zero G k : wfc G -> ty G (zero k) (nat_ k)
| t_succ G k n : ty G n (nat_ k) -> ty G (succ n) (nat_ k)
| t_natrec G C z s n k j :
    ty (nat_ j :: G) C (UU k) ->
    ty G z (C [(zero j)..]) -> ty (C :: nat_ j :: G) s (nrec_succ C) ->
    ty G n (nat_ j) ->
    ty G (natrec C z s n) (C [n..])

(* Prop, Prf, impredicative forall, bottom *)
| t_prop G k : wfc G -> ty G (prop k) (UU k)
| t_prf G k j p : j <= k -> ty G p (prop j) -> ty G (prf k p) (UU k)
| t_all G A p j k : ty G A (UU k) -> ty (A :: G) p (prop j) ->
    ty G (all j A p) (prop j)
(* The forall-lambda and forall-application are their OWN formers, plam and
   papp, not lam and app: with one lambda, `lam A t` inhabits both
   pi A (prf p) and prf (all A p), so neither the type nor the universe level
   is determined by the term.  They erase exactly as lam and app do
   (Syntax/Erasure.v), so this costs nothing on realisers, and their conversion
   rules are subsumed by c_prf_irr, every papp and plam living at a Prf type. *)
| t_all_intro G A p t j k : ty G A (UU k) -> ty (A :: G) p (prop j) ->
    ty (A :: G) t (prf j p) -> ty G (plam A t) (prf j (all j A p))
| t_all_elim G A p f u j k : ty G A (UU k) -> ty (A :: G) p (prop j) ->
    ty G f (prf j (all j A p)) -> ty G u A -> ty G (papp f u) (prf j (p [u..]))
| t_false G k : wfc G -> ty G (false_ k) (prop k)
| t_absurd G T e k j : ty G T (UU k) -> ty G e (prf j (false_ j)) ->
    ty G (absurd T e) T

(* NO Eq.  See the note on Eq at the top of the file. *)

with cv : ctx -> tm -> tm -> tm -> Type :=
(* equivalence, conversion of the type, proof irrelevance *)
| c_refl G t A : ty G t A -> cv G t t A
| c_sym G t u A : cv G t u A -> cv G u t A
| c_trans G t u v A : cv G t u A -> cv G u v A -> cv G t v A
| c_conv G t u A B k : cv G t u A -> ty G A (UU k) -> ty G B (UU k) ->
    cv G A B (UU k) -> cv G t u B
| c_prf_irr G j p e e' : ty G p (prop j) -> ty G e (prf j p) -> ty G e' (prf j p) ->
    cv G e e' (prf j p)

(* universes *)
| c_up G j A A' : ty G A (UU j) -> ty G A' (UU j) -> cv G A A' (UU j) ->
    cv G (up j A) (up j A') (UU (S j))
| c_up_tm G j A t t' : ty G A (UU j) -> ty G t A -> ty G t' A -> cv G t t' A ->
    cv G (uptm A t) (uptm A t') (up j A)

(* The lift COMPUTES on every former: one rule each, and the components are
   untouched, which is what keeps the rule well formed -- lifting the domain of
   a Pi would leave the codomain's annotations behind, at the old level.  On a
   variable `up` is stuck, and that case no rule can mend. *)
| c_up_univ G k j : j < k -> wfc G ->
    cv G (up k (univ k j)) (univ (S k) j) (UU (S k))
| c_up_nat G k : wfc G -> cv G (up k (nat_ k)) (nat_ (S k)) (UU (S k))
| c_up_prop G k : wfc G -> cv G (up k (prop k)) (prop (S k)) (UU (S k))
| c_up_prf G k j p : j <= k -> ty G p (prop j) ->
    cv G (up k (prf k p)) (prf (S k) p) (UU (S k))
| c_up_pi G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    cv G (up k (pi k A B)) (pi (S k) A B) (UU (S k))
| c_up_sig G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    cv G (up k (sig_ k A B)) (sig_ (S k) A B) (UU (S k))
| c_up_w G k i j A B : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    cv G (up k (wt k A B)) (wt (S k) A B) (UU (S k))

(* Pi *)
| c_pi G k i j A A' B B' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G A' (UU i) -> ty (A' :: G) B' (UU j) ->
    cv G A A' (UU i) -> cv (A :: G) B B' (UU j) ->
    cv G (pi k A B) (pi k A' B') (UU k)
(* The lambda congruence, in the same shape as c_pi: the PRIMED premises live
   in the PRIMED context.  It used to keep the codomain B and the body t' in
   the A-context while annotating the subject with A', and then the semantics
   of `lam A' B t'` could not be given: interpreting B and t' asks for an
   environment extended by A''s family, whose realiser is `ers rho A'`, and
   that is not an environment for A :: G.  Modulo context conversion -- which
   is admissible -- the two rules prove the same conversions. *)
| c_lam G k i j A A' B B' t t' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G A' (UU i) -> ty (A' :: G) B' (UU j) ->
    cv G A A' (UU i) -> cv (A :: G) B B' (UU j) ->
    ty (A :: G) t B -> ty (A' :: G) t' B' -> cv (A :: G) t t' B ->
    cv G (lam k A B t) (lam k A' B' t') (pi k A B)
| c_app G k i j A B f f' u u' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G f (pi k A B) -> ty G f' (pi k A B) -> cv G f f' (pi k A B) ->
    ty G u A -> ty G u' A -> cv G u u' A ->
    cv G (app A B f u) (app A B f' u') (B [u..])
| c_beta G k i j A B t u : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty (A :: G) t B -> ty G u A ->
    cv G (app A B (lam k A B t) u) (t [u..]) (B [u..])
| c_eta G k i j A B f : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G f (pi k A B) ->
    cv G (lam k A B (app (A ⟨↑⟩) (B ⟨up_ren ↑⟩) (f ⟨↑⟩) (var_tm 0))) f
       (pi k A B)

(* Sigma *)
| c_sig G k i j A A' B B' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G A' (UU i) -> ty (A' :: G) B' (UU j) ->
    cv G A A' (UU i) -> cv (A :: G) B B' (UU j) ->
    cv G (sig_ k A B) (sig_ k A' B') (UU k)
| c_pair G k i j A B t t' u u' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G t A -> ty G t' A -> cv G t t' A ->
    ty G u (B [t..]) -> ty G u' (B [t..]) -> cv G u u' (B [t..]) ->
    cv G (pair k A B t u) (pair k A B t' u') (sig_ k A B)
| c_fst G k i j A B p p' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G p (sig_ k A B) -> ty G p' (sig_ k A B) -> cv G p p' (sig_ k A B) ->
    cv G (fst A B p) (fst A B p') A
| c_snd G k i j A B p p' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G p (sig_ k A B) -> ty G p' (sig_ k A B) -> cv G p p' (sig_ k A B) ->
    cv G (snd A B p) (snd A B p') (B [(fst A B p)..])
| c_fst_beta G k i j A B t u : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G t A -> ty G u (B [t..]) -> cv G (fst A B (pair k A B t u)) t A
| c_snd_beta G k i j A B t u : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G t A -> ty G u (B [t..]) -> cv G (snd A B (pair k A B t u)) u (B [t..])
| c_surj G k i j A B p : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G p (sig_ k A B) ->
    cv G (pair k A B (fst A B p) (snd A B p)) p (sig_ k A B)

(* W *)
| c_w G k i j A A' B B' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G A' (UU i) -> ty (A' :: G) B' (UU j) ->
    cv G A A' (UU i) -> cv (A :: G) B B' (UU j) ->
    cv G (wt k A B) (wt k A' B') (UU k)
| c_sup G k i j A B a a' f f' : i <= k -> j <= k ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty G a A -> ty G a' A -> cv G a a' A ->
    ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ->
    ty G f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ->
    cv G f f' (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ->
    cv G (sup k A B a f) (sup k A B a' f') (wt k A B)
| c_wrec G k i j m n A B C C' s s' w w' :
    i <= k -> j <= k -> j <= n -> m <= n -> n = Nat.max j m ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty (wt k A B :: G) C (UU m) -> ty (wt k A B :: G) C' (UU m) ->
    cv (wt k A B :: G) C C' (UU m) ->
    ty (A :: G) (wbr k A B) (UU k) ->
    ty (wbr k A B :: A :: G) (wih n k A B C) (UU n) ->
    ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C) ->
    ty (wih n k A B C :: wbr k A B :: A :: G) s' (wsup_ty k A B C) ->
    cv (wih n k A B C :: wbr k A B :: A :: G) s s' (wsup_ty k A B C) ->
    ty G w (wt k A B) -> ty G w' (wt k A B) -> cv G w w' (wt k A B) ->
    cv G (wrec A B C s w) (wrec A B C' s' w') (C [w..])
(* the computation rule: the step is fed the label, the branching function,
   and the function sending a branch to the recursive result there. *)
| c_wrec_sup G k i j m n A B C s a f :
    i <= k -> j <= k -> j <= n -> m <= n -> n = Nat.max j m ->
    ty G A (UU i) -> ty (A :: G) B (UU j) ->
    ty (wt k A B :: G) C (UU m) ->
    ty (A :: G) (wbr k A B) (UU k) ->
    ty (wbr k A B :: A :: G) (wih n k A B C) (UU n) ->
    ty (wih n k A B C :: wbr k A B :: A :: G) s (wsup_ty k A B C) ->
    ty G a A -> ty G f (pi k (B [a..]) ((wt k A B) ⟨↑⟩)) ->
    cv G (wrec A B C s (sup k A B a f))
         (s [ wih_val n k A B C s a f .: (f .: a ..) ])
         (C [(sup k A B a f)..])

(* N *)
| c_succ G k n n' : ty G n (nat_ k) -> ty G n' (nat_ k) -> cv G n n' (nat_ k) ->
    cv G (succ n) (succ n') (nat_ k)
| c_natrec G C C' z z' s s' n n' k j :
    ty (nat_ j :: G) C (UU k) -> ty (nat_ j :: G) C' (UU k) ->
    cv (nat_ j :: G) C C' (UU k) ->
    ty G z (C [(zero j)..]) -> ty G z' (C [(zero j)..]) ->
    cv G z z' (C [(zero j)..]) ->
    ty (C :: nat_ j :: G) s (nrec_succ C) -> ty (C :: nat_ j :: G) s' (nrec_succ C) ->
    cv (C :: nat_ j :: G) s s' (nrec_succ C) ->
    ty G n (nat_ j) -> ty G n' (nat_ j) -> cv G n n' (nat_ j) ->
    cv G (natrec C z s n) (natrec C' z' s' n') (C [n..])
| c_rec_zero G C z s k j :
    ty (nat_ j :: G) C (UU k) -> ty G z (C [(zero j)..]) ->
    ty (C :: nat_ j :: G) s (nrec_succ C) ->
    cv G (natrec C z s (zero j)) z (C [(zero j)..])
(* The step's two variables are filled in one substitution: var 1 by the
   predecessor, var 0 by the recursive result. *)
| c_rec_succ G C z s n k j :
    ty (nat_ j :: G) C (UU k) -> ty G z (C [(zero j)..]) ->
    ty (C :: nat_ j :: G) s (nrec_succ C) ->
    ty G n (nat_ j) ->
    cv G (natrec C z s (succ n)) (s [ (natrec C z s n) .: n .. ]) (C [(succ n)..])

(* Prop *)
| c_prf G k j p p' : j <= k -> ty G p (prop j) -> ty G p' (prop j) ->
    cv G p p' (prop j) -> cv G (prf k p) (prf k p') (UU k)
| c_all G A A' p p' j k : ty G A (UU k) -> ty (A :: G) p (prop j) ->
    ty G A' (UU k) -> ty (A' :: G) p' (prop j) ->
    cv G A A' (UU k) -> cv (A :: G) p p' (prop j) ->
    cv G (all j A p) (all j A' p') (prop j)

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

Definition wfc_nat : wfc (nat_ 0 :: nil) :=
  w_cons nil (nat_ 0) 0 w_nil (t_nat nil 0 w_nil).

Definition wfc_u3 : wfc (univ 4 3 :: nat_ 0 :: nil) :=
  w_cons (nat_ 0 :: nil) (univ 4 3) 4 wfc_nat
    (t_univ (nat_ 0 :: nil) 4 3 (le_n 4) wfc_nat).

Definition natrec_at_4
  : ty nil (natrec (univ 4 3) (univ 3 2) (var_tm 0) (zero 0)) (univ 4 3) :=
  t_natrec nil (univ 4 3) (univ 3 2) (var_tm 0) (zero 0) 4 0
    (t_univ (nat_ 0 :: nil) 4 3 (le_n 4) wfc_nat)
    (t_univ nil 3 2 (le_n 3) w_nil)
    (t_var (univ 4 3 :: nat_ 0 :: nil) 0 (univ 4 3) wfc_u3
       (lookup_O (nat_ 0 :: nil) (univ 4 3)))
    (t_zero nil 0 w_nil).

(* ------------------------------------------------------------------ *)
(* Smoke test for the W rules.                                         *)
(*                                                                    *)
(* Trees labelled by numerals whose branching type is EMPTY: every     *)
(* tree is a leaf, and its branching function is the empty function.   *)
(* Then a recursion on one.  What this really checks is the de Bruijn  *)
(* bookkeeping of wbr, wih and wsup_ty: t_wrec's step premise is a     *)
(* typing judgement in the three-entry context they build, and every   *)
(* rule that types the step needs that context to be WELL FORMED --    *)
(* which is exactly the statement that those definitions are types.    *)
(* ------------------------------------------------------------------ *)

Definition Bot : tm := prf 0 (false_ 0).
Definition Wnat : tm := wt 0 (nat_ 0) Bot.

Lemma ty_Bot G (W : wfc G) : ty G Bot (UU 0).
Proof. exact (t_prf G 0 0 (false_ 0) (le_n 0) (t_false G 0 W)). Qed.

Lemma wfc_N G (W : wfc G) : wfc (nat_ 0 :: G).
Proof. exact (w_cons G (nat_ 0) 0 W (t_nat G 0 W)). Qed.

Lemma ty_Wnat G (W : wfc G) : ty G Wnat (UU 0).
Proof.
  exact (t_w G 0 0 0 (nat_ 0) Bot (le_n 0) (le_n 0) (t_nat G 0 W)
           (ty_Bot _ (wfc_N G W))).
Qed.

(* the leaf with label 0 *)
Definition leaf : tm :=
  sup 0 (nat_ 0) Bot (zero 0) (lam 0 Bot Wnat (absurd Wnat (var_tm 0))).

Lemma ty_leaf : ty nil leaf Wnat.
Proof.
  pose proof (w_cons nil Bot 0 w_nil (ty_Bot nil w_nil)) as WB.
  refine (t_sup nil 0 0 0 (nat_ 0) Bot (zero 0) _ (le_n 0) (le_n 0)
            (t_nat nil 0 w_nil) (ty_Bot _ (wfc_N nil w_nil))
            (t_zero nil 0 w_nil) _).
  refine (t_lam nil 0 0 0 Bot Wnat _ (le_n 0) (le_n 0)
            (ty_Bot nil w_nil) (ty_Wnat _ WB) _).
  exact (t_absurd _ Wnat (var_tm 0) 0 0 (ty_Wnat _ WB)
           (t_var _ 0 Bot WB (lookup_O nil Bot))).
Qed.

(* the two types the step's binders range over, which the rule now carries *)
Lemma ty_wbrN G (W : wfc G) : ty (nat_ 0 :: G) (wbr 0 (nat_ 0) Bot) (UU 0).
Proof.
  pose proof (wfc_N G W) as W1.
  refine (t_pi _ 0 0 0 Bot Wnat (le_n 0) (le_n 0) (ty_Bot _ W1) _).
  exact (ty_Wnat _ (w_cons _ Bot 0 W1 (ty_Bot _ W1))).
Qed.

Lemma ty_wihN G (W : wfc G) :
  ty (wbr 0 (nat_ 0) Bot :: nat_ 0 :: G) (wih 0 0 (nat_ 0) Bot (nat_ 0)) (UU 0).
Proof.
  pose proof (w_cons _ (wbr 0 (nat_ 0) Bot) 0 (wfc_N G W) (ty_wbrN G W)) as W2.
  refine (t_pi _ 0 0 0 Bot (nat_ 0) (le_n 0) (le_n 0) (ty_Bot _ W2) _).
  exact (t_nat _ 0 (w_cons _ Bot 0 W2 (ty_Bot _ W2))).
Qed.

(* the step's context is well formed *)
Lemma wfc_wstep :
  wfc (wih 0 0 (nat_ 0) Bot (nat_ 0) :: wbr 0 (nat_ 0) Bot :: nat_ 0 :: nil).
Proof.
  exact (w_cons _ _ 0
           (w_cons _ _ 0 (wfc_N nil w_nil) (ty_wbrN nil w_nil))
           (ty_wihN nil w_nil)).
Qed.

(* a recursion on trees, at the motive N: every leaf gets 0 *)
Definition wrec_leaf : tm := wrec (nat_ 0) Bot (nat_ 0) (zero 0) leaf.

Lemma ty_wrec_leaf : ty nil wrec_leaf (nat_ 0).
Proof.
  pose proof (wfc_N nil w_nil) as W1.
  refine (t_wrec nil 0 0 0 0 0 (nat_ 0) Bot (nat_ 0) (zero 0) leaf
            (le_n 0) (le_n 0) (le_n 0) (le_n 0) eq_refl
            (t_nat nil 0 w_nil) (ty_Bot _ W1) _ (ty_wbrN nil w_nil)
            (ty_wihN nil w_nil) _ ty_leaf).
  - exact (t_nat _ 0 (w_cons nil Wnat 0 w_nil (ty_Wnat nil w_nil))).
  - exact (t_zero _ 0 wfc_wstep).
Qed.

(* and it computes *)
Lemma cv_wrec_leaf :
  cv nil wrec_leaf
     ((zero 0) [ wih_val 0 0 (nat_ 0) Bot (nat_ 0) (zero 0) (zero 0)
                   (lam 0 Bot Wnat (absurd Wnat (var_tm 0)))
                 .: ((lam 0 Bot Wnat (absurd Wnat (var_tm 0))) .: (zero 0) ..) ])
     (nat_ 0).
Proof.
  pose proof (wfc_N nil w_nil) as W1.
  pose proof (w_cons nil Bot 0 w_nil (ty_Bot nil w_nil)) as WB.
  refine (c_wrec_sup nil 0 0 0 0 0 (nat_ 0) Bot (nat_ 0) (zero 0) (zero 0) _
            (le_n 0) (le_n 0) (le_n 0) (le_n 0) eq_refl
            (t_nat nil 0 w_nil) (ty_Bot _ W1)
            (t_nat _ 0 (w_cons nil Wnat 0 w_nil (ty_Wnat nil w_nil)))
            (ty_wbrN nil w_nil) (ty_wihN nil w_nil)
            (t_zero _ 0 wfc_wstep) (t_zero nil 0 w_nil) _).
  refine (t_lam nil 0 0 0 Bot Wnat _ (le_n 0) (le_n 0)
            (ty_Bot nil w_nil) (ty_Wnat _ WB) _).
  exact (t_absurd _ Wnat (var_tm 0) 0 0 (ty_Wnat _ WB)
           (t_var _ 0 Bot WB (lookup_O nil Bot))).
Qed.

(* the induction hypothesis the computation rule feeds to the step is itself
   well typed: this is what checks wsub's and wih_val's bookkeeping. *)
Definition empfun : tm := lam 0 Bot Wnat (absurd Wnat (var_tm 0)).

Lemma ty_wih_val :
  ty nil (wih_val 0 0 (nat_ 0) Bot (nat_ 0) (zero 0) (zero 0) empfun)
     (pi 0 Bot (nat_ 0)).
Proof.
  pose proof (wfc_N nil w_nil) as W1.
  pose proof (w_cons nil Bot 0 w_nil (ty_Bot nil w_nil)) as WB.
  assert (dempfun : ty nil empfun (pi 0 Bot Wnat)).
  { refine (t_lam nil 0 0 0 Bot Wnat _ (le_n 0) (le_n 0)
              (ty_Bot nil w_nil) (ty_Wnat _ WB) _).
    exact (t_absurd _ Wnat (var_tm 0) 0 0 (ty_Wnat _ WB)
             (t_var _ 0 Bot WB (lookup_O nil Bot))). }
  refine (t_lam nil 0 0 0 Bot (nat_ 0) _ (le_n 0) (le_n 0)
            (ty_Bot nil w_nil) (t_nat _ 0 WB) _).
  (* the body: the recursive call on the subtree at the branch (var 0) *)
  refine (t_wrec _ 0 0 0 0 0 (nat_ 0) Bot (nat_ 0) (zero 0) _
            (le_n 0) (le_n 0) (le_n 0) (le_n 0) eq_refl
            (t_nat _ 0 WB) (ty_Bot _ (wfc_N _ WB))
            (t_nat _ 0 (w_cons _ Wnat 0 WB (ty_Wnat _ WB)))
            (ty_wbrN _ WB) (ty_wihN _ WB)
            (t_zero _ 0
               (w_cons _ _ 0 (w_cons _ _ 0 (wfc_N _ WB) (ty_wbrN _ WB))
                  (ty_wihN _ WB))) _).
  (* the subtree itself: empfun applied to the branch *)
  refine (t_app _ 0 0 0 Bot Wnat _ (var_tm 0) (le_n 0) (le_n 0)
            (ty_Bot _ WB) (ty_Wnat _ (w_cons _ Bot 0 WB (ty_Bot _ WB))) _ _).
  - exact (t_lam _ 0 0 0 Bot Wnat _ (le_n 0) (le_n 0) (ty_Bot _ WB)
             (ty_Wnat _ (w_cons _ Bot 0 WB (ty_Bot _ WB)))
             (t_absurd _ Wnat (var_tm 0) 0 0
                (ty_Wnat _ (w_cons _ Bot 0 WB (ty_Bot _ WB)))
                (t_var _ 0 Bot (w_cons _ Bot 0 WB (ty_Bot _ WB))
                   (lookup_O _ Bot)))).
  - exact (t_var _ 0 Bot WB (lookup_O nil Bot)).
Qed.
