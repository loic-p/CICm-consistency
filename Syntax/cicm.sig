-- Signature for CIC^- : two term algebras (annotated tm, erased etm),
-- generated together so erasure tm -> etm is a single ordinary function.
--
-- Universe indices are plain Rocq nat, declared here as an external
-- (non-generated) sort; Syntax/Preamble.v does not need to import anything
-- for it since `nat` is already in scope from the prelude.

nat : Type

-- LEVEL ANNOTATIONS.  Every type former carries THE LEVEL IT LIVES AT, and its
-- components may sit at any level below: `pi k A B : univ (S k) k` for
-- A, B : univ (S j) j with j <= k.  The universe lift is then one step on the
-- annotation -- `up k (pi k A B) == pi (S k) A B`, `up k (nat_ k) == nat_ (S k)`
-- -- so `up` computes on every closed type expression and is stuck only on a
-- variable.  `univ k j` is the universe of level-j types, living at level k
-- (j < k), so `univ k j : univ (S k) k`.
--
-- Annotations are carried exactly where nothing else determines the level:
-- `lam`/`pair` (their types are the annotated Pi/Sigma), `zero`, and the type
-- formers themselves.  `succ`, `natrec`, `app`, `fst`, `snd`, `prf`'s
-- subject, `plam`, `papp`, `absurd` and `uptm` need none: a premise fixes it.

-- the annotated syntax

tm : Type

-- Two lambdas and two applications, one pair for Pi and one for the
-- impredicative forall.  They erase identically (Erasure.v), so this costs
-- nothing on realisers; the point is UNICITY OF TYPING.  With a single lambda,
-- `lam A t` inhabits both `pi A (prf p)` and `prf (all A p)`, so a term's type
-- -- and with it the universe level -- is not determined by its syntax, and
-- neither functionality of the interpretation on terms nor the level of a
-- forall-domain can be read off.  Splitting them fixes both.
-- FULL ANNOTATIONS on the eliminators and on the pair.  Every premise of
-- every clause of the interpretation mentions only syntax that is IN the
-- subject, which is what makes functionality of the interpretation a
-- syntax-directed induction.  Without them the decoder at `fst p` cannot name
-- the Sigma-type it projects from, so two readings of one term may interpret
-- its subject at two types the syntax never relates, and the isomorphism of
-- the two readings has to be reconstructed semantically instead of being
-- handed over by the induction hypothesis for the annotation.  `natrec`
-- already recorded its motive, and was correspondingly the one eliminator
-- that gave no trouble.
--
-- plam and papp are NOT annotated: a proof term is interpreted by i_proof,
-- which says nothing about the subject, so there is nothing to reconstruct.
lam    : nat -> tm -> (bind tm in tm) -> (bind tm in tm) -> tm
plam   : tm -> (bind tm in tm) -> tm
app    : tm -> (bind tm in tm) -> tm -> tm -> tm
papp   : tm -> tm -> tm
pair   : nat -> tm -> (bind tm in tm) -> tm -> tm -> tm
fst    : tm -> (bind tm in tm) -> tm -> tm
snd    : tm -> (bind tm in tm) -> tm -> tm
pi     : nat -> tm -> (bind tm in tm) -> tm
sig_   : nat -> tm -> (bind tm in tm) -> tm
nat_   : nat -> tm
zero   : nat -> tm
succ   : tm -> tm
-- natrec C z s n.  The step term carries its OWN binders rather than being a
-- function: s lives in the context extended by the scrutinee (var 1) and the
-- recursive result (var 0).  With s a function of type Pi N (Pi C (C[S])) the
-- rule was unusable above level 0, since that type is formed by t_pi and so
-- needs N at the motive's level, which t_nat does not give.  The binder form
-- needs no type for the step at all, so the motive is at an arbitrary level
-- and large elimination is available everywhere.  Erasure still emits the
-- function form (elam (elam .)), so the ERASED calculus is unchanged.
natrec : (bind tm in tm) -> tm -> (bind tm, tm in tm) -> tm -> tm
univ   : nat -> nat -> tm
-- The TYPE lift, annotated with the universe its subject's type lives in.
up     : nat -> tm -> tm
-- The TERM lift, annotated with the type it lifts.  The level is then
-- redundant -- it is the level of that type -- so it is not carried.
uptm   : tm -> tm -> tm
prop   : nat -> tm
prf    : nat -> tm -> tm
-- The impredicative forall is annotated with the level of the PROPOSITION it
-- forms, which its domain does not determine: `all j A p : prop j` for A at
-- ANY level (that is the impredicativity).  Without the annotation the level
-- of a forall over an EMPTY domain is not determined by the interpretation at
-- all -- the premise about p is vacuous there -- and level functionality,
-- which everything about the interpretation of propositions rests on, fails.
all    : nat -> tm -> (bind tm in tm) -> tm
false_ : nat -> tm
absurd : tm -> tm -> tm
eqty   : tm -> tm -> tm -> tm
refl   : tm -> tm -> tm
-- transp A B t u e b : B[u], for e : Eq A t u and b : B[t]. Both endpoints
-- are carried so the interpretation of raw syntax can name the codes of
-- B[t] and B[u] (the blueprint's 5-argument version drops t).
transp : tm -> (bind tm in tm) -> tm -> tm -> tm -> tm -> tm

-- the erased syntax; elam is the only binder, by design (Remark on Erasure.v)

etm : Type

elam    : (bind etm in etm) -> etm
eapp    : etm -> etm -> etm
epair   : etm -> etm -> etm
efst    : etm -> etm
esnd    : etm -> etm
epi     : etm -> etm -> etm
esig    : etm -> etm -> etm
enat    : etm
ezero   : etm
esucc   : etm -> etm
enatrec : etm -> etm -> etm -> etm
euniv   : nat -> etm
eprop   : etm
eprf    : etm -> etm
eall    : etm -> etm -> etm
efalse  : etm
estar   : etm
eerr    : etm
eeqty   : etm -> etm -> etm -> etm
