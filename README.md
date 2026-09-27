# A model for CIC⁻ in CIC, via `Acc`'s large elimination

Define CIC⁻ to be dependent type theory with Π, Σ, ℕ with large elimination,
W-types, impredicative `Prop` which supports ⊥ and Martin-Löf's identity type,
as well as a predicative universe hierarchy with explicit lifts. Put more
simply, CIC⁻ is the same as CIC *without the accessibility predicate*.

This repository shows that CIC⁻ is strictly weaker than CIC. We build a model of
CIC⁻ in Rocq by cleverly exploiting the power of the accessibility predicate.
From there, we deduce consistency of CIC⁻ (with its full universe hierarchy) as
a theorem of CIC.

This formalisation was written by a frontier LLM, following a strategy devised
by a human. The strategy was slightly revised to account for the obstacles found
by the LLM during the formalisation.

W types and the identity type have yet to be added. We know that the identity
type does not change the proof-theoretic strength of the system (one can use
setoid models to recover an equality). However, W types *do* increase the
strength of the system by quite a bit. I am confident that the proof strategy
will extend to W types.

## Proof outline

The observation that makes the proof work is that *proofs of propositions do
not play any role in the computation of types*. This is true in CIC⁻, but not
in CIC, as the termination of a computation might hinge on an accessibility
proof.

This observation was already made by Tabareau and myself in our paper
[Impredicative Observational Equality](https://hal.science/hal-03857705v2),
where we show normalisation of the *predicative* part of the calculus
with a logical relation argument that takes place in a very weak metatheory
(predicative MLTT). This model completely ignores everything that happens
in the impredicative layer, and as such, it is not able to show *consistency*
of the system, which is shown afterwards in a much stronger metatheory (ZFC).

In this repository, we start by doing a similar truth-agnostic normalisation
model, except that we define our PERs in `Prop` to handle the entire
universe hierarchy at once. Then, we use this model to get an ordinal which
encodes the "complexity" of each type (we call this ordinal the *rank* of the
type, by analogy with set theory). For instance, the rank of any proposition is
0, the rank of `Π A B` is the successor of the sup of rank(A) and rank(B(a)) for
any `a : A`, etc. Note that we need the normalisation model to compute ranks.

Then, we define a universe of *assemblies of bounded rank* by induction on
ranks (represented as Brouwer trees). An element of V_α is rougly defined as
```
V_0       = ∅
V_(α+1)   = ANat, AProp, APrf p, AUniv, Dependent sums/products of elements of V_α, embeddings
V_(sup f) = embeddings
```
Where `ANat` is the assembly of natural numbers, `AProp` is the codiscrete
assembly of modest assemblies, `APrf p` is the assembly for the proposition `p`,
`AUniv` codes for the universes that we have already defined, etc. We define
equalities of assemblies by induction on ranks.

Finally, we interpret the syntax of CIC⁻ in our universes of assemblies of
bounded rank. The empty proposition is interpreted as an empty assembly, which
shows consistency (`Interp/Consistency.v`). Throughout the entire development,
no axioms are used.

## Sanity checks

To make sure that I did not inadvertently cheat by forgetting some typing rules,
the directory `Tests/` contains a few derivations in our formalised calculus.
* `Tests/Eq.v` defines the equality of natural numbers by large elimination, and
  shows`eq 0 0` and `eq 0 1 -> False` 
* `Tests/Logic.v` defines the logical and and logical or using impredicative
  encodings, and shows their introduction/elimination rules.
* `Tests/Sigma.v` defines two high complexity types. First, define the powerset
  operator as `P(A) = (A -> Prop)`. Then, define the function `beth : Nat -> Type`
  by `beth 0 = Nat` and `beth (suc n) = P(beth n)`. Finally, define `beth_omega`
  as `Sigma (n : Nat) . beth n`. For the second high-complexity type, we replace
  the powerset operator by the modified powerset operator `P'(A) = (A -> Type)`.

## Type-checking the proof

The proof has been checked using Rocq 9.3. All the major results are axiom-free.
The proof takes quite a while to type-check on a medium-end laptop (expect
30 minutes).

## Details

### Syntax and Typing rules

The raw syntax for CIC⁻ is defined in the directory `Syntax/`. The terms (`tm`)
are maximally annotated in order to guarantee uniqueness of typing -- lambdas and
applications contain annotations for both the domain and the codomain, most of
the syntax is annotated with universe levels to handle explicit cumulativity,
etc. The syntax and renaming/substitution lemmas are generated using Autosubst2
from the signature `Syntax/cicm.sig`. The file `Syntax/Erasure.v` sends the
terms to their erased counterparts (`etm`), which removes most of the annotations.

The file `Reduction/Def.v` defines weak-head reduction of erased terms. No eta,
no reduction under binders. We define values, stuck terms (`Reduction/Stuck.v`),
and prove that the reduction is deterministic (`Reduction/Determinism.v`).

The file `Typing/Rules.v` defines the typing rules (`ty`) and conversion rules
(`cv`) of our calculus. In `Typing/Subst.v` we show that well-formed renamings
and well-typed substitutions preserve the typing judgments.

### Truth-agnostic normalisation model

`Layer1/Per.v` defines the basic calculus of `Prop`-valued PERs (the PER of
stuck terms, the PER of natural numbers, dependent sums/products of PERs, and
a rough approximation for the PER of propositions)

`Layer1/Def.v` defines a logical relation à la Allen (`LR`). The relation is
very similar to the paper "Impredicative Observational Equality", except that
the PERs are valued in `Prop` so that we can handle the full universes hierarchy
with only one metatheoretic universe.

The directory `Layer1/Bundle/` proves basic properties of our logical relation.
* In `Inv.v`, we show some inversion lemmas (if the head constructor of a reducible
  type is a Π, then the associated PER on terms is the dependent product of the PERs
  associated to the domain and the codomain, etc).
* In `Fun.v`, we show that given two reducibly equal types A and B, the logical
  relation between terms is is only determined by A.
* In `Sym.v` and `Trans.v`, we show that the logical relation is symmetric,
  transitive, closed under reduction and expansion, and contains stuck terms.
* In `Cumul.v`, we show cumulativity.

`Layer1/Fundamental.v` Proves the fundamental lemma of this model: for any derivable
judgment `Γ ⊢ t ≡ u : A`, then `er A` (the erasure of A) is reducible and its
associated PER relates `t` and `u`, etc.

`Layer1/BadTransp.v` shows that Martin-Löf's identity type does not fit nicely in
this model. This issue was solved in "Impredicative Observational Equality" by
switching to observational equality, and the authors of "Consolidating Equality
in a Proof Irrelevant Universe" explain how to adapt these methods to Martin-Löf's
identity type. We could follow that method if we wanted to have it.

### Ranks

`Ranks/Pred.v` defines the predecessor relation on types: if `T` reduces to
`Π A B` then `A ⊏ T` and `B u ⊏ T` for all reducible `u`, and likewise for Sigma
types.

`Ranks/Acc.v` shows that reducible types are accessible for the predecessor
relation.

`Ranks/Ord.v` defines ordinals as Brouwer trees (`Ord`). An ordinal is either
zero, a successor, or the sup of a family of ordinals indexed by the predecessors
of a type. We define bisimulation of Brouwer trees (`osim`).

`Ranks/Rank.v` associates a rank to any accessible type. The rank of `A` is
the sup of `suc(rk(B))` for any `B ⊏ A`. This is the place in the proof where
accessibility is used to build proof-relevant data by induction on an arbitrary
well-founded relation. 

### Bounded assemblies

The second model is similar to the first model, except that it must track the
truth of propositions. However, we cannot define a PER of reducible propositions
by induction (because of impredicativity!), so we want to over-approximate: a
proposition `P` is reducible whenever we can find a PER for the inhabitants
of `P`. The issue is that there can be many PERs that work for `P`, and thus
there might be several distinct witnesses of reducibility for `P`. This forces
us to use a proof-relevant version of PERs: assemblies.

An *assembly* is the data of a family `El : etm -> Type` and an equality
`Eq : forall t, El t -> forall u, El u -> Prop` that is symmetric and transitive.

A *dependent assembly* indexed over `(El, Eq)` is the data of
* an assembly family `Fam : forall t, El t -> Asm` 
* a coercion function `coe : Eq t tε u uε -> ((Fam t tε).El v) -> ((Fam u uε).El v)`
* a coherence equality `coh : Eq t tε u uε -> ((Fam t tε).Eq v vε w wε) -> ((Fam u uε).Eq v (coe vε) w (coe wε))`
* such that coercing along an equality between tε and tε does nothing
* and coercing from tε to uε, then from uε to vε is the same as coercing from tε to vε

(NB: this is the version with homogeneous equality, probably heterogeneous
equality would be easier)

In the file `Codes/Def.v`, we define a hierarchy of assembly universes by
induction on universe levels. Each assembly universe is defined by an
sub-induction on Brouwer trees: assume that we know how to define α-bounded
assemblies for all α < β. Then the term `T` is associated to the β-bounded
assembly `Tε` if either `T` is associated to `Tε` as an α-bounded assembly, or
one of the following holds:
* `T` reduces to `nat` and `Tε` is the modest assembly of natural numbers
* `T` reduces to `prop` and `Tε` is the co-discrete assembly of propositions
* `T` reduces to `prf p` and `Tε` is the modest assembly corresponding to some
  arbitrary proposition H
* `T` reduces to `univ i` and `Tε` is the universe assembly of level i (assuming the
  induction on universe levels is at stage > i)
* `T` reduces to `pi A B` and `A` is associated to an α-bounded assembly `Aε`, and
  and `B` is associated to a dependent α-bounded assembly `Bε`, and `Tε` is the
  dependent product of assemblies of `Aε` and `Bε`
* `T` reduces to `sigma A B` and `A` is associated to an α-bounded assembly `Aε`, and
  and `B` is associated to a dependent α-bounded assembly `Bε`, and `Tε` is the
  dependent sum of assemblies of `Aε` and `Bε`

`Codes/EqPER.v` shows that the equalities of the assemblies in the universe are PERs

`Codes/Iso.v` and `Codes/IsoPER` define an observational equality on the universe of
assemblies, and prove that it satisfies all the laws it should satisfy.

`Codes/Expand.v` shows that the assemblies are closed under reduction and expansion.

`Codes/WF.v` characterises the coercions that are packed in the universe

`Codes/Lift.v` and `Codes/LiftIso.v` handle universe lifts

`Codes/Sound.v` shows that the assembly model is a refinement of the earlier PER model.

### Interpreting the syntax

The directory `Interp/` interprets the syntax of the theory in the assembly model.

Interpretation is defined in `Inter/Def.v` as a pair of mutual partial functions
`ITy` and `ITm`, defined by induction on raw syntax. Then, all the type formers are
defined and shown to preserve the required structure (this part is mostly technical,
so it was left to the LLM). The proof that the interpretation relation is functional
is in `Interp/Fun.v`. Finally, the fundamental lemma is in `Interp/Fund.v`.

The consistency theorem is in `Interp/Consistency.v`.

