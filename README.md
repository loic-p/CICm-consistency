# A model for CIC⁻ in CIC, via `Acc`'s large elimination

The [Calculus of Inductive Constructions (CIC)](https://inria.hal.science/hal-01094195v1/document)
is an idealised version of the type theory that underlies the Rocq prover. It
features both a *predicative* hierarchy of universes and an *impredicative*
sort of propositions which sits at the bottom of the predicative hierarchy.
Both kinds of universes allow the formation of inductive families, with the
caveat that inductive propositions cannot be eliminated into `Type` unless
they satisfy a certain [subsingleton criterion](https://rocq-prover.org/doc/V9.2.0/refman/language/core/inductive.html#destructors).

For our purposes, it will be simpler to restrict our attention to six
prototypical inductive families. I believe that up to extensionality, any
inductive family can be encoded using these six:
* Σ-types
* the type ℕ of natural numbers
* type of well-founded trees `W A B`
* the False proposition
* Martin-Löf's inductive equality type
* the accessibility predicate `Acc`

The last three (`False`, `Id`, `Acc`) are inductive propositions that
satisfy the subsingleton criterion, and thus CIC allows large elimination
for all six. The mix of impredicative `Prop` and these inductive families
results in a system with very high proof theoretic strength.

Our focus in this development is `Acc`, the more mysterious of the bunch.
`Acc` may look rather innocuous at first sight, but it turns out that allowing
definitions by recursion on *propositionally* well-founded relations has
far-reaching consequences -- for one, it means that any terminating Turing
machine may be used to define a function of type `ℕ -> ℕ`. The goal of this
repository is to show that `Acc` plays an important role in the the proof
theoretic strength of CIC.

Define CIC⁻ to be CIC **without the large elimination rule for the accessibility
predicate**. We want to show that CIC⁻ is weaker than CIC. To do so, we build a
model of CIC⁻ in Rocq, making essential use of the fact that Rocq allows large
elimination the accessibility predicate. From there, we deduce the consistency
of CIC⁻ (with its full universe hierarchy) as a theorem of CIC. This shows that
CIC is strictly stronger than CIC⁻.

A set-theoretic reading of our model construction shows that CIC⁻ has the same
strength as Zermelo set theory + "V_α exists", for any ordinal α that is smaller
than the proof ordinal of *predicative* MLTT with W-types. This result extends
[Rathjen's analysis of MLV(P)](https://doi.org/10.1007/978-94-007-4435-6_15).

At the moment, our formalisation does not include identity types. The reasons
are mostly technical (I will say more on this later on), but in any case, we do
know that identity types do not increase the proof-theoretic strength of the
system, since [they can be simulated using setoids](https://arxiv.org/abs/1909.01414).
Therefore, this omission should not diminish the result.

## AI usage

This formalisation was written by a frontier LLM, following a strategy devised
by a human. The strategy had to be revised every now and then to account for the
obstacles encountered by the LLM during the formalisation. The commits of this
repository are artificially squashed to avoid advertising for the vendor of
said LLM. The README.md file is entirely written by a human (myself).

## Proof outline

The observation that makes the proof work is that *proofs of propositions do
not play any role in the computation of types*. This is true in CIC⁻, but not
in CIC, as the termination of a computation might hinge on an accessibility
proof.

This observation was already made by Tabareau and myself in 
[Impredicative Observational Equality](https://hal.science/hal-03857705v2),
where we show normalisation of the *predicative* part of the calculus
with a logical relation argument that takes place in a very weak metatheory
(predicative MLTT). This model completely ignores everything that happens
in the impredicative layer, and as such, it is not able to show *consistency*
of the system -- which is shown afterwards in a much stronger metatheory (ZFC).

In this repository, we start by doing a similar truth-agnostic normalisation
model, except that we define our PERs in `Prop` to handle the entire
universe hierarchy at once. Then, we use this first model to associate an ordinal
to every well-formed type, which encodes its complexity (we call this ordinal the
*rank* of the type by analogy with set theory). For instance, the rank of any
proposition is 0, the rank of `Π A B` is the successor of the sup of rank(A)
and rank(B(a)) for `a : A`, etc. These ranks are represented as Brouwer trees,
and defined *by induction on accessibility proofs* provided by the first model.

Then, we define a second model using these ranks. Unlike the first model, this
new model must keep track of impredicative truth values, so we interpret
types as *assemblies* (i.e., proof-relevant PERs) of bounded rank. More
specifically, we define a universe of assemblies by induction on ranks:
```
Univ 0       = ∅
Univ (α+1)   = ANat, AProp, APrf p, AUniv, Σ/Π/W of elements of V_α, embeddings
Univ (sup f) = embeddings
```
Where `ANat` is the assembly of natural numbers, `AProp` is the codiscrete
assembly of modest assemblies, `APrf p` is the modest assembly corresponding
to the proposition `p`, `AUniv` codes for the universes that we have already
defined, etc. We also define an `El` function, as well as equalities between
assemblies and (heterogeneous) equalities between their elements, in a
simultaneous way. Naïvely, this would require an inductive-recursive definition,
but we re-use an [old trick of mine](https://github.com/loic-p/setoid-universe/)
to encode it as a plain inductive definition.

Crucially, our use of ranks lets us define the universe hierarchy without
needing more than one meta-theoretic universe. The codes are defined by
*recursion* on ranks, which ensures that they remain small! Finally, we
interpret the syntax of CIC⁻ in our universes of assemblies of bounded rank.
The empty proposition is interpreted as an empty assembly, which shows
consistency (`Interp/Consistency.v`). Throughout the entire development,
no axioms are used.

## Sanity checks

To make sure that we did not inadvertently cheat by forgetting some typing rules,
the directory `Tests/` contains a few derivations in our formalised calculus.
* `Tests/Eq.v` defines the equality of natural numbers by large elimination, and
  shows`eq 0 0` and `eq 0 1 -> False` 
* `Tests/Logic.v` defines the logical and and logical or using impredicative
  encodings, and shows their introduction/elimination rules.
* `Tests/Aczel.v` uses W-types to define Aczel's sets and the bisimulation
  relation. We also define a handful of set theoretic constructions.
* `Tests/Sigma.v` defines two high complexity types. First, define the powerset
  operator as `P(A) = (A -> Prop)`. Then, define the function `beth : Nat -> Type`
  by `beth 0 = Nat` and `beth (suc n) = P(beth n)`. Finally, define `beth_omega`
  as `Sigma (n : Nat) . beth n`. For the second high-complexity type, we replace
  the powerset operator by the modified powerset operator `P'(A) = (A -> Type)`.

## Type-checking the proof

The proof has been checked using Rocq 9.3. All the results are axiom-free.
The proof takes quite a while to type-check on a medium-end laptop (expect
5 to 10 minutes).

## Details

### Syntax and Typing rules

In the directory `Syntax/`, we define two versions of the raw syntax for CIC⁻.
The first one (`tm`) is defined in `Syntax/Ann.v`, and uses heavy annotations
in order to guarantee uniqueness of typing (lambdas and applications contain
annotations for both the domain and the codomain, a lot of the syntax is
annotated with universe levels to handle explicit cumulativity, etc.) The
second syntax (`etm`) is defined in `Syntax/Erased.v` and removes annotations.
We also define an erasure function from `tm` to `etm`.

The syntax and the appurtenant renaming/substitution lemmas are generated
using [Sulfur](https://github.com/MathisBD/rocq-sulfur).

In the directory `Reduction/`, we define weak-head reduction of erased terms.
We also define values, stuck terms, and we prove that the reduction is
deterministic in `Reduction/Determinism.v`.

In the directory `Typing/`, we define the typing rules and the conversion rules
of our calculus. In `Typing/Subst.v` we show that well-formed renamings and
well-typed substitutions preserve the typing judgments.

### Layer 1: the truth-agnostic PER model

The first layer is a model of CIC⁻ which ignores everything that has to do with
propositions, hence "truth-agnostic". This layer is used to prove that every
type in the empty context is either stuck on a proof of False, or admits a
normal form which can be computed by head reduction. To do so, we interpret
types as partial equivalence relations (PERs) over `etm`. The interpretation
of non-propositional types roughly follows
[Allen's model](https://ecommons.cornell.edu/entities/publication/bef60b4e-2daf-4e41-b5f3-046862435277),
while propositions are interpreted as trivial PERs.

`Layer1/Per.v` defines the basic calculus of `Prop`-valued PERs. We define
the PER of stuck terms, the PER of natural numbers, dependent sums/products
of PERs, W-types of PERs, and a PER of propositions (which merely asks its
elements to have a head normal form).

`Layer1/Def.v` defines a logical relation à la Allen (`LR`). The relation is
very similar to the one used in [Impredicative Observational Equality](https://hal.science/hal-03857705v2),
except that the PERs are valued in `Prop` so that we can handle the full
universes hierarchy with only one metatheoretic universe.

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
this model. This problem was solved in
[Impredicative Observational Equality](https://hal.science/hal-03857705v2)
by switching to observational equality, and the authors of
[Consolidating Equality in a Proof Irrelevant Universe](https://inria.hal.science/hal-05688985)
explain how to adapt the same model to Martin-Löf's identity type. We could
follow their method if we really wanted to have identity types, but as we
said in the intro, they do not change the proof theoretic strength of the
system, so we chose not to bother with it.

### Ranks

`Ranks/Pred.v` defines the predecessor relation on types: if `T` reduces to
`Π A B` and `A` is reducible, then `A ⊏ T` and `B u ⊏ T` for all reducible
`u : A`. Likewise for Σ-types and W-types.

`Ranks/Acc.v` shows that reducible types are accessible for the predecessor
relation.

`Ranks/Ord.v` defines ordinals as Brouwer trees (`Ord`). An ordinal is either
zero, a successor, or the sup of a family of ordinals indexed by the predecessors
of a type. We define bisimulation of Brouwer trees (`osim`).

`Ranks/Rank.v` associates a rank to any accessible type. The rank of `A` is
the sup of `suc(rk(B))` for any `B ⊏ A`. This is one of the two places in the
proof where accessibility is used to build proof-relevant data by induction
on an arbitrary well-founded relation. 

### Layer 2: the bounded assembly model

The second model is similar to the first model, except that it must track the
truth of propositions. However, we cannot define a PER of reducible propositions
by induction (because of impredicativity!), so we want to over-approximate: a
proposition `P` is reducible whenever we can find a PER for the terms of type
`P`. The issue is that there can be many PERs that work for `P`, and thus
there might be several distinct witnesses of reducibility for `P`. This forces
us to use a proof-relevant version of PERs: assemblies.

An *assembly* is the data of a family `El : etm -> Type` and an equality
`Eq : forall {t u}, El t -> El u -> Prop` that is reflexive, symmetric and
transitive.

A *dependent assembly* indexed over `(El, Eq)` is the data of
* a type family `Fam : forall {t}, El t -> etm -> Ty` 
* a heterogeneous equality `Heq : forall {t u v w} (tε : El t) (uε : El u), Fam tε v -> Fam uε w -> Prop`
* a coercion function `coe : forall {t u v} {tε : El t} {uε : El u}, Eq tε uε -> Fam tε v -> Fam uε v`
* a coherence equality `coh : forall {t u v} {tε : El t} {uε : El u} (e : Eq tε uε) {vε : Fam tε v}, Heq tε uε vε (coe e vε)`
* such that `Heq` is reflexive, heterogeneously symmetric and heterogeneously transitive

Every assembly has a PER associated to it, which we call its *truncation*.
The truncation of `(El, Eq)` relates `t` and `u` whenver there exists
`tε : El t` and `uε : El u` such that `Eq tε uε`.

We define a hierarchy of assembly universes by induction on universe levels.
Each assembly universe is defined by an sub-induction on Brouwer trees: assume
that we know how to define α-bounded assemblies for all α < β. Then the term
`T` is associated to the β-bounded assembly `Tε` if either `T` is associated
to `Tε` as an α-bounded assembly, or one of the following holds:
* `T` reduces to `nat` and `Tε` is the modest assembly of natural numbers
* `T` reduces to `prop` and `Tε` is the co-discrete assembly of propositions
* `T` reduces to `prf p` and `Tε` is the modest assembly corresponding to some
  arbitrary proposition H
* `T` reduces to `univ i` and `Tε` is the universe assembly of level i (assuming the
  induction on universe levels is at stage > i)
* `T` reduces to `Π A B` and `A` is associated to an α-bounded assembly `Aε`, and
  and `B` is associated to a family of α-bounded assemblies `Bε`, and `Tε` is the
  dependent product of assemblies of `Aε` and `Bε`
* `T` reduces to `Σ A B` and `A` is associated to an α-bounded assembly `Aε`, and
  and `B` is associated to a family of α-bounded assemblies `Bε`, and `Tε` is the
  dependent sum of assemblies of `Aε` and `Bε`
* `T` reduces to `W A B` and `A` is associated to an α-bounded assembly `Aε`, and
  and `B` is associated to a family of α-bounded assemblies `Bε`, and `Tε` is the
  W-type obtained from the assemblies `Aε` and `Bε`.

Stated naïvely, this definition of the universe at stage β from the lower stages is
a huge inductive-recursive definition, because the fields `El`, `Eq`, `Fam`, `Heq`,
`coh`, `coe`, `refl`, `sym`, `trans`, `hrefl`, `hsym` and `htrans` are all mutual.
However, we have already solved that problem to build
a [universe of proof-relevant setoids](https://github.com/loic-p/setoid-universe/)
as an inductive definition, so we use the same recipe here.

We start by defining an over-approximation of `El` and `Fam` as an inductive family
(`Codes/Def.v`), where the recursive occurences in Π-types and W-types are equipped
with arbitrary "equality" relations which are possibly ill-behaved. Then, we define
the correct equality relations `Eq` and `Heq` by recursion on the over-approximated
family (`Codes/Eq.v`). Then, we carve out a subfamily of `El` and `Fam` where the
arbitrary equality relations match the correct ones (`Codes/WF.v`). Then, we show
reflexivity (`Codes/Refl.v`) and symmetry (`Codes/Sym.v`) by recursion on the
*well-formed* elements of `El` and `Fam`. Lastly, we define transitivity, coercion
and coherence simultaneously by recursion on the well-formed elements (`Codes/Str.v`).

This process is further complexified by the fact that equalities and their
properties must be defined *across ordinal stages*. We want to be able to compare
an element of the universe at stage α with an element at stage β. This adds even
more noise to the construction, even though there's nothing particularly difficult
there.

Now that we know how to define a stage of the universe from all the previous
ones, we prove two additional properties. In `Codes/Sound.v`, we show that if
`t` tracks an element `tε` of some assembly, then `t` is reducible in the
truncation of said assembly. In `Codes/Expand.v`, we show that the assemblies
are closed under reduction and expansion.

In `Codes/Level.v` we do the outer induction on universe levels, thereby finishing
off the definition of our hierarchy of assembly universes. Finally, we show
cumulativity in `Codes/Lift.v`.

### Interpreting the syntax

The directory `Interp/` interprets the syntax of the theory in the assembly model.

Interpretation is defined in `Interp/Def.v` as a pair of mutual partial functions
`ITy` and `ITm`, defined by induction on the annotated syntax. Then, all the type
formers are defined and shown to preserve the required structure (this part is
mostly technical, so it was left to the LLM). The proof that the interpretation
relation is functional is in `Interp/Fun.v`. Finally, the fundamental lemma is in
`Interp/Fund.v`.

The consistency theorem is in `Interp/Consistency.v`.

