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
model, except that we use define our PERs in `Prop` to handle the entire
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
shows consistency (`Interp/Canonicity.v`). Throughout the entire development,
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

## Architecture

* `Syntax/` — annotated syntax (`tm`, Autosubst2-generated from `Syntax/cicm.sig`),
  the erased calculus (`etm`), and erasure `er : tm -> etm` (`Syntax/Erasure.v`).
* `Reduction/` — weak-head reduction of `etm`, stuck terms, determinism.
* `Typing/Rules.v` — `ty`, `wfc`, `cv` for CIC⁻ **with full Church annotations**.
* `Typing/Subst.v` — admissibility of renaming and substitution for
  `wfc`/`ty`/`cv`, context validity (`ty_wfc`), `lookup`'s functionality and the
  type it finds (`lookup_ty`), and `ty_subst1`. Statements are `inhabited`-wrapped
  so that one `Combined Scheme` covers the three mutual judgements; nothing
  downstream needs the derivation itself, only its existence, because `funtm`
  consumes a derivation and yields a Prop. Required only by `Interp/Fund.v`, so
  adding it recompiles nothing else.
* `Layer1/` — the truth-agnostic Allen-style PER model **in `Prop`**: `LR`, `tau`,
  `eqty n A A'`, `Rel T a b`, `Good`, `Good_ty`, `NatPer`, `PiPer`, `SigPer`, and
  the layer-1 fundamental theorem (`Layer1/Fundamental.v`, `fundamental_ty`,
  `fundamental_U`, `fundamental_P`, `SEl`, `SubstRel`).
* `Ranks/` — Brouwer trees (`Ord`, `Pred`, `prec`, `rk`) built from `Acc`.
* `Codes/` — the stratified assembly codes: `Stage`, `Refine`, `El`, `eqEl`,
  `Transp`, `Ust`, `U`, `Code`, `iso`/`LIso`/`ciso`, the `HJ` record (transport),
  `cto`/`cpull`, `liftCode`/`liftIso`/`liftEl` (level lift).
* `Interp/` — the layer-2 model: universe families (`kUFam`, `kAt`, `kElAt`,
  `kEqAt`, `kRel`), the type formers (`piFam`, `sigFam`, `natFam`, `propFam`,
  `prfF`, `univFam`), the element operations (`piApp`, `sigFst`, `sigSnd`,
  `sigPair`, `semrec`), environments (`Entry`, `Env`, `ext`, `ers`, `EnvRel`,
  `EntryRel`), the interpretation `ITy`/`ITm` (`Interp/Def.v` = blueprint 9.1),
  its inversions (`Interp/Inv.v`), weakening/substitution stability
  (`Interp/Subst.v`), the canonical-form **decoder** (`Interp/Fun.v`) and
  section 9 itself (`Interp/Fund.v`).

