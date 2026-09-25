# CIC⁻ normalisation inside CIC, via `Acc`'s large elimination

Rocq formalisation of the consistency and normalisation of **CIC⁻** (MLTT with Π,
Σ, N with large elimination, impredicative `Prop` with ⊥, and a predicative
universe hierarchy with **explicit** lifts) inside plain CIC, following
`cicm-rigorous-proof.pdf` and `cicm-rocq-blueprint-v2.pdf`.

W types and the identity are not handled as of now. We know that the identity type
does not change the proof-theoretic strength of the system (one can use setoid models
to recover an equality). However, W types *do* change the strength of the system quite
a bit. There is no reason to expect that this method would be unable to handle them.

This formalisation was written by a frontier LLM, following a strategy devised
by a human. The strategy was slightly modified to account for the obstacles found
by the LLM during the formalisation.

---

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

