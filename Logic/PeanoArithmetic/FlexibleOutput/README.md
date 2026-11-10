# A divergent program with every possible output in a model of PA

**Status: proposed theorem with a paper proof and a conditional Lean
scaffold. The concrete theorem for first-order Peano arithmetic is not yet
proved in Lean.**

## The proposed theorem

There is one program code `e` for a partial computable function `φ_e : ℕ ⇀ ℕ`
such that

1. `φ_e(x)` diverges for every standard input `x`, and
2. for every standard natural number `n` there is a first-order model
   `M ⊨ PA` with `M ⊨ H_e(0, n)`,

where `H_e(x, y)` is one fixed arithmetical sentence saying "program `e` halts
on input `x` with output `y`". The same code and the same arithmetization serve
every `n`. Each such model is nonstandard, and its halting witness is a
nonstandard computation trace.

The program is a self-referential proof search. `Search(a)` enumerates PA
proofs and halts with output `k` on the first proof of `¬H_a(0, k)`; Kleene's
second recursion theorem gives `e` with `φ_e(x) = Search(e)`. If PA refuted
some output, the search would really halt with some output `k` (possibly a
different one), PA would verify that finite computation, and PA would prove
both `H_e(0, k)` and its negation. So PA refutes no output, the program never
halts, and completeness gives a model of `PA + H_e(0, n)` for each `n`. Only
the consistency of PA is used.

This is the single-input case of the self-reference proof (due to Vadim
Kosoy) in Joel David Hamkins, "Every function can be computable!", and a
consequence of Woodin's universal algorithm; the article gives the references.

## Layout

| Path | Contents |
| --- | --- |
| [`Lean/PAFlexibleOutput/Statement.lean`](Lean/PAFlexibleOutput/Statement.lean) | The concrete target in Foundation's first-order arithmetic and Mathlib's `Nat.Partrec.Code`: `universalGraph`, `haltSentence`, `MainClaim`, `StrongClaim`, `FullySpecifiedMainClaim`, and the named obligations. Definitions of propositions only; nothing is asserted. |
| [`Lean/PAFlexibleOutput/ProofCore.lean`](Lean/PAFlexibleOutput/ProofCore.lean) | The logical core over an abstract `ArithmeticInterface`, given a self-search fixed point: `no_standard_halt`, `no_output_refutation`, `every_output_has_model`, `exists_universalAtZero`. Imports `Std` only. |
| [`Lean/PAFlexibleOutput/MathlibAssembly.lean`](Lean/PAFlexibleOutput/MathlibAssembly.lean) | The same conclusion with the fixed point supplied by `Nat.Partrec.Code.fixed_point₂`: `exists_program_with_arbitrary_possible_output`, conditional on an `ArithmeticBridge` and a `SearchImplementation`. |
| [`Lean/PAFlexibleOutput.lean`](Lean/PAFlexibleOutput.lean) | Import surface, added at placement. |
| [`Article/pa_flexible_output.tex`](Article/pa_flexible_output.tex), [`.pdf`](Article/pa_flexible_output.pdf) | The draft: statement, complete mathematical proof, the Lean statement, the located repository and dependency results, and a five-stage route to a complete Lean proof. |
| [`Research/delivery/`](Research/delivery/) | The rest of the delivered package, unchanged: `README.txt`, `verification_status.txt`, `dependencies.json` (pinned revisions and inspected sources), `notes/mathematical_audit.txt`, `notes/api_audit.txt`, `scripts/`, `lean-toolchain`. |

## What is and is not verified

- The mathematical proof in the article is complete as a paper proof. It has
  not been independently reviewed in this repository.
- The three Lean files are the delivered bytes. The package's author had no
  Lean executable and delivered them uncompiled, which their module comments
  still say. At placement (2026-11-09) all three were compiled unmodified in
  the root workspace (Lean `4.32.0`, mathlib `v4.32.0`, the pinned Foundation
  submodule), with no errors:
  - `ProofCore`: the four printed theorems depend on no axioms;
  - `MathlibAssembly`: both theorems depend on `propext`, `Classical.choice`,
    `Quot.sound`;
  - `Statement`: elaborates; it contains definitions only.

  The only diagnostics are two `checkUnivs` linter warnings on the interface
  structures.
- `ProofCore` and `MathlibAssembly` are **conditional**: no instance of
  `ArithmeticInterface`, `ArithmeticBridge` or `SearchImplementation` for PA
  exists. `PAFlexibleOutput.FullySpecifiedMainClaim` is a `Prop`, not a
  theorem.

## Remaining obligations for the concrete theorem

Taken from the delivery's `verification_status.txt`; the names are those of
`Statement.lean`.

1. `UniversalEvalPartrec`, `UniversalGraphSigmaOne`, `StandardCorrectness`:
   partial recursiveness of the universal evaluator and the standard semantics
   of the chosen formula.
2. `FunctionalityInPAModels`: internal determinism of the chosen formula in
   every model of PA, nonstandard codes and inputs included. Foundation's
   `code_uniq` is commented out at the pinned revision, so this is new work.
3. `RefutationsRE` and an effective proof search with its soundness and
   completeness properties (a `SearchImplementation`).
4. `FiniteProofAdequacy`, consistency of PA and model existence from
   Foundation's Σ₁-completeness, soundness and completeness theorems (an
   `ArithmeticBridge`).
5. Instantiate `MathlibAssembly` and derive `FullySpecifiedMainClaim`; audit
   the axioms of the endpoint.

## Building

The modules belong to the root workspace library `PAFlexibleOutput`. Build one
target at a time:

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
lake build +PAFlexibleOutput.ProofCore
lake build +PAFlexibleOutput.MathlibAssembly
lake build +PAFlexibleOutput.Statement
```

Like `PAUndecidable`, the library imports Foundation and is therefore not part
of the `ProveIt.lean` facade. The delivered `scripts/check_lean.sh` expects
the package's original `lean/` directory and is kept for provenance only.

## Provenance

Delivered as `docs/incoming/pa_flexible_output.zip` (arrival commit
`cb5ce85523`, 364,120 bytes) and placed on 2026-11-09. All thirteen entries of
the package's `SHA256SUMS` manifest matched the placed files; the manifest
itself is not filed, since the repository keeps no package-local checksum
ledgers, and remains in the archive at the arrival commit. The package's
`lean/*.lean` is now `Lean/PAFlexibleOutput/*.lean`, its
`pa_flexible_output.{tex,pdf}` is under `Article/`, and everything else is
under `Research/delivery/`.
