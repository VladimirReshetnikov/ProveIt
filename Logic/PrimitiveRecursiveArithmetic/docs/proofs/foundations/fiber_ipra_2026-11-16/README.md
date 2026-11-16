# FIBER-iPRA

**Finite-query Interfaces with Bounded Evidence and Realizers**

This archive develops a compositional framework for translating finitary,
quantitative mathematics into the ordinary ProveIt iPRA judgment
`Prf PRAAx Γ φ`.

Repository baseline:
`VladimirReshetnikov/ProveIt` commit
`58627ed89814ba122e1f0f012f1aba103cda267b` (16 November 2026).

## Start here

- `paper/fiber_ipra_framework.pdf` - complete human-readable report.
- `paper/fiber_ipra_framework.tex` and `paper/sections/` - LaTeX source.
- `lean/FIBER/Kernel.lean` - small no-placeholder structural source candidate.
- `lean/FIBER/Blueprint.lean` - current-API definitions and theorem targets.
- `lean/FORMALIZATION_PLAN.md` - dependency-ordered route to compiled
  `Prf PRAAx` theorems.
- `reference/fiber_reference.py` - exact finite reference algorithms.
- `reference/test_fiber_reference.py` - 14 regression tests.
- `examples/` - generated demand, certificate, strategy, bisection, and net
  examples.
- `metadata/THEOREM_LEDGER.md` - claim-by-claim status.
- `metadata/difficulty_matrix.csv` - obstacle, repair, and residual boundary.
- `metadata/SOURCE_AUDIT.md` - inspected repository interfaces and prior work.

## Main contribution

Earlier repository packets develop finite certificates, residualized proof
graphs, bounded interaction programs, demand closure, and stable observations.
FIBER-iPRA unifies these ideas in one typed, query-indexed interface calculus:

1. each query has a finite certificate fiber, verifier, observation, and
   equivalence or metric relation;
2. a realizer carries an explicit finite demand map and a literal object
   soundness derivation;
3. local certificates are eliminated by `Prf.exE`;
4. bounded least search is used only when a public canonical code is required;
5. composition is proved by substitution and `Prf.trans`;
6. cyclic demands are closed by a finite monotone fixed-point theorem;
7. fixed bounded quantifier alternations use finite strategy certificates;
8. missing bounds, moduli, gaps, constants, and representatives are exact
   residual producer formulas with a hierarchy of internal eliminations.

The report also gives complete human proofs of a dyadic adjacent-motion Cauchy
theorem, finite-net lifting, guarded branch selection, stable cluster output,
master-certificate formation, and two obstruction results (no primitive-
recursive universal evaluator and no unguarded finite-use exact sign selector).

## Exact status

- Human mathematics: developed in the report.
- Existing ProveIt dependencies: inspected and cited, not rebuilt here.
- New Lean: source-oriented candidates and theorem targets only.  Lean was not
  available in the artifact runtime, so no new kernel-checked theorem is
  claimed.
- Python: all 14 exact finite tests pass.
- PDF: compiled and rendered as part of the archive validation.

A result becomes formally verified only after it compiles in the pinned
repository as a literal `Prf PRAAx` declaration and its axiom audit passes.

## Reproduce

From the archive root:

```sh
bash build.sh
```

This runs the Python tests, regenerates JSON examples, and compiles the PDF.
Lean integration requires a checkout of the pinned ProveIt repository; follow
`lean/FORMALIZATION_PLAN.md`.
