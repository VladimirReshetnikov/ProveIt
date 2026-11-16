# Proof-Carrying Observation Graphs for iPRA

This package develops a general framework for translating finite mathematical
constructions, quantitative approximations, relational witnesses, and local
proof contracts into derivations in intuitionistic primitive recursive
arithmetic (iPRA).

The source audit is pinned to the public `main` branch of
`VladimirReshetnikov/ProveIt` at commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.

## Start here

- `paper/ipra_pcog_framework.pdf` — the complete 59-page research report.
- `paper/ipra_pcog_framework.tex` and `paper/sections/` — complete LaTeX source.
- `THEOREM_LEDGER.md` — claim-by-claim status and formalization route.
- `lean/IMPLEMENTATION_PLAN.md` — dependency-ordered path to a complete Lean
  implementation in the existing `ConciseIPRA` library.
- `code/pcog.py` — exact finite reference implementation using only Python's
  standard library and `fractions.Fraction`.
- `examples/example_run.json` — reproducible graph and relational-cloud run.

## Main contribution

A **proof-carrying observation graph** (PCOG) is a fixed finite directed
acyclic graph whose nodes are:

1. exact primitive-recursive calculations;
2. bounded traces with quantifier-free invariants;
3. finite relational witness clouds;
4. stable observation/comparison rules; or
5. theorem-specific finalizers.

Every node carries, or is required to carry, an actual object-theory proof
constructor. A host-level compiler specializes the fixed graph to concrete
`PR` syntax, propagates precision and resource demands backward, proves each
recursive component by quantifier-free induction, and composes the resulting
`Prf PRAAx` derivations in topological order. Because program syntax is
specialized before internalization, no total primitive-recursive evaluator for
arbitrary encoded programs is assumed.

The report gives full human arguments for:

- fixed bounded-formula Booleanization and least bounded search;
- finite-trace reflection and terminal extraction;
- finite proof-graph compilation and staged internalization;
- least safe backward demand propagation and forward validity;
- finite relational viability and lexicographically least paths;
- shrinking finite-horizon coherence with an explicit Cauchy modulus;
- exact label recovery under a positive separation gap;
- stable observations from independent certificates;
- fixed-dimensional lexicographic descent fuel;
- common finite windows outside finitely many exceptional sets;
- conversion between explicit height bounds and complete finite lists;
- finite auxiliary exhaustion without a global witness selector.

## Difficulties addressed

The framework resolves recurring architectural problems in the repository:
semantic algorithms that stop before an embedded theorem, unstable exact
selectors, hidden precision choices, conflation of cardinality with a search
cutoff, and use of host computation in place of object-iPRA derivations.

It does **not** manufacture missing deep producers. General effective
Faltings/Siegel height bounds, uniform Mordell–Weil covering data, deep
prime-distribution estimates, and exact singular-branch selectors remain
explicit theorem-specific interfaces.

## Formal and executable status

- **Human mathematics:** complete for the generic results listed in
  `THEOREM_LEDGER.md`.
- **Python:** ten exact-arithmetic regression tests pass. The worked cubic
  graph verifies its local contracts and final precision bound.
- **PDF:** compiled, rendered page-by-page, visually inspected, and preflighted.
- **Lean:** repository-specific source and a detailed implementation plan are
  supplied. The files were not elaborated in this artifact environment because
  no Lean executable was available. No new theorem in this package is labeled
  kernel-checked.
- **Inherited checked facts:** the report reuses the repository's reported
  object-iPRA trace and stable-observation combinators, while clearly
  distinguishing them from new blueprints.

## Reproduce

From this directory:

```sh
bash build.sh
```

The script runs the Python tests, regenerates the exact example, rebuilds the
PDF with `latexmk`, and records validation output. Python needs only the
standard library. A TeX installation with the packages named in the main
source is required. Lean is intentionally not downloaded by the build.

## Package layout

- `paper/` — report source and compiled PDF.
- `lean/` — proof-composition core, bounded-formula and viability blueprints,
  and completion plan.
- `code/` — exact reference algorithms and tests.
- `examples/` — machine-readable worked run.
- `metadata/` — claims, source audit, framework schema, and difficulty matrix.
- `validation/` — actual test, build, PDF metadata, and preflight records.
- `MANIFEST.sha256` — integrity hashes of all distributed files except itself.

Finite tests support the implementation, but they are not an iPRA proof
checker. The final authority for a completed application remains a declaration
whose type is literally `Prf PRAAx [] phi`, followed by a successful build and
axiom audit.
