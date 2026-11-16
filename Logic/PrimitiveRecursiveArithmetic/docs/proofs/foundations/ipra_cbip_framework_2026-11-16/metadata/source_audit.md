# Source audit and novelty boundary

Audit date: 2026-11-16 (America/Los_Angeles)

Repository: `VladimirReshetnikov/ProveIt`

Close-out `main` snapshot: `210616e660a7ab5f0d706761c12bba673174cec9`

## Status boundary

The root PrimitiveRecursiveArithmetic README distinguishes:

- `ConciseIPRA`: checked Lean definitions and bi-interpretations;
- `Derivations`: checked `Prf PRAAx` derivations;
- `docs/proofs`: research packets filed as delivered and not globally rerun or certified.

This package preserves that distinction. No research-packet Lean file is treated as checked merely because it is present in the repository.

## Audited source interfaces

| Path | Audited content | Blob/SHA reported by connector |
|---|---|---|
| `ConciseIPRA/Lean/ConciseIPRA/PR.lean` | `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, recursion equations | `3251631592070d9ed3687cc0bf7dbd5eb452e46f` |
| `ConciseIPRA/Lean/ConciseIPRA/Deduction.lean` | `Prf`, substitution, weakening, cut, quantifier rules, equality transport | `0969040f77fdd3ed9526e360e7a998584b4d9d8c` |
| `Derivations/Lean/IPRADerivations/Core/Basic.lean` | arithmetic symbols, `inst`, open `ind`, congruence | `ae6dd343a7d2d590ae8c10c37a1668296d5ae534` |
| `Derivations/Lean/IPRADerivations/Core/Search.lean` | least bounded search, minimality, found-witness theorem | `519cde8cb4964a2a2b3a009b980bb05cfa955527` |
| `docs/proofs/algebra/ipra_stable_observables/lean/ObjectObservation.lean` | reported compiled object-level finite-loop/stability glue | `0aa94c32fb89ad76d49c3bc3561bc32ef464b27f` |
| `docs/proofs/foundations/ipra_finitary_interface_compiler_2026-11-15/lean/ObjectTraceCompiler.lean` | raw trace compiler outline with four explicit `sorry` milestones | `3bd4499f8cf78fdf370f40fdbfe14157a8bf2407` |

## Close-out change check

The latest commit at the close-out head adds `AnalyticNumberTheory/PowerCleared.lean`, registers it in `IPRADerivations.lean`, and updates derivation documentation. Its commit message reports 432 checks and no `sorryAx`. The core interface blobs listed above were fetched again at the close-out head; their APIs remain the ones used by the Lean plan.

## Closest prior frameworks

The following prior packets are baseline, not novelty claims of this artifact:

- finite-observation and embedding frameworks;
- demand-driven relational certificates / finite-use framework;
- proof-producing finitary interface graphs;
- finite strategy certificates;
- certified finitary presentations and the contract-DAG compiler;
- finitary interfaces and proof-producing compilation.

They already cover Booleanization, finite traces, demand propagation, relational viability, stable observations, finite nets, and numerous domain patterns.

## Additional contribution here

This package focuses on the remaining shared boundary:

1. a typed fixed-program interaction language combining deterministic, alternating, relational, guarded, and stable-observer nodes;
2. a two-stage compiler separating raw local normalization from a tiny normalized `Prf PRAAx` reflection kernel;
3. an explicit no-placeholder source candidate for the normalized kernel;
4. integration of dual bounded-game strategies with relational finite-use computation;
5. direct reuse of the now-large checked `IPRADerivations` core rather than rebuilding arithmetic/search infrastructure;
6. explicit halting reductions classifying several overstrong requested interfaces as impossible uniformly.

## Environment limitation

The artifact runtime had `pdflatex`, `latexmk`, Python, and Git, but no Lean/Lake installation. Network access from the container was unavailable, so the repository could not be cloned for a build. Source was audited through the GitHub connector. The Lean files in this package are therefore not claimed to be compiled.
