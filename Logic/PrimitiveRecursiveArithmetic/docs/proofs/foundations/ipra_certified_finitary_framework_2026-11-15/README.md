# Certified finitary interfaces for mathematics in iPRA

This artifact develops a demand-driven, relational, proof-producing framework
for translating finite mathematical constructions into intuitionistic
primitive recursive arithmetic (iPRA). It was prepared against ProveIt commit
`9df5cbdf39e6220be823f611987bd584d37711fd`.

## Main files

- `paper/ipra_certified_finitary_framework.pdf` - compiled research report.
- `paper/ipra_certified_finitary_framework.tex` and `paper/sections/*.tex` -
  complete LaTeX source.
- `lean/TraceReflectionRoadmap.lean` - explicit trace formulas and a detailed
  reduction to the repository's checked `primitiveRecursionAt` transformer.
- `lean/DemandRelationalRoadmap.lean` - backward-demand and viability targets.
- `lean/StableObservableRoadmap.lean` - complete cut combinators and the
  stable-observation/shrinking roadmap.
- `code/reference_framework.py` and `code/test_reference_framework.py` - exact
  finite reference algorithms and ten passing regression tests.
- `THEOREM_LEDGER.md`, `metadata/difficulty_matrix.csv`, and
  `metadata/framework_schema.json` - claim/status tracking.

## Principal contributions

1. **Demand-passing trace compilation.** Backward precision propagation is
   combined with the checked object-iPRA primitive-recursion invariant
   transformer. This handles parameter-changing induction without monotonicity
   assumptions or all-precision induction predicates.
2. **Stable-observable choice erasure.** Independently selected finite
   certificates produce a coherent observable whenever every two valid
   certificates satisfy an explicit cross-precision stability estimate. No
   compatible infinite witness sequence is needed.
3. **Viability only when necessary.** Backward viability and shrinking clouds
   are reserved for constructions whose mathematics genuinely depends on
   adjacent refinements.
4. **Finite-consumer metastability.** A bounded downstream computation may use
   one demand-closed stable window without falsely converting metastability
   into a global Cauchy modulus.
5. **Producer/verifier separation.** Height bounds, rational covering
   representatives, analytic constants, singular branch data, and similar deep
   inputs remain named producer obligations rather than being hidden inside a
   verifier.

## Status

The report gives complete human arguments for the generic finite theorems. The
Python tests pass. The Lean files are **blueprints, not completed
formalizations**: the artifact environment had no Lean executable or dependency
closure. Visible `sorry` placeholders mark exact integration work; no claim is
made that those targets are kernel checked.

The report reuses two already compiled repository components as planned
building blocks:

- `ipra_local_global/lean/ObjectIteration.lean`, whose conclusions include
  actual `Prf PRAAx` primitive-recursion invariant transformers; and
- `ipra_stable_observables/lean/ObjectObservation.lean`, whose conclusions
  include actual `Prf PRAAx` certificate/stability combinators.

## Reproduce

```bash
bash build.sh
```

The script runs the Python tests, compiles the PDF with `latexmk`, and writes
validation logs. A ProveIt/Lean checkout is required separately to complete and
check the Lean roadmaps.
