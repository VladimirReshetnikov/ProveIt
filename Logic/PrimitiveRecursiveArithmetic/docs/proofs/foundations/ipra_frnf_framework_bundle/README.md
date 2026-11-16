# Finitary Realizer Normal Form for iPRA

This archive develops a proof-producing framework for embedding finite and
quantitative mathematics into intuitionistic primitive recursive arithmetic
(iPRA). It was prepared after auditing
`VladimirReshetnikov/ProveIt/Logic/PrimitiveRecursiveArithmetic` on
2026-11-16. The current PrimitiveRecursiveArithmetic README at audit time was
commit:

```text
67f5216e0b1337b533b43064262aeff268bc56db
```

## Principal contribution

The report introduces **Finitary Realizer Normal Form (FRNF)**. A proof is
compiled to a finite acyclic graph of statically specialized
primitive-recursive transducers, bounded searches, clocked loops with
quantifier-free invariants, finite relational witness clouds, stable
observers, and explicit producer boundaries.

The main technical correction to ordinary “finite-use” frameworks is a pair of
horizons on every interface:

- the **computation horizon**, containing rows read by the executable routine;
- the **justification horizon**, containing rows whose contracts are required by
  the object-language correctness proof.

The graph runs a reverse demand pass before induction. An explicit bottom value
means “unused”; numerical demand zero means that row zero is genuinely required.
Bounded conditions are Booleanized, adaptive routines are verified as clocked
traces by quantifier-free induction, and local derivations are combined by
simultaneous cut into an actual `Prf PRAAx` endpoint.

The framework also treats nonunique approximate outputs relationally. Backward
viability constructs finite paths without an infinite-choice principle; stable
observers erase internal choices; exact branch labels require an explicit gap.

## Contents

- `paper/ipra_frnf_framework.pdf` — 60-page research report.
- `paper/ipra_frnf_framework.tex` and `paper/sections/*.tex` — complete modular
  LaTeX source.
- `lean/FRNF/Kernel.lean` — repository-aligned logical combinators whose intended
  outputs are embedded `Prf PRAAx` derivations.
- `lean/FRNF/ObjectTargets.lean` — explicit object-language implementation
  targets, with visible `sorry` placeholders where work remains.
- `lean/FRNF/Semantic.lean` — small host-level records; no semantic theorem is
  promoted to an object proof.
- `reference/frnf.py` — exact standard-library reference algorithms.
- `reference/test_frnf.py` — eleven regression tests.
- `metadata/obstacle_matrix.csv` — resolution and boundary status for recurring
  obstacles.
- `metadata/theorem_ledger.csv` — theorem-by-theorem claim ledger.
- `metadata/interface.schema.json` — machine-readable interface schema.
- `metadata/repository_audit.md` — contribution boundary relative to ProveIt.
- `validation/` — test output, placeholder audit, PDF metadata, and extracted
  text.

## Main results argued in the paper

1. Bounded-formula Booleanization.
2. Least bounded search.
3. The no-universal-primitive-recursive-evaluator diagonal barrier.
4. Dual-horizon sequential composition.
5. Least reverse demand closure on a finite DAG, with an explicit unused bottom.
6. Clocked trace internalization by quantifier-free induction.
7. Proof-producing topological schedules using simultaneous cut.
8. Backward viability and least viable finite paths.
9. Shrinking finite-horizon coherence without an infinite branch.
10. Stable-observer erasure and exact gap collapse.
11. Majorized frozen descent.
12. Quantitative finite-net minimization.
13. Guarded reciprocal under positive apartness.
14. The no-cardinality-to-cutoff halting reduction.
15. A conditional height-to-complete-list compiler.
16. The FRNF compilation theorem schema.

## Exact status

The mathematical arguments in the paper are human-readable, non-formalized
proofs. The Python reference tests pass using exact rational arithmetic.

The new Lean files were **not compiled** in the artifact environment because
Lean and Lake were unavailable. `FRNF/Kernel.lean` has no `axiom` declarations
or `sorry` placeholders, but that is only a source audit, not a kernel-check
claim. `FRNF/ObjectTargets.lean` deliberately contains eight visible `sorry`
markers for the unfinished object arithmetic/compiler layer. No new theorem in
this archive is advertised as kernel checked.

The upstream ProveIt `Derivations` library is different: it already contains
many checked terms of type `Prf PRAAx`. The proposed compiler is designed to
reuse that library and eventually emit the same kind of endpoint.

## Reproduce

From the archive root:

```bash
./build.sh
```

This runs the eleven Python tests, validates JSON/CSV metadata, compiles the
paper with `pdflatex`, extracts PDF text, records PDF metadata, and refreshes the
Lean placeholder audit. See `BUILD.md` for integration with ProveIt.
