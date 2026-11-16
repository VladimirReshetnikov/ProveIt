# Source audit and novelty boundary

Inspected read-only at ProveIt main commit
`0edaf721b175de6aa219755df18b1588be803a16`.

## Checked logical interfaces

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  (`PR`, `PTm`, `PRAAx`, `PRA.qfInd`, recursion equations).
- `.../Deduction.lean` (`Prf`, weakening, substitution, cut, equality,
  quantifier rules).
- `.../NativeBiInterpretation.lean` (`pra_iff_native`, `native_iff_pra`,
  round trips).

## Foundation prior art

- `foundations/ipra_embedding_framework`
- `foundations/ipra_evidence_framework`
- `foundations/ipra_finite_observation`
- `foundations/ipra_framework`
- `foundations/ipra_framework_2026-11-15`
- `foundations/ipra_uniform_certificates`
- `foundations/ipra_embedding_framework_2026-11-15`

These packets already contain bounded Booleanization, deterministic finite
traces, finite relational chains, quantitative names, robust branching,
metastability, finite nets, power gaps, and certificate architecture. They are
credited rather than presented as new discoveries.

## Obstruction/scope sources

- `algebra/puiseux_ipra/evidence/scope_obstruction.md`
- `diophantine-number-theory/faltings_ipra/README.md`
- `diophantine-number-theory/siegel_ipra/README.txt`
- Euler–Rodrigues, Minkowski, and Dirichlet–Kronecker packet discussions of
  LLPO/sign-choice boundaries.

## Additional contribution in this archive

The main additional theorem is consumer-oriented **finite-use relational
composition**: a bounded adaptive consumer is combined with a multivalued
finite producer through backward viability. The report adds certificate
reflection, exact branch-invariant elimination, quantitative diameter
elimination, and a precise distinction between finite-use success and an
infinite coherent selector.

The archive also gives a more explicit source-level generic `PRA.qfInd`
wrapper than the prior architecture documents. It is not claimed compiled.

No priority claim is made for general dynamic programming, constructive
analysis, proof mining, metastability, or certificate checking.
