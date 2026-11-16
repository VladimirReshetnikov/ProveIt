# Theorem ledger

The labels below match the paper.  “Embedded source” means that the supplied
Lean statement concludes `Prf PRAAx`; it does not mean that Lean compilation
was available in this runtime.

| ID | Result | Human proof | Lean / executable status |
|---|---|---|---|
| K1 | Proof-carrying step: a node derivable from earlier nodes and base hypotheses is derivable from the base hypotheses alone. | Complete, Theorem 6.2. | `ProofBuild.step`, no placeholders; uncompiled here. |
| K2 | Finite DAG compilation: every node of a reverse-topological proof schedule has an embedded derivation from the base context. | Complete, Theorem 6.4. | `ProofBuild`, `step`, `stepFrom`, `get`; generated schedule included. |
| K3 | QF loop reflection under a precondition, with a possibly quantified terminal theorem. | Complete, Theorem 7.1. | `invariantAtUnder`, `loopUnder`, `loopContract`; no placeholders. |
| K4 | Bounded search/least witness is primitive recursive when the bound and Boolean predicate are explicit. | Complete, Theorem 8.1. | Exact algorithm specified; object arithmetic definitions remain to instantiate. |
| K5 | Backward viability computes exactly the prefixes extendible to a full finite relational path. | Complete, Theorem 8.3. | Python implementation and tests pass; Lean arithmetic instance is a roadmap item. |
| K6 | Lexicographic viable selection constructs a full path without countable or dependent choice. | Complete, Corollary 8.4. | Python implementation and tests pass. |
| K7 | Stable-observable erasure: independent witnesses suffice when a comparison derivation controls their observations. | Complete, Theorem 9.1. | `stableObservable`, no placeholders. |
| K8 | Guarded exactness: approximation yields an exact branch only together with a gap/separation certificate. | Complete, Theorem 9.3. | `exactFromGap`, no placeholders. |
| K9 | Boundary factorization: a global or ineffective theorem remains an explicit premise and is never misclassified as a producer. | Complete, Theorem 10.1. | `withBoundary` and `BoundaryObligations.compile`. |
| K10 | Fixed-family specialization avoids the impossible requirement of a total universal evaluator for arbitrary PR codes. | Complete metatheoretic argument, Proposition 11.1. | Design restriction recorded in schema and interfaces. |
| E1 | Exact cubic bisection for `y^3+y=x`: the trace preserves a rational sign bracket and reaches width at most `2^-p` with explicit fuel. | Complete, Theorem 12.2. | Exact Python producer/verifier; example certificate checked. |
| A1 | Any domain packet filling `TraceObligations` obtains an embedded implication theorem mechanically. | Immediate from K3. | `TraceObligations.compile`, no placeholders. |
| A2 | Any domain packet filling relational, boundary, witness, or exactness obligations obtains the corresponding embedded theorem mechanically. | Immediate from K4/K7/K8/K9. | `ArithmeticInterface.lean`, no placeholders. |

## Explicitly open object-arithmetic work

1. Typecheck the two generic Lean modules in the pinned repository environment.
2. Supply a shared PR coding library for bounded lists, tables, rationals, and
   resource vectors.
3. Prove object-level defining equations and Boolean reflection for that
   library.
4. Instantiate bounded viability, least search, and cubic bisection as actual
   `Prf PRAAx` arithmetic developments.
5. For each deep theorem packet, provide the domain-specific producer or an
   explicit boundary theorem.  The generic compiler cannot manufacture a
   missing height bound, modulus, separation theorem, or finiteness cutoff.
