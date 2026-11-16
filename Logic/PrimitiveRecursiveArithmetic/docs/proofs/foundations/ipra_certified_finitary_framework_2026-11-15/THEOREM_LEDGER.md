# Theorem and claim ledger

Status vocabulary:

- **Human-complete** - a full mathematical argument appears in the report.
- **Finite-tested** - exact finite instances are exercised by the Python suite.
- **Repository-checked** - an inherited Lean theorem in ProveIt has actual
  `Prf PRAAx` conclusions and a recorded successful build.
- **Lean-blueprint** - source-oriented definitions/targets are supplied here,
  but this artifact did not compile them.
- **Conditional/open** - a named quantitative estimate or certificate producer
  remains to be supplied.

| ID | Claim | Report | Status | Artifact / repository dependency |
|---|---|---|---|---|
| K1 | Boolean `All`, `Any`, and least-search correctness | Sec. 3 | Human-complete; finite-tested; Lean-blueprint | `code/reference_framework.py`; shared fold module planned |
| K2 | Structural Booleanization of fixed bounded formulas | Sec. 3 | Human-complete; Lean-blueprint | Requires K1 and formula compiler |
| T1 | Embedded finite-trace theorem from local `Prf PRAAx` derivations | Sec. 4 | Human-complete; Lean-blueprint | `lean/TraceReflectionRoadmap.lean` |
| T2 | Reduction of T1 to `primitiveRecursionAt` | Secs. 4, 13 | Human-complete integration argument; inherited core repository-checked | ProveIt `ipra_local_global/lean/ObjectIteration.lean` |
| T3 | Certificate reflection | Sec. 4 | Human-complete; Lean-blueprint | Fold library + T1 |
| T4 | Closure of certified finite transducers | Sec. 4 | Human-complete; Lean-blueprint | T1 and proof-producing DSL |
| D1 | Backward schedule equations and coherence | Sec. 5 | Human-complete; finite-tested; semantic repository theorem checked | `BackwardDemand.lean`; object migration pending |
| D2 | Demand-passing transfer without monotonicity | Sec. 5 | Human-complete; finite-tested; Lean-blueprint | `DemandRelationalRoadmap.lean` |
| D3 | Variable finite-query envelope induction | Sec. 5 | Human-complete; finite-tested; Lean-blueprint | finite maxima + D2 |
| R1 | Viability iff existence of a finite compatible path | Sec. 6 | Human-complete; finite-tested; Lean-blueprint | relational roadmap |
| R2 | Least viable finite path | Sec. 6 | Human-complete; finite-tested; Lean-blueprint | bounded search + R1 |
| R3 | Full viability = reachability + backward viability | Sec. 6 | Human-complete; finite-tested; Lean-blueprint | path split/concatenation |
| R4 | Finite witness amalgamation | Sec. 6 | Human-complete; finite-tested | R1-R3 |
| S1 | Stable-observable choice erasure | Sec. 7 | Human-complete; finite-tested; Lean-blueprint | `StableObservableRoadmap.lean` |
| S2 | Independent-certificate cut combinators | Sec. 7 | Repository-checked; reimplemented trivially in roadmap | ProveIt `ObjectObservation.lean` |
| S3 | Exact certificate independence | Sec. 7 | Human-complete; Lean path explicit | S1 + equality substitution |
| V1 | Shrinking viable-cloud inequality | Sec. 8 | Human-complete; finite-tested; Lean-blueprint | paths, finite telescoping, metric kernel |
| V2 | Regular-name corollary from an explicit tail modulus | Sec. 8 | Human-complete; Lean-blueprint | V1 + modulus |
| V3 | Exact label stability under a positive gap | Sec. 8 | Human-complete | V1 + gap |
| M1 | Metastable finite-consumer theorem | Sec. 9 | Human-complete; finite-tested; Lean-blueprint | demand-closed query trace |
| E1 | Precision-contract composition | Sec. 10 | Human-complete | object proof is two cuts/substitutions |
| H1 | Height bound -> complete finite list | Sec. 11 | Human-complete; finite-tested; Lean-blueprint | bounded enumeration |
| H2 | Complete finite list -> height bound | Sec. 11 | Human-complete; finite-tested; Lean-blueprint | finite maximum |
| B1 | No total universal PR evaluator | Sec. 15 | Human-complete barrier | diagonal argument |
| B2 | Cardinality bound does not give a cutoff | Sec. 15 | Human-complete barrier | halting reduction |
| B3 | Exact sign/branch selection at zero is discontinuous | Sec. 15 | Human-complete barrier | LLPO reduction outline |
| B4 | Metastability does not generally yield a Cauchy modulus | Sec. 15 | Human-complete barrier | halting-weight sequence |
| O1 | General Faltings/Siegel height producer | Secs. 11-12 | Conditional/open | verifier and conversion isolated |
| O2 | General Mordell-Weil rational covering representative producer | Secs. 11-12 | Conditional/open | relational verifier isolated |
| O3 | Uniform exact Puiseux data from arbitrary Cauchy coefficients | Sec. 15 | Obstructed in stated generality | use algebraic/splitting input instead |
| O4 | Full Lean implementation of common finite kernel | Sec. 13 | Open engineering task | dependency-ordered roadmap supplied |
