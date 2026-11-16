# KIFC-S theorem and claim ledger

Status vocabulary:

- **Inherited checked** - declaration exists in the pinned ProveIt source as an
  embedded theorem; this artifact did not rebuild it.
- **Human-complete** - the report gives a full ordinary mathematical proof.
- **Finite-tested** - exact reference code has passing tests.
- **Source candidate** - no-placeholder Lean source is supplied but was not
  compiled in this runtime.
- **Lean blueprint** - definitions, theorem boundaries, and completion path are
  supplied; application proof fields remain to be constructed.
- **Conditional** - the consumer theorem is complete relative to explicit
  producer formulas.
- **Open** - a mathematical or integration producer remains.

| ID | Claim | Report | Status | Artifact |
|---|---|---|---|---|
| C1 | Contract-sequent equivalence | Section 4 | Human-complete; source candidate | `OpenContract.lean` |
| C2 | Contract identity, simultaneous cut, weakening, conjunction, substitution | Section 4 | Human-complete; source candidate | `OpenContract.lean` |
| C3 | Native contract equivalence | Sections 4, 13 | Inherited checked transfer plus C1 | `OpenContract.lean`, `BridgeBlueprint.lean` |
| Q1 | Least backward query reachability | Section 5 | Human-complete; finite-tested | Python tests |
| Q2 | Least stable residual frontier | Section 5 | Human-complete; finite-tested | Python tests |
| Q3 | Topological contract compilation | Section 5 | Human-complete relative theorem; Lean blueprint | `GraphCompilerBlueprint.lean` |
| Q4 | Multi-query union and dead-code invariance | Section 5 | Human-complete; finite-tested | report, Python |
| S1 | Two-sided bounded-strategy certificate schema | Section 6 | Human-complete; finite-tested semantics | Python, blueprint |
| S2 | Local decidability for each fixed reflected bounded formula | Section 6 | Human-complete; Lean blueprint | `BoundedStrategyBlueprint.lean` |
| B1 | Boolean reflection and bounded folds | Section 7 | Human-complete schema; inherited arithmetic/search | report, upstream |
| T1 | Normalized trace reflection | Section 8 | Human-complete; source candidate | `NormalizedTrace.lean` |
| D1 | Acyclic reverse demand | Sections 5, 9 | Human-complete; finite-tested | report, Python |
| D2 | Capped cyclic demand closure | Section 9 | Human-complete; finite-tested | report, Python |
| R1 | Backward viability iff extendable suffix | Section 10 | Human-complete; finite-tested | report, Python |
| R2 | Least viable finite path | Section 10 | Human-complete; finite-tested | report, Python |
| H1 | Finite-use stable-observer elimination | Section 11 | Human-complete; Lean blueprint | report, `CoherenceBlueprint.lean` |
| H2 | Coherent path from explicit extension system | Section 11 | Human-complete; Lean blueprint | report |
| H3 | Regular name from motion and tail modulus | Section 11 | Human-complete conditional theorem; Lean blueprint | report |
| G1 | Guarded totalization | Section 12 | Human-complete conditional theorem | report |
| G2 | Finite-net transfer and gluing | Section 12 | Human-complete conditional theorem | report |
| A1 | Checked algebraic backend reuse | Section 13 | Inherited checked backend | upstream |
| P1 | Full Foundation open-sequent transport | Section 15 | Open integration plan | `BridgeBlueprint.lean` |

## Barriers retained

| ID | Barrier |
|---|---|
| X1 | no total primitive-recursive universal evaluator for all PR functions |
| X2 | horizonwise finite paths do not yield a primitive-recursive infinite path |
| X3 | coherent paths do not yield a convergence modulus in general |
| X4 | finiteness/cardinality does not yield a height cutoff |
| X5 | represented nonzero does not yield positive apartness |
| X6 | exact labels at collisions require separation or quotient reformulation |
