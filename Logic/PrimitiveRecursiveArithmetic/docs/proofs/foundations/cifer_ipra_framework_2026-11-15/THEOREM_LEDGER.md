# CIFER theorem ledger

Status vocabulary:

- **Human-complete**: a full argument appears in the PDF.
- **Finite-tested**: exercised by the exact Python reference.
- **Lean source**: source/prototype supplied, not built here.
- **Formalization target**: exact endpoint and dependencies specified.
- **Residual/open**: theorem-specific producer intentionally remains explicit.

| ID | Claim | Status |
| --- | --- | --- |
| R1 | Backward marking computes exactly the dependency closure of a target in a finite topological graph. | Human-complete; finite-tested |
| R2 | Reachable primitive boundary leaves form the canonical dependency-normal residual. | Human-complete; finite-tested |
| R3 | Every graph node is derivable from its residual plus the permanent context. | Human-complete; Lean source |
| R4 | Embedded proofs of all residual formulas close the target by simultaneous cut. | Human-complete; Lean source |
| R5 | Replacing a boundary by a derived producer monotonically removes/substitutes residual obligations downstream. | Human-complete |
| B1 | Every fixed quantifier-free formula has a primitive-recursive Booleanizer with two-way reflection. | Human-complete; formalization target |
| B2 | Every fixed strictly bounded formula has a reflected finite Boolean fold. | Human-complete; formalization target |
| S1 | Least bounded search proves success, minimality, and failure. | Human-complete; finite-tested pattern |
| S2 | Bounded filtering produces a sound and complete increasing list. | Human-complete; formalization target |
| D1 | Capped inflationary demand iteration stabilizes within an explicit rank bound. | Human-complete; finite-tested; Lean definitions |
| D2 | Under monotonicity, the stabilized demand is the least prefixed point above the seed. | Human-complete |
| T1 | A fixed primitive-recursive trace with a QF invariant yields the invariant at arbitrary PR fuel. | Human-complete; Lean source |
| T2 | A terminal extractor may conclude an arbitrary formula. | Human-complete; Lean source |
| V1 | Backward viability is equivalent to a compatible finite path. | Human-complete; finite-tested; Lean definitions |
| V2 | A nonempty viable system has a lexicographically least finite path. | Human-complete; finite-tested |
| O1 | A stable finite observer eliminates internal witness choice. | Human-complete; finite-tested; Lean composition source |
| O2 | A diameter-bounded cloud determines an approximate branch-independent output. | Human-complete; finite-tested |
| O3 | A positive separation gap collapses an approximate cloud to one exact label. | Human-complete; formalization target |
| C1 | Changing finite horizons yield a Cauchy name under shrinking-diameter and motion-tail moduli. | Human-complete; formalization target |
| H1 | A positive height bound yields a complete finite list for a decidable coded predicate. | Human-complete |
| H2 | A complete finite list yields a height bound by finite maximum. | Human-complete |
| H3 | A cardinality bound alone is not a search cutoff or list producer. | Interface distinction established |
| A1 | Finite auxiliary exhaustion avoids a global selector. | Human-complete |
| E1 | Exact rational bisection preserves the bracket for `y^3 + y = x`. | Human-complete; finite-tested |
| E2 | Coarse primitive-recursive fuel gives dyadic interval width. | Human-complete; finite-tested |
| E3 | Nested midpoints form the unique represented cubic root. | Human-complete; formalization target |
| X1 | General effective Faltings/Siegel height producer. | Residual/open |
| X2 | General rational Mordell-Weil cover representatives. | Residual/open |
| X3 | Full effective constants for strong uniform prime-distribution estimates. | Residual/open |
| X4 | Exact selector through arbitrary collisions without a gap. | Deliberately not claimed; use relation/observable/gap |
