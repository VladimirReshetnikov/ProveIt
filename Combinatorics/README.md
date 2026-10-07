# Combinatorics

Formal enumeration of expression trees and their distinct semantic values,
and exact growth-rate bounds for square-lattice polyominoes.

- [`Polyominoes/KlarnerConstant/`](Polyominoes/KlarnerConstant/) contains the
  exact rational certificate improving the upper bound for Klarner's
  polyomino growth constant from `4.5238` to `4.5235`, its finite recurrence
  proof, square-lattice geometry, and independent Python/Wolfram audits.  A
  computer-assisted, unformalized improvement to `4.498` is a report in the
  research-report collection
  ([`polyomino-growth-finite-prefix-corrections`](../SetTheory/Cardinals/docs/reports/enumerative-combinatorics/polyomino-growth-finite-prefix-corrections/README.md)).

- [`ExpressionEnumeration/PowerTowers/`](ExpressionEnumeration/PowerTowers/)
  contains the common parenthesization semantics and A000081, A002845,
  A198683, and A199812.
- [`ExpressionEnumeration/RadicalExpressions/A158415/`](ExpressionEnumeration/RadicalExpressions/A158415/)
  contains the radical-expression semantics, exact certificates through size
  15, their Wolfram generator, and proof-engineering reports.

- [`Ramsey/`](Ramsey/) contains Lean formalizations of papers on
  3AP-free permutations and Ramsey-type counting (Davis–Entringer–Graham–Simmons
  1977, LeSaulnier–Vijay 2010 and 2011, Sharma 2012, Gowers–Szemerédi), with
  the source papers.  The research-report collection's
  [`a003407-dyadic-scaling-rigidity`](../SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a003407-dyadic-scaling-rigidity/README.md)
  builds on its parity recurrences and Sharma's Theorem 2.8; its own
  theorems are not formalized.  Beside the Gowers–Szemerédi development,
  [`Ramsey/Research/GowersSzemeredi/local-quantitative-refinements`](Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md)
  is a research report built from fifty-nine external manuscripts of
  6 October 2026 (batches 115–125 of [`docs/incoming`](../docs/incoming/README.md);
  sources 01–39 written in so far, 40–59 placed): sharper local estimates
  for density transfer and phase-flat partitions, the inverse step, cube
  and progression counts and the Proposition 17.7 phase extraction, each
  compared with the corrected statements of the Lean catalogue and its
  ledger `gowers-proof-status.json`.  Some sources give written proofs of
  catalogue statements that were open when they arrived, and
  `FORMALIZATION_STATUS.txt` points at them; the report itself is not
  formalized and gains no formal status from its placement.

The A198683 research corpus is preserved under
`PowerTowers/Research/A198683`; its wave-5 ledger is the authoritative account
of proved, conditional, data-certified, and heuristic claims about `a(12)`.

Coq parity is intentionally explicit: A002845 currently reaches `n=17`
versus Lean's `n=18`; A158415's Coq surface checks the finite headline table
without replaying the full real-radical ordering proof; A199812's Coq port
checks the ordinal-note recurrence without the Lean ordinal-semantic bridge.
