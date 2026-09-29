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
  theorems are not formalized.

The A198683 research corpus is preserved under
`PowerTowers/Research/A198683`; its wave-5 ledger is the authoritative account
of proved, conditional, data-certified, and heuristic claims about `a(12)`.

Coq parity is intentionally explicit: A002845 currently reaches `n=17`
versus Lean's `n=18`; A158415's Coq surface checks the finite headline table
without replaying the full real-radical ordering proof; A199812's Coq port
checks the ordinal-note recurrence without the Lean ordinal-semantic bridge.
