# Combinatorics

Formal enumeration of expression trees and their distinct semantic values,
and exact growth-rate bounds for square-lattice polyominoes.

- [`Polyominoes/KlarnerConstant/`](Polyominoes/KlarnerConstant/) contains the
  exact rational certificate improving the upper bound for Klarner's
  polyomino growth constant from `4.5238` to `4.5235`, its finite recurrence
  proof, square-lattice geometry, and independent Python/Wolfram audits.

- [`ExpressionEnumeration/PowerTowers/`](ExpressionEnumeration/PowerTowers/)
  contains the common parenthesization semantics and A000081, A002845,
  A198683, and A199812.
- [`ExpressionEnumeration/RadicalExpressions/A158415/`](ExpressionEnumeration/RadicalExpressions/A158415/)
  contains the radical-expression semantics, exact certificates through size
  15, their Wolfram generator, and proof-engineering reports.

The A198683 research corpus is preserved under
`PowerTowers/Research/A198683`; its wave-5 ledger is the authoritative account
of proved, conditional, data-certified, and heuristic claims about `a(12)`.

Coq parity is intentionally explicit: A002845 currently reaches `n=17`
versus Lean's `n=18`; A158415's Coq surface checks the finite headline table
without replaying the full real-radical ordering proof; A199812's Coq port
checks the ordinal-note recurrence without the Lean ordinal-semantic bridge.
