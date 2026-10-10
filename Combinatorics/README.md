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
  is a research report built from one hundred and seven external manuscripts
  of 6 to 8 October 2026 (batches 115–138 of [`docs/incoming`](../docs/incoming/README.md),
  all written in): sharper local estimates
  for density transfer and phase-flat partitions, the inverse step, cube
  and progression counts and the Proposition 17.7 phase extraction, each
  compared with the corrected statements of the Lean catalogue and its
  ledger `gowers-proof-status.json`.  Some sources give written proofs of
  catalogue statements that were open when they arrived, and
  `FORMALIZATION_STATUS.txt` points at them; the report itself is not
  formalized and gains no formal status from its placement.  Three more
  research reports sit under `Ramsey/Research/`, placed on 7 October 2026
  from manuscripts that arrived with the Gowers batches but do not concern
  Gowers's argument, with their delivered layout and their writes pending:
  [`VanDerWaerden/superexponential-lower-bounds`](Ramsey/Research/VanDerWaerden/superexponential-lower-bounds/)
  (superexponential lower bounds for two-colour van der Waerden numbers by
  robust colourings),
  [`SquareDifferences/spectral-list-mixing`](Ramsey/Research/SquareDifferences/spectral-list-mixing/)
  (two merged manuscripts sharpening the finite mixing layer of an external
  construction for square-difference-free sets) and
  [`QuasipolynomialProgressions/sparse-grid-moments`](Ramsey/Research/QuasipolynomialProgressions/sparse-grid-moments/)
  (exact relation codes and quadratic closure for grid moments of sampled
  polynomial values).  Each refines an external openai/math release, with
  attribution; none continues the Lean development, and none is formalized.

- [`BooleanFunctions/`](BooleanFunctions/), [`Sidorenko/`](Sidorenko/) and
  [`OrderedMatrices/`](OrderedMatrices/), opened on 7 October 2026, hold
  research reports only, placed from [`docs/incoming`](../docs/incoming/README.md)
  with their delivered layout and no article write yet:
  [`BooleanFunctions/Research/square-root-degree-bound`](BooleanFunctions/Research/square-root-degree-bound/README.md)
  (cell Fourier degree against retained variance on the Boolean cube, from
  four manuscripts; the fourth, of batch 138, re-derives the first without
  citing it and supersedes nothing) and
  [`BooleanFunctions/Research/sensitivity-block-sensitivity`](BooleanFunctions/Research/sensitivity-block-sensitivity/README.md)
  (an explicit exponent above 65/32 for block against ordinary sensitivity;
  its batch-138 Part II, a threshold-resolved amplification, reaches only
  `3667/1809`), each with a README of dated reconciliation notes
  (`eb8dee994`) pending the write;
  `Sidorenko/Research/local-fourier-sign-codes`,
  `Sidorenko/Research/polar-discriminant-mixing` and
  `Sidorenko/Research/sharp-incidence-stability`, three refinements of one
  external Sidorenko preprint that share no theorem, and
  `Sidorenko/Research/four-cycle-quasirandomness` (batch 138, placed without
  a write: the sharp set-cut discrepancy of kernels with small four-cycle
  excess; it uses no Sidorenko theorem and is filed here by provenance); and
  `OrderedMatrices/Research/ordered-matrix-removal` (a 5 × 5 pattern for
  which polynomial ordered matrix removal fails, under a nested Apache-2.0
  licence).  Each builds on an external openai/math release, with
  attribution; none is formalized.

The A198683 research corpus is preserved under
`PowerTowers/Research/A198683`; its wave-5 ledger is the authoritative account
of proved, conditional, data-certified, and heuristic claims about `a(12)`.

Coq parity is intentionally explicit: A002845 currently reaches `n=17`
versus Lean's `n=18`; A158415's Coq surface checks the finite headline table
without replaying the full real-radical ordering proof; A199812's Coq port
checks the ordinal-note recurrence without the Lean ordinal-semantic bridge.
