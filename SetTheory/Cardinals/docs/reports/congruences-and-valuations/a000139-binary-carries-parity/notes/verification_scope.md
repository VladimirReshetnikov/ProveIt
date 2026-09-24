# Verification scope and proof-audit notes

## Executed finite checks

The complete original reports are in `data/verification.json` and
`data/symbolic_verification.json`. All checks passed.

- Direct exact factorial quotients for 0 <= n <= 2000 were compared with
  popcount valuations, explicit column carries, the six-state automaton,
  and the parity predicate.
- All n below 2^20 were checked for the digit-formula/parity agreement;
  the dyadic histograms were compared with the order-three recurrence.
- Explicit carry propagation and the automaton were independently compared
  with digit sums for all n below 2^18.
- Every bound 0 <= N <= 2048 was checked by comparing the digit-DP histogram
  against enumeration.
- For every 0 <= m <= 256, the digit DP and recurrence were compared,
  together with exact rational moment formulas and extremal/Fibonacci counts.
- Least positive indices for 0 <= r <= 18 were established computationally
  by exhaustive search within the enumerated interval.
- Formula witnesses for 3 <= r <= 1000 were checked for their valuation;
  this did NOT exhaust the smaller indices at these large valuations.
- The full histogram below 10^100 was computed and its sum checked exactly.
- Exact symbolic rational identities were checked with SymPy 1.14.0,
  including fixed-level expressions for r=0,...,12 and eigenvalue/cumulant
  expansions through degree four.

The million-index test is not a million-factorial computation. The
non-dyadic large-bound total check is not an independent exhaustive check of
every histogram entry. The theoretical proofs justify these extensions.

## Boundary conditions audited

1. a(0)=2 and v(0)=1. Empty words carry terminal weight y.
2. Carry propagation includes a final outgoing carry beyond the leading bit.
3. The correction -v2(n+1) is not dropped when passing from the binomial
   coefficient to the factorial quotient.
4. The carry core alone counts c(n), not v(n). Three prefix states account
   for trailing ones in the full automaton.
5. Appending leading zeros preserves the terminally evaluated valuation.
6. Bounds are exclusive, and the digit DP retains comparison state -1.
7. The dyadic recurrence begins at m=4, because the numerator has degree
   three. Four initial polynomials are specified.
8. The m=0 variance is handled separately; its second factorial-moment
   series has an isolated constant correction.
9. The dyadic maximum theorem begins at m=3. Least indices are positive,
   so valuation one first occurs at index two rather than index zero.
10. Fixed-valuation asymptotics are not claimed uniformly for r growing
    with m. The local Gaussian theorem is not a relative tail estimate.
11. The local limit argument includes a strict spectral gap away from the
    trivial unit-circle point; a central limit theorem alone is not used
    as a substitute for this condition.
12. The small printed coefficient table was cross-checked against the
    generated data, including its row sums.

## Not performed

No Lean or other proof-assistant formalization; no independent peer review;
no exhaustive literature/priority certification; no empirical numerical
experiment treated as a proof of an asymptotic statement.
