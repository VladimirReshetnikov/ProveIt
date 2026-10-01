# Proof audit

## Claim dependencies

- **Rank/clock formulas:** credited earlier ProveIt background, with self-contained proofs in Section 2.
- **Exact-length fragment criterion:** elementary concatenation/restriction of accepting runs; Section 3.
- **Periodic-interior equivalence:** Sections 4–5, using only finite-state eventual periodicity. No generic limitedness theorem is used.
- **Quadratic rank bound:** combines the structural theorem with the explicitly imported corrected unary progression theorem, normalized with two additional states.
- **PSPACE upper bound:** phase/subset reachability with polynomial-bit representations, plus Savitch's theorem. The upper bound could also use the elementary exponential cycle bound and does not logically depend on the quadratic improvement.
- **Binary PSPACE hardness:** imported all-initial/all-final NFA universality hardness, followed by the two-unary-loop construction and the newly proved factorial amplification argument.
- **Deterministic safe core:** statewise determinism is essential. The two-state universal NFA counterexample prohibits applying it to arbitrary nondeterministic states.
- **Logarithmic-order sharpness:** the finite one-1 language family. This proves a linear rank lower bound, not a quadratic one.

## Adversarial checks addressed

1. Empty language, empty length slices, and the empty word have explicit conventions.
2. Stable phase sets are used only when both distances to the ends are beyond their transients.
3. Every live phase has at least one allowed letter; this permits periodic padding.
4. A one-letter obstruction cannot exist. Each repeated obstruction therefore has a strict internal cut slot.
5. Repeated blocks have period-divisible lengths. The total-length residue and the obstruction's start phase remain fixed.
6. Prefix coordinates remain valid because only their long suffix distance changes; suffix coordinates are handled symmetrically.
7. Restricting one fragment's seed witness to an obstruction is enough; no common run is assumed across fragments.
8. Remainder padding upgrades a subsequence construction to every sufficiently large length of one residue.
9. In the binary hardness reduction, a missing factorial word x forces the missing mixed word x01; unary loops cannot produce a false universal positive instance.
10. In the delimiter comparison, shared separator letters do not mean shared internal boundary slots. The omitted empty-word case is explicitly included.
11. A large period does not enter the stabilizing rank bound; only transient boundary widths do.
12. DFA core deletion is polynomial in an expanded periodic system, not claimed polynomial in original DFA size.
13. The least complete-DFA decision complexity, optimal finite rank order, and exact growth slopes are not claimed solved.
14. The reference implementation uses explicit graphs and is not claimed to realize the polynomial-space bound.

## Executed checks

See `../data/verification.json` and `../data/verification.txt`. The standard-library suite passed. Rank calculations were compared against an independently enumerated seed-substring oracle on the stated finite ranges. Literal crossover generations were also checked separately. All exhaustive ranges, sampled ranges, and overlapping counts are distinguished.

No Lean or Rocq build was run. This is an author-side proof audit, not independent peer review.
