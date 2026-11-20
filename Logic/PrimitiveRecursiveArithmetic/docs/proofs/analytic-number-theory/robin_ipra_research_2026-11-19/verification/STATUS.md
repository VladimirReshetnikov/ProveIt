# Verification status

## Executed here

- RobinCertificateLogic.lean compiled using Lean 4.32.0.
- All eight printed axiom dependencies are empty.
- Exact certificates generated for 2 <= n <= 100000.
- Full certificate replay recomputed every interval and every divisor sum.
- A separate exact-rational reference audit checked elementary interval
  arithmetic and independently recomputed all divisor sums using prime
  factorizations; all checks passed.
- LaTeX report compiled with resolved references; PDF layout inspected.

## Human mathematical proofs

- Elementary rational interval and tail estimates.
- Euler-constant nested enclosure.
- Robin inequalities for integers with at most three distinct prime factors
  above the specified cutoff.
- Elementary Chebyshev bound and the finite LCM excursion transfer.
- Conditional quantitative forward separation.
- Conditional Herbrand/negative-translation transfer from classical PRA.

These have not been turned into values of ProveIt's object-theory proof type.

## Uncompleted

- Concrete implementation and internal proof of the eta/winding zero checker.
- Analytic adequacy of that checker in the required formal setting.
- Weighted explicit formula and sharp RH-dependent estimates in iPRA.
- Nicolas--Landau converse in iPRA.
- Full finite startup certificate port and soundness in iPRA.
- Full Robin equivalence as an object-iPRA derivation.

## External source claims

ProveIt source and its own status records were inspected at a pinned commit;
its complete build was not rerun.

The classical kimihiro64/Robin1984 Lean project was inspected as source,
including its companion mathematical paper. Its compiler toolchain and full
kernel/independent-kernel audits were not rerun. Its advertised classical
theorem is not counted as a checked iPRA theorem in this archive.
