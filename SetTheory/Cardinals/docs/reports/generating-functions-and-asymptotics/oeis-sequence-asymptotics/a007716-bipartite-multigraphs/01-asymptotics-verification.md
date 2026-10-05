# Verification scope

The mathematical argument was checked separately for the exact invariant-partition count, all global and weighted tails, Bell saddle normalization, marked-cycle overlap factors, both positive cutoffs, the all-orders coefficient algorithm, inverse errors and recurrence obstruction.

The package includes three distinct exact counting checks:

1. `check_cycle_formula.py` uses a recurrence on selected nontrivial element cycles and a cycle-type Burnside sum. It checks 2,714 types through n=20 and reproduces the sequence there.
2. `check_invariant_partitions.py` directly enumerates fixed set partitions through n=8 and compares the cycle formula on 67 types, including its global bounds.
3. `check_independent.py` directly enumerates fixed partitions through n=10, checks the matrix-mass normalization by a separate rectangular inclusion-exclusion count, checks removal of a marked transposition, and verifies 38 exact Ewens factorial moments. It covers 139 types.

The two symbolic implementations are separate:

- `compute_first_two.py` enumerates the retained long-cycle and mark profiles and averages them by a polynomial Poisson-moment recurrence.
- `reconstruct_Q2.py` first reverts the Lambert-W shift implicitly, then sums seven compressed cycle/mark contributions. In particular its two-mark term retains overlaps explicitly. It averages via Stirling numbers of the second kind.

Both reconstruct Q1 and Q2 exactly and reject floating-point coefficients. The displayed Bell-core correction is checked by exact algebra. Every packaged script is replayed under Python optimization after clean archive extraction.

These checks do not replace the analytic proofs and do not establish an effective onset. No worldwide novelty determination, external referee approval or machine-checked formalization is claimed.
