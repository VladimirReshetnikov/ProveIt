# Proof-audit notes

The manuscript's main dependencies are:

1. Never-yet-leading tokens remain in original order. A nonleader position
   never increases. After its first throw, a token stays within its own weight.
2. The waiting-or-barrier induction either makes a token at position p lead
   within 2^p-1 steps or finds a closed front strictly before that token.
3. Before the first visit to label j, every token before it has label < j.
   Admissibility of that earlier prefix rules out the barrier alternative.
4. At the first visit to J in the first bad prefix, the m earlier low tokens
   and token J occupy all m+1 positions at most m. They are already a closed
   core at that state. Minimality of m rules out a proper closed subfront.
5. Sparse backward parking fails exactly at an inadmissible prefix. At a failure,
   the first unoccupied slot beyond the failed deadline bounds the finite
   closure scan that finds the *least* overloaded threshold.
6. The bounded configuration inverse is forced by the least-weight token
   currently at its own throw position. If there is none, the predecessor
   is the unique wildcard move. This proves a permutation, not just a map.
7. The minimum token is a periodic clock. Deleting it and its times subtracts
   one from every other throw length. The exact divisibility condition after
   restoring that clock proves the least period, not merely a period bound.
8. In a critical reverse stride path, a rise from a to a+1 changes the period
   by exactly (a+1)/a because the current period is a multiple of a. Unit-rise
   runs telescope, proving the sharp extremal bound.
9. Density normalization is obtained from finite telescoping. It equals one
   exactly when the reciprocal-stride series diverges.

## Executed cross-checks

- The parking certificate is checked using independent sorting inequalities.
- Predicted cores are compared with actually recurrent labeled tokens from
  explicit finite queue simulations.
- Every bounded inverse is checked on every enumerated state; actual complete
  cycle decompositions are compared with periods and frequencies.
- The extremal formula is checked against every critical stride profile up to
  size 13, not just against the proposed attaining family.
- The finite-horizon truncation logic is checked against sufficiently long
  genuinely closed queues.

## Not claimed

No independent referee has checked the manuscript. No Lean formalization is
provided. No all-size sharp formula for transient length or full classification
of numerical quotient cycles is claimed. No mathematical conclusion relies on
a failed literature search alone.
