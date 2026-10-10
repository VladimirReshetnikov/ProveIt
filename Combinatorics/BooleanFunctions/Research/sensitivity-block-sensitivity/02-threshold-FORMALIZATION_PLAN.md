# Formalization plan (not an executed formal proof)

A useful next artifact would be a Lean development that separates finite combinatorics from the large arithmetic certificate. No `.lean` file is included as if it had already been verified.

1. Define nested finite predicate families on a finite cube, single sensitivity, and simultaneous endpoint sensitivity. Prove interval containment directly from event-set inclusion.
2. Define labelled tournaments and coherent subsets. Formalize the probabilistic existence bound, or equivalently a counting inequality over all label assignments.
3. Model candidate clauses by their lists of distinct child conditions. Prove a raw-bit reversal can change at most one condition in a fixed clause.
4. Formalize the target/gate classification and all four assertions of the candidate-list packing lemma. Pay particular attention to which gate candidate can be adjoined to the coherent target set in the two-gate case.
5. Derive all four threshold-resolved inequalities. The joint zero-to-one case should retain the stronger endpoint `Q` for nonsink gate repairs.
6. Define the integer recurrence as a recursive function and prove its soundness by induction on depth and interval length. Avoid asserting that the computed bounds equal true sensitivities.
7. Prove minimum-weight multiplication under zero-preserving composition and exact block packing from a partition into minimum-weight accepting supports.
8. Evaluate or verify the final integer certificate inside the trusted proof kernel. The short binary comparisons avoid formalizing numerical logarithms.

The source repository has a formalization catalogue, but this package neither imports an uninspected Lean result nor claims a checked dependency on one. A formalization should pin a toolchain, source dependencies, and the exact theorem statement and should distinguish kernel-checked evaluation from untrusted external certificate generation.
