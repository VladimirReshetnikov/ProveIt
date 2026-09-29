# Claims and validation boundaries

## Proposed research contributions with complete written proofs

1. **Arbitrary finite binary profiles (Theorem 2.1).** For every m >= 2 and every
   nonempty finite list of values from {2,...,m}, the construction gives
   A = {a^m} and a finite binary target B. Its full shuffle is an entire
   fixed-letter-count class. Exactly the designated outputs have the prescribed
   degrees, and every other output has degree 1. Each designated output has a
   unique target word in B; uniqueness of its position mask is NOT claimed.

2. **Fixed-binary classification (Corollary 2.2).** Every finite positive-integer
   set containing 1 is attainable. A nontrivial spectrum requires at least two
   alphabet symbols, and one inserted word is the smallest nonempty source.
   No optimality of target-language cardinality is claimed.

3. **Sharp length (Theorem 2.3).** With A = {a^m}, full coverage of a binary
   fixed-letter-count class, and exactly one output above degree 1 whose degree
   is m >= 3, output length is at least m^2. Equality is attained for every
   m >= 6. This minimizes over all target languages in that class, not only the
   explicit construction, but it is NOT a general lower bound without the
   full-coverage hypothesis. Exact optimal lengths for m = 3,4,5 are not claimed.

4. **Quantitative and structural extensions.** Exact target/output cardinalities,
   arbitrary higher-degree multiplicities, succinct membership, and the contrast
   between identical real-rooted singleton histograms and arbitrary aggregate
   gaps are proved. The degree-one multiplicity is not independently prescribed.

## Established facts not claimed as new

- The unary-source singleton no-gap theorem is Hughes's Theorem 9.
- The existing ProveIt report already gives arbitrary finite spectra over growing
  alphabets, a binary spectrum {1,2,4}, and representation erasure.
- The paper supplies its own proof of real-rootedness of a classical-type
  singleton polynomial, but does not assert priority for that fact.

## Computational checks

The receipt in data/verification.json is from an actual successful execution.
The 26 listed profiles are exhaustive over their output classes, including all
376,992 outputs at m = 6 and length 36. Costs are obtained from exhaustive
cost-ordered deficit search against the target definition, not by returning the
predicted profile. Stopping after an accepted cost-one candidate is exact.

The worked example is also checked independently using literal letter masks and
literal-word dynamic programming. These checks do not rely on gap vectors.
The direct target-membership definition is checked against the arithmetic
interval test on all 207,694 target candidates in the exhaustive profiles.

The large-parameter output tests are samples only (seed 20260928). Parameter
inequalities are checked for 316 (m,q) cases through m = 80. Infinite validity
comes from the written proofs, not those samples.

A regression guardrail rejects a tempting insufficient-total example with two
large gaps: at m = 6 and total 28, the output vector (5,5,5,5,4,4) cannot be a
one-piece insertion. The strict total-size hypothesis in the escape lemma is
therefore explicitly retained.

## Not established

No unrestricted both-singleton theorem, classification of infinite spectra,
minimum target-language size, optimal general automaton size, proof-assistant
checking, independent peer review, or exhaustive worldwide priority search is
claimed. No repository files were modified and no pull request was submitted.
