# Proof audit and verification status

This is the drafting audit for the accompanying manuscript, not an independent
referee report. No Lean proof or automatic verification of a Turing nonreducibility
is claimed.

## Main proof chains

### Core realization: compactness route

1. The columns `c_n(k) = 2^n(2k+1)-1` partition the natural numbers.
2. The tail at level s has exactly `floor(m/2^s)` positions below m.
3. A density-zero error restricts to density zero on each fixed column.
4. Repeated factorial blocks recover their encoded set from any error pattern of
   upper density strictly less than 1/2. Incorrect block majorities infinitely
   often would force error upper density at least 1/2.
5. Consequently each ideal level is below every description of the carrier.
6. Keeping finitely many layers yields a set in the ideal and error at most 2^-s.
7. Published HJKS Theorem 3.7 excludes every set outside the ideal from the core.

### Core realization: independent exact-pair route

1. Protect finitely many columns at stage s. The infinite protected pattern is
   computable from the single finite ideal level A_s.
2. The two finite extensions tested for cross-disagreement are independent.
3. If no such disagreement exists and both designated computations are total and
   equal, their common value can be found by searching admissible extensions using
   A_s. Totality guarantees termination; absence of a cross-disagreement guarantees
   correctness. No decision of totality is made.
4. Process all distinct pairs of leaves and all functional pairs bounded by the
   current binary-tree level. Every distinct pair of eventual paths is addressed
   for every relevant pair of indices.
5. A finite disagreement is preserved by all later extensions. In the other case,
   a common output is below some A_s and thus belongs to the ideal.
6. The protected regions increase to density one in the finite-head/tail sense;
   for each fixed s, all eventual errors outside a finite prefix are in its tail.
7. The family is perfect in both the Cantor topology and the prefix-density metric.
   The latter follows from an explicit modulus in the shared binary index prefix.
8. Existence of a cross-disagreement is c.e. in an oracle W computing the target.
   Hence W' builds the splitting system. The path bound is W' join Q, not W' alone.

This second chain uses no HJKS compactness input and no unproved hyperdegree
forcing fact from the repository.

### Dyadic insertion and fixed-core embeddings

1. A description of R(B) gives a pointwise convergent majority approximation to B.
   Conversely, a convergent approximation can be written down the dyadic columns.
2. The relativized limit lemma yields: D computes a description of R(B) iff B <= D'.
3. Finite joins of descriptions project and interleave correctly, including at odd
   prefix lengths. This gives the exact intersection formula for spectra.
4. Each finite dyadic truncation uses only finitely many bits of B and is therefore
   individually computable. Its program need not be obtainable uniformly from s.
5. Joining these truncations to carrier truncations keeps the approximants inside
   the same ideal, proving core preservation. Protected-region fusion supplies a
   second proof of the same assertion.
6. Monotonicity for uniform coarse reducibility uses bounded simulations of a
   fixed Turing reduction against pointwise approximations. All output bits are
   produced in finite time, including on early incorrect approximation stages.
7. To reflect order, a parameter C >= Z' is inverted to D >= Z with D' = C in degree.
   Such D computes the carrier and a description of R(C), so a reduction to the
   B-parameter construction forces B <= C. The required base-oracle bound is not
   omitted: Appendix A proves the relativized inversion statement explicitly.
8. Finite joins are preserved by concrete projections/interleavings and dyadic
   transformations. No distributivity of the Turing jump over joins is used.

## Quantifiers that were not interchanged

- For every n there is a reduction to A_n is not a uniform reduction to the
  infinite presentation join.
- For every s there is a computable finite truncation is not a computable sequence
  of truncation indices.
- No cross-disagreement implies a bound on a *common total output*; it does not
  imply that either partial functional becomes total.
- A W'-computable splitting system does not place uncountably many paths below W'.
- No least spectrum element does not imply no minimal spectrum element.
- A formula involving the carrier spectrum is not a complete classification of
  all spectra with the same core.
- The embedding domain is a Turing upper cone, not the entire degree structure.
- The Turing argument is not automatically a hyperarithmetic or effective-dense
  argument.

## Actual checks

The Python test run passed 616,836 finite cases in eight groups. The precise
ranges and counts are in `checks/results.json`. All inequalities use integers
or `fractions.Fraction`. A fixed seed is recorded for the sampled finite error
patterns; other groups exhaust the specified finite ranges.

The final LaTeX build completed without warnings, undefined references, missing
characters, or overfull/underfull boxes in its final log. The 22-page PDF was
rendered with MuPDF and visually inspected, including the title, contents,
construction and embedding sections, dependency table, questions, and references.
Those typesetting checks establish only artifact integrity.

## Novelty limits

The repository explicitly lists countable-core realization as unresolved at the
pinned snapshot. The exact all-ideal realization and general fixed-core upper-cone
embedding statements were not found in the specific primary sources examined.
This is a limited comparison, not an exhaustive literature search or a priority
certificate. Standard coding, spectrum bookkeeping, limit-lemma arguments, and
jump inversion are not presented as newly discovered mathematics.
