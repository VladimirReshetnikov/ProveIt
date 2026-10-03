# Research and verification status

## Repository baseline

Repository: VladimirReshetnikov/ProveIt.
Pinned commit: 781594d886f8dc56069221e2b56bd1e94d9c6e5f.
Inspected on: 2026-09-30.
Relevant report: `dfao-reversal-coloring-obstruction`, under the
Cardinals research collection's automata-and-formal-languages category.
Its pinned README blob is ac535a941bbc600f5875ab31bd7996b303d042e5.

The inspected Part III proves an exact closest-coprime formula past an
explicit N(k) <= 3 k^4, with additional exact small-k and finite-range
results. Part IV improves the four-output analysis. Those results are
not claimed as new here. The present advance is the O(k log k) sufficient
threshold and joint-limit consequences made accessible by that threshold.

## External result actually used

Sylvie Davies, “State Complexity of Reversals of Deterministic Finite
Automata with Output,” arXiv:1705.07150v2, 17 October 2017.
Theorem 3 and Corollary 3 supply accessible two-generated witnesses for
4 <= k < n and coprime cycle lengths 1 < a < b. Their proof rests on a
two-generation theorem for the U_(a,b) monoid. The article imports this
existence theorem; it does not claim to re-prove that monoid-generation
result. Original-state minimality is checked separately in the article.

The primary PDF's theorem statements, witness argument, and page-17 open
problem were read. Focused public searches did not establish an exhaustive
bibliography or a priority claim. Absence of a search hit is not evidence
that no related result exists.

## Mathematical audit

The positive allowed-palette envelope is NOT the exact chromatic count.
Its lower comparison uses only disjoint all-used palette families.
Since palettes can have k-1 colors, the saturation exponent is bounded
using 2k, not k. The final definition S=ceil(1+2k log(8k)) includes that
worst-case denominator, and the asymptotic leading threshold constant is 4.

The paired construction counts 2^R orientations of occupied pairs, not
2^h orientations of all pairs. This avoids overcounting unused pairs.
The entire permutation order is bounded, including residual cycles.
Every nonfull collision case is separated by a positive explicit margin;
full cases are optimized by strict biclique balancing.

The theta proof uses summable Gaussian domination. The broad-palette law
uses a separate Riemann-sum proof with controlled tails; no unjustified
interchange of the theta and small-parameter limits is used.

Rigidity is necessary and includes orbit saturation. The cycle lengths,
unique double fiber, and full-period output alone are not asserted sufficient.

## What was executed

`python code/verify.py --full` passed:

- 1,440 exact two-formula counting comparisons;
- 30 literal small coloring enumerations;
- 550 exact strict-balancing comparisons;
- 1,440 exact occupancy-subfamily comparisons;
- 477 structural rows containing 167,095 strict integer comparisons;
- the distinguished candidate equalities and original-minimality tests;
- 1,296 numerical occupancy inequalities;
- 90 numerical imbalance and 90 numerical saturation checks;
- numerical threshold comparisons for 4 <= k <= 1000;
- 18 theta-limit numerical diagnostics.

These are regression tests, not independent formal certification. The
structural code uses the mathematical reduction proved in the article.
High-precision Decimal diagnostics are not validated interval arithmetic.
All infinite claims are based on the written mathematical proofs, not the
finite computational ranges.

The LaTeX was compiled successfully. Rendered pages were inspected for
layout, including the title, contents, proof pages, tables, and references.
The delivered build has no overfull boxes or unresolved references.

## Claims not made

No claim of independent peer review, Lean verification, exhaustive novelty
review, a best possible threshold constant, exactness in the full dense
regime k proportional to n, or resolution of the k=n monoid problem.
No repository files were modified.
