# Preparation-workflow proof audit

This is a self-audit of the manuscript and its finite checks, not a human peer
review, independent referee report, or proof-assistant verification.

## Critical proof points checked

**Energy normalization.** E counts ordered quadruples, and the natural-valued
ordered triple count equals (M_m-E)/4. The energy recurrence counts the cases
of one, two, and four occurrences of the last point separately. Repeated
summands in a Schur relation are allowed. The verifier checks both difference-
and sum-multiplicity definitions against the ordered triple formula.

**Consecutive zero defects.** Each zero gives a permutation by reflection of
an exact prefix. Their composition is a successor map by d=c_1. Finiteness
and the absence of any other terminal point give the full arithmetic chain;
no discreteness assumption about the original real set is used.

**The 3r+1 threshold.** The first non-arithmetic tail begins with a positive
local defect and has no two consecutive zero defects. Thus its length is
at most 2r. The initial arithmetic block has L >= n-2r > r points. A first
nonlattice point costs at least L. At a first target >= 2L+2, the preceding
post-block points have already cost at least their number s, while the target
costs at least L-s. Both arguments are contradictions to the total budget.
This is the essential infinite-family proof; finite enumeration is not used.

**Two-hole cancellation.** Before the forbidden large target, two holes cannot
sum to an existing point, so the local defect is exactly c_i/d-i. The family
[1,2r+2] minus {r+1} deliberately violates this condition and shows that a
size qualification cannot be dropped.

**Reflection of partitions.** The last gap sets the scale, and translation
sets the minimum. The boundary-hole parameter is a partition of the same
weight but need not be the identical shift partition. The paper does not
identify them without reflection bookkeeping. The hole maximum is at most r.

**Boundary constant.** The overlap R_H(h,x) is subtracted in kappa because it
is added back in the inclusion-exclusion triple count. The energy law needs
N >= 2 max H; the direct endpoint-weight count uses N > 2 max H. The actual
normal-form size hypothesis supplies the strict inequality.

**Envelope equality.** Every summand of kappa is at most max H <= r. If the
sum reaches r^2, then the largest hole is r and the preceding holes are
1,...,s-1. The pair (1,0) makes equality impossible whenever s >= 2. Hence
the unique maximizer is H={r}.

**Third equality cases.** The proof includes the two-sided-hole set
[0,m+1] minus {1,m}, in addition to the reflected pair of one-hole sets.
A third-level bound plus one construction would not establish completeness.
The proof treats arithmetic, second-level, and other prefixes separately.
The last case uses the full defect-two partition theorem, valid for n >= 7.

**Fourth equality cases.** The other-prefix case leaves endpoint budget at
most three. Its three defect-three templates have total defects 3n-9,
3n-7, 3n-6, all too large at n >= 10. The sufficient cutoff m >= 11 is kept
throughout. It is not replaced by a smaller experimental cutoff.

**Transfer.** Only the finitely generated torsion-free subgroup of the finite
set is embedded in R. A template's step is an actual difference of two image
points and therefore lifts. The cyclic lifting condition is q > 2L, not q > L.
For a graph, a nonzero first-coordinate direction is forced by the graph
property, yielding the asserted rational affine map.

## Computational and document checks

The actual default verifier run is recorded in data/verification.json and
.log. All arithmetic is exact. The implementation also checks the advertised
boundary-obstruction family, rather than testing only successful examples.
Conjecture diagnostics are reported separately and do not alter theorem bounds.

The article was compiled with pdfLaTeX. Rendered pages were inspected with
Poppler; full-page images and overview contact sheets were used. The table of
contents was moved to its own page, and bibliography spacing was adjusted.
The final build has no undefined references, missing citations, or overfull
boxes. Build and replay details are in data/build_validation.json.

## Remaining trust boundary

The written proofs are the justification for the general results. Exact finite
checks can expose mistakes in formulas or small cases but cannot establish
universality. Publication priority remains unestablished, and no formal
verification has been performed.
