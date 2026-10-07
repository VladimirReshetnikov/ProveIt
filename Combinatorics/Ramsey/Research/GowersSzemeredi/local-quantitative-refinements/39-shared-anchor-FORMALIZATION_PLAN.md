# Formalization and integration plan

This is a proposed implementation sequence, not a report of a successful Lean
build. The mathematical proofs are in `article.tex`. No new Lean file,
unchecked axiom, or `sorry` skeleton is included.

## 1. Integrate the finite sampler before the optimality theory

The useful local improvement does not require Poisson limits, calculus,
minimax symmetrization, or the quadratic cap. The first milestone should be
an unnormalized finite counting theorem followed by the existing
`Section16SampledOrAnchoredOn` interface.

### Basic objects

Use finite types for rows and columns, with `J` a nonempty finite column set.
Each row has a finite indexed family of pairwise-disjoint subsets of `J`.
The union may be a proper subset of `J`. For a sample set `R` of cardinality
`r`, define discarded targets in a class `C` by:

- they are in `C \ R`;
- the intersection `C ∩ R` has cardinality strictly less than `t`.

Keep the threshold convention literal: reconstruction requires at least `t`
**distinct** sampled columns. A sampled point survives even when its class
contains fewer than `t` sampled columns.

### Proposed counting declaration

`sharedAnchor_doubleCount` should count pairs `(R,x)` with
`card R = r`, `x ∈ C \ R`, and `card (C ∩ R) < t`.

The bijection is `(R,x) ↦ (R ∪ {x},x)`. The inverse removes `x`.
The target pairs have `card T = r+1`, `x ∈ T ∩ C`, and
`1 <= card (T ∩ C) <= t`.

Prove this first over natural-number cardinalities. The exact integer identity
is stronger and simpler to audit than an initial statement involving a
probability measure. The `r=m` endpoint must be handled separately, since
there are no `(r+1)`-subsets in that case.

### Averaging declaration

`exists_sharedAnchorSet_mass` should sum over the row classes and then average
over all `r`-subsets of `J`. Bound the target-pair contribution from any
`(r+1)`-subset by `t`. After normalizing, the result is

`t*q*(m-r)/(m*(r+1))`.

An initial unweighted fixed-`q` version suffices for the source application.
The weighted and variable-row-class-count versions can be separate lemmas.
Handle empty row sets before dividing by their size. The target sampling
budget is `min(m, ceil(2*q/eta))` in the affine case.

## 2. Produce the existing sampled-or-anchored predicate

The inspected definition in `Proofs16ShortColumns.lean` has an inner anchored
set `K` contained in a larger good set `F`. It requires that every retained
domain point be either in `K` or directly sampled. The anchors for points in
`K` must also lie in `K`.

Construction:

1. Partition each vertically covered fibre by assigning a point to its first
   covering affine graph.
2. Select the shared subset `R` using the new mass theorem.
3. Let `K` be the union of **whole** classes having at least two sampled
   members. Every anchor selected from such a class lies in `K`.
4. Let `F` be the ambient product with uncertified domain points removed.
   It includes `K`, every directly sampled domain point, and points outside
   the partial domain.
5. Enumerate `R` injectively as `Fin r → J` and then into the field.
6. Apply the existing two-anchor affine interpolation identity.

Suggested new interface name: `section16_subset_recovered_good_set`.
This should not redefine or weaken `Section16SampledOrAnchoredOn`.
It should accept arbitrary column lengths, with `r=m` covering the short case.

After this milestone, the existing recovered and synchronized cover theorems
can consume the smaller sample parameter without changing their candidate
index type or their geometric assumptions.

## 3. Preserve individual horizontal slice labels

A second milestone is a labelled common refinement. The state of the
induction must retain, for every sampled slice, its individual candidate
family on each current cell. Refining for a later slice restricts the earlier
families but does not take a Cartesian product of their indices.

Required hypotheses:

- admissible cells are closed under the supplied refinement operation;
- the scale lower bound is valid on every parent encountered;
- candidate spaces are closed under restriction;
- the single-slice exceptional mass bound is measured relative to the parent;
- the parent cells partition the full base, so new error costs add correctly.

At errors `epsilon/r`, each slice list should retain bound
`L = Q(epsilon/(r*b), gamma, k)^b` while the scale exponent is
`c(epsilon/(r*b), gamma, k)^(r*b)`.

Proposed theorem name: `labelled_common_slice_cover`.
No claim is made that this declaration already exists or has been compiled.

### Candidate indexing

For affine fibres, use a disjoint union of:

- a sampled anchor and one list index;
- an unordered two-element subset of anchors, with one list index at each
  member.

The count is `r*L + choose(r,2)*L^2`. With unequal list sizes the dependent
index count is `sum L_a + sum_{a<b} L_a*L_b`.

The values need not be consistent across all anchors simultaneously. For one
retained target, choose correct list branches at its two certifying anchors.
This distinction is central to avoiding a product of all slice-list sizes.

## 4. Do not bypass the geometric synchronization hypotheses

`Proofs16SynchronizedCover.lean` already transports a cover through the
compatible tiling step without adding candidates. To reuse it with the
labelled cover, carry the same parent-axis containment, properness, unit-step,
shortness, and width hypotheses.

In particular, a base cell times the original final progression is not
silently a common-step box. The lower width condition involving `v^2+1`
must still be proved. If the labelled common refinement does not preserve
an input needed by the short-parent construction, that input requires a
separate lemma, not an assumption omitted from the result.

## 5. Optional extremal formalization

These results certify sharpness and exact finite computation, but are not
needed to integrate the initial sampling improvement.

- `sharedAnchor_minimax_profile`: symmetric group action on a fixed disjoint
  profile. Every fixed `r`-subset has the same average row loss.
- `sharedAnchor_loss_firstDifference`: distinguished-column coupling.
- `sharedAnchor_loss_secondDifference`: two successive couplings and the
  exact curvature formula.
- `sharedAnchor_loss_initialConcavity`: the sign change of
  `(r+1)*(s+2) - (t+1)*(m+1)` and the final nonpositive first difference.
- `sharedAnchor_balanced_profile`: clip at the first mode, fill the available
  budget, and transfer units from larger to smaller classes.
- `sharedAnchor_affine_firstMode`: quadratic sign computation and the exact
  ceiling characterization. Use integer square root only for executable
  evaluation; the mathematical statement can be about the real root.

The existing Python dynamic program should remain as an independent test
oracle for the closed formula. It is not a proof assistant certificate unless
its arithmetic and logical assertions are imported through a verified route.

## 6. Analytic formalization can be separate

The uniform Poisson limit needs:

- the elementary symmetric mean product bound;
- a uniform hypergeometric lower-tail estimate;
- compact-parameter probability limits using falling factorial ratios;
- a tail/compact decomposition of the uniform error;
- the exact continuous capped-and-balanced optimization.

A pointwise Poisson limit is insufficient for the minimax statement. The
uniformity lemma and the rounding argument must be formalized explicitly.
The sharp sample-budget corollary then follows by a monotone sandwich.

## 7. The global numerical gap stays separate

Do not replace the source's desired closing bound with an unchecked axiom.
The inspected closing-comparison file exhibits a wrong-direction inequality
and an endpoint obstruction. The new results furnish local output parameters;
they do not prove domination by the old global controls. A revised recurrence
must be stated and proved separately before changing the status of Lemma16.10
or any theorem downstream from that gap.

## Evidence in this package

The two JSON certificates contain 11,212 exact finite test cases. They are
regression evidence for the formulas and algorithms, not Lean kernel output.
A completed integration needs its own pinned Lean/mathlib version, build
commands, actual build output, and dependency audit.
