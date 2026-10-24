# Literal profiles for the paired-index guard replacement

This research measures the actual quadratic systems licensed by the
separately sealed ordinary proof in `research/paired-index-guards`.
It preserves the full original1259-coordinate/1177-row raw source, or
its exact667-coordinate/585-row affine contraction. Every original body
coefficient and variable metadata record is held fixed. No existing
candidate, page, source theorem or Lean file is changed.

The domain has75 retained scalar guards plus two new predicates:

    raw656-1 >= 0,
    raw674*raw861 >= 0.

The old scalar guards on raw674, raw861 and raw1214 are omitted.
Each nonnegative integer expression E is imposed by the quadratic row
E-a²-b²-c(c+1)=0 with three fresh unrestricted integer coordinates.
For an integer E this is equivalent to E>=0. The ordinary local proof
first uses raw656>=1 to recover all nonzero Pell ordinates and raw1214,
then interprets only calls1,5,6, proves factorial0=K!, and uses parity
and the product to recover both original index-slack signs pointwise.
Thus these new parent systems have the same zero-existence as the
accepted78-guard systems. This depends on that proof; it is not inferred
from a finite computation or from having77 rather than78 predicates.

The `direct` realization uses the actual quadratic product in its guard
row. The `wire` realization first adds a fresh integer p and the row
p-raw674*raw861=0, then guards p. Both use raw656-1 directly, without
an additional subtraction wire. All75 retained scalar guards remain in
their original relative order, followed by the two new predicates.
Auxiliary metadata and insertion order are fixed by the producer.

## 1. Actual direct-product profiles

Every row count below includes all quadratic source/guard residuals.
The displayed terms and heights refer to the complete collected sum of
squares, whose exact degree is4 in every case.

| Baseline | Profile | Integer variables | Quadratic rows | Quartic terms | Height |
|---|---|---:|---:|---:|---:|
| Compact | unprojected | 898 | 662 | 4727 | 63905863 |
| Compact | support4 | 639 | 403 | 5605 | 63905891 |
| Compact | support8 | 613 | 377 | 8622 | 2445790974704 |
| Compact | support16 | 611 | 375 | 8717 | 2445790974704 |
| Compact | support32 | 610 | 374 | 10053 | 2445790974704 |
| Raw | retained | 1490 | 1254 | 4972 | 428 |
| Raw | support2_affine1 | 843 | 607 | 3804 | 4750 |
| Raw | support2_affine2 | 698 | 462 | 5564 | 737653 |
| Raw | support4_affine2 | 636 | 400 | 8897 | 737653 |
| Raw | support8_affine2 | 622 | 386 | 8861 | 938261 |

The compact projected profiles save three variables and one row against
their matched78-guard profiles, at unchanged heights, while adding40
quartic monomials. The raw support2 profiles also save three variables.
At support4/support8 with affine support2, the nonlinear paired guard
blocks two former eliminations: the net saving is only one variable,
and there is one more surviving row. Therefore projected coordinate
counts cannot be inferred by multiplying a guard saving by three.

The unprojected retained height is428, rather than the old427: shifting
the actual V guard by1 changes the collected coefficients. Projected
heights in the table are unchanged from the matched old profiles.
These are measured profiles of the stated optimizer settings, without
a global minimum or Pareto completeness assertion.

## 2. Product-wire comparison and exact integer maps

Before projection, the product wire adds exactly one integer coordinate,
one quadratic row and two quartic monomials, with the same height.
At every nonzero support setting listed above, the optimizer removes
that wire. The matching direct/wire projected coordinate metadata and
collected polynomials are identical; this comparison is checked exactly.
Their complete residual lists agree up to row order and signs. In the
compact family the negative product-guard row survives under the earlier
product-definition label, whereas the raw family has literally identical
residual lists. The output `variant` metadata and input/projection hashes
also distinguish their two construction histories.

The independent checker first verifies every parent guard polynomial,
all original body rows and every auxiliary position. It then checks the
following unbounded integer identities, before applying any sign proof:

* The raw/direct and compact/direct parents are in a literal zero
  bijection using all592 original affine integer restoration recipes
  and the same77 guard triples.
* The same592-coordinate bijection holds for the product-wire parents.
* Each wire parent is in a zero bijection with its direct parent by
  deleting the one monic defining row and restoring its exact product.
  No fresh sign witness or assumption is used in these maps.
* Every emitted monic projection is verified over unrestricted integers,
  including every substitution, deleted defining row, surviving guard
  row and retained coordinate. There is no unconstrained deletion.

The projections restore the entire new77-predicate parent first. Only
then is the sealed paired-index proof used to choose the three removed
old guard triples into the accepted78-guard source. The accepted signed
comparison-base lift and subsequent pointwise sign-recovery theorem
remain the separate downstream source equivalences. There is no claim
that all original raw values are natural at an arbitrary new integer
zero, nor that the q4 value remains fixed through its comparison lift.

## 3. Reproduction and scope

`SOURCE_PINS.json` pins all actual inputs and the whole immutable407/888
archive. The producer reads only its independently reviewed terminal
elimination module. The checker never imports that optimizer; it uses
the separately authored projection verifier plus an independent complete
sum-of-squares collector. Every emitted equation, projection certificate
and full sparse polynomial is retained, including both wire histories.
`CENSUS.json` is the machine-readable count record.

```sh
python3 -B Computability/DiophantineConsistency/research/paired-index-guard-profile/build.py --check
python3 -B Computability/DiophantineConsistency/research/paired-index-guard-profile/check.py --output /tmp/paired-profile-normal.json
python3 -B -O Computability/DiophantineConsistency/research/paired-index-guard-profile/build.py --check
python3 -B -O Computability/DiophantineConsistency/research/paired-index-guard-profile/check.py --output /tmp/paired-profile-optimized.json
```

Finite arbitrary-signed restoration fixtures and corrupted inverse,
guard and quartic controls accompany the full symbolic checks. Their
role is diagnostic; the monic substitution certificates establish the
unbounded integer bijections. These are ordinary source/projection
research artifacts. Native refutation calibration and an internal-ZFC
equivalence are not newly discharged, and Lean remains paused.
