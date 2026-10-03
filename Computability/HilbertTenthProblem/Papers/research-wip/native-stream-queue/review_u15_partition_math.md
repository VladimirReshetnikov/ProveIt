# Independent partition/finalizer degree census

**PASS.** For the seven labelled factors with exact degrees
`(12,78,332,726,898,834,65)` and retained residual square sum of exact degree 1936, the independently enumerated operation/degree frontier is:

| Operations | Exact degree | Groups | Finalizer | Number of optimal labelled forms |
|---:|---:|---:|---|---:|
|511|4881|1|Single anchor|1|
|513|3120|2|SOS|1|
|515|2116|3|SOS|8|
|517|1936|4|SOS|41|

The [census program](review_u15_partition_math.py) and [complete frontier receipt](review_u15_partition_math.json) are independent of the pending compiler/API implementation. This bounded review takes the seven exact factor degrees and retained-SOS degree as premises already established for the actual source; it does not repeat the native-source degree or universality proofs.

## Exhaustive scope and independent count

Restricted-growth strings enumerate each set partition exactly once. The numbers with 1 through 7 blocks are respectively
`1,63,301,350,140,21,1`, totaling 877. Every partition with g blocks has one SOS form and g choices of single anchor, giving 4,140 forms in total.

A second enumeration independently assigns each factor to an occupied labelled block, fixes factor 0's block label to 0, and divides the counts by `(g-1)!`. It reproduces the partition counts, minimum degrees and multiplicities of optimal forms for every group count. The minimum degrees for g=1 through 7 are
`4881,3120,2116,1936,1936,1936,1936`, with respective optimal-form multiplicities `1,1,8,41,50,14,1`.

The frontier is exact within this finite family: disjoint factor groups, no factors repeated or omitted, and either SOS or one anchored group. It does not assert optimality among arbitrary arithmetic circuits, multiple/nested anchors or other polynomial constructions.

## Why the degrees are exact

Work over the real polynomial ring after fixing a valid program slice. Each factor has its given positive exact degree and is nonzero. A nonempty group's product U therefore has exact degree equal to the sum of its factor degrees: polynomial rings over the reals have no zero divisors, so the product of nonzero highest homogeneous parts is nonzero. Since this degree is positive, subtracting 1 preserves it.

Let S be the retained SOS, with exact degree 1936, and let w_j be the group weights. The SOS finalizer is

```
S + sum_j (U_j-1)^2.
```

Its exact degree is `max(1936,2*max_j(w_j))`. At the maximal degree, the homogeneous part is a sum of real squares, at least one nonzero. Such a sum cannot vanish identically. Thus this formula is not merely a syntactic upper bound, even when several groups tie.

For anchor group a the polynomial is

```
U_a * (1 + S + sum_{j!=a}(U_j-1)^2) - 1.
```

The bracket has exact degree `max(1936,2*max_{j!=a}(w_j))`, taking the maximum over an empty group set as 0. The same SOS argument excludes cancellation in the bracket. Multiplication adds the positive degrees, and the final subtraction of 1 cannot cancel its nonzero leading part. The exact anchor degree is consequently

```
w_a + max(1936,2*max_{j!=a}(w_j)).
```

The argument is characteristic-zero. Modular evaluations alone would not exclude cancellation between squares at a chosen prime; they are unnecessary for this partition-degree deduction. Uniform exact degree across valid fixed-program slices depends on the previously proved uniform exact degrees of the factors and S.

## Integer zero-set and paid cost

Only the last factor, the loader checksum, lacks an independent exclusion of -1. Every partition contains that factor in exactly one group. If all group products equal 1, the protected factors within each group are forced to 1; the lone checksum is then also1. Conversely, all original factor equations give group products 1.

Both finalizers force all group equations and retained residuals: SOS by nonnegativity; the single anchor because its bracket is a positive integer and their integer product is 1. No group placement of the single checksum invalidates this proof. Integer integrality is essential; arbitrary-real zero-set equivalence is not implied.

The base certificate has 431 gates. Producing g disjoint products of the seven already-paid factors needs exactly `7-g` additional multiplications in this schedule. There are 24 retained nonunit comparisons. The SOS finalizer has `3*(24+g)-1=71+3g` operations. The anchor puts 24 retained residuals and g-1 other group residuals into its bracket, then pays one product and one subtraction: `3*(24+g-1)+2=71+3g`. Both complete costs are therefore

```
431 + (7-g) + (71+3g) = 509+2g.
```

This arithmetic count assumes the specified literal grouping schedule; it is not a lower bound on all ways to compute these polynomials.

## Representative optimal partitions

Indices 0 through 6 follow the stated weight order.

- At 511 operations, all factors form the anchor group, weight 2945, giving degree 2945+1936=4881.
- At 513 operations, the unique optimum is SOS on `{0,1,2,4,6} | {3,5}`, with weights 1385 and 1560.
- At 515 operations, all eight optima are SOS and contain `{2,3}`, weight 1058. One representative is `{0,1,4,6} | {2,3} | {5}`, with weights 1053, 1058, 834.
- At 517 operations, one of 41 optimal SOS partitions is `{0,1,2,6} | {3} | {4} | {5}`, with weights 487, 726, 898, 834. Every group weighs at most 968, so the retained SOS fixes degree 1936.

The three-group bottleneck also has a short direct proof: if every group weighed at most 1057, the three heavy factors 898, 834, 726 would occupy separate groups. The 332 factor cannot join any of them, because its smallest possible sum is 1058. Thus three groups need maximum weight at least 1058, and the displayed partition attains it. Four groups attain the unavoidable retained-SOS floor 1936.

Replay with explicit output:

```sh
python review_u15_partition_math.py --output review_u15_partition_math.fresh.json
```
