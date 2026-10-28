# Independent review: adaptive sixteen-group streamed separators

Status: passed. Reviewed `research/asymptotic_route/adaptive_separator_proof.tex` and independently reconstructed the finite covariance matrix before reading that proof. The independent checker is `verify_separator_covariance_independent.py`; its deterministic output is `separator_covariance_independent.json`.

## What was checked

1. **Path convention.** For a fixed complete balanced binary tree on sixteen leaves, an unordered edge belongs to a leaf's path-cut union precisely when that leaf lies in the least common ancestor subtree of the edge's endpoints. Every path includes 85 unordered pairs, equivalently 170 directed pairs.
2. **Mean and RMS convention.** With sixteen leaf costs, the inequality is `max <= mean + sqrt(15) * population_RMS_deviation`. The population RMS uses division by sixteen. The factor follows from the other fifteen deviations summing to the negative maximal deviation.
3. **Random relabeling covariance.** The centered covariance must subtract each tree's own leaf mean before the permutation average. The independent construction does this. Averaging over edge-pair permutation orbits gives 19/192 on the diagonal, 5/168 for adjacent pairs, and -179/17472 for disjoint pairs.
4. **Spectral domination.** The covariance is bounded by `(33/56)*(I-J/120)`. The independent checker verifies an exact rational PSD certificate, not numerical eigenvalues: `Q=A/210`, where A has entries 182, -13, 2 on identical, adjacent, disjoint pairs; `A*A=210*A`, rank Q is 104; and the difference is `(33/56-85/2912)*Q`.
5. **Scalar calculation.** Jensen and two-dimensional Cauchy-Schwarz give beta squared `725/1344`. Dividing by the former `170/256` gives exact ratio squared `290/357`.
6. **Algorithmic accounting.** Select a tree separately for every exact pair-budget array. The number of paid group-factor calls is at most the sum over leaves of the product of pair-list sizes on its path, hence at most sixteen times the maximal path product. The group factors remain actual recursive child contractions. No cache or free oracle is introduced, and independent sibling sums use distributivity rather than joint enumeration.
7. **Space and schedule.** Enumeration of a fixed number of relabelings uses polynomial space; the selected tree's contraction is streamed. Its local recurrence is a multiplicative branch-count recurrence, as claimed. The previous r=16 packing, precision, child-degree, leaf, and entry-evaluation gates are unchanged because only summation order changes.

No gap found in these steps. The theorem remains relative to the imported exact-contraction interfaces; this review is not a full independent proof of the upstream SAT result.

## Symbolic derivation of the covariance values

The sixteen-leaf tree has edge LCA classes of sizes 64, 32, 16, 8, with leaf-incidence means 1, 1/2, 1/4, 1/8. Thus the trace of the fixed-tree leaf-centered covariance is

`32*(1/4) + 16*(3/16) + 8*(7/64) = 95/8`.

There are 120 unordered edges, so the permutation-averaged diagonal is `(95/8)/120 = 19/192`.

For a fixed leaf the path-degrees of the sixteen vertices are 15, 14, 12, 8, with multiplicities 2, 2, 4, 8. Every vertex has mean degree 85/8 when the leaf varies. Hence the sum over vertices of their degree variances is

`[2*35^2 + 2*27^2 + 4*11^2 + 8*21^2]/64 = 495/4`.

Each covariance diagonal appears twice in that degree-variance sum. The sum over the 3360 ordered adjacent distinct edge pairs is therefore `495/4 - 2*(95/8) = 100`, giving `5/168` per pair.

Constant edge weights give every leaf the same cost 85, so all covariance entries sum to zero. The sum over the 10920 ordered disjoint edge pairs is consequently `-95/8 - 100 = -895/8`, giving `-179/17472` per pair.

## Limitations to retain in the report

- The initial proof allowed exhaustive checking of at most 16! relabelings. The delivered implementation supersedes that search with an exact subset dynamic program using 14,827 states and 462,465 balanced splits; its independent correctness review is recorded in `independent_review.md`. This construction has not established a practical SAT solver speedup.
- The new polynomial-space coefficient is 50.210434836331..., versus 55.709478318910..., and the SAT logarithmic order is unchanged.
- The theorem does not beat unproved n/log(n)-type targets or give a numerical comparison with unspecified constants of the separate primary manuscript.
