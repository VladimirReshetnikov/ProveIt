# Independent audit of the higher dimensional extension

Date: 3 October 2026

## Conclusion

The geometric extension in PROOF.md is sound. The two wording corrections identified below have been verified in the revised proof. I found no genuine mass-four obstruction in the 2+1+1 case. Exact affine lattice rays, rather than a multidimensional hull argument, supply the missing reduction to one unbounded scalar. This audit covers the decision argument in Sections 1–12. The inherited five-particle upper bound in Section 13 was not independently rechecked. This is a mathematical audit, not a machine-checked proof or a literature-priority assessment. No earlier release was changed.

## Two corrections identified and resolved

1. The original final sentence of Section 7 overstated finite-control dependence. Whether a compact triple eventually hits the distant marker can depend on the actual scalar x, beyond its residue. The needed statement is weaker: whether the next encounter continues live or exits live is determined by mode, residue and the lower-bound guards. Once a compact outcome occurs, use the actual marker vector in Section 4 to decide terminal versus ordinary and compute elapsed time and translation. A repeated all-live cycle cannot later acquire a compact outcome, because its local seed and library outcome type are fixed by its repeated finite control.
2. The decreasing-cycle argument in Section 9 now correctly says its residual prefix exits live to ordinary or terminal. Near the lower guard, a formerly successful ray may have only negative candidate period counts. The current W definition guarantees ordinary for successful small-gap launches; a failed flight is also a valid terminal exit. Alternatively, enlarge W to include the entire finite small-gap launch superset, including unsuccessful flights. Either formulation preserves termination.

Both corrections were verified in PROOF.md with SHA-256 3e8eb41fe43b5b4b61d0e0a5b4bece3b01cf628f834a820ecc369f4da427b30a. Reverse replacement of the sole nonmathematical wording change (from “genuinely new” to “additional ... needed for this extension”) exactly reproduces the previously audited SHA-256 e2c5fbed8a4f4c283bb6ad161d36d6ff464a4a7300d914a1ccd7020486869b51. Neither issue introduces another counter; the corrected continuation invariant is sufficient for the decision procedure.

## Geometry and arithmetic checked

- **Weighted dimers.** In the maximum norm, a weight-two singleton produces support in one radius-S cube. Two units farther than S apart are stationary. Otherwise all successor support lies in the intersection of their radius-S cubes, including the two original sites, so diameter remains at most 2S. Hence finitely many normalized shapes suffice in every finite dimension.
- **Mass three.** Outside the diameter-4S core, the only nonstationary case is one bounded dimer and one stationary unit. First core entry is a finite union of one-variable integer interval calculations. Finite normalized core returns therefore give the asserted effective independent or translated-periodic profiles, including intermediate excursions.
- **Actual contacts.** A phase Q_r+kD contacts v exactly when v belongs to Q_r+[-2S,2S]^d+kD. All candidate offsets are finite. Earliest contact is obtained by actual integer time, so ties and multidimensional misses are covered.
- **Nonparallel switches.** Equation (6.1) has the correct sign for v'=-v-c. Two independent drift vectors determine at most one rational pair of flight counts for each finite right-hand side; integrality, nonnegativity and the remaining coordinates are explicitly checked. This gives a computable finite exceptional set, not merely an asymptotic argument.
- **Finite transverse state.** With primitive direction ν and λ(ν)=1, a successful ray has transverse part a-λ(a)ν from a finite list. Recording this part, source side, phase and scalar residue gives additive scalar transitions and bounded vector anchor updates. Absolute anchor position never controls the dynamics.
- **Exact time.** Every long flight has time αx+β with α>0, on its allowed residue. A repeated expanding cycle therefore has affine cycle durations and quadratic accumulated section time. Complete flight phases are affine in the cycle index and a bounded-by-affine period variable; local prefixes have fixed finite data.

## Thresholds and original frame

The threshold construction is noncircular. First compute the original mass-three seed library, B, emission phase offsets, marker shifts, primitive directions and nonparallel exceptions. Then choose N using those finite lists and the norm bounds for λ. Only afterward choose W to absorb bounded scalar launch states, compact contacts and safety margins. The tagged-live convention handles overlap with ordinary states.

The exact exceptional-switch bound is essential. For M=1,000,000, let D=(M,1), D′=(−M−1,−1), a=a′=0 and c=(0,−1). Then k=M+1 and k′=M give kD+k′D′=(0,1)=−c. The exceptional marker vector has maximum norm M²+M=1,000,001,000,000. Thus near-parallel directions can produce a very large finite exception despite small offset data; a small offset-only cutoff would be unjustified.

The original-frame cutoff is correct. Throughout shuttle cycle n, all stationary-frame support coordinates are O(n), including local prefixes and the whole flight. If δ_i is nonzero, the term δ_i T_n has nonzero quadratic leading coefficient and dominates those linear bounds uniformly over every time in the cycle. A computable n_* therefore excludes all later anchored occurrences requiring a nonzero site; wholly zero patterns occur afterward. This argument needs neither coordinatewise monotone motion nor a general quadratic Diophantine solver.

## Why the old hull test cannot be reused

For S=1 in Z², take packet sites (0,0) and (1,1), and a proposed target (-2,3). The target lies in the packet's expanded bounding box [-2,3]², but its maximum-norm distance from each occupied site is 3. It therefore fails the true radius-2 contact test. Section 5 correctly avoids this hole by enumerating occupied-site contact boxes. Likewise, a translating packet can miss a marker in higher dimensions; Sections 4, 5 and 8 correctly retain that terminal alternative.
