# Proof audit

This is a self-audit of the written arguments and their finite implementation, not independent peer review or proof-assistant verification.

## Geometry and equality

**Whole-field semantics.** Cells are affine over the entire field F_q. Subfield-affine partitions can behave differently. The proof does not replace disjoint partitions by overlapping covers.

**Why q > 2.** Two proper zero sets of affine functions cannot cover a d-flat when 2*q^(d-1) < q^d. This puts every admissible flat in one coordinate orthant. The argument includes even characteristic for q >= 4. At q=2 an affine line can join two distinct arms, so the exclusion is necessary for this proof.

**Torus capacity.** Selecting d independent actual coordinate functions yields an affine bijection to F_q^d. Nonzero values in all ambient coordinates force nonzero selected coordinates. This proves the capacity (q-1)^d without assuming axis-parallel cells.

**Equality criterion.** The dimension defect G(d)=1+(t-1)q^d-t^(d+1) is zero exactly at d=0,1. Thus an equality partition consists of torus points and lines contained in the cross product with one boundary point each. The phrase “contained in X” is part of the precise statement.

## Chain construction

**Existence of support chains.** Adjacent support layers admit left-saturating matchings because their degrees are (m-j)*s and j+1. The selected matchings give at most one predecessor and one successor, not branching trees. Every lower-support word belongs to exactly one head chain.

**Arms along a chain.** A full word extending a head extends every lower word in its chain. Every anchor therefore lies in the assigned orthant.

**Prefix separation.** At different zero counts z < z', the ratio in the last zero coordinate of the shorter prefix is a for one family and b for the other. Both ratios use the same first zero coordinate, and a != b are nonzero. The minimum head size two prevents the first coordinate from also being the distinguishing last coordinate.

**Boundary versus torus collisions.** Every constructed line has precisely one boundary anchor; all other points have full support. Distinct boundary words therefore cannot collide with torus portions of other families.

## Common-invariant fiber construction

**Common invariants.** All zero sets assigned to one coloring use the same products H_j. Disjointness would not follow if invariants were defined separately for each zero set.

**Rainbow requirement.** A z-element zero set must have exactly one coordinate in each of z color classes. This makes the missing-coordinate equations solvable by one affine parameter, with all coefficients nonzero.

**Directions depend on anchors.** The ratios A_z/A_j depend on the fixed outside values. This is allowed: each cell separately is an affine line. The proof does not claim a common direction for an entire fiber family.

**Surjectivity and uniqueness.** A torus point in a specified fiber determines its outside coordinates, hence its anchor and all A_j; the missing coordinates are then forced. This verifies full fiber coverage, not just containment or a cardinality estimate.

**Two unrelated algebraic structures.** Arm labels belong to Z/sZ; coordinate values belong to F_q. The residue trick uses only addition in Z/sZ, so it does not require s to be a prime power or s to divide q-1.

**Slot graph counts.** For a class E and r arm-sum residues, left degree is r*s^(z-1)*t^(z-1), right degree is |E|. The right vertex is the pair (orthant, invariant value), not merely the orthant.

**Separation of coloring groups.** Different coloring groups reserve disjoint arm-sum residues. This avoids unjustified comparisons between different invariant systems. Tail chains use another disjoint residue set and at most one head per assigned orthant.

## Uniform asymptotics

**Rounding overhead is retained.** Each coloring class costs at most one extra residue, and the tail costs at most one. The term K(s,R)+1 is not discarded until its subpolynomial size has been proved.

**Perfect hashing.** The probability of a rainbow z-set is z!/z^z. The union bound uses at most s^z candidate zero sets. Integer bit length b_s bounds the natural logarithm from above; no floating-point comparison is used in the definition of K_z(s).

**Cutoff.** R_s is the least r with (r+1)! >= s. This gives a tail at most 1/s and log K_s ~ log s/log log s. In particular, K_s is not asserted to be polylogarithmic.

**Uniformity in q for the threshold.** The construction uses c_q >= 2/3 and c_q < 1 uniformly for q>2. Hence its sufficiently-large-s threshold and the error K_s+3 are independent of q.

**Uniformity is not transferred without proof.** The analytic root expansion fixes q. Since F_q(c_q)=1/t, its derivatives become poorly conditioned as q grows; no uniform high-arm rate expansion in growing q is asserted.

**Order of limits.** The inner n->infinity rate is controlled by a lower bound valid for every n and by the infimum over finite blocks. No fixed-n asymptotic is silently passed through that limit.

**Positive centered error.** Strict convexity makes the Jensen lower endpoint strictly larger than t*s-gamma_q. Its quadratic Taylor term supplies a positive multiple of 1/s. This establishes the logarithm in the error-exponent theorem is well-defined and supplies the lower half of the sharp exponent.

**What remains unknown.** Matching the inverse-linear exponent does not identify the coefficient of 1/s. Exact attainment at the final capacity-feasible integer is also not proved in general.

## Finite validation actually run

The exact checker passed on eight full partitions, including F_4. Across these examples it inspected 188,625 points and 37,316 affine lines. It also checked all 115 nonzero final-block slices, 511 invariant-fiber partitions over 96 configurations, field axioms for five fields, 2,552 polynomial/defect parameter triples, duplicate-cell rejection, and q=2 rejection.

The numerical bound script verified all reported routing budgets in rational arithmetic. Decimal evaluations are explicitly labelled non-directed approximations. No mixed-integer solver, numerical optimum, or unbuilt Lean file is used as a theorem certificate.
