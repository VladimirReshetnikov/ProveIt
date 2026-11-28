# Lean migration plan (not compiled Lean)

Baseline: ProveIt commit `cdecfeba5d834fbf2f97de71cc7766b58ec4520e`.
All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/New/`.

## Phase A: remove the geometric counting bridge

Keep the definitions `permStep`, `pieriCone`, and the exact pointwise
`sum_indicator_positiveStepSet` / `sum_sign_indicator_pos_eq_indicator_pieriCone` in `UpperBound/ElementaryDivisors/PieriCone.lean` (adapt intervals if needed). Keep `RootLemma.lean`, the power-packing injectivity theorem, and the existing simple-root shift in `DefectCount.lean`.

New lemmas, expressed here as mathematical contracts, not claimed Lean code:

1. **`intStep_det_abs`**: integer step matrix indexed by `Fin k × ZMod N`; abs determinant is the product of `P^(N*l)-1` over monodromy cycle lengths. Show det nonzero. Factor signed diagonal and within-letter permutation to obtain `P • permMatrix U - 1`. A cycle enumeration proves the formula; using the already proved real determinant identity via casts is a safe initial option.
2. **`intStep_range_index`**: for an integral square matrix of nonzero determinant, additive quotient of `Z^d` by its range has cardinal `natAbs det`. Use integer Smith normal form or existing index theorem if available. Include the adjugate containment `natAbs det • Z^d ≤ range` and product of residue cardinalities; no assumption of a square-free determinant. Check actual Mathlib names rather than assuming any particular API.
3. **`signed_lattice_count`**: for all bounded degree intervals, `(k!)^N * count(id-lattice & positive & cone) = sum_sigma sign(sigma) * count(sigma-lattice & positive slab)`. Work in integers to avoid natural-number subtraction. Reuse the existing signed indicator identity with degrees allowed in arbitrary intervals. Show finite support by bounding step images and injectivity. Transport the sum by coordinate permutation and `T_sigma`.
4. **`alternating_cycle_sum`**: evaluate the signed average using fixed exponent tuples. Use absolutely summable geometric series, or prove coefficientwise equality of formal power series and then evaluate at `1/q`. To avoid an extensive formal-power-series detour, use sums over fixed total degree, signed stabilizer cancellation via a transposition, sorted distinct tuples, and their gap bijection; geometric-series summability is elementary. The exact scalar to export is `1 / [k]_q!`.
5. **`degree_count_limit_coset`**: for positive integer tuples with a fixed residue class mod h, use representatives in `{1,...,h}` and stars and bars. Cumulative counts use `Nat.choose` and a zero branch for a negative degree. Normalize by M^k. Prove the binomial limit by the fixed-k falling-factorial formula, ceilings/floors divided by M, and elementary limits. Product over letters; no boundary measure. Include D_j=1 and arbitrary bounded fixed degree padding. `Filter.Tendsto` is fine; do not replace the limit by an unjustified finite estimate.
6. **`degree_count_limit_image`**: sum over the finitely many residue classes of the image lattice. `h^d/index` classes, and each has the same limit. This proves H(D)/index. Use a separate quotient-cardinality lemma, not an assumed bijection to all integer vectors.
7. **`defect_cone_int_shift`**: sum the existing shifts `exists_mem_defectCone_sum_le` over all simple roots. Large multiple plus all-ones vector gives strict positivity and strict negativity of every defect. Multiply by image-lattice index. Absorb all residue representatives with a fixed multiple. Parameters P,k,N are fixed before the packing scale tends to infinity. No quantitative bound on the new shift needed.
8. **`finrank_defectConditions_le_discrete`**: apply the preexisting `finrank_defectConditions_mul_pow_le` at `M = q^e`; rescale mesh points to integer vectors. Use a per-coset injective translation to a single padded positive slab. Apply signed count and the individual lattice limits. Take the signed sum's limit before making any inequalities. Export the flag-weighted bound by H(D). Reuse `index_mul_relIndex_le` and existing cone correspondence; replace `index_mul_finrank_defectConditions_le` proof. The elementary binomial bound in report §6 is optional, or retain the existing exponential estimate.

### Deletion / compatibility audit

- Candidate for deletion or separation: real-volume preimage lemmas, integration of the signed indicator, one-letter specialization and triangular-volume proof, lattice-point-to-volume limit, slab volume lemmas, and corresponding measure imports. Search all uses first: `rg 'prod_mul_volume_real_inter_degreeSlab|volume_real_inter_degreeSlab_eq_signed_sum|exists_finrank_defectConditions_le_volume|volume_degreeSlab_le|volume_real_pieriCone_inter_degreeSlab_one' src`.
- Do not delete exported auxiliary lemmas with nonlocal callers; keep compatibility module if necessary. Quantify actual net reduction using the same file set before and after. The paper identifies ~477 affected lines for Phase A, including comments, not guaranteed savings.
- Keep `index_mul_finrank_defectConditions_le` statement unchanged. Check `exists_isEdgeCondition` compiles without edits beyond importing the discrete bridge.

## Phase B: direct bad Smith directions (independent of A)

In `UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`, preserve edge coordinates, edge condition, exact near-inverse congruence, end factorizations and range inclusions. Replace the generic generator-count argument at lines 64–255 and the middle wrapper at 1011–1079 only after checking uses.

1. Prove a finite valuation-domain Smith saturation helper: for a rectangular full-column-rank matrix T, its fraction-field span intersected with the integral module has a split free basis of rank equal to its number of columns. Can instead use the Smith form and show the explicit basis vectors satisfy `a • v ∈ range T` without a fraction-field submodule: if `T = U * diag(t_i) * V`, take first s columns of U. For each column v, `t_i • v = T • (V⁻¹ e_i)`. Apply `pi * A * T = a • U0` to show `t_i ∣ a` (because the coordinate vector `V⁻¹ e_i` is unimodular and U0 invertible). Therefore `a • v ∈ range T`; `R • v = 0` by cancellation. This is equivalent to the saturation proof and may be simpler in Lean. Handle s=0 and zero Smith entries of AQ explicitly. No discrete valuation assumption.
2. Prove the theorem from report §7. In Smith output basis of AQ, define the finite index set of `alpha_i ∈ a • maximalIdeal`. The projection `1 - Q*R` sends B-columns to `C ∩ ker R`. Its selected bad output block equals `a * U0` with `U0` reducing to identity; `det U0` is a unit. Combine the split bases of Q and saturation via explicit left inverse `(R, rho ∘ (1-Q*R))`. Reduce matrices mod maximal ideal and apply rank comparison. The budget is `D+s ≤ finrank S0`.
3. Direct truncated certificate: pick each `c_i` equal to the divisor of smaller valuation among `alpha_i` and z (by total divisibility, no real valuation). Build a diagonal-basis matrix with range in `range(AQ) ⊔ z • top` and determinant dividing `g^(D-s)*z^s`, `g` chosen from a,z by the same divisibility comparison. Apply `ColengthDvd.of_det_dvd`.
4. Instantiate `a=p^(2*C*)`, `u=w^(5*C*-1)`, with `w^2=p`, `C*≥2`, `w` nonunit. The range hypotheses and near-inverse congruence already occur in the old wrapper. Set `S0` to pointwise residue subspace; dimension = edge-count × local dimension. This supplies s ≤ θD.
5. Compose certificates for the middle and both endpoint maps using `ColengthDvd.comp`. Preserve `exists_colengthDvd_range_pairingMap_mul_edgeRestriction` and `elementary_divisors`; first implement with old bound `(3*c_div+θ*m)*D`, then optionally expose stronger bound `min(m*D,e0+min(c2,m)*(D-s)+m*s)`.

### Verification gates

- Use the project's pinned Lean toolchain and Mathlib; fetch dependencies and run the repository's build and verification procedure. Do not infer a successful build from the mathematical note.
- Search usages of the old helper names before deletion. Check all theorem statements and `#print axioms` for exported results, plus full downstream RH/GRH endpoints. Test the already-planned proposal merges independently or in a separate branch.
- Test k=1, N=1 for abstract determinant/signed identities; alternating N≥2 for the defect shift; D=1 endpoints; repeated values; zero Smith factors; m=0; nondiscrete valuation domains. For the scalar algebra, confirm a=nonzero and u/a in maximal ideal. An assumption `a | u` alone is insufficient.
- Record old/new noncomment lines, build time, dependencies and proof term sizes before claiming savings. Keep the old proof until both implementations compile and the same exported contracts are kernel-checked.

No new Lean file was compiled in this session. The report gives paper-level proofs rather than unverifiable tactic scripts or placeholder `sorry`s.
