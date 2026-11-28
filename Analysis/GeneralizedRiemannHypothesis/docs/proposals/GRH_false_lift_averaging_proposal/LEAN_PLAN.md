# Lean migration plan (not compiled)

## Preserve the public theorem

Use the existing theorem statement verbatim: `New.DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate` at line 1466 of [BottomOfTower.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/9050b04000647d588d0c78d945180abcd3b0bcf7/Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/New/OneLift/FalseLifts/BottomOfTower.lean#L1466). Retain the original first reduction `DescentsVanish.of_schrodingerOp`, and replace only the argument for the fixed `u`, `P`, `g`, `Ψ`.

The following are proposed declaration contracts, not code known to elaborate. Use the actual source types and instances rather than replacing the definitions of `FormV`, `levelGroup`, `HyperplaneSumsAnnihilate`, or `translatedBlockFn`.

| Proposed declaration | Mathematical contract | Reuse |
|---|---|---|
| `DescentPair.triangularLevel` | subgroup H of `stdLevel E n` with upper/lower triangular reductions at the two place families | `reduceFamily`, `mem_levelGroup_of_reduceAt`, finite residue matrices |
| `DescentPair.triangularRep` | complex linear representation on `O.FormV`; factor through first-block residue homomorphism | `blockAction` (1267), `smul_chosenGLRep_eq_apply_of_triangular` (998) |
| `exists_common_finite_quotient` | for a given local SB function, choose normal N of finite index acting trivially on its translates and on the forms | local constancy, compact support, congruence reductions; or directly finite-orbit machinery from prior orbital exchange proposal |
| `hyperplaneSumsAnnihilate_orbitSpan` | orbit span U is stable; every single-place hyperplane sum kills all U | `sum_formAction_mulSingle_eq_zero` (1296), `sum_blockAction_eq_zero` (1356), conjugation of rank-one matrices |
| `translatedBlockFn_triangular` | `Φ_T(h·) = c • Φ_(TS)` | `residueBlockDatum`, `residueDatum_of_eq_map` (750), `translatedBlockFn_leftMul` (797), first-block triangular conditions |
| `descentPairing_translatedBlockFn_orbitSpan_eq_zero` | B vanishes on all right block translates and all v∈U | `descentPairing_translate` (1103), `descentPairing_translatedBlockFn_eq_zero` (1185), conjugate-linear span induction |
| `bad_stabilizer_invariants_eq_bot` | for a bad x, a U-vector fixed by H_x is zero | `exists_isAnnihilatingRow_of_not_hasIntegralBlockRatio` (365), shear construction (1376); strengthen witness to state triangular membership explicitly |
| `exists_normalized_block_orbit` | every good x has normalized translated datum with nonzero locus Kx, an open compact orbit | `exists_leftMul_eq_of_translatedBlockFn_ne_zero` (833), `translatedBlockFn_eq_one_of_hasIntegralBlockRatio` (955) |
| `reynolds_descent` | B(Ψ,y)=0 by finite average and contraction | above contracts; Sections 3–6 of the note |

## Implementation order

1. Introduce H as the preimage of the finite product of parabolic subgroups. Prove that first-block extraction is multiplicative. Define its action directly from `blockAction`; this bypasses proving that arbitrary adelic lifts of the same residue act equally. Use the existing equality with `algFormRep` when applying equivariance. Show restriction to K equals `levelChar` scalar. Do not silently identify a lift with the finite group element.
2. Work on the finite product of local matrix spaces, or stay with source functions invariant under `idem O.places • x`. Transfer compactness to the local product, **not** to the whole finite adelic space with unrestricted unused coordinates. Reuse the local SB API. Choose a common congruence precision that preserves the support box and fixes the function. An alternative is to take the core of its finite-index stabilizer intersected with the representation kernel; the quotient must act on the whole orbit. All representatives act on the function and form through this quotient. No Haar integration of `B` is needed.
3. Let U be the span of the finite action orbit of y. For conjugation invariance, compute `s * (1 + vecMulVec a l) * s⁻¹` and reindex the hyperplane subgroup; determinant weights are preserved. Work with a linear submodule for the kernel of the weighted operator. Extend B-vanishing by span induction using its semilinear second variable. For the translated datum identity, the order of the right product is `T * S`, not `S * T`; at chosen places S lifts the first block and at twist places S is the identity.
4. At a bad x, retain the exact integral annihilating row. The existing shear proof explicitly constructs a maximal-level element for every `s`; record the two triangular block equations as part of its output. This is not a choice of lifts forming a group homomorphism and does not need to be. It gives the desired action on every vector and a point stabilizer. The nonzero row is necessary to use the annihilation lemma. Average over `hyperplaneGroup l`, whose cardinality is nonzero in ℂ.
5. Define F by the finite sum of `star (Ψ (h⁻¹ • x)) • ρ(h)y`, normalized by the cardinality. Prove equivariance by a change of variable in the finite group. Prove support compactness/local constancy via a finite union of translated supports; F vanishes at bad points by the stabilizer result. Use the existing orbit-support and normalized-value lemmas, plus the character identity. Extract a finite subcover of the compact nonzero support by disjoint K-orbits; avoid claiming the complement of the good locus is open.
6. Implement the contraction with a finite basis of U (the coordinate functions are locally constant and compactly supported). If `b_i` is a basis, define `contract F = ∑ i, B (star ∘ coord_i F) b_i`. Prove the single-product formula `contract (fun x ↦ star (Ψ x) • v) = B Ψ v` by expanding v in the basis and using semilinearity. This proves additivity and conjugate-linearity, and the finite-average identity follows. The good-orbit formula then proves zero directly. This approach avoids a new general tensor-product development; the generic tensor lemma is optional.
7. Replace the proof of the exported theorem. Preserve `HyperplaneSumsAnnihilate` and external APIs. Rebuild all immediate consumers, then remove old helpers if the actual compiler/dependency scan confirms they are dead.

## Candidate regions

Inclusive physical lines in the inspected blob `b113ad2b09b23d465d369e727f9e584920c7e554`: 387–557 (171), 624–645 (22), 886–954 (69), 1211–1263 (53), 1437–1485 (49). Total 364. The entire file is 1492 lines. These regions are targets, not a deletion patch; some contain potentially useful auxiliary lemmas. The existing scalar coinvariant machinery may reduce the new implementation cost, but the needed vector-valued stabilizer and contraction remain distinct.

## Acceptance checks

- Verify the exact theorem statement before and after (including all implicit/typeclass arguments). No `sorry`, new axioms, altered hypotheses, unproved analytic assumptions, or weakened target.
- With the repository toolchain and Mathlib revision, run `lake env lean src/New/OneLift/FalseLifts/BottomOfTower.lean`, then the corresponding files `HyperbolicPlaneStep.lean`, `PeriodsOfFalseLifts.lean`, `GluingMaps.lean`, `LiftVolumeHeight.lean`; ensure the dependencies are built, or use `lake build` first. Then rebuild the complete project and run its existing comparator/kernel-check scripts. Check `#print axioms` on the unchanged public theorem and final RH/GRH declarations against the original build.
- Test empty support, trivial orbit span (y=0), zero twist-place family, singular top block, nonintegral bottom ratio, and chosen-place integral but nonzero reduced ratio. Test `r=1` and `r>1`. Check conjugation signs and the order of right multiplication.
- Measure nonblank noncomment lines and imported dependency closure before and after, after the other proposals are integrated. Report net changes, not merely removed blocks. Do not count a moved proof as a mathematical simplification. If a newly imported library proves the same result at equal complexity, report that honestly.

No Lean toolchain was present in the artifact environment. These are concrete formalization obligations and acceptance criteria, not a verified patch.
