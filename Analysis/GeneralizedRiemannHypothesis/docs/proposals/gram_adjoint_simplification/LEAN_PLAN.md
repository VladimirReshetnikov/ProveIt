# Integration blueprint

Status: mathematical proof in `gram_adjoint.tex`; no elaborated patch. Suggested declaration names below are new, not assertions that they already exist. Use the pinned readable project, its toolchain and manifest. Keep `src/Statements.lean` and `src/Main.lean` unchanged.

## 1. First preserve the original comparison operator

Work in `New/OneLift/LiftVolumeHeight.lean` and retain `comparisonOp`, `IsComparisonOperator`, and `heightLe_liftDeterminant_ratio` with their original signatures. Prove stronger lemmas for `n_aut * h` in intermediate steps and multiply by the extra integral `h` only at the end. This minimizes downstream changes.

### A. Integer Gram matrix certificate

In `Lib/GLn/SchurModule/GramMatrix.lean`, define an abbreviation `fockGramInt` for the integer matrix of Fock pairings of `nablaBasis`. Reuse `weylGram_mul_fockPairing`, which is `G * H = h • 1`. Obtain `H * G = h • 1` over ℂ via invertibility of the positive definite Gram matrix. Alternatively transpose the original identity, using symmetry of both matrices. Do not define any new inverse over the integer ring. Prove a mulVec identity, `H *ᵥ (G *ᵥ a) = h • a`, after integer casts. Use `Matrix.mulVec_mulVec` or coordinate sums. Tensor/table blocks are handled by the same identity at each `(ChoiceIndex j × SecondFactorClasses)` coordinate, so a giant block matrix need not be introduced.

### B. Adapted coordinates at a finite prime

Choose the rational translates `δ c` as in existing `comparisonOp_mem_integralForms` (lines 413 ff). Reuse the unitary map of the existing `exists_frame_weightRep_eq_intCast` proof:

```
J δ z := star (weightRep ... δ (star z))
J δ⁻¹ (J δ z) = z
```

Define `tupleBasisAt δ (q,k)` to be supported at q with value `J (δ q.2)⁻¹ (Pi.single k 1)`. Prove that for any tuple `z`, the coordinate table of `z` in this basis is `q ↦ J (δ q.2) (z q)` and the Gram blocks are `weylGramOver`. A basis object can be avoided: prove the identity pairing each `tupleBasisAt` with `z` directly via `PiLp.inner_apply`, `Finset.sum_eq_single`, and `gramForm_map_weightRep`.

Prove a local coordinate iff using `IsIntegralFormTuple`, `weylGauge_embFin`, `weylGauge_le_one_iff` and `star_star`:

```
IsIntegralFormTuple ι z ↔ ∀ q k, ‖ι.ιₚ (J (δ q.2) (z q) k)‖ ≤ 1
```

The gauge starts at `ι.ιₚ.comp conj` on `star (z q)`; the second conjugation cancels the first. This same basis works for the conjugate embedding. It is not sufficient to prove only that the chosen basis is integral: the iff is needed for the output. `δ` need not be integral itself.

### C. Integral adjoint

For an integral `φ`, set `z = (glue j ϑ).adjoint φ`. For each block q define `p k = (D.chosenGroupOrder : ℂ) * inner ℂ (glue j ϑ (tupleBasisAt δ (q,k))) φ`. Show `p k` belongs to the valuation ring, using `glue_mem_integralForms` at the conjugate place and `norm_nsmul_inner_le_one` with exactly the same stabilizer divisibility lemma as the old proof. By the adjoint identity and the block Gram pairing, `p = n_aut • (G *ᵥ a)` where `a = J (δ q.2) (z q)`. Multiply by `H` to get `H *ᵥ p = (n_aut * h) • a`.

Since every entry of `H` is an integer cast, each entry of this vector is integral (valuation ring closure under finite sums/products). The coordinate iff implies `IsIntegralFormTuple ι ((n_aut*h) • z)`. Apply `glue_mem_integralForms` and linearity to prove integrality of `n_aut*h*glue*glue.adjoint`. For the conservative refactor, multiply by `h` and close with the original `comparisonOp_mem_integralForms` signature.

No claim of self-duality or of orthogonal integral bases is needed. Do not try dividing the original operator by `h` in its old integrality theorem.

### D. Conjugate norm of the adjoint

Use the coordinatewise complex field automorphism `σ` on the full tuple table. Define `σc := (starRingAut.trans σ).trans starRingAut`, the exact automorphism in `norm_map_inner_le`. Prove for tuples `v,z` the pairing identity

```
σ (inner ℂ v z) = inner ℂ (applyAutTuple σc v) (applyAutTuple σ z)
```

Unfold `PiLp.inner_apply`, `gramForm_apply`, rational/integer entries, and `map_sum`, `map_mul`. Similarly `formTupleNormSq σ z = ‖applyAutTuple σ z‖^2`. Prove `applyAutTuple σc (applyAutTuple σc.symm (applyAutTuple σ z)) = applyAutTuple σ z` by pointwise inverse cancellation. These are not linear maps over ℂ, so use functions, not `LinearMap`s.

Set `z = glue.adjoint φ`. If `formTupleNormSq σ z = 0`, the bound is immediate. Otherwise choose `v = applyAutTuple σc.symm (applyAutTuple σ z)`. The pairing identity makes `‖σ (inner ℂ v z)‖` equal to `formTupleNormSq σ z`. Apply adjointness, then `norm_map_inner_le` to `glue v, φ`, then `normSqAt_glue_le` at `σc`. Cancel the positive square root of the tuple norm. This proves the squared norm bound for the adjoint with multiplier `exp (2*A)` where `A = f*m*b*logB^2`. Apply `normSqAt_glue_le` once more for the product, multiplier `exp (4*A)`.

The target of `glue` is never conjugated into a purported automorphic form. Only the tuple coordinate space is closed under the entrywise operation. A proof using `σ (conj z) = conj (σ z)` would be invalid for general σ.

### E. Scalar bounds

Use `M_pow_denominatorExponent_sq_mul_le_exp` and the inequalities from lines 449 ff of the original size proof to bound `n_aut ≤ exp(A/2)` (handle the empty tuple case separately, or use nonzero source and injective period map). Reuse `hookNumberMinus_le` and `6 * x^999 ≤ A/2` to give `h ≤ exp(A/12)`. The original operator requires `exp(3*A)^2`; the new squared bound is at most `exp(2*(8/3)*A)` for h² and `exp(2*(31/12)*A)` for h. Use `Real.exp_add`, `Real.exp_le_exp` and simple arithmetic, or use the coarser bound `n_aut*h² ≤ exp A` to keep constants elementary. Retain `normSqAt_comparisonOp_le` signature.

## 2. Optional normalization change

After the conservative version builds, change `comparisonOp` to `n_aut*h • glue ∘ₗ glue.adjoint`. In `inner_goodLift_comparisonOp`, `isComparisonOperator_comparisonOp.exists_inner_eq`, replace the scalar `h²` by `h`. In the orthogonality proof, update scalar simplification. The unchanged identity `cϑ • glue.adjoint ∘ₗ goodLift = periodLift` implies the same ratio and strict positivity. `liftCompression` and the generic determinant estimates remain unchanged. Use the stronger local and archimedean lemmas without multiplying by `h`.

## 3. Acceptance gates

- Search the entire checkout for uses of `TightFrameIndex`, `exists_frame_weightRep_eq_intCast`, `exists_tight_frame_formTuples`, `comparisonOp_eq_sum`, `card_prod_mul_card_tightFrameIndex_mul_sq_le`, `exists_tightFrame`. Only delete declarations with no remaining callers. Preserve the general Weyl library lemma if externally used.
- Build the comparison module, `New/Determinant/Twist/LongForms`, `New/Reduction/MainInequality`, `New/Reduction/OneSidedBound`, and finally the full `Main` target (`lake build`). Follow the upstream README for dependency caches and toolchain. Measure the net line count, elaboration time, memory, and proof export size rather than asserting a reduction based on deleted source lines alone.
- Run `lake env lean scripts/PrintAxioms.lean`. Check all five public theorem types against unchanged `Statements.lean` and `Challenge.lean`; do not permit `sorryAx` or additional axioms. Replay the affected modules and repeat independent export checking and Comparator as resources allow.
- Test both conservative and one-hook variants separately. If other proposals have already landed, preserve their public interfaces and compare both builds against the same combined baseline.

The original proof's independent verification is not evidence that this refactor elaborates. The plan is an implementation specification, and all proposed universal mathematics is in the report.
