# Arithmetic review: three fresh, checked mechanisms

Snapshot: `e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11`; Lean 4.32.0; mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
All four original target files were verified against their Git blob hashes in the root source-tree manifest. The changed public theorem statements are byte-for-byte unchanged. `validation.json` contains hashes and counts.

## A. Preserve the rational root when proving it integral

Targets: `NearSquareFinalizer.integer_roots_of_norm_zero` (original lines 117–166) and `MarginFinalizer.integer_roots_of_separated_norm_zero` (48–94).

The existing rational reconstruction supplies specific `r,s : ℚ` satisfying both square equations and the linear relation `theta / omega = r + w*s`. The old code proves the radicands are integer squares, discards these particular roots, obtains new integer roots `r₀,s₀`, and recovers the linear relation through four independent sign cases. This is unnecessary loss of witness information.

For any `n ≠ 0`, if `q^n = (a : ℚ)` for `a : ℤ`, reduced rational denominators give `q.den^n = 1`, hence `q.den = 1`, so `(q.num : ℚ) = q`. The exact new helper compiles as:

```lean
theorem num_cast_of_pow_eq_int {q : ℚ} {a : ℤ} {n : ℕ}
    (hn : n ≠ 0) (h : q ^ n = (a : ℚ)) : (q.num : ℚ) = q := by
  apply Rat.coe_int_num_of_den_eq_one
  apply (pow_eq_one_iff_left hn).mp
  simpa only [Rat.den_pow, Rat.den_intCast] using congrArg Rat.den h
```

The hypothesis `n ≠ 0` is essential: `q^0=1` gives no integrality information. For the application use `n=2`. Rewriting the existing square equations and linear relation with these two numerator identities preserves the chosen signs automatically; `exact_mod_cast` supplies the integer equations.

The general separated-radicand theorem belongs in `NearSquareFinalizer`, which already contains the rational reconstruction. The old bound-specific theorem first proves `a ≠ w²b` and then invokes it. The existing public `MarginFinalizer` theorem becomes a one-line forwarding proof. This removes the duplicate root argument while preserving both existing theorem interfaces. No new positivity assumption or consistency axiom is introduced.

Measured size: NearSquareFinalizer remains 255 physical lines because it now owns the reusable general theorem and denominator lemma; MarginFinalizer falls from 177 to 135. Combined reduction: **42 lines**, counting all added helper code and retained comments. Both complete original modules and both complete patched modules were compiled. The four audited exported theorem axiom lists, including both modules' `exists_value_zero_iff`, are identical before and after: `[propext, Classical.choice, Quot.sound]`.

Novelty boundary: both existing proposal packets were searched; neither discusses rational-root descent, numerator/denominator integrality, these two finalizer modules, or preservation of signed algebraic witnesses. This is separate from the previous proposal to decode source-register equations once. The mathematical improvement is retention of the selected witness, not merely helper relocation.

Artifacts: `RationalDescent.lean`; `NearSquareFinalizer.lean.patch`; `MarginFinalizer.lean.patch`; complete patched modules; `axioms_baseline.log`; `axioms_patched.log`; baseline and patched compiler logs.

## B. Prove polynomial support by degree arithmetic before examining coefficients

Target: `SelectiveCarry.coeff_rowProduct_eq_zero`, original lines 43–68.

For `rowProduct = encoded² * combined`, the old proof unfolds every coefficient of the four nested sums and establishes that none of their exponents equals the queried exponent. The theorem only needs the upper support envelope, so this expands substantially more structure than its conclusion uses.

First prove `natDegree(encoded) ≤ W` from the monomial bounds, reuse the existing `combined_degree_le`, and derive `natDegree(rowProduct) ≤ 2W+D` using the existing power and product inequalities. Then `coeff_eq_zero_of_natDegree_lt` supplies the desired vanishing. The replacement proof is nine physical lines:

```lean
  have he : (encoded w u).natDegree ≤ W := by
    unfold encoded
    exact natDegree_sum_le_of_forall_le _ _
      (fun i _ => (natDegree_monomial_le (u i)).trans (hw i))
  have hd := natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 he)
    (combined_degree_le w s a E D hD)
  apply coeff_eq_zero_of_natDegree_lt
  change (encoded w u ^ 2 * combined w s a E).natDegree < n
  omega
```

Crucially, this uses upper bounds rather than exact degree equalities. It therefore handles zero coefficients, cancellation, empty row families, and the zero polynomial with no added nonvanishing hypotheses. Natural upper bounds also cover Lean's `natDegree 0 = 0` convention. The condition `D+2W<n` already implies the strict exponent range needed.

Measured size: SelectiveCarry 204→196 lines, **8 removed**, including one explicit import. The exact replacement declaration was compiled against the original SidonPositions, QuadraticCoding, and SelectiveQuadraticCoding modules, not stubs. The prototype copies the original rowProduct and combined_degree_le definitions verbatim. It imports the original SelectiveQuadraticCoding module and explicitly imports Mathlib.Algebra.Polynomial.BigOperators. The production patch adds that same narrow import rather than depending on the target’s large Packing import to supply polynomial degree machinery. The entire packing-dependent SelectiveCarry module was not rebuilt. Axiom list: `[propext, Classical.choice, Quot.sound]`.

Novelty boundary: the old reports address weighted/multivariate syntax degrees and earlier placement of degree machinery. This changes the direction of the univariate support proof, from nested coefficient expansion to a compositional degree envelope. Avoid claiming the generic idea of moving a helper earlier as new; the patch introduces no such relocation.

Artifacts: `SupportEnvelope.lean`; `SelectiveCarry.lean.patch`; `support_envelope.log`; original dependency compiler logs.

## C. Extract all unit factors from the product in one pass

Target: `ShortSystem.product_eq_one_iff`, original lines 36–57, together with its private helper at 20–24.

The old proof constructs a separate complementary product for each sign-fixed factor and invokes `ring` four times solely to regroup the same six-factor product. A product equal to one is a unit; `IsUnit.mul_iff` decomposes that fact along the existing multiplication tree. `Int.isUnit_iff` then gives the six ±1 alternatives without any algebraic rebracketing.

The order of reasoning remains important: `na ≠ -1` is conditional on `ns=1`. The checked proof extracts `ns=1` first, then resolves the auxiliary factor's negative alternative using `ha hs1`. It retains only `nk*nt=1`, so both unconstrained signs remain permitted.

The replacement uses one `IsUnit` construction and one `simp only` pass:

```lean
  have hu : IsUnit (n0 * n1 * na * nk * nt * ns) := hp.symm ▸ isUnit_one
  simp only [IsUnit.mul_iff, Int.isUnit_iff, or_iff_left h0,
    or_iff_left h1, or_iff_left hs] at hu
  rcases hu with ⟨⟨⟨⟨⟨h01, h11⟩, hau⟩, _⟩, _⟩, hs1⟩
  have ha1 := hau.resolve_right (ha hs1)
```

The private factor-extraction helper is then unused and removed. Full ShortSystem size: 1117→1104 lines, **13 removed**. The complete patched ShortSystem module compiled against unchanged original ShortEquation, ShortCircuit, and ConsecutivePell modules. The standalone exact-signature theorem also compiled, with axioms `[propext, Classical.choice]`.

Novelty boundary: prior ShortSystem proposals simplify `residualSum_zero_iff` using sums of squares. Neither prior packet proposes product-unit factorization or mentions this theorem. This is a separate algebraic normalization step before residual aggregation.

Artifacts: `IntegerUnits.lean`; `ShortSystem.lean.patch`; complete patched module; `integer_units.log`; `short_system_patched.log`.

## Combined scope and limits

Across these four production files, all added helper code included: **1753→1690 physical lines, 63 removed**. Three full patched modules compiled, the fourth exact target declaration compiled with its real encoding dependencies. The finalizer axiom comparison is exact. No end-to-end repository build or performance speedup is claimed; elapsed times in logs are individual run observations only.

The proposals modify proofs and add reusable theorems. They preserve the existing executable definitions, equation data, public theorem statements, positivity/side hypotheses, and the finalizer arithmetic boundaries. Source-level equality of changed theorem statements is recorded in validation.json. Existing mathematical claims remain exactly those of the pinned repository snapshot.
