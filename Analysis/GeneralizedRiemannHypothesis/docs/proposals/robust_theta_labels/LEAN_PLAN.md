# Integration blueprint (not compiled)

## Goal and invariants

Build against `Analysis/GeneralizedRiemannHypothesis/Lean/grh` at the pinned revision in `source_audit.tsv`. Keep `Statements.lean`, `Main.lean`, q₂, the actual admissible data, the two level primes, the all-place allowed condition, and all numerical bounds exported by the three volume theorems unchanged. This is not a drop-in source patch: the good projector defines dependent spaces. The following steps are proposed to make each build failure local and interpretable.

## 1. Local finite-field lemmas

Add a predicate (proposed name `IsRobustPolynomial`) in or adjacent to `New/UpperBound/Objects/LabelsAndIndexTypes.lean`. Require `IsLabel r c`, `Irreducible c`, and an algebraic-closure root `z` with the three nonvanishing powers in the report. Define the integer exponents from q = Nat.card k, A = q^(r/3), and N = q^r-1. Restrict theorem statements to `r = 3^a`, `a > 0`, `q ≡ 1 [MOD 6]` as appropriate. The generic predicate can be defined even outside this range, but only the indicated hypotheses are used to prove its advertised properties.

Suggested statements, mathematical signatures rather than elaborated Lean:

* `robust_orbit`: for robust `z`, any prime ℓ and any u, the map `i ↦ (z^(q^i))^(ℓ^u)` is injective on `i < r`.
* `robust_scaleRoots`: if `6*H ∣ q-1` and `a^H = 1`, scaling roots by `a` preserves the predicate.
* `robust_common_norm`: all roots have the same `E = ∑ i < r, q^i` power `y`; `6^s ∣ q-1` implies `6^s ∣ orderOf y`.
* `primitive_implies_robust` under the rank and field hypotheses.
* `card_robust_polynomials`: exact root count `3*C*r*W = (q^r-1)*(C-1)`, with `C=(A^2+A+1)/3`, or directly the weaker integer statement `q^r ≤ 8*r*W`.

Avoid using real division in counting lemmas. Factor the difference of powers, establish `B=3*C`, `C % 3 ≠ 0`, `C % 2 ≠ 0`, `6*C ∣ N`, and use cyclic roots of unity. An existing orbit enumeration is `aroots_eq_frobenius_orbit`. The exponent count can be implemented by the CRT or a `Fin N` count of classes modulo `6*C`, and the map to `minpoly` has fibers of size r. A simpler sufficient count via the union bound is `q^r ≤ 15*r*W`; using that variant throughout changes the bound `8*r` to `15*r` and also satisfies the old scale inequality. The exact formula and both lower bounds are proved in the paper.

## 2. Selector and Plancherel gate

* `LabelsAndIndexTypes.lean`: change only the existential witness in `goodTuples` and `mem_goodTuples`; leave `IsAllowedPolynomial`, `goodTupleFamilies` (structural assembly), label projectors, and `hyperplaneSum_mul_e₀` untouched in meaning. Keep primitive lemmas temporarily to support regression and bisecting. Rebuild users of `mem_goodTuples` and `mem_goodTupleFamilies`.
* `BadTypes.lean`: retain `card_not_isAllowedPolynomial_le`, `one_sub_le_card_allowed_mul`, `prod_le_re_tupleIdem_coeff_one`. Replace `totient_le_mul_card_isPrimitivePolynomial` and `card_not_primitive_mul_le` by the robust count and nonrobust weight bound. In `re_coeff_one_sub_sum_tupleIdem_le`, use `u=1/(8*r)` and hypotheses giving the robust count, leaving the product proof and Bernoulli step unchanged.
* `SpanningTheorem.lean`: establish `r=3^a`, `a>0`, `q ≡ 1 mod 6` from admissible data. Keep `h_small` at line 224. Old `h_le_f` implies `8*r*(9*log b) ≤ f`; prove by monotonicity or obtain directly from the log-bound machinery. Do not reduce f. `bad_types_rare` must keep the `b^-8/2` bound. Check the following mean-square result for the changed projector.

## 3. Trace and lift settings

* `EqualMultiplicities.lean`: replace `exists_isPrimitivePolynomial` (line 57) with `exists_isRobustPolynomial` or simply `exists_irreducible_label`. In `trace_mul_tupleIdem_eq` at line 249 retain only `IsLabel` and `Irreducible`, exactly as in the old proof.
* `SelmerHypotheses.lean`: replace the primitive half of `IsLiftSetting.exists_primitive_or_one` with the robust predicate, preserving `card r = D.r`, the witness at each level prime, and the separate rank-one `X-1` branch. Rename to `exists_robust_or_one` to avoid misleading names.
* `AttachedRepresentations.lean`: adapt the constructor at line 81; retain the all-place allowed argument proving `not_isRoot_scaledTypePoly`. In the constructor at line 122, the rank-one branch is structurally identical. Verify the new label remains an allowed label as needed.
* `RowsFromEigensystems.lean` (line 506) and `NormOfChain.lean` (lines 456, 502) use the good families and their idempotents. These definitions are dependent on the selector: rebuild them instead of assuming definitional equality with the previous spaces.

## 4. Galois bridge

In `RowsAndColumnsFromLabels.lean`, introduce a replacement for `not_q₂_dvd_mul_pow_mul` (line 119): `¬ 6 ^ D.towerExp ∣ j * (ℓ ^ b * t)` under the original bounds on j,t,b. The proof uses the prime 2 or 3 distinct from ℓ, plus the exact original estimate `D.m*(4*D.r+2) < 2^D.towerExp`. Establish `6^D.towerExp ∣ P.q₂ D.towerExp` once from `P.dvd_q₀` and the definition of q₂.

Weaken the `dvd_of_pow_eq_one` field of `IsCommonRootPower` (line 326 onward) to `6 ^ D.towerExp ∣ j*x`. All other fields stay unchanged. At the full-rank witness replace the proof at line 356 by the three finite-field lemmas. The tame scaling factor has order dividing q₂ by the same old proof. In the rank-one branch (line 401 onward), compose the old `q₂ ∣ j*x` result with `6^s ∣ q₂`. Do not apply the rank-r predicate to `X-1`.

In the caller `IsRepOfType.isMainSummandLike` at line 548, replace only witness extraction and `not_q₂_dvd_mul_pow_mul` in the unit argument. Keep the type and proof of `eventually_span_eq_top_and_exists_scalar_of_tame_pair`; reuse `norm_pow_sub_pow_eq_one`, the existing coefficient-ring eventuality, the characteristic polynomial killing relation, and the inertia estimates. The `IsMainSummandLike` output must remain literally the original property.

## 5. Verification gates

1. Run the supplied `check_labels.py` and source manifest verifier in the old checkout.
2. Build the local finite module, then `BadTypes`, `SpanningTheorem`, `EqualMultiplicities` and the three Galois files with pinned Lean v4.35.0 and Mathlib revision from the baseline. Use `lake build <module>` for targeted builds, then `lake build`.
3. Rebuild all dependent files; check remaining occurrences of `IsPrimitivePolynomial`, `exists_primitive_or_one`, `goodTuples`, `IsCommonRootPower` and uses of the changed data (search is not a proof of dependency completeness). No new axioms or sorries in the production sources.
4. Confirm that `star_inequality`, the one-sided theorem and `grh` have the same mathematical statements as before. Run `lake env lean scripts/PrintAxioms.lean`; the five public theorems must retain only the original standard axioms. Compare against the unchanged challenge statements; perform independent export/checker replay, following the repository's instructions.
5. Compare proof lines and elaboration time versus baseline. The expected simplification is removal of the full primitive-generator/norm and totient-count arguments from the proof dependency cone. A net line-count decrease has not been measured, and generic primitive-polynomial results may be worth retaining as library lemmas.

No Lean build, independent kernel replay, or repository write was performed in preparing this blueprint. The mathematical substitutions are explicit in the report, but compilation is the necessary next test.
