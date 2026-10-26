# Residual proposal: identify the two-radicand polynomial before evaluating it

Snapshot: ProveIt `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
Target: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/RefinedPair.lean`, especially `value_eq` (original lines 61--79).

## Why this survives the prior proposals

The prior-art agent searched all 12 incoming primary reports and supplementary notes plus the six placed packets. `RefinedPair` appeared only in an inventory; `expand_injective`, `expand_two_core` and `radicalProduct` did not appear as proposals. Previous rational-root descent preserves a root while showing it integral, and concerns Pell/carrier witnesses. This proposal instead establishes a polynomial identity without choosing any roots.

## Existing proof

`value_eq` chooses complex square roots of the two integer radicands using `IsAlgClosed.exists_pow_nat_eq`. It invokes `RefinedRelationCombiningPolynomial.value_eq_product`, uses the already-proved four-factor formula `radicalProduct_eq`, and casts the resulting equality back to integers. This is correct, but the target is a universal polynomial identity and the proof introduces algebraic closure and existential roots solely to expose the identity.

## Algebraic replacement

Work over the coefficient ring C = Z[V0,V1,n,B,C0,D], with outer radicand variables A0,A1. Define K=B(2D-1), T=Bn+C0-K(C0+V0V1), and

    Q = (T^2 + K^2 A0 - K^2 V0^2 A1)^2 - 4 T^2 K^2 A0.

Let delta be the algebra endomorphism sending every outer variable Ai to Ai^2 and fixing C. Mathlib's `MvPolynomial.expand_injective` proves delta injective at expansion factor 2. The repository already supplies

    delta (core 2) = rawProduct 2

as `RefinedRelationCombiningPolynomial.expand_two_core`. Applying the existing `radicalProduct_eq` in the polynomial ring itself gives

    rawProduct 2 = delta Q.

Injectivity proves `core 2 = Q`. Evaluation at arbitrary integer radicands and parameters then proves `value_eq` by simplification.

This replaces a value-level argument via complex roots with one stronger formal-polynomial identity. All public integer parameters remain unrestricted, all executable arithmetic data remain unchanged, and the literal four-factor product remains the mathematical source of the formula.

## Intended Lean artifact

`compiler_prototype.lean` copies the small existing formula and four-factor lemma under an isolated namespace, adds `core_eq`, and replaces `value_eq` by evaluation of that identity. It deliberately omits the direct `Mathlib.Analysis.Complex.Polynomial.Basic` import. The proposed module was not reached by the compiler: dependency replay stalled under memory pressure. See the final validation section below.

Three upstream repository dependency files were fetched from the pinned commit through GitHub and compared to the existing local compiler source cache. Their Git blob SHA-1 values agree exactly:

- SignInvariantPolynomial.lean: `5de32ab4b385efdafaa19fa3d744debc85f2599a`
- RelationCombiningPolynomial.lean: `5c7a5086ac619e7cb75f26adfb973d9ad883f10f`
- RefinedRelationCombiningPolynomial.lean: `93dce0d481f2160523b0a3f77fb97d30d6f7936a`

## Honest benefit and limitations

The principal benefit is simpler mathematical dependencies and a stronger reusable polynomial identity. The integer endpoint should become three lines, but the auxiliary universal identity must be charged to total source cost. Do not claim total line savings without measuring the final module. Do not claim elimination of the `Classical.choice` axiom: polynomial definitions and finite equivalences may retain it even after existential square-root choice disappears. Do not infer build-time improvement from the removed direct import; it requires an actual before/after build measurement.

## Final primary artifacts and metrics

The primary proposal now contains only the algebraic change. `pairSigns` and `prod_signs` are preserved byte-for-byte, so the contribution is not mixed with earlier-style finite-equivalence cleanup. The primary source is `compiler_build/RefinedPair.lean`; its diff is `compiler_build/refined-pair-algebraic.patch`. `compiler_prototype.lean` is the same source under an isolated namespace.

The original module has83 physical lines and the new module86, an increase of3. The old `value_eq` proof body has16 physical lines (64--79); the new body has3 (80--82). The new `core_eq` proof body has7 physical lines (68--74), while its full declaration including statement has12 (63--74). The whole-file count charges all new statement, namespace-opening, documentation and axiom-print lines. No net line reduction is claimed. Metrics are in `compiler_build/primary_metrics.json`.

## Final validation outcome

The production patch and prototype were **not compiler-validated**. Dependency replay stalled under memory pressure; the proposed `RefinedPair` module was never reached. The exact-source attempt and an import-only narrowed replay were both stopped, with no observed dependency proof error. See `compiler_build/VALIDATION.md` and `compiler_build/validation_status.json` for scope and reproduction instructions.

The stale introductory reference to complex roots in the proof has been removed. Public `value_eq` and `radicalProduct_eq` headers, the executable `value` definition, and the original private finite-equivalence scaffolding are unchanged byte-for-byte. No `sorry`, `admit`, or new axiom declarations occur.

An optional earlier combined77-line variant is retained under `compiler_build/optional/` solely as working history; it need not be packaged or discussed in the primary report.
