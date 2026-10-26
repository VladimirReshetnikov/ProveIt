# Three additional arithmetic simplifications

Baseline: `29936089835c0c55cca81edc86b4fb0c70ce34d5`, 26 October 2026.

These are deliberately narrow, source-specific deltas after treating the earlier simplification packets as applied. The novelty audit found no proposal about the indicated coprime divisibility decomposition, geometric-sum proofs, or positive-margin interval argument. These edits do not claim a new general proof methodology. In particular, the first should not be presented as the old generic recommendation to avoid unpacking divisibility witnesses; the actual new target is cancellation in the orthogonal sum `Q*F + J*T` under `IsCoprime F J`.

## 1. Extract divisibility from the two orthogonal summands

Target: `RatioReparameterization.combined_dvd_iff`, lines 24–41 of the baseline source.

The theorem is

`J * F ∣ Q * F + J * (H - C) ↔ J ∣ Q ∧ F ∣ H - C`,

with the single premise `J ∣ F - 1`. That premise makes `F` and `J` coprime. The old proof separately constructs four witnesses, subtracts off each divisible summand, and constructs a new quotient for the reverse direction.

The proposed proof keeps the same number-theoretic argument at the level of the divisibility API. From divisibility by `J*F`, first weaken to divisibility by `J` or `F`; use `dvd_add_left`/`dvd_add_right` to discard the summand already divisible by that factor; use coprimality to cancel the other factor. For the reverse direction, `mul_dvd_mul_right`, `mul_dvd_mul_left`, and `dvd_add` suffice. This removes all explicit quotient witnesses and the closing `ring` proof.

The public type and the existing helper `isCoprime_of_congruence` remain exactly the same. No nonzero or positivity hypothesis is added. This matters because, for example, `J=0, F=1` and `F=0, J=±1` satisfy the existing premise and should remain covered. The proof is valid at these degenerate values.

Measured declaration size: 18 → 11 physical lines. Complete module: 180 → 173 lines. Axiom footprint before and after: `[propext, Quot.sound]`.

## 2. Remove both bespoke geometric-series inductions

Targets: `PolynomialRangeBounds.geometric_identity` and `geometric_lt_two_top`, baseline lines 16–32.

Let `S_d = ∑ i∈range d, B^i`. Mathlib's `mul_geom_sum` states exactly `(B-1)*S_d = B^d - 1`, so `geometric_identity` becomes that theorem directly. For `B≥2`, each summand of `S_d` is nonnegative, and `1≤B-1`. Therefore

`S_d ≤ (B-1)*S_d = B^d-1`,

hence `S_(d+1) = S_d+B^d < 2*B^d`. The second proof uses the first identity and positivity instead of another induction.

Both public statements are unchanged, including `d=0`. The geometric identity itself remains valid for every integer `B`; only the estimate requires `B≥2`. The patch adds one explicit import, `Mathlib.Algebra.Ring.GeomSum`, and counts that import in its savings.

Measured declaration sizes: 7 → 3 and 9 → 7 lines. Complete module: 150 → 145 lines, including the added import. Both axiom footprints before and after are `[propext, Classical.choice, Quot.sound]`.

This is distinct from the old coefficient-envelope and polynomial-support proposals: it removes the elementary geometric-series inductions underneath the evaluation estimates, without changing the coefficient-bound abstraction or the polynomial data.

## 3. Read a positive quadratic margin as an interval

Target: `MarginSeparation.coordinate_gt_of_margin_pos`, baseline lines 73–91.

Write `z=C-K*Y`. The premise is

`0 < (K^2 - 4*z^2)*cap - 8*g*K^2`,

where `K>0`, `cap>0`, `g≥0`, and `Y≥2`. The nonnegative tail gives `(K^2-4*z^2)*cap>0`; cancel the positive `cap` to obtain `4*z^2<K^2`. Applying `abs_lt_of_sq_lt_sq'` to `2*z` gives the two-sided interval

`-K < 2*(C-K*Y) < K`.

Only its lower endpoint is needed. Since `K*Y≥2*K`, it yields `2*C>3*K`; positivity of `K` then implies `C>K`.

The old proof instead assumed `C≤K`, manufactured `K≤-(C-K*Y)`, built a square-monotonicity certificate, and contradicted the margin. The proposed proof follows the geometric meaning of the positive quadratic directly. It uses `nlinarith only` for the two small residual linear/polynomial steps, and preserves all premises and the theorem conclusion exactly.

Measured declaration: 19 → 11 lines. Complete module: 141 → 133 lines. Axiom footprint before and after: `[propext, Classical.choice, Quot.sound]`.

The positive `cap` and nonnegative `g` are essential to the cancellation step; no stronger source assumptions have been silently introduced. The proposal differs from prior rational-root descent and minimum-saturation ideas, which operate on a different mathematical stage of the finalizer.

## Validation completed by this subtask

- `AlgebraBaseline.lean` contains the four original declarations with enough local scaffolding to reproduce their proofs; compilation exit 0.
- `AlgebraDeltas.lean` contains the four replacement declarations with the same statements; compilation exit 0.
- Both files were checked using Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and the cached repository-pinned Mathlib dependency.
- The `#print axioms` outputs match theorem by theorem and contain no `sorryAx`.
- `measurements.json` contains exact before/after declaration texts and SHA-256 hashes for complete baseline/proposed modules.
- `patches/*.patch` are independent reviewable diffs; `proposed/*.lean` are complete patched modules.
- Compilation of these exact-statement fragments does **not** by itself establish a rebuild of the complete modules or downstream clients. The parent task is performing that additional validation and should report its outcome separately.

All three complete module deltas sum to **20 physical lines removed**. This excludes any savings previously proposed and includes the new explicit import. It is not a compilation-time benchmark or a count of proof-term nodes.

## Integration

Apply the three patches to the pinned repository, retain the old public names, and compile all three complete modules. Compile direct clients such as `RatioMarginFinalizer` and `NativeQuadraticSource52` against the rebuilt objects. These are proof-only changes; executable data, polynomial expressions, variable counts, degree bounds, and consistency assumptions are not edited.

Any proposal to expose `A^2≤D` and `A≤G` already derived inside `pell_register_bounds` would be a related small cleanup, but is omitted from the delivered patches: it is not needed for the three validated mechanisms above and overlaps the older general source-facts recommendation.
