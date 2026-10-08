# Independent correctness review of the interval/Fitting continuation

Reviewed on 2026-10-07 by the literature/theory audit agent, independently of the implementation agent. Scope: `work/fast/fastunknot/scalar_split.py`, `barcode_scan.py`, `order_dp.py`, and integration in `recognize.py` and `__main__.py`. The review also followed the relevant invariants through `component_scan.py`, `scan_fast.py`, and `planar.py`. This is a mathematical/code review with small independent probes, not formal verification or a performance measurement.

## Outcome

No unresolved correctness defect was found in the reviewed algebraic or integration paths. Two CLI issues identified in an earlier snapshot—missing exact `khovanov --barcode/--fitting` switches and uncaught negative order-option errors—were fixed by the root agent. The current CLI was reread and contains both the switches and explicit error-code-2 handling. The root agent separately reported that the three integration tests pass.

## Algebra and representation invariants

1. **The scalar endomorphism equations are complete.** Variables mix only equal matching IDs in equal homological degrees. The equations equate every coefficient of every entry of `Qd` and `dQ`, including zero entries that receive contributions from other incidences. Over the chosen morphism basis these are ordinary binary linear equations.

2. **Fitting conjugation preserves all attachments.** `_change_basis` evaluates the full expression `P_target^{-1} d P_source` for every outgoing incidence, and does not restrict the transformation to a chosen internal edge or submatrix. The exponent used for the Fitting power is at least every block dimension. The constructed kernel/image basis is independently checked for invertibility. Before accepting a split, the implementation checks the original commutator and every transformed cross-partition coefficient. The bounded search is incomplete by design; failure to find a split leaves the component unchanged.

3. **Caching does not infer geometry from a scalar signature.** The scalar cache key records complete matching-equality colors, relative homological degrees, and every coefficient/target entry. It discards actual matching names only where the scalar equation depends on equality of objects and linear coefficient arithmetic. A positive hit rechecks commutation and the transformed cross-block zeros on the current component. The scanner's other shape/transfer caches depend on matching geometry and complete morphism coefficients. A scalar change of object basis does not change the morphism basis of a fixed matching pair, so those cache keys remain valid; stage-specific caches are reset by the existing scanner.

4. **The interval detector satisfies the common-nilpotent hypothesis.** Every object must have the same matching, every nonzero differential entry must equal the same nonzero packed coefficient, and the identity coefficient must vanish. In the implemented endomorphism algebra over F2, this is exactly an augmentation-ideal element, whose square is zero. The rank-invariant inversion computes interval multiplicities for an arbitrary type-A scalar quiver and checks nonnegativity and conservation of the original vector-space dimensions. It does not incorrectly impose `A_(h+1) A_h=0` on the scalar arrows.

5. **Ancestry and multiplicities remain attached to whole summands.** Both new passes require a common original parent for every connected component. Every summand produced by a basis change or interval decomposition inherits that parent's weight polynomial. Subsequent sharing sums the inherited weights and adjusts only the correct global homological shift. Thus splitting one weighted representative into several direct summands does not discard virtual copies, apply a weight twice to one summand, or infer that a large intermediate object count forces a large original homology rank.

## Decision-only replacements

The exact rank entry points do not apply rank or interval-length caps; `fitting_khovanov_rank` explicitly rejects non-null decision caps. The decision entry points use cap 3 and expose the capped result, not a reconstructed exact rank or homological grading. When interval shortening is enabled, stage statistics are renamed to describe the weighted decision model and the former original-complex lower-bound claim is removed. Integration evidence explicitly records decision equivalence.

The length-two replacement has the correct mathematical scope: the input is a validated one-component classical knot; shortening is applied to whole common-nilpotent direct summands; the relevant continuation is the raw suffix-and-closure functor. Such a nonempty matching closes in every raw suffix resolution to a nonempty union of circles. Consequently the total homology rank of its continuation is even. Together with the classical dual-number decomposition formula, this proves preservation of total rank capped at 3 under shortening to length 2. This argument does **not** preserve exact rank, chain homotopy type, or quantum grading. The implementation and current public descriptions respect that distinction.

## Window optimization

The first subset-DP pass correctly minimizes the global peak, including the fixed peak outside the window. The second pass minimizes the additive objective among paths satisfying that optimal peak. This avoids the invalid single-label lexicographic recurrence. The full-window boundary state is included in the variable part, while all later and earlier frontier states are fixed; their additive costs are constant. Accepting only a strictly better full-order score is consequently sound.

## Small independent probes

All probes passed, using fixed random seed 923771 and no timing experiment:

- 84 small binary equation systems: compared the complete solution set generated by `binary_nullspace` with exhaustive direct parity evaluation, for 0 through 6 variables.
- 30 independently scrambled two-layer direct sums, with five distinct matching/degree blocks and all source-to-target matching incidences present: recomputed the returned commutator and full conjugation using separate dense binary Gaussian elimination and coefficient-array arithmetic; all returned splits agreed entrywise and had zero cross-partition incidences.
- 40 window-optimization cases on six-vertex paired-edge graphs, covering both `sum` and `mass`: compared the selected score with every permutation of the chosen window, keeping the outside order fixed. Every score was globally optimal under that restriction.

These probes test different representations of the relevant algebra rather than mirroring the packed implementation. They do not establish exhaustive correctness for arbitrary input size, validate a quasi-polynomial complexity bound, or measure speed. No implementation files were changed during this review.
