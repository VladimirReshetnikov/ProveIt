# Exact Conditioning Order for Fabius Observation Masks

This six-page research note proves a fixed-weight comparison for independent common-tilt uniform coordinates on summable caps. Any cap-dominating injection between observation masks gives convex order of the projected likelihood ratios, a binary Blackwell kernel, and every f-divergence inequality. The weight is bounded, nonnegative and log-concave, with positive expectation. Finite/countable and overlapping masks are included.

For the original uniform product conditioned below any admissible threshold, the hypothesis holds. In the repository's Fabius convention, this proves overlap_late <= overlap_early for every 0<q<1, rho>0, n>=2 and 1<=m<n. The names refer to the hidden blocks; the late-hidden mask observes the larger caps.

The kernel may depend on the fixed weight. All inequalities are nonstrict. Arbitrary independent noise is not covered without an effective-profile hypothesis. This does not replace the arithmetic classification for a single kernel valid for all weights.

## Files and reproduction

- `exact_fixed_conditioning_order.pdf`: complete mathematical report
- `exact_fixed_conditioning_order.tex`: editable LaTeX source
- `build.sh`: three-pass build with an ordinary TeX Live installation
- `checks/verify_rectangle_exact.py`: standard-library exact rational verification
- `checks/rectangle_exact.json`: 18,083 rectangle comparisons on 5,115 sign profiles and 29,928 level-trapezoid comparisons, all passing
- Other scripts and JSON: finite-product exploratory checks using NumPy and SciPy; they support normalization and orientation, and do not prove the theorem
- `SOURCES.md`, `validation.json`, `SHA256SUMS`: references and artifact verification

Run `python3 checks/verify_rectangle_exact.py` for the exact checks. The optional numerical scripts write their result JSON beside themselves. Run `bash build.sh` to rebuild the PDF.

The continuous and countable statements are proved in the manuscript. The proof uses classical marginalization, convex-order and martingale-coupling results and makes no worldwide priority claim. It is not formally verified or externally refereed.
