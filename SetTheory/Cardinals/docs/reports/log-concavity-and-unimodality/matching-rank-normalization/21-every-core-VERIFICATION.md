# Verification record

## Mathematical scope

The article proves the two shifted conditional Newton inequalities for every genuine 3+3 minimum cover, with unit left activities and arbitrary positive right activities. The ambient lower-gap bound allows arbitrary positive activities on both shores. The higher bound is 21/8, with a checked 75/28 refinement. The full-polynomial conclusion is eventual strict ULC6 under common scaling of the three right-cover activities.

The global rank-six statement, for any chosen minimum cover, also uses the previously proved all-field theorem for covers with a shore of size at most two. It is nonstrict. The eventual-failure bracket [7,38] and finite-activity bracket [6,38] refer to distinct questions.

## Written review

The complete proof and final mathematical transcription received two independent internal review passes. These checked the weighted plane-incidence Hessian, both Schur complements, exact virtual/private support counts, invertible and singular core cases, unit incidence bounds, leading powers of all five gaps, and the rank38 comparison. The refined 75/28 constant was checked separately.

These reviews are ordinary mathematical review within the research task, not external peer review or proof-assistant verification.

## Exact checks

The standard-library verifier checks:

- 960 unit plane-incidence instances
- 960 positive-integer-weighted plane-incidence instances
- 512 exact integer-matrix instances, indexed by every Boolean 3 by 3 core mask
- 38 full endpoint-minor enumerations, independently compared with the virtual-vector coefficient formulas
- Both the 21/8 and 75/28 inequalities
- The ambient lower-gap inequality in every full enumeration

The independently written weighted-plane checker verifies 600 additional cases with three through twelve vectors and activities one through eleven. It reconstructs the line-class counts directly from determinants.

Both scripts and the comparison driver pass under optimized Python, using explicit exceptions rather than removable assertions. The finite checks are supplementary regressions, not the general proof.

## PDF and package checks

The final article is six pages. All pages were rendered and visually inspected. No clipping, overflow, missing glyph, overlapping text or unexplained blank page was found. The TeX build has no overfull/underfull-box warnings or unresolved references. All fonts are embedded.

The package manifest covers all deliverable files other than itself. The archive is checked from a fresh extraction, including exact output comparison. Raw review correspondence and exploratory files are excluded.

