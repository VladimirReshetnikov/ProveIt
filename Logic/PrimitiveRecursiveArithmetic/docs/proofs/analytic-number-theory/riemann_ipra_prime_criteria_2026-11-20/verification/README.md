# Verification

The Lean version and Mathlib revision are pinned in the project. From its root, run `lake build` and `lake env lean verification/Audit.lean`. The audit prints both theorem types and representative axiom dependencies. `Prf PRAAx` in the type identifies a derivation in the scoped first-order theory. Some standard-model or Mathlib proofs use classical choice in the Lean metatheory. The accompanying report states where the analytic correspondences are proved.

`examples.txt` records the outputs from the four standard-library Python checkers and the single-polynomial input printed in the report. `build.txt` records the successful separate build of the local sources. These checks were run on November 20, 2026.
