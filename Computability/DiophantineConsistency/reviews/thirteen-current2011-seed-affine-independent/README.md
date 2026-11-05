# Independent review: natural seed and affine carrier helpers

The checked `natural_seed` theorem applies in an IΣ₁ model to parameters `a, R, b, c` under `b > 0`, `c > 0`, `R % 4 = 3`, and `c = ycoord R a`. It composes `strong_index` and `auxiliary_seed_of`, producing the stated positive natural seed and auxiliary witnesses with their equalities and residue. Actual outer session 49737 and both Lean runs exited 0.

The checked `positive_affine_carrier` theorem applies in an IΣ₁ model given the exact positive `b`, positive ring element `G = ι b * g`, residue witness `y + 1 = 4*b*e4`, and signed absolute-value bound in its source; it returns a positive ring carrier satisfying the displayed affine equation. Actual outer session 68312 and both Lean runs exited 0. Neither conditional helper proves the completion or an iPRA endpoint.

Earlier attempts 98597 and 86952 failed: their logs report unresolved `absdiff` and `modelFacts`, respectively, and include `sorryAx` in their axiom reports. The corrected natural source differs only by opening `ArithmeticPellHalfIndex`; the corrected affine source differs only by opening `FreshCarrierSpheres`. Both successful reports list only `propext`, `Classical.choice` and `Quot.sound`.

The checker verifies exact source changes, hashes, actual outer and nested exits, compilation logs and successful objects, all 100 recorded direct guards and 1,025 overlay symlinks for each attempt. It does not rerun Lean, and these checks inherit the provider base rather than rebuilding its complete dynamic/transitive ancestry. Run the checker using Python 3.
