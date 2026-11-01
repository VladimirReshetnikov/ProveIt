# Thirty-two-variable degree-six positive-main-root candidate

This 142-operation graph replaces the signed main-root `D` pair in the 33-variable degree-six candidate with one positive coordinate. `generate.py` pins the parent and checks changed rows, liveness and gate order. `verify_substitution.py` checks all 22 parent residuals under the positive embedding `dPositive = dValueVariable + 1`, `dNegative = 1` as exact sparse polynomials. `verify_degree.py` checks that the residuals have degree at most three and the sum of squares has exact degree six.

`AdaptiveAQ32.shifted_no_zero_iff` now proves positive-shift no-zero equivalence with the 33-variable parent in every IΣ₁ model for natural port vectors with the first port at least 2 in the model. The proof derives positive signed `D` from the actual main-root and supporting residuals. `AdaptiveAQ32.current_no_zero_iff` discharges the first-port bound for the exact fixed ports using a previously checked fixed-beta bound. Both context/literal bindings are definitional, and all 142 Lean gates are checked against the pinned graph. A focused paired replay matched; its [receipt and scope](../../reviews/adaptive-aq32-model-replay/README.md) retain inherited historical ancestry.

The fixed-port native endpoint remains under preparation, following the 33-native replay. No global minimality is claimed.
