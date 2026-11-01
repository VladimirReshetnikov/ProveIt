# Thirty-three-variable degree-six positive-transport candidate

This 143-operation graph replaces the signed `W` pair in the 34-variable degree-six candidate with a single positive coordinate. `generate.py` pins the parent and checks the changed rows, liveness and gate order. `verify_substitution.py` checks all 22 parent residuals under the positive embedding `wPositive = wValueVariable + 1`, `wNegative = 1` as exact sparse polynomials. `verify_degree.py` checks that the residuals have degree at most three and their sum of squares has exact degree six.

`AdaptiveAQ33.shifted_no_zero_iff` now proves positive-shift no-zero equivalence with the 34-variable parent in every IΣ₁ model for arbitrary natural port vectors. It derives the positivity of signed `W` from the actual first-norm and root residuals, and `AdaptiveAQ33.current_no_zero_iff` specializes the result to the exact fixed ports. Both context/literal bindings are definitional, and the 143 Lean gates are checked against the pinned graph. A focused paired replay matched; its [receipt and scope](../../reviews/adaptive-aq33-model-replay/README.md) retain the inherited historical ancestry.

The fixed-port native endpoint is under separate replay preparation, following the 34-native replay. No global minimality is claimed.
