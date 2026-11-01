# Thirty-four-variable degree-six orientation candidate

This 144-operation graph replaces the signed `Z` pair in the 35-variable parent by one positive coordinate. `generate.py` pins the parent and checks the changed rows, liveness and gate order. `verify_degree.py` checks that the 22 residuals have degree at most three and that their sum of squares has exact degree six. `verify_substitution.py` checks all parent residuals under the positive embedding, while `verify_orientation.py` checks the exact polynomial identity for the negative-root orientation.

`AdaptiveAQ34.shifted_no_zero_iff` now proves, in every IΣ₁ model and for arbitrary integer ports, that the positive-shift 34-variable literal has no zero exactly when the corresponding 35-variable literal has no zero. Its proof obtains the positive magnitude of `Z` from the first residual and adjusts `r` when the signed root is negative. The exact 144-gate Lean literal and both context bindings are checked, and a focused paired 13-module replay matched; its [receipt and scope](../../reviews/adaptive-aq34-model-replay/README.md) retain the inherited historical ancestry. The 35-variable parent has a matched native endpoint on that historical provider.

The native endpoint for this candidate is under separate replay. No global minimality is claimed.
