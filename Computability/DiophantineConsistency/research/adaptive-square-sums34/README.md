# Thirty-four-variable degree-six equation

This 144-operation graph replaces the signed `Z` pair in the 35-variable parent by one positive coordinate. `generate.py` pins the parent and checks the changed rows, liveness and gate order. `verify_degree.py` checks that the 22 residuals have degree at most three and that their sum of squares has exact degree six. `verify_substitution.py` checks all parent residuals under the positive embedding, while `verify_orientation.py` checks the exact polynomial identity for the negative-root orientation.

`AdaptiveAQ34.shifted_no_zero_iff` now proves, in every IΣ₁ model and for arbitrary integer ports, that the positive-shift 34-variable literal has no zero exactly when the corresponding 35-variable literal has no zero. Its proof obtains the positive magnitude of `Z` from the first residual and adjusts `r` when the signed root is negative. The exact 144-gate Lean literal and both context bindings are checked, and a focused paired 13-module replay matched; its [receipt and scope](../../reviews/adaptive-aq34-model-replay/README.md) retain the inherited historical ancestry. The 35-variable parent has a matched native endpoint on that historical provider.

The fixed-port `IPRAAQ34Native.literal_equivalence` now proves the candidate-native equivalence to mapped Foundation ZFC refutation negation. Its [focused native replay](../../reviews/adaptive-aq34-native-replay/README.md) matched, with inherited historical ancestry. No global minimality is claimed.

The [base-10 presentation](../../equation6-34.pdf) has separately named
positive variables. `generate_equation6_34.py` creates the TeX and
`verify_display6_34.py` checks 43 definitions, 22 residuals, 144 circuit rows,
fixed constants and mutation controls. Two clean PDF builds matched SHA-256
`f4dacb67fd82c1323a2fba080eab6d9332babdb6f1649ee01fb900911b1514e3`.
