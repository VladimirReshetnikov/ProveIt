# Weighted product upper bound

`Trace75ProductPower.whole_product_lt_power` is an arithmetic lemma valid
in every IΣ₁ model. Given `X≥32`, `b≤X²`, and `r≥20`, it proves

`b*(X+2^(2r+1))*(2^(2r+1)*X+1) < X^(r+1)`.

This adapts the earlier product estimate to allow an additional factor of
`X`: the proof uses `s=r−3` and `4r+4<5s`. The theorem has no graph-zero
premise or conclusion and does not alone prove any power or halt identity.

`run-productpower.py`, `observations/productpower-attempt01/`: Lean exit 0,
no warning/error; object `/tmp/trace75-productpower-q28seu81/Trace75ProductPower.olean`,
SHA-256 `2999b26c4638f4d192f3a13784f1da2dd88e6c67f67b3ecbc3c21884dbeeb35e`.
Selected direct imports are pinned; historical provider/transitive and
package ancestry remain inherited limits.
