# Entire-product exponential comparison

`Direct80ProductPower.whole_product_lt_power` proves in every indicated IΣ₁ model that, for `X≥32`, `b≤X`, and `r≥15`, setting `t=2^(2r+1)` gives `b*(X+t)*(tX+1)<power X (r+1)`. The proof bounds the left side by `X³(t+1)²`, then uses `(t+1)²≤2^(4r+4)<32^(r−2)≤X^(r−2)`. It does not assume `X=t` or cancel any factor.

Self-pinning guarded author `run-power.py`, `observations/power-attempt02/`, passed in session 18173 with output `/tmp/absorb89-chain-l1zbfrb0/lib/Direct80ProductPower.olean`; attempt01 failed due a missing `ArithmeticPow` import and an exponential rewrite, and is retained. Exact source, selected project pins, resource samples and output are recorded. The theorem is abstract and does not itself supply the graph-side `X≥32`, `r≥15`, `b≤X`, or `power X (r+1)<H` hypotheses. Full package/dynamic and historical source/object ancestry remain inherited; no independent Lean replay or endpoint is claimed.
