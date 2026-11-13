# Independent source review: factored n6/r11 upper

Source-only PASS for mathematical argument, no Lean replay. Base `7923fcd2ecfb72f02f56b25bb6f4236c639ab059fb25fa04fcde5b1acaa838fd`; upper `2ca0844e5c5c53a2089c03579adcd3914135acbbdcbebc3a7be42ce551093719`. Base matches independently expanded positive D/P polynomials. For t≥T, positivity of D, P and t shows (x⁵t−a¹⁰)t>C, then multiplication by t⁹ gives a¹⁰t¹⁰+Ct⁹<x⁵t¹¹. Nonnegative shifted y6 terms give ky≥x⁵t¹¹; the eleven shifted y11 coefficients and t^j≤t⁹ bound c≤a¹⁰t¹⁰+Ct⁹, contradicting explicit ky<c. No graph or guard claim.

Lean elaboration/resource behavior is untested. In particular, `positivity` on `1≤T`, `mul_le_mul` argument orientation, and high-degree `nlinarith` are potential tactic/instance issues; if needed, supply explicit nonnegative B then linear arithmetic. This is an observation, not a claim of failure or timeout cause.

The author subsequently revised upper source to `b232a0507deff7edd9b3a7c577431399c72b5eadd97cc27ace0abf321a839a0f`, replacing the flagged `1≤T` positivity step with nonnegative B and linear arithmetic. The same mathematical review applies to these latest bytes; all remaining tactic/instance and resource concerns remain untested.
