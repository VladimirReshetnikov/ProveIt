Shifted twelve-positive-variable norms

Recommended product: positive12_shift_b_product.json, 111 operations, exact degree1041.
Recommended system: positive12_shift_b_system.json, three equations,107 operations,maxdegree1032.
Simplest evaluator: positive12_shift_base_product.json,110 operations,degree1081; system106ops.
Lowestdegree here: positive12_shift_half_aux_product.json,124operations,degree1022; system120ops,max1013.
Other three tradeoffs:114/1033,116/1025,119/1023. See SHIFTED12_PROOF.md for complete definitions,
soundness, strictpositive completeness, and exact leading-degree proofs.

All coefficients must be a single complete tuple supplied by the enclosingrelease's binding.
The upstreambinding is provenance only and is not a license to mix port values.

Run python3 check_shifted.py to verify frozen packets. NumPy required for exact small-prime
polynomial convolution; maximum arrays below2200 terms, so int64 convolution remains safe.
Run python3 build_shifted.py to regenerate the twelve JSON packets.
Programs are locallyauthored; upstream executable text is stored with .inert suffix and notused.
No new Lean/Rocqcertificate, consistencyproof, globalminimality, or accepting computation is claimed.
