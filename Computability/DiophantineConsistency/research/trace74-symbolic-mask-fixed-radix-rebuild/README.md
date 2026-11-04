# Fixed-radix isolation diagnostic

The [prelaunch review](../../reviews/trace74-mask-isolation-prelaunch-independent/README.md) approved one run. Attempt01 completed with actual outer exit 0 and child status PASS. The [child result](observations/attempt01/result.json) SHA-256 is `cad5eb2a633c763c79e7e2197caed91cc5aacd3e1bde8f9af738ad7f924011e8`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `42f36fac9ed372fe19e717d4a643d3571977eac0c58b4c87a56329073ce8a115`; object SHA-256 is `2232e9d8877bd3b6b854378884d7b5d4df5e62df27d064c1d352f077a931669d`. The [independent result audit](../../reviews/trace74-fixed-radix-result-independent/README.md) passed.

This checks the low-plus-defect identity with base `2^67` while keeping lengths, special index and support symbolic under explicit bounds. It does not establish the concrete mask cover or graph guard. Capture-relative provider and package ancestry limitations remain.
