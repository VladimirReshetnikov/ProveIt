# Fixed-index isolation diagnostic

The [prelaunch review](../../reviews/trace74-mask-isolation-prelaunch-independent/README.md) approved one run. Attempt01 completed with actual outer exit 0 and child status PASS. The [child result](observations/attempt01/result.json) SHA-256 is `10bb0bb2110d3255326fb78b3dc207b7cc2c1fac821596305e1a441289637cf8`; the [outer receipt](observations/outer-attempt01/terminal.json) SHA-256 is `e984190e70e2d09deeb5f40c57b30af0065fc3bbef103efd767dfde657ffec35`; object SHA-256 is `2861e8ade4581abb1eade8b4fb45b738fc9c8a0d59a71ab265532d7b311ef728`. The [independent result audit](../../reviews/trace74-fixed-indices-result-independent/README.md) passed.

This checks the low-plus-defect identity with indices 3297, 8807 and 1063 while keeping the base and support symbolic under explicit bounds. It does not establish the concrete mask cover or graph guard. Capture-relative provider and package ancestry limitations remain.
