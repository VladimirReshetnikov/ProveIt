# Literal adaptive zero from factor units

`zero_of_factor_units` proves that if the four actual syntax factors represent `+1`, their actual unshifted expression is zero for arbitrary integer ports in every model of the stated `IΣ₁` assumptions. `shifted_zero_of_factor_units` converts a positive unshifted witness to the shifted natural equation. Both theorems report `[propext, Classical.choice, Quot.sound]`.

The four factor-unit hypotheses are explicit. This theorem does not establish them for the constructed witness, instantiate Assembly, or prove an HA proof-existence theorem.

The author build passed at `/tmp/adaptive-construction-factor-zero-qe79l53i` against `/tmp/adaptive13-assembly-recomposed-q9s50zdl`. The [18-file evidence manifest](adaptive-construction-factor-zero2011-author-evidence/FILES.json) has SHA256 `bd2f29b3c7a5ac37323b17b886ab59a101ff1267a42270dd2b3c2228ea46f6da`; it includes the first failed shifted-expression rewrite, the corrected build, source snapshots, logs, timings, driver and provider/guard records. To replay set `ADAPTIVE_ASSEMBLY_BASE` to the authenticated composition and run `success/driver.py`; canonical and package boundaries remain inherited.
