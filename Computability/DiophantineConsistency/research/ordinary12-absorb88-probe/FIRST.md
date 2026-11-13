# First factor of the 88 candidate

`Absorb88First` binds the actual 88 graph's first residual to its signed pair and extracts its scaled norm from a full graph zero. `Absorb88FirstQuotient` obtains the positive first Pell root when the scale `b=J*beta` is positive. The exact statements are in the Lean sources and apply to every indicated IΣ₁ model. They do not conclude `Bt>0` or a reverse witness map; the explicit counterexamples in the README show why that remains a separate issue.

The guarded author check `run-first.py` passed both stages in fresh session 8745, exit 0; exact source snapshots, commands, selected provider pins, resource samples and results are in `observations/first-attempt01/`. The first source locally suppresses the unused-variable and unused-simp-argument linters. The check inherits package-transitive, dynamic and historical source/object ancestry; no independent Lean replay is claimed.
