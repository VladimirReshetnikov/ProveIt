# Nonzero transport quotient from rank growth

The all-model theorem `radix_le_multiplier` proves `q ≤ w` from `q=exp u`, `exp R=q*w`, and `2*u≤R`. The theorem `transport_quotient_positive` then proves `1≤q*(z-1)` from the unscaled transport equation, positive `q` and gap `C`, `F<q`, and `q≤w`. This supplies the positivity premise needed by the conditional first-carrier construction once these hypotheses are connected to the actual Assembly. Both theorems report `[propext, Classical.choice, Quot.sound]` in Lean.

The rank-growth and actual transport hypotheses are explicit. This does not itself invoke Assembly, construct a thirteen-variable zero or prove an HA proof-existence theorem.

The author build passed at `/tmp/adaptive-construction-transport-positive-12u3bo39` against `/tmp/adaptive13-assembly-recomposed-q9s50zdl`. The [11-file evidence manifest](adaptive-construction-transport-positive2011-author-evidence/FILES.json) has SHA256 `9bfaf4700a7dba7a3f86490dcd8a3e24941d74482fa2b0b76d5a11d744f0d163`, and contains source snapshots, full logs and timings, driver, provider metadata, canonical state and guards. For replay set `ADAPTIVE_ASSEMBLY_BASE` to the accepted composition and run `success/driver.py`; the canonical and package boundaries remain inherited.
