# Generic syntax-context bridge for the 87-gate rewrite

A separate Lean source/check pair passed for arbitrary `Expr.subst` contexts over any commutative semiring. It proves that substitutions with equal split-natural values give equal split-natural values for the whole expression, then applies the earlier local root identity under any one-hole `Expr` context and preserves its split zero test. This does not assume cancellativity or positivity and is valid for arbitrary formal signed subexpressions.

The generic substitution theorem reports no axioms; the root-context split and zero-test theorems report only `propext`. The first build attempt failed because the simplifier did not match expression constructors to the notation-based lemmas; its source snapshot and diagnostics are preserved. The corrected build uses explicit constructor-to-notation changes and rewrites. It passed without warnings.

The [19-file author evidence manifest](adaptive-first-root-factor87-context-author-evidence/FILES.json) has SHA256 `72b9fba49413b22748505f328b95b9a6e176411beb2f84f3dc204f85961e087a`. It preserves both attempts, their source/log/timing records, driver, provider metadata and input state. The author provider is `/tmp/adaptive-first-root-factor87-context-4d9yb1po/lib`. For independent replay, set `ADAPTIVE_FACTOR87_SYNTAX` to the independently replayed syntax-provider directory and run `success/driver.py` from the evidence packet. Package/toolchain internals and the accepted canonical base remain inherited boundaries.

The specific 88-row maintained expression and 87-row candidate have not yet been identified as substitutions into a shared one-hole context by a Lean theorem. This packet does not change the maintained equation or establish a syntactic HA proof.
