# Thirty-five-variable degree-six equation

This 145-operation graph substitutes `V²` for `squareVariable` in the
36-variable parent, removing its defining residual square and accumulation
gate. `generate.py` pins the parent and verifies the changed rows, liveness and
topological order. `verify_substitution.py` checks all 23 parent residuals as
exact sparse integer polynomials under the substitution, with the removed
residual becoming zero. The remaining 22 residuals have degree at most three,
and `verify_degree.py` checks exact degree six.

Unlike the four substitutions in the parent, `V²` is not positive for every
positive input. The zero-set argument derives `V ≠ 0` from the
auxiliary residual: with `Q > 0` and `y² > 0`, its equation
`y² - Q*(y² - V²) - 1 = 0` is impossible if `V = 0`. This is proved in the
model transport; it does not make the substitution a valid positive valuation
map for arbitrary inputs.

The graph is bound to a Lean literal, and `AdaptiveAQ35.shifted_no_zero_iff`
proves its no-zero equivalence to the 36-variable parent in every IΣ₁ model
for arbitrary integer ports. Its [native endpoint](../../Lean/DiophantineConsistency/IPRAAQ35Native.lean)
has a [matched ten-module replay](../../reviews/adaptive-aq35-native-replay/README.md).
The preceding 36-to-40 step requires a nonnegative first port, discharged at
the fixed ports. The endpoint uses the mapped Foundation refutation predicate;
its identification with Con(ZFC) uses the separate interpretation and
refutation bridge. Historical project, package-transitive and dynamic-import
ancestry remain inherited. No minimality is claimed.

The [base-10 presentation](../../equation6-35.pdf) uses separately named
positive variables. `generate_equation6_35.py` creates its TeX and
`verify_display6_35.py` checks 44 definitions, 22 residuals, 145 circuit rows,
fixed constants and mutation controls. Two clean PDF builds matched SHA-256
`8d39b9411e005cb9e98d30ae55092d51d19da8218a28a93d947a5ee10b8cde99`.
