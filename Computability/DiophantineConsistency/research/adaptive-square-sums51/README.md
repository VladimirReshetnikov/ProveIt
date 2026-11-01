# Fifty-one-variable degree-4 candidate

[equation4.pdf](../../equation4.pdf) presents this circuit and its fixed
constants in base 10. `generate_equation4.py` constructs the TeX from the
pinned graph; `verify_display4.py` checks every displayed definition, all
187 gates, the fixed constants and mutation controls. Two `pdflatex` runs
produced the identical PDF SHA-256
`b33a646de5629f06ad9f41549db32fa94f408374fe8e001789bbaf423a10dea1`;
both pages were inspected.

This 187-operation circuit extends the 42-variable degree-6
candidate with five positive names and two signed names represented by four
positive coordinates. The seven names stand for `delta*n`, the rank seed,
`Y*k`, `k*W`, `X+a*c`, `varphi*gamma`, and `T*c`. Seven squared constraints
bind them to their old expressions. The graph is a sum of 35 squares.

`generate.py` deterministically builds the graph from the pinned parent and
checks liveness. `verify_degree.py` expands all 35 residual polynomials,
checks the newly added square-sum wiring, and finds all residuals have degree
at most two in the 51 unknowns. One degree-two residual contains a monomial
with port-independent coefficient 1. Its sum of squares therefore has exact
degree 4, including after positive-variable shifting. These finite Python
checks are not Lean degree theorems.
An exploratory direct `rfl` attempt at the concrete syntactic degree bound
timed out at 12 million heartbeats; its [failure record](../../reviews/quartic51-degree-structural-attempt/README.md)
suggests using a shared gate certificate instead of reducing the full tree.

`verify_literal.py` matches the actual Lean literal and all 187 gate rows to
the pinned graph. `AdaptiveNamedValues51.shifted_no_zero_iff` proves both
positive-zero directions in every IΣ₁ model, for every integer port vector.
The [paired model replay](../../reviews/adaptive-square-sums51-model-replay/README.md)
matched on a historical provider.

The [native iPRA endpoint](../../Lean/DiophantineConsistency/IPRANamedValues51Native.lean) has a matching [guarded replay](../../reviews/ipra-named51-native-verification/README.md) on a historical provider. It uses the chosen mapped ZFC-refutation predicate; the shared project, package, and dynamic-import ancestry remains inherited. No global minimality claim is made.
