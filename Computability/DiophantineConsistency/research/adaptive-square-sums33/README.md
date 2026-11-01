# Thirty-three-variable degree-8 candidate

[equation8.pdf](../../equation8.pdf) presents the circuit and fixed constants
in base 10. `generate_equation8.py` constructs the TeX from the pinned graph;
`verify_display8.py` checks the display, 139 gates, fixed constants and two
mutation controls. Two `pdflatex` runs produced identical PDF SHA-256
`ffdb16f7dec72d09f2665c5388676ac5c0c62d28cec68861b3d8bfb5d9f7165c`;
both pages were inspected.

The graph extends the degree-12, 26-variable graph with positive variables `zPositive`, `zNegative`, `dPositive`, `dNegative`, `vPositive`, `vNegative`, and `deltaVariable`. It replaces Z, Dstar, and V by their signed differences and Delta by `deltaVariable`; four further squared residuals constrain these names to the former expressions. The graph has 139 binary arithmetic operations.

`verify_degree.py` checks the 20 residual polynomials exactly and obtains maximum residual degree 4, hence degree 8 for their sum of squares after fixing the four port constants. It verifies a degree-4 residual term with a nonzero fixed-port-independent coefficient, so the highest homogeneous component of the sum of squares cannot vanish. The positive shift preserves the degree. `verify_lean_graph.py` compares the variables, ports, all 139 literal gates, and output against `AdaptiveNamedValues33.literal`.

`AdaptiveNamedValues33.shifted_no_zero_iff` establishes, in Lean and uniformly in every IΣ₁ model, equivalence of the shifted no-zero statements for this literal and its 26-variable parent for every integer port vector. The reverse witness construction represents each signed expression with two positive variables by adding 1 to both components of its signed evaluation, and proves the discriminant expression positive. The matching focused model replay is in `reviews/adaptive-square-sums33-model-replay`.

The model replay shares its historical model-26 peer provider; project/package-transitive ancestry and dynamic imports remain inherited. This is not a complete current-source closure. The [native iPRA endpoint](../../Lean/DiophantineConsistency/IPRANamedValues33Native.lean) has a matching [guarded replay](../../reviews/ipra-named33-native-verification/README.md) on a historical provider. It uses the chosen mapped ZFC-refutation predicate; the shared project, package, and dynamic-import ancestry remains inherited.
