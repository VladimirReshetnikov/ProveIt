# Thirty-three-variable degree-8 candidate

The graph extends the degree-12, 26-variable graph with positive variables `zPositive`, `zNegative`, `dPositive`, `dNegative`, `vPositive`, `vNegative`, and `deltaVariable`. It replaces Z, Dstar, and V by their signed differences and Delta by `deltaVariable`; four further squared residuals constrain these names to the former expressions. The graph has 139 binary arithmetic operations.

`verify_degree.py` checks the 20 residual polynomials exactly and obtains maximum residual degree 4, hence degree 8 for their sum of squares after fixing the four port constants. It verifies a degree-4 residual term with a nonzero fixed-port-independent coefficient, so the highest homogeneous component of the sum of squares cannot vanish. The positive shift preserves the degree. `verify_lean_graph.py` compares the variables, ports, all 139 literal gates, and output against `AdaptiveNamedValues33.literal`.

`AdaptiveNamedValues33.shifted_no_zero_iff` establishes, in Lean and uniformly in every IΣ₁ model, equivalence of the shifted no-zero statements for this literal and its 26-variable parent for every integer port vector. The reverse witness construction represents each signed expression with two positive variables by adding 1 to both components of its signed evaluation, and proves the discriminant expression positive. The matching focused model replay is in `reviews/adaptive-square-sums33-model-replay`.

The model replay shares its historical model-26 peer provider; project/package-transitive ancestry and dynamic imports remain inherited. This is not a complete current-source closure. The fixed-port native-theory endpoint and the separate identification of its mapped refutation predicate with Con(ZFC) must be assessed separately.
