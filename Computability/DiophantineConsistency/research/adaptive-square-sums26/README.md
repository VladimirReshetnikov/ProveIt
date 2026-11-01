# Twenty-six-variable degree-12 candidate

This 124-operation circuit adds four squared constraints to the 22-variable,
degree-16 circuit. Four new positive coordinates name `q^3`, `(X*Y)*q`,
`f^2`, and `c^2`. The constraints require each coordinate to agree with its
expression. The 16-square structure forces all four constraints at every
zero, while positivity of the named expressions supplies the reverse witnesses.

`AdaptiveNamedValues26.shifted_no_zero_iff` establishes the same no-zero
statement as the 22-variable parent for every natural port vector in every
model of IΣ₁. `current_no_zero_iff` specializes it to the actual fixed ports.
The [paired model replays](../../reviews/adaptive-square-sums26-model-replay/README.md)
match on a historical provider. The native iPRA endpoint and its own replay
remain separate work.

`generate.py` deterministically builds the 124-row candidate from the pinned
22-variable graph and checks graph liveness. `verify_literal.py` matches the
26-variable Lean literal, all four ports, and every row to the candidate.
`verify_degree.py` expands the residuals as exact integer sparse polynomials;
their degrees in the 26 unknowns are
`[6, 6, 5, 4, 6, 2, 3, 4, 2, 2, 4, 2, 3, 3, 2, 2]`. The sum has exact
degree 12: its degree-12 homogeneous part is a sum of squares and one
maximum-degree residual has an explicit coefficient 1. A positive-variable
shift preserves exact degree. The Python checks are not Lean degree theorems.
These metrics are candidate-specific; no global minimum is claimed.
