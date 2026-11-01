# Twenty-two-variable degree-16 candidate

[equation16.pdf](../../equation16.pdf) presents the circuit and its fixed
constants in base 10. `generate_equation16.py` constructs its TeX from the
pinned graph, and `verify_display16.py` checks the display, all 112 circuit
lines, the fixed-constant block, and two negative mutation controls. Two
`pdflatex` runs produced the same PDF SHA-256
`c94fd7641cac27848330f3f11d573938578c62309a5797bf1618530660956c9c`;
both rendered pages were inspected.

This 112-operation circuit adds four squared constraints to the 17-variable,
99-operation degree-20 circuit. Three new positive coordinates name
`c = eta + Y*(eta+zeta)`, `a = X*Y+Y`, and
`ell = X*Y*Y*(eta+zeta)`. Two more positive coordinates represent the signed
expression `Bt` as their difference. Four squared equations require these new
values to agree with the parent expressions. The circuit is a sum of twelve
squares, so all four constraints must vanish at a zero.

`AdaptiveNamedValues22.shifted_no_zero_iff` establishes the same no-zero
statement as the 17-variable parent for every integer port vector in every
model of IΣ₁. The reverse construction chooses the positive natural values
for the first three names and the two signed-pair components plus one for
`Bt`. The [paired model replays](../../reviews/adaptive-square-sums22-model-replay/README.md) match on a historical provider. The [native iPRA endpoint](../../Lean/DiophantineConsistency/IPRANamedValues22Native.lean) has a matching [guarded replay](../../reviews/ipra-named22-native-verification/README.md) on a historical provider. It uses the chosen mapped ZFC-refutation predicate; the shared project, package, and dynamic-import ancestry remains inherited.

`generate.py` deterministically builds the 112-row candidate from the pinned
17-variable graph and checks graph liveness. `verify_literal.py` matches the
22-variable Lean literal, all four ports, and every row to the candidate.
`verify_degree.py` independently expands each residual with integer sparse
polynomials. Their degrees in the 22 unknowns are
`[8, 8, 6, 6, 8, 4, 3, 4, 2, 2, 4, 2]`. The sum has exact degree 16: its
leading degree-16 part is a sum of squares and one degree-8 residual has an
explicit coefficient −1. A positive-variable shift preserves exact degree.
These finite Python checks are not Lean degree theorems. The metrics are
candidate-specific, with no global minimality claim.
