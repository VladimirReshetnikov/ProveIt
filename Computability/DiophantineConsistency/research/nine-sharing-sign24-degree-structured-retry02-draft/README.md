# Sign24 compositional degree closed-reduction retry

The preceding residual check failed because `decide` refuses a goal with the
free port vector `p`, even though syntax degree ignores constant coefficients.
This source-only retry reduces each residual's degree definitionally via
`change` to a closed numeral inequality, then uses kernel `decide`. It does not
evaluate concrete port values or replace them with guessed numbers: `p`
remains arbitrary, and the kernel must check the definitional equalities.
The same local heartbeat and guarded resource limits apply.

This proposes only a Lean polynomial degree upper bound of eight, not exact
degree or external JSON/PDF correspondence. The proof is uncompiled; a fresh
prelaunch review and assigned Lean slot are required.
