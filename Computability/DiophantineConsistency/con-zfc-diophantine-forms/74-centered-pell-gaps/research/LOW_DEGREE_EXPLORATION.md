# Low-degree branch: checked observations and limits

Snapshot inspected: ProveIt `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49`,
under `Computability/DiophantineConsistency/con-zfc-diophantine-forms`.

## Verified baseline comparison

Source 64 supplies a quartic in 41 unrestricted integer variables and 26
quadratic residuals. Its proof first establishes absolute-radix bounds,
recovers the Pell power, and only then recovers the radix sign.
Source 62 supplies sextic and octic companions in respectively 35 and 30
unrestricted integer variables. Its reductions include a Pell-root shear
and relocation of a square guard.

Combining these methods does **not** immediately yield 34 and 29 variables.
One of source 62's eliminations deletes its explicit square-scale register;
source 64 has already removed that register. Counting it again would be a
double subtraction. The straightforward combined companions still have
35 and 30 variables.

## A valid but modest equal-count simplification

The octic companion of source 64 may use exactly the factored rows of
source 62's `octic30_readable.json`, with the following coordinated changes:

* Replace its two scale-root variables by `u,w`.
* Replace every `8*rho^2` by `2*u^2`.
* Replace its scale equation by `2*u^2-4*w*q=0`.
* Replace its transport equation by `(K0+4*w)*C-F-z*(q-1)=0`.

The whole source-64 coefficient tuple is retained. These replacements are
obtained by the same triangular eliminations from the literal source-64
quartic, and its scale and transport residuals have degree two instead of
three. The total degree is still eight and the number of unknowns still
30. No claim that this is the optimal circuit at that point is made.

## Approaches that did not establish a further reduction

An index quotient can be absorbed into a rational principal-root carrier,
but at octic degree the principal root must be supplied as a register.
That register cancels the apparent saving unless another norm cancellation
is found. Squaring the carrier directly raises the degree and does not
prove an octic improvement.

Deleting the global twice-square guard is not justified by the existing
argument. If the global power coordinate is negative, the relevant Pell
parameter is the absolute value of a negative integer and its recurrence
introduces rank-dependent signs. The simple nonnegative-power proof cannot
be applied unchanged. No valid guard deletion was established here.

These observations identify limits of the attempted reductions. They are
not claims of impossibility for other constructions.

## Independent centered-norm algebra

Let `D=f0^2+e`, `x=n+f0+V`,

    B = 2*(Q-1)*x,
    H = (Q-1)*(n^2+2*V*n+e)-V^2+1,
    A = (Q-1)*(x^2+D)-Q*V^2+1.

Then `A=H+B*f0` exactly and hence

    A^2-B^2*D = H^2+2*B*f0*H-B^2*e.

The attached independent sparse-polynomial check verifies both identities
using exact integer coefficients and the Python standard library.
For evaluation, `(H+B*f0)^2-B^2*D` takes six binary operations after its
inputs are available; the centered form is preferable for proving the
degree cancellation.

There is a second exact divisibility identity. If
`V=D*Z-c` and `Q=Delta*(D-1)`, then

    A = G-(Delta+1)*x^2
        + D*(Delta*x^2 + Delta*D - Delta - 1
             - Delta*D^2*Z^2 + Delta*D*Z^2
             + 2*Delta*D*Z*c - 2*Delta*Z*c - Delta*c^2),
    G = 1+Delta*c^2.

Thus `A` is congruent to `G-(Delta+1)*x^2` modulo `D`.
This does not itself permit deleting a quotient or dividing a residual by
`D`; such a change needs a separate equivalence proof. No further degree
improvement is claimed from this observation.

All conclusions concern literal polynomial algebra and the inspected
written reductions. They do not constitute a new end-to-end formal proof
of an instantiated consistency equation.
