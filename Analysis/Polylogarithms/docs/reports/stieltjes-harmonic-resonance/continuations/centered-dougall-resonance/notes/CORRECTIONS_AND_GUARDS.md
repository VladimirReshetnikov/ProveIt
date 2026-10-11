# Corrections and guards for integration

No new erratum in the inspected canonical statements was confirmed. The
following are requirements for the new construction, not claims that the
existing material violated them.

## The spectral variable has half the hypergeometric excess

The actual exponent is `-1 - 2*u`. The centered counterterm spectral
argument is `1 + 2*u + 2*j`; its pole has residue `1/2` in `u`.
Every order derivative consequently contributes powers of 2. A direct
copy of the Gauss exponent or its unit-residue counterterm is incorrect.

## Even inverse powers require the centered coordinate

Use `x = n + kappa`, where the four Gamma pairs have arguments
`x+r` and `x+1-r`. The odd terms do not generally disappear in an
uncentered expansion in `n`. The Bernoulli reflection identity proves
parity only after this coordinate choice.

## Vanishing terms must be differentiated as analytic functions

At kappa = b = c = 1/2 and u = -1 + t,

`W_0(-1+t) = 2*Gamma(2-t)/Gamma(t) = 2*t + O(t^2)`.

Thus `W_0(-1)=0`, but `W_0'(-1)=2`. The derivative of the complete
counterterm at n = 0 is 11/6, leaving the required head contribution
1/6. Dropping the zero term before differentiation gives a false identity.

Likewise, `rho_N = 0` does not justify setting the full Taylor series
of `Q_N` to zero. Replace a problematic reciprocal Gamma factor by

`1/Gamma(w+t) = product(w+j+t, j=0..L-1)/Gamma(w+L+t)`

with w+L positive. Expand the finite polynomial and regular Gamma germ.
Never evaluate a Bell formula as zero times a divergent polygamma value.

## Endpoint and primitive claims have stated scope

At z = 1 take the limit of the complete bracketed series. The individual
hypergeometric and polylogarithmic pieces can diverge there. A spectral
continuation value of an individual special function is not automatically
an ordinary endpoint value of its defining power series.

All Euler-primitive endpoints are reduced here for the **first** symmetric
harmonic jet. General higher-jet primitive closure is an open follow-up.
The center-parameter primitive theorem handles every resonance at **zeroth
spectral order**; it is not a claim about all mixed spectral primitives.

## Diagnostics are not proof certificates

The finite asymptotic tails used for numerical checks are not infinite
convergent expansions. The observed residuals do not establish a rigorous
number of correct digits. Exact polynomial assertions check finitely many
instances; the all-order statements rely on the analytic/algebraic proofs.
No proof-assistant formalization or arithmetic independence result is
contained in this package.
