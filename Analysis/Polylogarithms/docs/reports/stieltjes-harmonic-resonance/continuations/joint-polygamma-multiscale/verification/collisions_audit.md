# Independent audit of the monomial Stieltjes collision theorem

## Scope and outcome

The audited source is `output/ProveIt_Polygamma_Moments_and_Stieltjes_Resonances_2026-10-12/sections/03_multiscale_collisions.tex`, especially `mc:main`, the mixed contacts `mc:mixed-contact`, the singular contact `mc:singular-contact`, and the two-branch expansion `mc:two-branches`. I rederived these formulas independently from the exact Hurwitz recurrence and the beta integral. I found no sign, factorial, or missing-contact defect in the current theorem and contact formulas. The explicit `q=2` and `q=3` ordinary renormalized limits and both polylogarithmic primitives also check. This is an internal derivation and consistency audit, not external peer review.

During final assembly, the report's author caught a harmless constant-normalization omission in the auxiliary display `mc:harmonic-jets`: the series is the logarithm of `j!/(1-u)_j`, not of `1/(1-u)_j`. The latter would require the additional constant `-log(j!)`. The display has been corrected. All differentiated contact formulas and the exact coefficient compiler already retain the correct factorial normalization and are unchanged. The primitive-verification sentence was also adjusted to describe the actual independent quadrature in `verify_stieltjes_contacts.py`, rather than an unrecorded direct coefficient check.

One clarification was recommended and communicated: after choosing the truncation index `J`, state the spectral-disk condition

`(J+1)(alpha-beta) - beta(r+t+1) - (alpha+beta)eta > 0`.

Together with `eta < min(1, beta/alpha, alpha/beta)` and a small disk preserving the gamma domains, this makes the last uniform-tail estimate explicit. Such a positive disk always exists once `J` is chosen as in the theorem.

## Analytical checks

1. **The reference finite part.** The omitted critical terms are correct: the integral of `x^(-1-u)` on `(delta,1)` is `(delta^(-u)-1)/u`, whose fixed spectral derivatives have no `delta^0 (log delta)^0` coefficient. Removing the entire critical quotient before defining the holomorphic finite-part germ preserves the stated cutoff coordinate.

2. **Mixed contacts.** Direct beta integration gives, for `k<r`,

   `P_r(u) integral_0^infinity x^k (x+a)^(-r-1-u) dx = (-1)^r k! (1+u)_(r-k-1) a^(k-r-u)`.

   The coefficient `k!` cancels the Taylor denominator. At `k=r`, the exact singular contribution is `(-1)^r r! (a^(-u)-A_r(u))/u`; the `A_r` term is necessary and has the sign in the draft. Expansion of the analytic coefficient at its *actual shift* `1+b` then gives precisely `beta ell = alpha(r-k)`. The exchanged condition is also correct and may contribute despite `alpha>beta`.

3. **Uniform remainder.** The Taylor remainder at `1+b` is `O(x^(r+1))`, so after the singular factor it is bounded by `C x^(-eta)`. Replacing the critical coefficient at `1+b` by its value at one costs at most `C b a^(-eta)(1+|log a|)`. This vanishes on a monomial path for `eta<beta/alpha`; the exchanged estimate requires `eta<alpha/beta`. Local uniform convergence on the disk justifies all fixed spectral derivatives by Cauchy's formula.

4. **Singular branch pairing.** Put `A=r+1+u`, `B=t+1+v`, `C=r+t+1+u+v`. The two series in the draft have the correct gamma factors. After multiplication by `P_r P_t`, the first branch has sign `(-1)^(t+1)` and coefficient `Gamma(1-u)Gamma(R+j+u+v)/(u Gamma(1+v)j!)`. The second branch at `k=r+j` has sign `(-1)^t` and coefficient `Gamma(R+j+v)/(u Gamma(1+v)(1-u)_j)`. These are exactly the two summands in `H_j`. Their common base exponent is `j(alpha-beta)-beta R`. The numerator vanishes at `u=0` for every `v` and every fixed `log epsilon`; its removal before differentiation is essential and correct.

5. **Low-index specialization.** With `r=1,t=0`, the baseline `F=ζ(2)` cancels the `-ζ(2)` piece from the critical `A_1` contact. The remaining critical term is `ζ(2)log(mu/lambda)`. The mixed resonance gives `(-1)^(q+1)ζ(q+1)mu^q/lambda` for integral `q>=2`, and the singular contact gives `lambda^j/mu^(j+2) ((j+1)log(mu/lambda)-1)` for `j=2/(q-1)` integral. This reproduces the independent ordered digamma calculation.

6. **First-Stieltjes contact.** For `r=t=0`, `lambda=mu=1`, the two critical contacts vanish identically. Expanding the paired numerator to second order in `u` gives `H_j(u,0)=(H_j^(2)-ζ(2))u+O(u^2)`. Hence `-partial_u H_j(0,0)=ζ(2)-H_j^(2)`, as claimed. The displayed general-amplitude formula also checks.

7. **Primitive.** Differentiating `2ζ(3)-Li_3(z)-2Li_3(1-z)+log(1-z)Li_2(1-z)` gives `(ζ(2)z-Li_2(z))/(z(1-z))`, and its value at `z=0` is zero. The nested-polylog representation has the same derivative and normalization.

## Finite bivariate coefficient compiler

I also checked the two polynomial logarithms in `verification/stieltjes_contacts.py::singular_contact` directly against the meromorphic Gamma expression. Set `R=r+t+1` and `N=R+j`. After taking out the factor

`C=(-1)^t Gamma(N)/j! * lambda^j/mu^(R+j)`,

the singular contact is `C (exp(L)-exp(M))/u`, where the normalized exponentials are exactly

`exp(L)=lambda^(-u) mu^(-v) [j!/(1-u)_j] Gamma(N+v)/(Gamma(N)Gamma(1+v))`,

`exp(M)=mu^(-u-v) Gamma(1-u)Gamma(N+u+v)/(Gamma(N)Gamma(1+v))`.

Thus the first logarithm is

`L=-log(lambda)u-log(mu)v + sum_(h>=1) [H_j^(h)u^h + (-1)^(h+1)H_(N-1)^(h)v^h]/h`.

For the second one, splitting `Gamma(N+w)/Gamma(N)=Gamma(1+w) product_(k=1)^(N-1)(1+w/k)` gives

`M=-log(mu)(u+v) + sum_(h>=1)(-1)^(h+1)H_(N-1)^(h)(u+v)^h/h + sum_(h>=2)ζ(h)[u^h+(-1)^h((u+v)^h-v^h)]/h`.

The three linear Euler-constant contributions cancel exactly. These are precisely the two polynomials formed by the code when truncated at total degree `m+n+1`. At `u=0` both exponentials agree identically in `v`, so extracting the coefficient of `u^(m+1)v^n` performs the removable division by `u`. Multiplication by `(-1)^(m+n)m!n!C` then gives the desired spectral derivatives. The rectangular truncation bounds `(m+1,n)` and exponential loop through degree `m+n+1` preserve this coefficient; terms of greater total degree cannot contribute. No additional numerical run was needed for this algebraic check.

## Independent ordinary quadrature

The executable `identity_audit.py` uses mpmath 1.3.0 at 90 decimal digits. It evaluates the ordered collision integral after *exact* analytic integration of its singular rational pieces. In particular, the remainder is obtained from the ordinary integral formula reproduced in the article, equation `mc:ordered-remainder`, without numerical differentiation in the small parameter. It separately subtracts the finite divergent power-log series and compares the surviving constant with the proposed formula. These are floating-point diagnostics, not interval certificates and not a substitute for the all-index proof.

At `epsilon=10^-9`, the unaccelerated errors in the constant approximants are:

| Exponent ratio and amplitudes | Predicted constant | Approximation error |
|---|---:|---:|
| `q=2`, `lambda=mu=1` | `-1-ζ(3)` | `-6.2472159e-8` |
| `q=3`, `lambda=mu=1` | `-1+ζ(4)` | `-1.9630556e-7` |
| `q=4`, `lambda=mu=1` | `-ζ(5)` | `-1.2073279e-7` |
| `q=5/3`, `lambda=mu=1` | `-1` | `-1.1341081e-3` |
| `q=2`, `lambda=1.3, mu=0.7` | `-21.58185224237367528137...` | `9.3644616e-7` |

Each row was also computed at `10^-3` and `10^-6`; the full values are in `collisions_audit.json`. The slower `q=5/3` error is consistent with the surviving positive exponent `1/3`.

The irrational case `q=sqrt(2)`, `lambda=1.3`, `mu=0.7` illustrates a useful numerical issue rather than a contradiction. Its first retained positive-power kernel term has exponent `5sqrt(2)-7 = 0.071067811865...`. At the displayed scales this term is still hundreds in size; it eventually tends to zero only very slowly because of its logarithm. Removing the first two *vanishing* terms, `j=5,6`, leaves the same constant and gives errors `5.9623974`, `0.02480773`, and `0.0000758097` at the three scales. This directly supports the draft's warning that the constant formula is not a uniform approximation as the exponent ratio approaches a resonance.

## Barnes companion verification

The same script independently evaluates five centered Barnes/logistic moments by direct quadrature on the real line. The normalized mean, absolute second moment, complex second moment, mixed cubic, and absolute fourth moment agree with the exact formulas to absolute error below `3e-91` at the working precision. A separate direct trigamma-square check was added. The mathematical basis is the traditional first Barnes lemma, NIST DLMF 5.13.3; no novelty is claimed for that lemma or for the general practice of parameter differentiation.

`barnes_companion.tex` is the compact input fragment intended for an appendix. `identity_notes.tex` contains that derivation together with the independent low-index collision proof. Quarter-argument values in these files include the corrected difference `psi'(1/2)-psi'(1)=2ζ(2)`.
