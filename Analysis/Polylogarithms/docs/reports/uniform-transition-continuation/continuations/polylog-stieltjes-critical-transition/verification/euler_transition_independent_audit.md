# Independent audit of the near-critical Euler transition

Audited source: `agent_euler/near_critical_transition.tex`, including its final small-`T` majorant, numerical table, and integer-index corollary. The inherited phase statement was checked against `agent_euler/03b_phase.tex`.

## Conclusion

No substantive mathematical flaw was found in the theorem or its proof. The argument supplies the parameter-uniform estimate needed to promote the pinned repository's conjecture `research:conj:crossing` to a theorem. The conclusions are uniform for `b` in a fixed compact subinterval of `(0,infinity)` and for fixed derivative order. They do not establish uniformity when `b` tends to either endpoint or when the derivative order grows.

## Points independently checked

1. The compensated fractional derivative formula has the stated signs and remains legitimate when the seed density has its integrable singularity at zero. The moment expansion keeps the essential factor `epsilon` in its algebraic remainder. The seed density must be retained separately because it supplies the exponentially small contribution competing with the algebraic term.
2. The first two seed moments are `m0=b*zeta(b+1)` and `m1=b*(b+1)*zeta(b+2)/2`. Their signs and normalization agree with the density expansion.
3. Under `t=sqrt(s)*exp(-T)` and `L=(log s)/2`, the kernel becomes Gaussian to the required order. The logarithmic moments have the signs claimed in the two coefficients: `alpha=psi(r+1/2)/2+m1/m0` and `beta=b-b*psi(r+1)/2`.
4. The two error estimates in the joint-window lemma are separate, relative estimates. In particular the `epsilon*exp(-T/2)` density error is negligible relative to the algebraic contribution uniformly for `lambda/2 <= L <= 2*lambda`; it need not be compared solely with the smaller exponential contribution throughout this window.
5. The explicit local majorant added during review,

   `C_B*(T^(-epsilon0)+T^(b_min-1-epsilon0))*(1+abs(log T))`,

   is integrable, including after multiplication by any fixed logarithmic power. Together with `q(T)^s <= exp(-exp(L))` on the lower tail and the central/upper estimates, it closes the parameter-uniform tail argument.
6. The root-balance constant is

   `K=b*Gamma(b+1)*zeta(b+1)*Gamma(r+1/2)/Gamma(r+1)`.

   The first correction is `delta=beta-alpha`. The displayed expansion of the logarithmic root, its exponentiation, and the correction to the negative Lambert branch all have the stated coefficients and signs.
7. For `r=0`, the correction simplifies to

   `delta=b+(b+1)*EulerGamma/2+log(2)-(b+1)*zeta(b+2)/(2*zeta(b+1))`.

8. The scale and height normalization give the limit `x^(-1/2)-x^(-1)`. Differentiating the exact integral establishes the claimed convergence in each fixed `C^m` norm on compact positive intervals. The derivative-root ratios are `[4^r/binomial(2*r,r)]^2`.
9. The inherited one-crossing theorem identifies the locally isolated asymptotic roots as the unique global roots. Likewise the inherited strict increase/decrease identifies the global maximum, so that compact profile convergence is not being used to assert a global conclusion without additional control.
10. The integer maximum is attained at one of the integers adjacent to the continuous maximum. The first strictly positive integer comparison is `floor(nu0)+1`, including the case in which the continuous root is itself an integer.

## Numerical and editorial scope

The independent exact-density quadrature is useful corroboration and is correctly labeled as floating-point diagnostics, not certified enclosures or a proof premise. The theorem itself has no effective numerical bound on its asymptotic error for a specified finite `epsilon`. A missing TeX `\log` and an invisible character were corrected during review. No other change to the source's mathematical claims was required.

Auditor: the Stieltjes/Lerch research subagent, independently from the author of the Euler-transition section.
