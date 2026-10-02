# Independent audit of the fixed-power family extension

1 October 2026. Mathematical outcome: APPROVED for every fixed real alpha>0 and integer beta>=0. The source FIXED_POWER_FAMILY.md is pinned separately in family_approval.json. Its asymptotic, exact-saddle and inverse statements are valid. No uniformity at alpha=0 or as beta grows is asserted.

## Checks of the ordinary argument

The weighted slot injection is genuinely injective for arbitrary positive real alpha. The target has a unique newly occupied largest slot; its label recovers the moved slot. The remaining occupied slots and labels do not change. Its weight increases strictly, proving the monotonicity required for discrete inversion without relying on an integer-color interpretation.

Set d=beta+1. Choosing delta<min(1/2,d/(2alpha)) ensures both alpha*delta<d and d+r-alpha+alpha*delta<d+r for every r>=0. Thus the small-k exponent max(alpha*delta,d+r-alpha+alpha*delta) is strictly below d+r, including logarithmic borderline sums. The same estimate works for integral tails away from zero; the bounded neighborhood of zero is integrable for beta>=0. This fixes the difficulty that the simple half-range bound for alpha=1 would not handle every large alpha.

The boundary window still has length comparable to m/log m, but each k contributes k^beta independent Bernoulli slots. Accordingly the effective size is W=m^d/log m, V is comparable to m^2 W, and cumulants of fixed order r>=2 are O(m^r W). The analytic-disk proof from the approved single-slot note remains valid with a harmless alpha-dependent modification: on k>2m the tilted factor is O(m^(-alpha)), rather than O(m^(-1)). It still tends uniformly to zero and gives the required convergent logarithm and derivative bounds. This clarification does not change the submitted theorem.

The modulus bound multiplies the active-window sine-square sum by a positive multiple of m^beta. Its noncentral suppression is exp(-c m^d/log^3 m); its central Gaussian cutoff and weighted Taylor argument are exactly those of the approved exact-saddle proof with w replaced by W. In particular the error really is O(W^(-R-1)), rather than an inverse power of the unweighted window length.

For the sum-integral estimates, the absolute derivative of x^beta log(1+exp(g)) is controlled by beta times the corresponding positive integral with power beta-1, plus x^beta |g'|p. This is O(m^beta log m). The derivative of x^(beta+1)p is controlled by (beta+1)x^beta p plus x^(beta+1)|g'|p(1-p), giving O(m^(beta+1)). For beta=0 the first estimate follows directly from unimodality. Both errors are smaller than the main scales divided by every fixed power of log m.

Direct integration gives

f_hard=alpha m^d[L/(d(d+1))-1/d^2].

The inverse-function derivative formulas include the correct alpha powers. The second derivative of x(v)^beta x'(v) is O(m^d/L^3), and the first derivative of x(v)^(beta+1)x'(v) is O(m^(d+1)/L^2). Even/odd kernel cancellation therefore gives the claimed thermal term and saddle displacement. The exact identity

Q0'(m)=alpha(L-1)[m^(d-1)/(d+1)-n/m^2]

implies Q0''(m0)=alpha(L0-1)m0^(d-2). Its displacement cost is O(m0^d/L0^3), the same order as the retained remainder.

The entropy derivative is alpha m^(d-1) log m. Writing u=m^d transforms the inverse equation to u(log u-1)=d^2 s/alpha, so the Lambert-W normalization is correct. The relative perturbation of m is -pi^2/[6 alpha^2 L(L-1)], and raising m to power d+1 gives the displayed inverse coefficient. The quadratic correction to that power is already within O(L^(-4)). Integer rounding is negligible for this inverse-log statement.

The derivative signs and normalization for the exact-saddle inverse also agree with the approved single-slot proof: the error in the logarithmic approximant is O(W^(-R-1)), its derivative is asymptotic to t, and the pre-rounding uncertainty is O(W^(-R-1)/t). This may be smaller than one; it is an interval for the real threshold followed by integer rounding, not an unconditional exact rounding rule near an integer.

## Source boundary and finite corroboration

The reviewer directly verified the A022629 and A092484 product definitions in primary OEIS pages, and A092484's December 27, 2020 logarithmic conjecture. A266891's product and the thesis-scope discussion require the separate source-screening evidence before publication; this is not an analytic dependency of the family theorem. No literature-wide novelty is approved here.

The independent standard-library check_family.py compares 819 coefficients from two exact constructions for nine integer-parameter pairs, verifies 801 strict monotonicity cases, and checks 900 rational identities for the hard integral, inverse derivatives, and stationary second derivative. Its real-alpha parameter tests include alpha=1/3. These checks are supplementary to the ordinary argument, not a finite proof of the infinite theorem. Disabled assertions are rejected.
