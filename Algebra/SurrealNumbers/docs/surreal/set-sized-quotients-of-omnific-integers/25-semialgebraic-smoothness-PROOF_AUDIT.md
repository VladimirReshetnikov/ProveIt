# Proof audit and verification boundary

This is an internal written-proof review, not an independent referee report.

## Core rigidity checks

1. **Cofinality is a hypothesis.** The discrete ring R is cofinal in the real closed field F. Ordinary Z is not cofinal in a non-Archimedean field. Extrapolation therefore uses a large step h in R, not a purported sufficiently large standard integer.
2. **The finite difference is exactly zero only at the lattice first.** An eventual bound below 1, combined with membership in R, gives zero. A cofinal semialgebraic zero set then contains a ray.
3. **Mean-value arguments are tame.** Rolle, monotonicity and differentiation are used only for semialgebraic functions and ordinary finite orders over a real closed field. No claim is made for arbitrary surreal functions.
4. **Polynomial growth is finite-degree.** A semialgebraic graph is eventually on an algebraic branch. A root bound gives an ordinary integer power bound, with arbitrary field-valued constants. Monotonicity of the absolute derivative converts O(x^r) to O(x^(r-1)).
5. **The periodic kernel is semialgebraic.** Period 1 plus eventual monotonicity forces constancy, even though finitely many ordinary increments cannot bridge every non-Archimedean interval.
6. **Identity propagation is not analytic-series convergence.** Reciprocal semialgebraic growth gives a power lower bound at a putative boundary; finite Taylor–Rolle estimates contradict flatness.
7. **Degree bound uses total graph degree after quantifier elimination.** The contact polynomial Q(X,P(X)) has degree at most D*max(1,deg P). The arithmetic tail enters before this purely semialgebraic continuation argument.
8. **Dimension-independent refinement.** Under C^(D^2), each lattice coordinate slice is polynomial of degree at most D. A tensor interpolant agrees on R^n. Coordinate-by-coordinate continuation uses the same finite-order graph-contact theorem, not an unjustified density claim. Once the map is polynomial, one original graph atom is divisible by Y-P, giving total degree at most D.
9. **Vector graph convention.** D bounds scalar coordinate graphs. A degree bound for a full vector graph requires output-coordinate elimination before the scalar theorem can be applied.

## Support and flexibility checks

10. **Growth and valuation conventions are distinguished.** Positive powers of omega are infinite and permitted in Oz; negative growth exponents are forbidden.
11. **Constant extraction is restricted.** It is multiplicative on the nonnegative-support ring, not all of No.
12. **K_H is handled through set-sized support fields.** Any finite coefficient and input collection lies in a set-sized divisible exponent hull inside H. Real closedness and semialgebraic closure can be applied there.
13. **No improper class union.** The entire bounded window is controlled by the convex group H_a, not by a union of all input supports. The latter would generally be a proper class.
14. **Exact multiplier criterion.** Necessity uses all monomial inputs omega^(-h); sufficiency uses positivity of every possible product exponent. Cancellation can remove exponents but cannot create a nonpositive one.
15. **Sharp radical obstruction.** The binomial expansion at omega^a-1 has nonzero coefficients and distinct strictly decreasing exponents. Failure of b > n*a for all standard n produces an actual negative exponent. A finite numerical truncation is not used as a proof.
16. **Endpoint smoothness.** The bump is a polynomial power times a square root. Derivatives through k vanish at both endpoints; the difference quotient of its kth derivative at an endpoint has a nonzero x^(-1/2) leading behavior. Infinite coefficients do not alter the order-topological argument.
17. **Non-piecewise-polynomial claim is strong but finite.** Agreement with a polynomial forces a root of P(X)^2 - L^2[X(T-X)]^(2k+1). Odd root multiplicity makes this a nonzero polynomial. Finitely many such root sets cannot cover the ordinary positive integers inside the window.
18. **Surcomplex scope.** The real-semialgebraic theorem is in 2n real coordinates. Holomorphic polynomiality additionally assumes Cauchy–Riemann equations and follows by polynomial algebra in z and conjugate z. The cutoff shears are not claimed holomorphic.

## Sampling checks

19. **The tested family is set-sized.** A proposed set S gives a set union of supports of sqrt(s^2+1), so a new exponent b can be chosen.
20. **The bad point is explicit.** At x=omega^(b+1), the coefficient of omega^(-1) in omega^b sqrt(x^2+1) is exactly 1/2. The succeeding exponents are strictly lower for b>0.
21. **Fixed total degree does not fix coefficient scale.** The full quadratic equation has total degree 2 but its coefficient omega^(2b) depends on the test set. Thus the theorem rules out coefficient-independent testing, not coefficient-adapted algorithms.
22. **Exception removal.** A set of exceptions is bounded above. This produces a good tail and invokes smooth propagation. The argument extends along coordinate lines for a set of bad vector inputs.

## Computation

`code/verify.py` passed 1,578 exact assertions with CPython 3.13.5. These are finite algebraic sanity checks only. The recorded groups and counts are in `verification.json`. The script does not claim to decide equality of arbitrary surreal notations or to verify infinite supports, class quantifiers or semialgebraic calculus.

## Not performed

No Lean formalization or build; no Wolfram computation; no independent proof review; no full repository audit; no exhaustive literature priority search. The article provides complete written arguments, but these limitations remain material.
