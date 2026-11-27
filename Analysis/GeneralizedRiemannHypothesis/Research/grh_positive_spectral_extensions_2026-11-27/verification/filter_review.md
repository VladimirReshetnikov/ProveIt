# Independent adversarial review of the two-frequency filter theorem

Reviewed 2026-11-27. Source reviewed: `research/filter_theorem.tex`.

**Final delivery note:** Both requested clarifications below were incorporated
in `papers/filters.tex`: the cancellation of the common cubic term is shown
explicitly, and the shortening infimum is explicitly over probability measures.
This review was performed by a separate AI agent in the same research run;
it is not external peer review or a Lean formalization.

**Verdict:** The classification, nonsymmetric uniqueness, asymmetric resonance law, square-root stability, and sharp first-order shortening law are mathematically sound. I found no substantive gap. Two small clarifications in the written proof are recommended below. This was an analytic review; no redundant numerical checks were run.

## Recommended clarifications

1. In the outer-node Puiseux argument, explicitly exhibit the absence of a linear term in z in the divided equation. Analyticity and a nonzero derivative alone give `w=2C+O(z)`, whereas the stated result uses `O(z^2)`. The stronger estimate is valid: uniformly for v,w in compact positive neighborhoods,

\[
 \frac{\sin((n+z^3)zw\pm\pi z^3/2)}{\sin(zw)}
 =n+z^3+z^2\left(\pm\frac{\pi}{2w}-A_nw^2\right)+O_n(z^4).
\]

The common z^3 cancels on subtracting the two quotients. Since `v(z)=C_n+O(z^2)`, the reduced equation is its displayed limiting cubic expression plus `O_n(z^2)`. The implicit function theorem then gives the asserted `w=2C_n+O_n(z^2)`.

2. In the definition of `D_r(d)`, explicitly state that the infimum is over probability measures. This is intended by context, but should appear in the displayed constraint or preceding sentence; otherwise the zero measure would make a literal unqualified infimum zero.

An optional clarification in the t=0 uniqueness proof is that `sin(T)` is nonzero. The eventual first-band formula gives `pi/2<T<pi`, or directly a crossing at T=pi would require a nonresonant r in (1,3) to be odd.

## Global branch selection

For `r in (2k+1,2k+3)` and `s=(-1)^k`, the function

\[
 f(u)=s\frac{\cos(ru)}{\cos u},\qquad 0\le u<\pi/2,
\]

tends to minus infinity at pi/2, since `s cos(r pi/2)<0`. Its positive lobes have centers congruent to k modulo two. Every earlier positive-lobe point can indeed be shifted forward by a multiple of `2pi/r` into the last positive lobe, preserving its numerator and strictly reducing its positive denominator. Thus the global maximum lies on the last positive lobe, rather than an accidentally selected local branch.

The identity

\[
 W'(u)=(1-r^2)s\cos(ru)\cos u
\]

is correct. It is negative on the last positive lobe, and W is positive at its center and negative at its right endpoint. Therefore the tangency node is unique and lies in the stated open subinterval. When k=0, the maximum is uniquely at zero.

On the outer branch `(pi/2,U)`, `U=(2k+3)pi/(2r)`, both `s cos(ru)` and `cos u` are negative. Even for the first band with r near 1, where U may exceed pi, U is still less than `3pi/2`, so the denominator keeps the claimed sign. W is strictly negative and decreasing, and f decreases continuously from plus infinity to zero. Hence the crossing exists uniquely on the stated branch.

## Nonnegative certificate and all minimizers

The function `g=M cos u-s cos(ru)` is nonnegative on the full optimal interval, with precisely the listed inner and endpoint zeros. The inner zeros are quadratic and the endpoint zeros simple. Consequently every admissible probability measure of no larger diameter, after centering, is supported on those nodes. This works for arbitrary measures and does not presuppose symmetry, finite support, or a chosen number of atoms.

The argument excluding nonsymmetric solutions is valid. At T,

\[
 W(T)=\cos T\{M\sin T-sr\sin(rT)\}<0,
\]

so the bracket is positive. At t,

\[
 r\sin(rt)=sM\sin t.
\]

The determinant of the two sine equations is therefore nonzero whenever t>0. The odd masses vanish, and total mass plus the first cosine equation determine the two even mass groups. Both endpoint masses are strictly positive, proving that no smaller diameter works. At odd resonance, the elementary nonnegative certificate cos u proves the two-endpoint solution and its uniqueness.

The explicit first-band solution is consistent with the branch analysis. The discontinuity as r approaches 1 from above is not a contradiction: at r=1 the two constraints coincide, while a nearby distinct second constraint effectively carries extra information.

## Inner-node cubic root

The localization argument is valid. On every compact set away from y=0, `sin(ny)/sin y<n`, while testing y of order `epsilon^(1/3)` makes the maximum tend to n. The maximizing y must tend to zero.

The stationary equation expands as

\[
 H(\varepsilon,y)=\frac\pi2\varepsilon-2A_ny^3
 +O_n(y^5+\varepsilon y^2+\varepsilon y^3+
       \varepsilon^2y+\varepsilon^3).
\]

The error is uniformly `o(epsilon+y^3)` as both variables tend to zero through nonnegative values, so it rigorously gives comparability and then

\[
 y^3/\varepsilon\longrightarrow\pi/(4A_n)=C_n^3.
\]

After setting epsilon=z^3 and y=zv, the quotient `H(z^3,zv)/z^3` extends analytically. It has no z term, and its v derivative at the limiting root is nonzero. Thus `y=C_n z+O_n(z^3)` as claimed.

## Outer node and the ratio two

The outer root tends to zero by the same strict inequality away from the endpoint and the already-proved branch monotonicity. The scaled limiting equation is

\[
 A_n\left(\frac{2C_n^3}{w}-w^2+3C_n^2\right)=0.
\]

Multiplication by w gives the factorization

\[
 (w-2C_n)(w+C_n)^2=0,
\]

so there is only one positive solution. Its derivative is `-9A_n C_n/2`, nonzero. The refined expansion described under the recommended clarification proves `x=2C_n z+O_n(z^3)`. The mass limits P=2/3 and Q=1/3, with `O(z^2)` errors, then follow by expanding sin x and sin y.

The approach from below is regular: for n>=5 the previous-band maximum is an interior nondegenerate stationary point, so its location and value vary analytically with r. For n=3 the maximum remains exactly at zero with value one. The outer equation gives the displayed linear coefficient `pi/(n+M_n^-)` for the diameter. The checks `M_3^-=1` and `M_5^-=5/4` are correct.

## Stability exponents

The global bound `g>=c dist(.,G)^2` on the fixed optimal interval follows from the identified zero orders and compactness. Its integral is at most `(M+1)epsilon`. Rounding to G has transport cost `O(sqrt(epsilon))`, and the finite moment map on G has an injective weight map by the uniqueness argument. This yields the claimed transport estimate.

For sharpness, splitting any inner atom symmetrically by displacement a changes each Fourier moment by O(a^2). The 1-Lipschitz test function `dist(.,G)` shows that the Wasserstein distance from the original minimizer is at least its displaced mass times a. This excludes every exponent greater than 1/2. The t=0 case is covered by splitting the central atom. At odd resonance, cos u controls distance to the endpoints linearly, giving exponent 1; moving endpoints inward proves sharpness.

Constants here depend on fixed r. They need not remain bounded near an odd resonance.

## Sharp shortening: lower and upper constants agree

Put `a=-g'(T)/2` and `K=Qa`. The proposed correction `h_0(u)=K cos u/cos t` has values K at the inner nodes and K-a at the outer nodes, using the exact formulas for P,Q. On the shortened interval,

\[
 \min(g+d h_0)\ge dK-O_r(d^2).
\]

Near an inner node, completing the square bounds the possible loss from the d-sized linear perturbation by O(d^2). Near an endpoint, g is monotone and grows linearly inward; the new endpoint has value da+O(d^2), which combines with d(K-a)+O(d^2) to give dK+O(d^2). The remaining compact region has a positive unperturbed minimum.

Integration yields the lower bound with denominator `M+1+dK/cos t`. Its first-order coefficient is

\[
 L_r=\frac{Qa}{M+1}.
\]

For the upper bound, the proposed two symmetric node pairs remain inside the shortened interval for small d. The linear condition `hat nu(1)+s hat nu(r)=0` has a unique positive pair of group masses near P,Q because the corresponding node values have opposite signs at d=0. Their outer group mass is Q+O(d). Consequently

\[
 (M+1)\widehat\nu(1)=\int g\,d\nu=Qa\,d+O_r(d^2),
\]

with positive right side, and the two moment moduli are equal. This proves the matching first-order upper bound, not merely an unspecified approximate cancellation.

For the resonance dependence, differentiate the underlying trigonometric expression, not an uncontrolled big-O remainder. With x=2y+O(epsilon) and `y=C_n epsilon^(1/3)+O(epsilon)`,

\[
 g'(T)=3A_n(y^2-x^2)+O_n(\varepsilon)
       =-9A_n C_n^2\varepsilon^{2/3}+O_n(\varepsilon).
\]

Combining Q=1/3+O(epsilon^(2/3)) and M=n+O(epsilon^(2/3)) gives exactly the stated coefficient of `epsilon^(2/3)` in L. The two asymptotic statements have separate limits: first d tends to zero for fixed r, then the coefficient L_r is examined as r tends to n. No uniform two-variable error estimate is established or needed.

## Arithmetic application

Exponential tilting preserves support and correctly transforms vanishing at `beta+i alpha`, `beta+i gamma` into ordinary Fourier vanishing. Tilting the classified optimal measure back gives positive weights and preserves the optimal diameter. In a smoothed explicit formula, averaging at multiplicatively shifted x multiplies each selected zero contribution by the required exponential moment, so the application is valid. Common multiplicities affect coefficients but do not require derivative vanishing. The argument does not rely on simplicity or spacing of the arithmetic zeros.

The unconditional optimization theorem and its asymptotic laws should remain distinguished from the GRH application, exactly as the draft currently does.
