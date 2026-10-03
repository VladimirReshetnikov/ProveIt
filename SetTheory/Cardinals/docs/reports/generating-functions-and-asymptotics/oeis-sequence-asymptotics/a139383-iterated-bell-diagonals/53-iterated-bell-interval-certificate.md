# Interval certificate for the outer integral

Scope: certify the radius-1/2 outer-contour contribution

J = (1/pi) integral from 0 to pi of Re[u(theta) exp(Psi(u(theta)))] dtheta,
u(theta)=exp(i theta)/2,
Psi(u)=lim_M (2/h^M(u)-M+log(M)/3), h(u)=log(1+u).

This is the positively oriented full outer circle divided by 2 pi i, using the upper and lower boundary values at the negative real endpoint. Conjugation gives the displayed real integral. This document certifies J only; it does not independently certify contour deformation for the original coefficient problem or the whole-cut bound.

## Analytic facts used, independently checked

Put g(w)=2/log(1+2/w), with the continuation compatible with principal logarithms, and

rho(s)=2/[log((2-s)/s)^2+pi^2], 0<s<2.

Then g(w)=w+1-integral_0^2 rho(s)/(w+s) ds on C minus [-2,0]. To verify the representation, g-w-1 is analytic there, has O(1/w) decay, and upper-minus-lower jump 4 pi i/[log((2-s)/s)^2+pi^2] at w=-s. Both g endpoint limits are zero, so g-w-1 stays bounded at the endpoints and the small endpoint contour integrals vanish. Cauchy's formula gives the representation with the displayed sign. Expansion at infinity gives mass mu_0=1/3; symmetry rho(2-s)=rho(s) gives mu_1=1/3. All moments are positive and mu_k<=2^k/3.

For |w|>2, truncate after K moments:

g(w)=w+1-sum_(k=0)^(K-1) (-1)^k mu_k/w^(k+1)+R_K,
|R_K| <= 2^K/[3 |w|^K (|w|-2)].

This follows directly by finite geometric expansion of 1/(w+s) and positivity of rho. The verifier obtains the exact rational coefficients by reciprocal power-series division of log(1+2/w)/(2/w); the first correction coefficients are -1/3, 1/3, -19/45, 3/5. Thus it does not numerically integrate rho or estimate its moments.

For Re(w)=x>=4, let V(w)=w+log(w)/3+1/(18w). The rigorous tail is

|Psi(u)-(V(w_M)-M)| <= 2/(Re w_M)^2.

Here is a check of its constants. Write a=g(w)-w. The representation gives |a-1|<=1/(3x), Re(a)>=11/12, |a|<=13/12<7/6, and

a=1-1/(3w)+1/(3w^2)+R, |R|<=2/(3x^3),

using mu_2<=2 mu_1=2/3. With delta=a/w, |delta|<1/3. In log(1+delta), the error in replacing a/w by 1/w-1/(3w^2) is <=(1/3+1/6)/x^3; the error in replacing a^2/(2w^2) by 1/(2w^2) is <=25/(72x^3)<1/(2x^3); and the cubic logarithm remainder is <1/x^3. Hence

log(1+delta)=1/w-5/(6w^2)+E, |E|<=2/x^3.

Also 1/(w+a)-1/w=-1/w^2+E2 with |E2|<=9/(4x^3): use |1-a+a/w|<=3/(2x) and |1+a/w|>=2/3. Combining cancels the coefficients of 1/w and 1/w^2 in V(g(w))-V(w)-1, leaving at most 35/(24x^3)<2/x^3. Along the orbit, Re w_j>=x+11j/12, so the sum of the defect bounds is at most 2/x^3+12/(11x^2)<2/x^2. This proves convergence and the tail bound. Also w_j=w+j+O(log j), directly by summing |a-1|, so log(w_j)-log j tends to zero and this limit has exactly the normalization defining Psi.

## Interval integration, not quadrature sampling

Partition [0,pi] into Q equal panels. Each panel is represented by a closed outward-rounded interval theta=[j pi/Q,(j+1) pi/Q]. The code encloses every point on the associated arc using interval exp(i theta)/2. An outward-roundoff undershoot in its imaginary lower bound is clipped to zero, because the exact arc is in the closed upper half-plane. The first 12 iterates use complex interval principal log(1+u), then w=2/u. All remaining iterates through M=64 use the K=20 moment polynomial plus its rigorous complex remainder, enclosed in a rectangle [-epsilon,epsilon]+i[-epsilon,epsilon]. The code checks |w|>2 before each series evaluation, and Re w_M>=4 before the tail bound. No inference from float convergence is used.

For each panel set B=V(w_M)-M, eta=2/(Re w_M lower bound)^2. The exact F=exp(Psi) is within |exp(B)|[exp(eta)-1] of exp(B), for each true point B in its interval enclosure. Thus the real integrand is enclosed by Re[u exp(B)] plus/minus half that error. Summing these interval ranges divided by Q encloses J. These are Darboux-range bounds over entire panels; there is no unbounded quadrature remainder.

## Audit limits

The arithmetic certificate uses mpmath.iv outward-rounded interval elementary functions with 30 decimal digits. Rational coefficients are constructed using Python Fraction. It assumes correct implementation of the Python/mpmath interval runtime and its elementary functions; it is an executable interval certificate, not a proof-assistant-checked theorem or an independent implementation of transcendental rounding. Floating conversions, if any, are printed only as diagnostics and are not used to bound the integral. All inequalities needed for domain validity and the final coarse endpoints are interval assertions. Principal upper boundary values at theta=pi are used; the endpoint itself has measure zero. No packages are installed, no external service is used, and no data are published.

The independently run Q=512 prototype already gave [1.7369005289899737368065175663083557, 2.8151628090229196132302079590131773], which alone proves J>1. The production Q=2048 output and its deliberately rounded rational enclosure are recorded with the verifier.

## Certified result

The Q=2048 run gives

    J in [2.148710226926796756397661371493759,
          2.423911766794793944536818666505863].

The machine-independent statement deliberately rounded outwards is

    214/100 < J < 243/100.

Minimum final real-part lower bound across panels is approximately 59.08024 (diagnostic only; the verifier checks the rigorous inequality >=4 on every panel). With the separate analytic bound |whole-cut contribution|<1/2, the total amplitude integral is >164/100, hence positive. Multiplication by sqrt(2 pi)/2 preserves strict positivity. No finer digits of the true amplitude are claimed.
