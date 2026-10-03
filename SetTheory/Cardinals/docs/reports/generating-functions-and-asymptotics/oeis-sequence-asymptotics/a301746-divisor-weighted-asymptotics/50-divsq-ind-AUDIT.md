# Independent audit of A301746 asymptotics and inverses

1 October 2026. Outcome: APPROVED as ordinary analytic proofs. The frozen main source and separate inverse-shift addendum are pinned in approval.json. The review covers the exact-saddle expansion, derivative-controlled Mellin polynomial, every fixed logarithmic order, all three displayed forward/inverse corrections, global monotonicity, and both inverse-bracket statements.

No Riemann-hypothesis assumption is used. No convergent series, complete exponentially improved transseries, effective numerical threshold, or literature-wide priority claim is approved.

## Mellin transform and constants

The prime-power generating series gives sum d(k)^2 k^(-s)=zeta(s)^4/zeta(2s) for Re s>1. The Mellin kernel for log(1+exp(-x)) is Gamma(s)(1-2^(-s))zeta(s+1). Their product is therefore exactly the displayed integrand. The normalized analytic factor at s=1 is h(1)=1/2. Its exponential Taylor expansion gives the residue polynomial

P(L)=[(L+b)^3+3c(L+b)+d]/12.

I checked all three logarithmic derivatives. The Gamma terms contribute -gamma,zeta(2),-2zeta(3); the factor1-2^(-s) contributes log2,-2(log2)^2,6(log2)^3; the zeta ratio contributes -Z1,-3Z2,-7Z3. The factor[(s-1)zeta(s)]^4 contributes 4gamma,-8gamma1-4gamma^2,12gamma2+24gamma gamma1+8gamma^3. These give exactly the stated b,c,d.

For any fixed sigma in(1/2,1), the reciprocal zeta(2s)^(-1) has an absolutely convergent Dirichlet series on the new line. Standard polynomial vertical bounds for the other zeta factors and exponential Gamma decay justify the shift, with only s=1 crossed. Using Gamma(s+r) before shifting yields the derivative errors directly. The same exponential comparison works in closed subsectors of the right half-plane. There is no unjustified differentiation of an unspecified error or crossing of a possible zeta-zero pole.

The recurrence P_r=product_(j=1)^r(D+j)P is correct. Its leading coefficient is r!/12. In particular V~t^(-3)L^3/6, kappa3~t^(-4)L^3/2 and kappa4~2t^(-5)L^3. Substitution gives E1-1~-(9/4)t/L^3, with the displayed sign.

## Uniform analytic and Fourier bounds

The inequality d(k)^2<=d4(k) follows from (j+1)^2<=binomial(j+3,3) on every prime power. Summing the four-fold divisor convolution gives sum_(k<=X)b_k<=X(1+log X)^3. This elementary upper estimate suffices for every derivative bound; no average-order theorem for d(k)^2 is hidden here.

The logarithmic series converges normally on compact subsets of Re z>0. In |z-t|<=t/2, the derivative series is bounded by the displayed positive double sum. For kt<=1, its inner sum is O_r((kt)^(-r)); for kt>1 it is exponentially bounded. Partial summation then gives O_r(t^(-r-1)L^3). These estimates are valid at the intermediate complex points needed for Taylor remainders, not just at the real saddle. The variance lower scale follows from the Mellin leading term, giving the normalized cumulant scale M^(-(r-2)/2).

The random sum exists almost surely for each t>0 because sum b_k p_k converges. Its mean decreases continuously from infinity to zero with derivative -V<0, so every positive real saddle target has a unique solution.

The consecutive block[1/t,2/t] uses only b_k>=1 and probabilities bounded away from0 and1. The elementary geometric-sum estimate thus controls all Fourier phases, including potential rational resonances. At theta0=M^(1/12)/sqrt(V), its exponent is bounded below by a positive multiple of M^(1/6)/L^3. This tends faster than every logarithm of M, so the discarded probability contribution is smaller than every fixed algebraic order even after multiplication by sqrt(V). Losing the factor L^3 by using one slot per size does not invalidate the argument.

The central expansion follows the same ordinary weighted-Taylor argument as the independently reviewed A022629 proof: put epsilon=M^(-1/2), hold the normalized bounded cumulant coefficients fixed, and expand the exponential in an auxiliary parameter through weighted degree2R+1. On |u|<=M^(1/12), the remainder is epsilon^(2R+2) times a fixed polynomial under exp(-u^2/4). The complex derivative bound controls the logarithmic Taylor remainder at that order. Odd terms integrate to zero, leaving exactly the stated finite Gaussian-moment polynomial. Thus equation(4) has the claimed arbitrary-fixed-order relative remainder.

## Global monotonicity and exact-saddle inverse

The Euler-transform identity is exact: w_k=b_k-1_(2|k)b_(k/2). At k=2^a m with m odd, w_k=(2a+1)d(m)^2>=1. Removing the unique size-one factor leaves a nonnegative series whose coefficient at every degree at least2 is positive. Therefore a0=a1=1 and a_(n+1)>a_n for every n>=1. This proof does not assume monotone original slot multiplicities.

The derivative identities t_x'=-1/V and (kappa_r(t_x))'=kappa_(r+1)/V have the correct signs. They imply (log A0)'=t-kappa3/(2V^2)=t(1+O(M^(-1))) and E_R'=O_R(t M^(-2)). Consequently all A_R are eventually positive and increasing. The logarithmic coefficient error O(M^(-R-1)), divided by this slope, gives O(M^(-R-1)/t)=O(t^R/L^(3R+3)). Global sequence monotonicity then yields the two ceiling bounds. Near an integer the bracket need not select a unique integer; no stronger rounding claim is made.

## Cubic-pole model and all logarithmic orders

Let hat t=exp(-ell), with n=exp(2ell)Q(ell) and Q=P+P'. The model mean is eventually strictly decreasing as a function of t, so its large solution is unique. The r=1,2 derivative-controlled Mellin estimates first locate the exact saddle comparably and then give

t_n-hat t=O(hat t^(2-sigma)/ell^3).

The model entropy is stationary at hat t. Its displacement cost is O(hat t^(1-2sigma)/ell^3)=o(hat t^(-sigma)) because sigma<1. The direct Mellin error is O(hat t^(-sigma)); the Gaussian logarithm is O(ell). Hence equation(13) follows. These errors are smaller than every fixed inverse-logarithmic relative precision, but they are not a multiplicative coefficient error after exponentiation.

For the forward hierarchy, writing z=ell+b gives Q=q(z)/12 and T=r(z)/6 with the stated cubic polynomials. I independently substituted z=H/2+r_H/2+u1/H+... in the exact logarithmic model equation. The first correction is u1=-3(r_H+2)/2. Expansion of r(z)/sqrt(q(z)) then gives precisely equation(14). Each further equation has leading derivative2, so its finite Taylor residual controls the true root error uniformly as powers of log H/H. This is a finite-depth implicit-function argument, not an interchange of an infinite series and a limit.

For the inverse, equation(15) is exact for the cubic model. Its error relative to the exact inverse is below every fixed inverse-logarithmic order: an entropy error O(exp(sigma ell)+ell), divided by slope comparable to exp(-ell), gives the stated index error, while n is comparable to exp(2ell)ell^3. The equation in z has leading derivative1, and q(z)z^3/r(z)^2 has exactly the displayed expansion. Direct reversion yields equation(16). The Lambert-W cores and their first displacements are correctly normalized. The centered variable v=z+1/2 removes the quadratic term in the entropy polynomial and improves the core displacement to O(v_*^(-2)).

The independent checker uses Fraction-based polynomial arithmetic in Q[r,c,d][x], without importing the producer's symbolic program. It reconstructs the forward and inverse normalized saddle equations and verifies all three displayed correction polynomials exactly, including F3 and I3. Thus the updated three-correction statement is covered by this approval.

## Separate first inverse-shift addendum

Write g=log A0 and h=log E1. The established derivatives give g'~t, g''=O(t^2/M), h=O(M^(-1)), and h'=O(t M^(-2)). The implicit difference Delta=x1-x0 is initially O(1/(tM)); over this interval the local scales remain comparable. Taylor's theorem gives

g'(x0)Delta+h(x0)=O(M^(-3)),

hence Delta=-h/g'+O(1/(tM^3)). Replacing h by exact C1 and g' by t costs O(1/(tM^2)). The sign is positive at leading order because C1~-(9/4)t/L^3. Combining this approximation with the R=1 threshold bound yields radius C t/L^6 around x0-C1(t)/t. Replacing exact C1 by its leading equivalent would lose that precision. The constant C is an asymptotic existence bound; this does not provide a numerical interval-certified threshold algorithm with a supplied effective constant.

## Source status and supplementary checks

I independently retrieved the indexed primary OEIS entry confirming the generating function and August29,2018 conjectural leading equivalent. I inspected the simple-positive-pole hypothesis(P2) in Bridges--Brindle--Bringmann--Franke, and Proposition5/equations18–19 in Ahmadi--Gomez-Aiza--Ward. Their stated kernels support the source note's distinctions: the former positive poles are simple, while the latter high-order family has zeta(s)^k but not the denominator zeta(2s) here. The primary publisher introduction for Berndt--Robles--Zaharescu--Zeindler defines the two-divisor convolution and an unrestricted product, again supporting the stated narrower comparison. These checks validate those scope distinctions, not a proof audit of the cited papers or a comprehensive absence-of-prior-art claim.

The independent exact checker passes151 three-way coefficient identities (finite plus product, positive Euler product, logarithmic recurrence),149 strict monotonicity cases,30 Euler-factor identities, the leading -9/4 correction, and all eight forward/inverse formal coefficients through order three. It rejects -O and accepts a temporary output directory. Producer numerical computations are explicitly diagnostics, not proof dependencies.
