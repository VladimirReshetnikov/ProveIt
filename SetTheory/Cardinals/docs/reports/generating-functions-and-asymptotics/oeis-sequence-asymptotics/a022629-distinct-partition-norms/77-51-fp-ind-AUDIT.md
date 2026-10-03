# Independent audit of the A022629 asymptotic and inverse proofs

Date: 1 October 2026. Outcome: APPROVED as ordinary analytic proofs. The three reviewed source files are pinned in approval.json and were not edited by the reviewer.

## Approved statements and scope

For a_n=[q^n] product_{k>=1}(1+kq^k), the reviewed notes establish:

1. With m0=sqrt(2n), log a_n=m0(log m0-1)+O(m0/log m0), including strict increase for n>=1 and the stated Lambert-W inverse with relative error O((log log y)^(-2)).
2. The exact-saddle, relative cumulant expansion to each fixed order R, with relative bracket remainder O_R(w^(-R-1)), and the inverse threshold brackets of width O_R(w^(-R)).
3. The explicit correction log a_n=m0(log m0-1)+(pi^2/6)m0/(log m0-1)+O(m0/log^3 m0), and its refined Lambert-W inverse with the displayed relative O(log^(-4) m_*) error.

These are asymptotic assertions as the real or integer parameter tends to infinity. They do not assert a complete exponentially small transseries, convergence of the formal expansion, a uniformly useful expansion at small n, or literature priority. The proposed generator for further inverse-logarithmic coefficients in the thermal note is a route to future explicit statements, not an additional checked coefficient list. The exact saddle data and the inverse-logarithmic expansions have different precision scales: finitely many inverse-logarithmic terms cannot simply replace exact f(t_n) in the relative saddle theorem.

## Elementary bound and inverse

The partition 1,...,M-1,M+r has distinct parts, total n, and product at least M!, where M(M+1)/2<=n<(M+1)(M+2)/2. Since M=sqrt(2n)+O(1), elementary factorial bounds give the claimed lower estimate.

For the upper estimate choose t=(log m)/m, m=sqrt(2n). The split at floor(m) is an exact identity even though g(1)=-t<0. That single correction is bounded. Concavity ensures g(k)>=0 on 2<=k<=floor(m), for large m. The bounds on the three other ranges are valid, including the tail geometric sum with nonintegral m. The small-k error sqrt(m) log m is indeed o(m/log m). The residual main sum differs from m(log m-1) by O(log m).

Increasing the largest colored part is injective; the unique largest output identifies the part that must be decreased. The new one-part object with the largest available color is outside the image. Thus a_{n+1}>a_n for n>=1. No strict inequality is claimed at a0=a1=1. Inverting H(m)=m(log m-1) gives exactly m=s/W(s/e). Perturbing n by relative C/log^2 m changes H by order C m/log m, while rounding has size O(log m/m). This validates both the discrete and interpolation inverses.

## Exact saddle and analytic estimates

For fixed t>0, sum p_k and sum k p_k converge, so the Bernoulli random sum is finite almost surely. Its generating function and characteristic function are well defined. The mean decreases continuously from infinity to zero with derivative -V<0, establishing the unique saddle for every positive real target.

All stated cumulant bounds follow from Bernoulli cumulants p(1-p) times fixed polynomials, the three-range estimates, and the active interval of length comparable to w=m/log m at k=m. In particular, V is comparable to m^2 w, with a genuine lower bound. The comparison mu=m^2/2+O(m^2/log m) is sufficient here.

The complex disk |theta|<c/m is valid. For k<=2m the denominator 1-p+p exp(ik theta) remains bounded away from zero; its derivatives of order at least two are bounded by constants times k^r p(1-p). For k>2m, k exp(-(t-c/m)k) is uniformly O(1/m), so the logarithm series and its derivatives converge uniformly on a smaller disk. Centering only changes the linear term. Thus every fixed derivative of order r>=2 has bound O_r(m^r w), also at the complex points used in Taylor's remainder.

## Minor arcs

For a consecutive interval of W integers, the squared modulus identity

W^2-|sum exp(ij theta)|^2=sum_{i,j}(1-cos((i-j)theta))

implies a lower bound c W^3 theta^2 for the sine-square sum at |theta|<=1/W. At intermediate |theta| up to C/W, retain differences in a fixed subinterval of [1,W/C]; this yields a positive multiple of W. Beyond C/W the ordinary geometric bound suffices. Translation of the interval cannot decrease the lower bound obtained from the modulus. Consequently the stated bound c W min(1,W^2 theta^2) is valid throughout [-pi,pi].

On the smaller arc |theta|<=c0/m, every active k has |k theta|<=1 and gives the stronger Gaussian exponent c m^2 w theta^2. Combining these estimates yields exp(-c w^(1/6)) and exp(-c m/log^3 m) on the two discarded ranges. Both are smaller than every fixed inverse power of m, even after multiplication by sqrt(V). In particular, the possible approximate resonances at multiples of 2pi/m are suppressed. There is no unstated aperiodicity hypothesis.

## Arbitrary-order integrated remainder

This is a detailed independent justification of the compact argument in Section 3. Put epsilon=w^(-1/2), u=theta sqrt(V), and b_r=kappa_r/(r! V^(r/2) epsilon^(r-2)). For each fixed r the real numbers b_r are uniformly bounded. Taylor's theorem in theta through degree 2R+3 has remainder

O_R(epsilon^(2R+2) |u|^(2R+4)).

This uses the complex derivative bound at order 2R+4, not just a bound on derivatives at the origin. On |u|<=w^(1/12), the remainder is uniformly o(1).

For fixed t and u introduce the auxiliary polynomial P(eta,u)=sum_{r=3}^{2R+3} b_r (iu)^r eta^(r-2). Taylor-expand exp(P(eta,u)) at eta=0 through degree 2R+1 and then set eta=epsilon. For 0<=eta<=epsilon, |P(eta,u)|<=C_R epsilon |u|^3=o(1). The derivative of order 2R+2 of this exponential is bounded by a fixed polynomial in |u| times exp(C_R epsilon |u|^3). Therefore its remainder, after multiplying by exp(-u^2/2), is bounded by

C_R epsilon^(2R+2) P_R(|u|) exp(-u^2/4).

This bound is integrable uniformly in t. The logarithmic Taylor remainder obeys the same type of bound after exponentiation. Extending the retained Gaussian integrals to the real line is exponentially harmless.

Parity is exact: sum(r-2)j_r has the same parity as sum r j_r. Thus every odd weighted-degree term integrates to zero; the remaining terms are precisely E_R. The Gaussian moment sign and factorial normalization give +kappa4/(8V^2) and -5 kappa3^2/(24V^3) at the first correction. This proves the stated O_R(w^(-R-1)) remainder without dropping an unbounded polynomial factor on the integration range.

## Inverse localization

The signs d kappa_r/dx=kappa_(r+1)/V and dt_x/dx=-1/V are correct. Hence (log A0)'=t-kappa3/(2V^2). Every nonconstant monomial in E_R has even weighted degree at least two. Differentiation bounds its derivative by an additional factor O(1/(m w)), giving E_R'=O(1/(m w^2)). Since E_R=1+O(1/w), A_R is positive and strictly increasing eventually, with logarithmic derivative asymptotic to t=1/w.

The coefficient theorem gives a logarithmic error O(w^(-R-1)); dividing by the derivative gives a real crossing error O(w^(-R)). Monotonicity of a_n then yields the stated integer brackets and the existence of epsilon_R in the ceiling formula. Near an integer no exact rounding choice is implied. R=0 indeed yields an O(1) error for the integer inverse.

## Thermal correction and its inverse

The function log(1+x exp(-tx)) is unimodal with height O(log m), so sum-integral error O(log m) is valid. The integral on (0,2), including the integrable log x singularity after subtraction, is O(1). All tails bounded by powers of m smaller than m itself are o(m/log^K m) for every fixed K.

On the monotone upper branch h(x)=tx-log x, h'(x) is comparable to log m/m. Direct inverse differentiation gives

x'(0)=m/(L-1), x''(0)=-m/(L-1)^3, x'''(0)=m(2L+1)/(L-1)^5.

Uniformly for |v|<=L/4, x'''(v)=O(m/L^4). The soft-cutoff kernel is even, its total mass is pi^2/6, and its second moment is finite. The odd linear term cancels exactly. This proves f(t)=m(L/2-1)+(pi^2/6)m/(L-1)+O(m/L^4).

For mu, the integrand x/(1+exp(h(x))) is unimodal with height O(m). Its soft-minus-hard kernel is odd. On the central range, (x x')'=O(m^2/L^2); the remaining ranges are smaller. This establishes mu=m^2/2+O(m^2/L^2), and hence m=m0(1+O(L0^(-2))) at the saddle.

Q0'(m)=(L-1)(1/2-n/m^2) and Q0''(m0)=(L0-1)/m0. Therefore replacing saddle m by m0 costs O(m0/L0^3), as does the variation of the first thermal term. The Gaussian logarithmic prefactor is O(L0), negligible at this scale. Finally, substituting m=m_*[1-C/(L_*(L_*-1))] cancels the thermal term to error O(m_*/L_*^3). Division by H' gives O(m_*/L_*^4); squaring gives the stated inverse coefficient -pi^2/[3L_*(L_*-1)]. Integer rounding is negligible at this scale.

## Sources and corroboration

The current primary OEIS page https://oeis.org/A022629 was independently inspected on 1 October 2026. It states the product and the May 8, 2018 logarithmic conjecture credited to Vaclav Kotesovec. No literature-wide negative claim is certified here.

The accompanying standard-library check.py independently compares 251 exact coefficients by finite-product dynamic programming and logarithmic differentiation, verifies 249 strict monotonicity cases and 250 factorial lower bounds, constructs the formal Gaussian corrections through R=4 and checks the known R=1,2 rational coefficients, and verifies 48 inverse-derivative identities. It rejects disabled assertions. These finite checks are supplementary; the infinite statements above rest on the ordinary proofs.
