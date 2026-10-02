# Independent all-finite-orders audit: relaxed ternary trees

Date: 2026-10-02. Scope: the 04:49 UTC version of `all-orders-reduction.md`, together with the separately approved leading singular-gap and tracking proof. This audit does not extend to DFA counts, does not compute the positive leading amplitude, and does not establish convergence of the formal infinite series.

## Verdict

The proposed extension is valid as an expansion to every fixed finite order. The added arguments genuinely supply the step missing from the leading theorem: arbitrary-order forward defects, a common limiting projection, and a zero-limit backward bootstrap. They do not assume that leading tracking automatically transfers arbitrary orders. Below are explicit quantifiers and estimates needed when turning the reduction into a theorem.

## 1. Exact formal equation and polynomial solvability

With epsilon = i^(-1/3), x = epsilon(j+1), tau = (1-epsilon^3)^(-1/3), both preceding-time positions are exactly (x+d epsilon)tau, d=-1,2, and the preceding amplitude variable is epsilon tau. Substitution in the exact rational U gives the displayed U(epsilon,x). No phase-dependent term is omitted: all phases evaluate this same equation at their own mesh points.

At epsilon^(m+2), the unknown phi_m enters through 3(D^2-x-a)phi_m. The zero-order terms cancel against 3phi_m; the order-one differential term cancels because 2(-1)+2=0. The new scalar s_(m+2) multiplies f. Unknown higher profiles therefore cancel or do not enter. Derivatives of polynomial-Airy pairs remain polynomial-Airy pairs by f''=(x+a)f.

To avoid a factor-of-three ambiguity in (C), first divide (B) by 3. For L(Af+Bf')=Pf+Qf', the exact elimination is

K B = P-Q'/2,  K=-D^3/2+2(x+a)D+1,
A'=(Q-B'')/2.

On polynomials of degree at most d, K has diagonal 1,3,...,2d+1 and lower-degree remaining terms. It is invertible. Adding delta to its forcing adds precisely the constant delta to B. Thus the scalar in (B), after division by 3, adjusts B(0) with nonzero derivative 1/3. It uniquely enforces B(0)=0. Since f(0)=0 and f'(0) is nonzero, this is exactly the boundary condition phi_m(0)=0. A(0)=0 fixes the remaining homogeneous f gauge.

This proves existence at every finite stage without a Fredholm obstruction or logarithmic profile. It is a polynomial argument, not merely a check of finitely many coefficients.

## 2. Independent coefficients

`check_coefficients.py` independently reconstructs the shifted previous-time profiles using truncated polynomial arithmetic, reduces derivatives in the basis f,f', and solves the triangular polynomial equations. It checks the exact polynomial residual for each newly solved stage. Outputs are in `coefficients.json` and `scalar-endpoint-checks.json`.

In the A_m(0)=B_m(0)=0 gauge it gives:

- s_3 = 15/2
- s_4 = 23a^2/45
- s_5 = 11a/270
- s_6 = -(3428a^3+79395)/28350
- s_7 = -82813a^2/85050

The first correction is A_1=-x(2a+5x)/12, B_1=0. The next is

A_2=x(20a^2x+100ax^2+125x^3+2072)/1440,
B_2=x(16a+123x)/540.

These match the independently generated coefficients supplied by the proof author through s_6. The infinite-order proof rests on the triangular argument above; finite symbolic agreement only checks its implementation and conventions.

## 3. Scalar log-ratio reversion

For H_i=G_i exp(sum_(r=1)^J h_r i^(-r/3)), with leading constant exactly one, the exact formal logarithm of H_i/H_(i-1), minus log 3, is

3a/epsilon [1-(1-epsilon^3)^(1/3)]
 -(5/2)log(1-epsilon^3)
 +sum h_r epsilon^r [1-(1-epsilon^3)^(-r/3)].

Its initial terms are a epsilon^2+(5/2)epsilon^3, agreeing with log(s(epsilon)/3). The first appearance of h_r is -(r/3)h_r epsilon^(r+3); hence every later coefficient can be matched uniquely. In particular,

h_1=89a^2/90,  h_2=571a/135.

The nonzero epsilon^3 term is already accounted for by i^(5/2). There is no missing extra logarithm. Matching s itself instead of log s would multiply the first new coefficient by 3; the quoted -r/3 is correct specifically in the logarithm convention.

## 4. Uniform residual at an arbitrary requested order

Fix p>1. Choose an integer K at least max(4,ceil(3p)), solve the profiles through m=K-2 and the scalars through s_K, and match the logarithmic scalar ratio through epsilon^K with J=K-3. Then the finite uncut equation has remainder O(epsilon^(K+1) W(x)), where W is a fixed polynomial-Airy envelope depending on K. This is at least as small as i^(-p). Taking extra stages is harmless.

For completeness the remainder bound is uniform on the moving cutoff support x<=2log i. Expand the rational U using its denominator bounded away from zero and the small quantity O(epsilon^2 x+epsilon^3); expand tau and every factor (epsilon tau)^m to the required finite order. Each remainder is bounded by its target power of epsilon times a fixed polynomial in x. Spatial displacements are O(epsilon+epsilon^3 x). Taylor's integral remainder uses finitely many derivatives of finitely many polynomial-Airy profiles. Those derivatives satisfy a common bound C(1+x)^D exp(-c x^(3/2)) for x>=1 and are bounded on a fixed interval at zero. Slightly reducing c absorbs all intermediate shifted arguments. Products and all remainder terms therefore admit a common square-integrable W independent of i.

The fixed weights lie between 1 and 3/2. Uniformly for all three residue meshes,

sum_j omega(j) W(epsilon(j+1))^2 <= C epsilon^(-1).

Since N_i is comparable to epsilon^(-1/2), the weighted residual is O(H_i N_i epsilon^(K+1)). It is important to use this integrable envelope rather than a supremum on [0,2log i], which would introduce unnecessary logarithmic factors.

Choose the same smooth cutoff convention as in the approved leading proof, applied to the finite sum of profiles. Differences of cutoff factors at consecutive times or shifts are supported at x>=log i-O(epsilon+epsilon^3 log i). All such terms are smaller than every power of i because exp(-c(log i)^(3/2)) dominates all fixed polynomial factors in i and log i. The rational coefficients and finite profile degrees cause no difficulty there.

At the only missing lower input, j-1=-1, the corresponding scaled coordinate is exactly zero and every profile is identically zero. At the upper boundary the cutoff is identically zero with a margin, since its height is O(i^(1/3)log i), far below i. Thus there is no unaccounted physical-boundary residual. Positivity of high-order corrected profiles is not needed by this argument.

This proves (E) at every requested fixed p. Constants and the sufficiently large starting index can depend on the truncation order, as is normal for an asymptotic expansion; no uniformity in the number of orders is claimed.

## 5. Exact common normalization and amplitude

Let P_i=product_(m=L)^i t_m and S_i=P_i N_i/N_(L-1). The summable tail expansion of log t_m proves P_i/G_i tends to a positive finite kappa. Its fixed lower limit L is essential.

The unscaled approximation H_i Phi_i/S_i has limiting projection N_(L-1)/kappa. Indeed H_i/G_i tends to one and Phi_i/N_i-psi_i tends to zero in norm. Consequently the definition

Z_i=(kappa/N_(L-1)) H_i Phi_i/S_i

has limiting projection exactly one, independently of the number of retained terms. Moreover Z_i-psi_i tends to zero. The two reciprocal constants must not be interchanged: N_(L-1)/kappa is the limit BEFORE the explicit prefactor, and one is the limit AFTER it.

Dividing the raw residual by S_i gives the normalized defect O(i^(-p)), because H_i N_i/S_i is bounded above and below. Multiplication by the fixed kappa/N_(L-1) does not change its order. If the exact normalized solution u_i has limiting projection C, the same C works for every truncation. Undoing S_i yields the common raw prefactor C kappa/N_(L-1), not a truncation-dependent constant.

Changing L changes the intermediate constants coherently but not the raw solution or its asymptotic amplitude. Changing the polynomial amplitude gauge also changes the scalar coefficients; scalar and profile factors must be transformed together. The stated gauge and leading constant one remove that ambiguity.

## 6. Zero-limit bootstrap

The approved leading proof supplies the exact block estimates for A_i=T_i/s_i. Apply them to E_i=u_i-CZ_i, whose forcing is O(i^(-p)). Its central projection alpha_i tends to zero, and alpha_i and the stable component w_i are initially bounded because both u_i and Z_i are bounded in norm.

For any fixed q>=0, assume |alpha_i|=O(i^(-q)). Iterating the stable block bound gives

||w_i||=O(i^(-q-2/3)+i^(2/3-p)).

One rigorous convolution bound splits source times into m<=i/2 and m>i/2. The first part has stretched-exponential suppression exp(-c i^(1/3)), with any polynomial initial/source size absorbed. In the second part, powers of m are comparable to powers of i, and the kernel is bounded by exp(-c(i-m)i^(-2/3)); its sum is O(i^(2/3)). This proves the displayed estimate for every fixed q and p.

The central increment bound is then an absolutely summable combination of i^(-q-4/3), i^(-q-5/3), i^(-p-1/3), and i^(-p), provided p>1. Summing BACKWARD using alpha_infinity=0 gives

|alpha_i|=O(i^(-q-1/3)+i^(1-p)).

Starting at q=0 and replacing q by min(q+1/3,p-1) reaches q=p-1 after finitely many steps. Hence ||E_i||=O(i^(1-p)). There is no circular appeal to an unknown rate of convergence and no logarithmic resonance at the endpoint exponent. The p>1 hypothesis should be explicit; arbitrary-order applications can always choose such p.

## 7. Endpoint extraction and finite-order conclusion

On residue-zero times, psi_i(0) is comparable to i^(-1/2). Evaluation at coordinate zero is bounded in the fixed weighted norm. Therefore the relative endpoint error is O(i^(3/2-p)). The comparison endpoint Z_i(0) is asymptotic to psi_i(0), so either denominator gives the same loss. This loss is deliberately coarse but sufficient for arbitrary finite order by choosing p sufficiently large.

Every phi_m vanishes at x=0, so the endpoint expansion at x=epsilon begins with Ai'(a)epsilon and has an ordinary power series in epsilon after factoring out that leading term. Independent symbolic evaluation gives

Phi_i(0)/(Ai'(a)epsilon)
 =1+(4a/135)epsilon^2-(103/810)epsilon^3+O(epsilon^4).

There is no epsilon term in this gauge. Combining the scalar factor H, this Taylor expansion, restriction i=3n, and the full Stirling expansion gives a relaxed-count expansion in powers of n^(-1/3), with the same strictly positive leading constant certified in the leading theorem.

For an explicit remainder O(n^(-(M+1)/3)) after terms through n^(-M/3), choose p>=3/2+(M+1)/3 and retain sufficient formal and endpoint terms. Choosing a strict inequality avoids any concern about the transfer error contributing at a retained order. Nothing here proves an analytic convergent series or controls growing M with n.

The DFA defect sum and its growing-level behavior are absent from this argument. No all-orders DFA claim follows.

## 8. First count coefficients as an additional convention check

With the leading amplitude factored exactly as

R_n=C_R (n!)^2 (27/4)^n exp(3*3^(1/3)*a*n^(1/3)) n^(5/3)
     *[1+c_1 n^(-1/3)+c_2 n^(-2/3)+c_3 n^(-1)+O(n^(-4/3))],

the above independently computed scalar/profile coefficients and (2n)!/(n!)^2=4^n/(sqrt(pi*n))*(1-1/(8n)+O(n^(-2))) give

c_1 = 3^(-1/3) * 89a^2/90,
c_2 = 3^(-2/3) * (7921a^4/16200+115a/27),
c_3 = 704969a^6/13122000+115931a^3/85050+1514/945.

These are checks in the exact normalization above. Their formal values do not determine C_R. The complete finite-order theorem, rather than the symbolic script alone, justifies their use as asymptotic coefficients.

Reviewed reduction SHA-256: d46e01a3dfd5fe6a7ec44299cdd6992ad553291686e60b4eea78dbbcb7890d71.
