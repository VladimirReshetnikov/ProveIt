# Independent audit of the fixed Taylor sectors

Audit date: 1 October 2026 (UTC). Verdict: **PASS**, with no mathematical repair required for the fixed-sector statements in the audited source. This audit concerns the integral and its Taylor sectors; identification with combinatorial growth constants remains a separate theorem.

## 1. Exact source versions and audit scope

SHA-256 of the sources read and checked:

- `fixed-taylor-sectors.md`: `eb796ae1044a019737f7c5af20cc2a217f8e95bbdffa25c17ab565ae23632d3d`
- `fixed-sector-verify.py`: `3d9312dac122e4321c23fffeec7b15e963411765341438a887b37eeff66ac09a`
- `fixed-sector-validation.json`: `acc26ec5eb919f42b5242eab5346c1fee9da0be78bc644dcd30fd07356c53f59`

The companion independent files are `fixed-sector-independent-audit.py` and `fixed-sector-independent-validation.json`. They import neither the author's coefficient code nor the root's Gamma-centered-moment code. Their two principal checks use (i) discrete geometric moments of the exact tail-index sum and (ii) exact rational integration of a finite exponential-polynomial expansion. Symbolic differentiation and the exact first-sector formula supply additional checks.

## 2. The exact-sector theorem and next-sector remainder

Let x=e^v, R=x−E_b(v), and D=1−t+tx. The geometric expansion of 1/(D−tR) is finite and exact. Its remainder is positive and equals the integrand in source equation (6). Since

0 ≤ tR/D ≤ R/x < 1,

its lower bound is a_(K+1)(x)R^(K+1), and its upper bound is (x/E_b(v)) times that quantity. This establishes (7) without interchanging any asymptotic series. At v=0 the values are obtained continuously and do not affect integration.

The source's uniform lower bound for e^(−b)E_b(b) is valid. The approximately √b/2 terms immediately below degree b each have size bounded below by a positive constant times b^(−1/2): the product bound follows from log(1−u)≥−2u in the stated range. Monotonicity then gives E_b(v)/e^v≥c throughout 0≤v≤b.

For sufficiently large b and v≥b, E_b(v)≥v^b/b!≥2 and log E_b(v)≤v. Thus

∫_b^∞ [f(E_b(v))−f(e^v)]dv ≤ 2b! b^(2−b)/(b−2)=O(b^(3/2)e^(−b)).

The tail bound is used only for large b; the denominator b−2 creates no issue in an assertion as b→∞. Together these facts prove the integrated bounds (10). Once the fixed-sector asymptotic is established, they give the asserted O_K(b^((2−K)/2)β_(K+1)^b) remainder. Applying the same result one level further yields

R_(K,b)=A_(K+1,b)[1+O_K(b^(−1/2)(β_(K+2)/β_(K+1))^b)].

The b^(−1/2) power is correct: successive sectors' polynomial powers differ by exactly −1/2. The lower bound makes the remainder positive. The exact infinite identity follows by monotone convergence for each fixed b≥2, since every Taylor sector is nonnegative and T_b is finite. Neither this identity nor the fixed-K estimate implies uniformity in K.

The bases β_r=(r/(r+1))^r strictly decrease to e^(−1): the derivative of −r log(1+1/r) is negative, and its limiting value is −1. In particular, every fixed β_r exceeds e^(−1), so the tail above is exponentially negligible relative to every fixed next sector.

## 3. Derivative formula and exponential corrections

Changing variables in the integral for a_r gives source equation (12). An independent symbolic check of

(−1)^r f^(r)(x)/r! = x^(−r−1)[log x−Σ_(j=1)^r(1−1/x)^j/j]/(1−1/x)^(r+1)

returns exact zero differences for r=1,…,6. The continuous value at x=1 is 1/(r+1), also immediate from the integral representation.

For v≥1, expanding the finite numerator and bounded denominator gives the uniform fixed-r estimate (13). For v≤1, R_b(v)≤e/m!, while both derivative expressions are bounded; this supplies the separately required superexponential contribution. The power-series coefficient bound in (15) is valid because R_b(v)^r is a coefficientwise subseries of e^(rv), with its first possible degree rm. Integrating (1+v)v^k gives the displayed geometric tail and hence equation (16).

The base (r/(r+2))^r is at most 1/3 for integer r≥1, since r log(1+2/r) is increasing. This is strictly smaller than e^(−1), so the combined derivative correction is below every fixed primary sector. No uniform-in-r estimate has been proved or used. For r=1 the exact correction is especially transparent:

A_(1,b)−J_(1,b)=m Σ_(h≥3)h^(−m−1), while J_(1,b)=m/2^(m+1).

The numerical implementation's small-v hypergeometric branch is correct: with q=1−e^(−v), the bracket in (12) is Σ_(k≥0)q^k/(r+1+k) = ₂F₁(1,r+1;r+2;q)/(r+1). The regularized lower incomplete gamma used by the code is exactly R_b(v)e^(−v).

## 4. Uniform endpoint expansion, localization, and all orders

The differential equation (1−s)S_m+(s/m)S_m'=1 follows directly from the series coefficient ratio m/(m+j). Thus σ_0=(1−s)^(−1) and σ_j=−sσ_(j−1)'/(1−s) are correct.

The claimed product Taylor bound is valid. For P_ℓ(u)=∏_(i=1)^ℓ(1+iu)^(−1), its alternating derivatives attain their largest absolute values for u≥0 at zero. Its order-N remainder is bounded by m^(−N−1)h_(N+1)(1,…,ℓ), and the complete homogeneous polynomial h_(N+1) is at most (Σi)^(N+1). Summing this polynomial bound against s^ℓ, with any fixed number of s-derivatives, is uniformly finite on [0,d] for d<1. This fills in the direct justification of (18), rather than merely using a formal differential equation.

The localization is sound. For s≤a the phase is increasing and below its saddle maximum. For d≤s≤1, S_m(s)≤m+1 follows by dominating its term ratios by m/(m+1); the phase gap beats this polynomial. For v≥m, R_b(v)≤e^v gives O_r(me^(−m)). The unique nondegenerate saddle is s_r=r/(r+1), with curvature λ=(r+1)^2/r. Therefore the standard interior Laplace expansion, with the uniform amplitude expansion just justified, produces a genuine expansion to every fixed algebraic order.

The author's finite Gaussian-moment algorithm includes all necessary phase terms through z^(2N), all relevant Stirling terms, and the needed amplitude derivatives. Odd powers vanish by Gaussian symmetry. Rational saddle, curvature, harmonic number, Bernoulli numbers, and Gaussian moments ensure rational relative coefficients. The m=b+1 conversion is correctly implemented as (1+1/b)^(p−j)b^(−j), p=(3−r)/2. The order-zero case also works.

## 5. Independent discrete-geometric coefficient derivation

This check is distinct from both the author's local Gaussian expansion and the root's Gamma-centered-moment expansion.

Write j=(j_1,…,j_r), J=Σj_a, q=r/(r+1), and H=H_r. Expanding the r copies of the exact Taylor tail and integrating each monomial gives

J_(r,b) = (rm)!/[(m!)^r(r+1)^(rm+1)] · rm/(r+1)
            · Σ_(j_a≥0) q^J [1+(J+1−(r+1)H)/(rm)]
            · ∏_(i=1)^J(1+i/(rm)) / ∏_(a=1)^r∏_(i=1)^(j_a)(1+i/m).

Normalize the sum by (1−q)^(−r)=(r+1)^r. It is then an expectation over r independent geometric random variables with probabilities (1−q)q^j. With P_k(n)=Σ_(i=1)^n i^k, the logarithm of the product ratio has coefficient

(−1)^(k+1)[r^(−k)P_k(J)−Σ_aP_k(j_a)]/k

at m^(−k). Exponentiate this polynomial series, multiply by the displayed linear factor, and take geometric moments. The independent script obtains those moments by repeated application of q d/dq to (1−q)^(−1), then multiplies by the separate factorial-ratio Stirling correction

exp{Σ_(k≥1) B_(2k)(r^(1−2k)−r)m^(−2k+1)/[2k(2k−1)]}.

This gives exactly the coefficient lists in the author's JSON for r=1,2,3,4 through degree 3.

This alternative expansion can also be justified asymptotically. Restrict J≤m^δ with fixed 0<δ<1/2 to expand the product logarithm with polynomially controlled remainders and sum them against geometric weights. The remainder of the exact sum, J>m^δ, is exponentially small in m^δ up to polynomial factors: group by total degree and use the same coefficient domination by e^(rv) employed in (15). Thus the geometric method is more than a numerical extrapolation.

At first order, E j_a=r, E J=r², and E J²=r⁴+r³+r². The product-ratio correction averages to −r²(r+1)/2+r, while the linear factor contributes r+1/r−(r+1)H_r/r. The factorial-ratio Stirling term is (1/r−r)/12. Their sum is

d_(r,1)=−r²(r+1)/2+23r/12+13/(12r)−(r+1)H_r/r.

Adding p=(3−r)/2 confirms the stated c_(r,1) for every fixed r, independently of the source's Laplace-correction calculation.

## 6. Constants and explicit coefficients

The independent exact-tail formula and Stirling yield

D_r=r^(3/2)(r+1)^(r−2)(2π)^((1−r)/2),
C_r=D_rβ_r=r^(r+3/2)(2π)^((1−r)/2)/(r+1)².

Hence C_1=1/4, C_2=8/(9√π), and C_3=81√3/(32π), confirming the proposed leading constants.

The independently reproduced relative coefficients in b are:

- r=1: 1, 1, 0, 0
- r=2: 1, −27/8, 5669/128, −962949/1024
- r=3: 1, −43/3, 33952/81, −42671116/2187
- r=4: 1, −211/6, 2962805/1536, −645794613/4096

In particular, both explicit expansions in source equation (4) pass unchanged.

## 7. Exact rational numerical checks and reproducibility

The independent script uses the identity

R_b(v)^r=Σ_(k=0)^r(−1)^k binom(r,k)e^((r−k)v)E_b(v)^k.

If E_b(v)^k=Σ_n d_(k,n)v^n/n!, the integers d_(k,n) are computed by exact binomial convolution. Integrating every term then gives the finite rational expression

J_(r,b)=Σ_(k=0)^r(−1)^k binom(r,k)Σ_n d_(k,n)
         · [(n+1)−(k+1)H_r]/(k+1)^(n+2).

This calculation uses no quadrature, no incomplete gamma, and no saddle approximation. Exact Fraction arithmetic avoids cancellation errors. After normalization, all six values r=2,3 and b=50,100,200 agree with the author's recorded values to at least 44 decimal places; their absolute discrepancies are between 7.4×10^(−47) and 4.4×10^(−46), consistent with rounding 45 significant digits. The independent script also checks J_(1,b)=m/2^(m+1) exactly for b=0,…,30 and verifies all three recorded exact A_1 values against m(ζ(m+1)−1).

Reproduce the independent checks with:

    python fixed-sector-independent-audit.py > fixed-sector-independent-validation.json

The JSON records source hashes, all coefficient arrays, all numerical comparisons, and `all_checks_pass: true`. SymPy 1.14.0 and mpmath were used. This script's numeric comparisons cover the six J entries specified above and the three A_1 entries; the theorem is supported by proof, not by treating a finite numerical check as exhaustive.

The author's full numerical command was also rerun independently in this environment:

    python fixed-sector-verify.py --order 3 --numerics > fixed-sector-audit-reproduced.json
    cmp fixed-sector-validation.json fixed-sector-audit-reproduced.json

It completed successfully, and `cmp` returned exit code 0: the entire supplied validation JSON, including b=500 principal values and exact A_2/A_3 quadratures, reproduced byte-for-byte. This is a reproducibility check, distinct from the independent rational and geometric methods above.

## 8. Scope that must remain in the final report

The source's asymptotic-scale warning is essential and correct. Replacing an exact earlier sector by finitely many powers of 1/b generally creates an algebraic truncation error at that sector's larger exponential base, overwhelming later sectors. Exact-sector remainder formulas cannot be restated with finitely truncated sector expansions without adding those errors.

The following are not established by this work: uniformity as r grows with b, optimal truncation or summability, a justified sum of all asymptotic sector formulas, a complete description at the accumulation scale e^(−b), or any combinatorial identification independent of the separately audited cap theorem. These are limitations of scope, not defects in the fixed-sector theorem.

**Final conclusion:** the fixed-K positive remainder theorem, next-sector equivalence, fixed-r all-orders algebraic expansion, derivative-exponential separation, leading constants, and displayed r=2 and r=3 coefficients all pass this independent audit.
