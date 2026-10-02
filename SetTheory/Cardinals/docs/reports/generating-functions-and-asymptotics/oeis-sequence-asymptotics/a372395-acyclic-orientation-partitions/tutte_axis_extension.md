# Fixed positive chromatic parameter extension

This is a separate corollary proposal, kept outside the frozen core proof.

Let v>0 be fixed and put H_v(G)=(-1)^|V(G)| chi_G(-v). For either unrestricted or distinct partitions, sum H_v(K_lambda) over lambda of n, obtaining B_eta,v(n). All conclusions below are uniform for v in a fixed compact subset of (0,infinity).

The exact Gamma formula is

    H_v(K_lambda)=1/Gamma(v) integral_0^infinity
                    exp(-t)t^(v-1) product_i P_{lambda_i}(t) dt.

After extracting profiles of total size n, the normalized expectation uses T~Gamma(n+v,1). Consequently the core theorem extends as

    B_eta,v(n)=Gamma(n+v)/Gamma(v) * A_eta n^(-p_eta) exp(C_eta sqrt(n))
                * (1+a_eta,1(v)/sqrt(n)+a_eta,2(v)/n+...),

with the same A_eta,C_eta,p_eta as at v=1 and

    a_eta,1(v)=a_eta,1(1)+(v-1)M_2/2.

## Exact modifications to the coefficient generator

Keep the root, Euler--Maclaurin and Fourier terms unchanged. In the formal exponent Q of proof.md, replace the Gamma-density part by

    sum_{j>=1}(-1)^(j+1)epsilon^j Z^(j+2)/(j+2)
      +(v-1)log(1+epsilon Z)
      -sum_{r>=1}(-1)^(r+1) B_{r+1}(v) epsilon^(2r)/(r(r+1)),

where B_r(v) are Bernoulli polynomials. This follows by applying the generalized Stirling expansion to Gamma(n+v) at n=epsilon^(-2). At v=1 it reduces to the original expression. The only first-order change is (v-1)Z, whose Gaussian tilted expectation is (v-1)M_2/2.

## Tail checks

For t/n in [1/2,2], the extra factor t^(v-1) is uniformly comparable to n^(v-1), and Gamma(n+v) is uniformly comparable to n! n^(v-1). Thus the uniform quadratic majorant and pointwise Gaussian decay extend with constants uniform on compact v sets. For the lower signed tail, including v<1, retain the integrability of t^(v-1): e^(-t)(t+M)^n is increasing on [0,n/2] for large n, so multiply its endpoint bound by integral_0^(n/2)t^(v-1)dt=(n/2)^v/v. This gives the same exponential suppression uniformly when v is bounded away from zero. The upper tail is unchanged by fixed powers. The normalized weights and their complex/Fourier estimates are identical.

For the far largest-part tail one can avoid any appeal to AO monotonicity outside v=1. The chromatic polynomial has alternating nonnegative coefficients, so H_v(G)>0 for v>0, and deletion--contraction gives H_v(G+e)=H_v(G)+H_v(G/e). This proves edge monotonicity. The graph consisting of one independent part of size L and m=n-L singleton parts has

    H_v(K_{L,1,...,1}) = Gamma(m+v)/Gamma(v) * (m+v)^L.

Dividing by Gamma(n+v)/Gamma(v) and using log(1+x)>=x/(1+x) gives the exact bound

    H_v(K_{L,1,...,1})/(Gamma(n+v)/Gamma(v))
        <= exp(-L(L-1)/(2*(n+v-1))).

This transfers the same superpolynomial cutoff removal uniformly for compact positive v.

## Inverse

Relative to n! n^(v-1), the amplitude is A_eta/Gamma(v). Thus the logarithmic inverse formula uses

    alpha0=v-1/2-p_eta,
    d0=log(A_eta*sqrt(2*pi)/Gamma(v)),

with the same C_eta and the same Lambert-W core N=L/W(L/e). The Gamma-ratio expansion modifies beta_2 and higher coefficients, and does not change beta_1=a_eta,1(v).

This extension adds a natural fixed-parameter chromatic/Tutte family. It does not claim uniformity when v itself grows with n, and no v=0 limiting theorem is asserted.
