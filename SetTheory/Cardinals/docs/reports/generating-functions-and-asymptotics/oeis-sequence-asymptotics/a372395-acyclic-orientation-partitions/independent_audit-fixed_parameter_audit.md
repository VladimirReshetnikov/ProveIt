# Audit of the fixed positive chromatic parameter corollary

Review date: 1 October 2026

Reviewed source: tutte_axis_extension.md, SHA256 fc8faac3bbde751638e4828ef4c6ccb92471715069a02f2d42e985931f4d180d.

The proposed extension is mathematically valid for fixed v>0, uniformly for v in compact subsets of (0,infinity). Its normalization, generalized Gamma exponent, first correction, large-part estimate, and inverse constants all check out. It can be included as a corollary of the core theorem.

The exact integral changes the Gamma law from shape n+1 to shape n+v. Writing T=n+sqrt(n)z, its logarithmic density differs by

    (v-1)log(1+epsilon z)

and by replacing the ordinary Stirling correction with

    -sum_{r>=1} (-1)^(r+1) B_(r+1)(v) epsilon^(2r)/(r(r+1)).

This is the standard generalized Stirling expansion about n. At v=1 the Bernoulli-polynomial values recover the original correction. The leading density and its Gaussian tilt are unchanged, so the normalization Gamma(n+v)/Gamma(v) preserves the same A, C, and p. The first new term is (v-1)epsilon z, giving precisely a1(v)=a1(1)+(v-1)M_2/2.

Deletion-contraction gives H_v(G+e)=H_v(G)+H_v(G/e), and all terms are positive for v>0. Thus the edge-monotonicity comparison remains available. Directly evaluating the chromatic polynomial of a clique on m vertices joined to an independent set of size L gives

    H_v = (v)_m (m+v)^L.

After division by (v)_n, each factor is (m+v)/(m+v+j-1), j=1,...,L. The logarithm inequality in the corollary therefore gives the stated denominator n+v-1 and exponent -L(L-1)/(2(n+v-1)). This is uniform on the indicated compact v sets.

One endpoint detail should be explicit in the final manuscript. For 0<v<1, t^(v-1) is unbounded at zero, so one cannot replace it by a uniform pointwise bound throughout the lower Gamma tail. The required estimate nevertheless follows immediately from integrability. With M=o(n), the function e^(-t)(t+M)^n is increasing on [0,n/2] for sufficiently large n. Hence

    integral_0^(n/2) t^(v-1)e^(-t)(t+M)^n dt
      <= e^(-n/2)(n/2+M)^n (n/2)^v/v.

Relative to Gamma(n+v), this is exp(-Omega(n)+O(M)) times a fixed power of n, uniformly for v bounded away from zero and infinity. The upper tail has no endpoint singularity and is controlled by the same fixed-parameter Gamma-tail argument. This supplies the otherwise abbreviated signed-tail step.

Finally, Gamma(n+v)=n! n^(v-1)(1+v(v-1)/(2n)+O(n^(-2))) gives alpha0=v-1/2-p and d0=log(A sqrt(2pi)/Gamma(v)). The first logarithmic inverse correction is still beta1=a1(v); higher corrections include the Gamma-ratio series. No step establishes uniformity for v growing with n or a limit at v=0, and the corollary properly excludes those claims.
