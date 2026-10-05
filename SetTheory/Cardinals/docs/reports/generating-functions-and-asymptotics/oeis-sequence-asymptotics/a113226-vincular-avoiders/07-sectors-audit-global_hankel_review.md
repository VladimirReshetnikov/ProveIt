# Independent global Hankel audit

Status: the independently checked global construction passes. The local all-orders saddle proof separately passed the complete review recorded in sector_remainders_review.md.

## Findings returned by the global auditor

1. The global branch A(z)=F(exp(z/2)) is valid, with cuts zeta_k+[0,infinity), period 4 pi i, and odd local strength 2 pi versus even local strength pi.
2. The complete cut contour must be clockwise: lower bank from infinity inward, endpoint loop clockwise from lower to upper bank, upper bank outward. In delta=zeta_k-z coordinates the loop angle decreases from pi to -pi. The pole test confirms the sign.
3. The explicit upper/lower bank values are epsilon_k B_cut(s) exp(+-i g_k pi/q), q=sqrt(1-exp(-s)); the common modulus tends to 2 exp(-3) at the endpoint and is (1/4)exp(-s)(1+O(s exp(-s))) at infinity.
4. The bank jump integral DOES converge absolutely down to the endpoint. Its incompleteness is caused by the potentially nonzero limiting endpoint-loop integral, not divergence of the banks. A fixed positive radius avoids this pitfall, and cut-annulus Cauchy proves radius independence.
5. The bound |H_k(n)| <= C_r (|zeta_k|-r)^(-n-1) holds uniformly in k,n>=1. One possible C_r is r M_r+(1/pi)int_r^infinity B_cut(s)ds. It gives absolute convergence of the exact sector sum.
6. Uniform large-t asymptotics on both half-planes, up to their banks, are F(t)=-t^(-2)[1+O(log|t|/|t|^2)]. Hence the right vertical sides decay; the left sides decay because F(t)~t at zero.
7. On horizontal lines Im z=+-(2K+1)pi, |A| has a common integrable envelope B_strip. Rectangle deformation yields [z^n]A=sum_{|k|<=K}H_k+R_K and |R_K| <= ||B_strip||_1/[pi ((2K+1)pi)^(n+1)]. Letting K grow proves the exact sector sum.
8. Reflection gives H_{-k}=conj(H_k), including the orientations and factor 1/(2 pi i).

The proof note subsequently corrected one explanatory orientation sentence: the slit domain's own cut boundaries are clockwise and already equal the H contours. Its H definition and theorem sign were correct throughout.

## Supplementary checks by the proof author

- Symbolic circle-Gaussian expansion independently verifies the first correction and gives
  c2 = kappa^4(1-zeta)^2/8 + kappa(53 zeta-17)/72 -35/(2592 kappa^2).
- Direct high-precision loop-plus-bank quadrature for k=0,1,2 at n=512 and4096 agrees with the first three terms, with bounded n-scaled residuals.
- These numerical checks are regression evidence, not a substitute for the local saddle proof or its separate independent review.

Frozen source SHA-256: 1e10659694dd56c8e2e8bf97bb443cb40c1c86e694a363e44295892d1f81c842.
