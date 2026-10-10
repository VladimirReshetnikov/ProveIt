# Claim-status ledger

Baseline: `28357e8ca63dd78327db91d9be239d75e4462879`.

| Claim | Status | Scope / evidence |
|---|---|---|
| Finite signed Hausdorff representation iff a+b >= 1 | Proved analytically | a,b > 0; article Theorem 3.1. |
| One-crossing density above threshold | Proved analytically | a+b > 1; normalize by the gamma kernel and differentiate. |
| Critical atom has mass 1/a | Proved analytically | a+b = 1; unique representing measure; no density-only replacement possible. |
| Critical defect differences and Hankel matrices are strictly positive | Proved analytically | Positive density on the whole open interval. |
| Critical atom emerges weakly from the supercritical kernels | Proved analytically | Fixed 0<b<1, a=1-b+epsilon. |
| Positive double kernel | Proved analytically | Every a,b>0 on the principal slit plane. |
| Nonzero zeros absent in the closed unit disk, except excluded z=1 | Proved analytically | Every a,b>0, even a+b<1. |
| Slit-plane nonvanishing | Proved analytically | a+b >= 1; below threshold not established. |
| Unique simple angular zero | Proved analytically | a+b >= 1, every radius 0<rho<=1. |
| Critical normalized radius strictly increases | Proved analytically | a+b=1, both orders strictly positive; exact positive derivative. |
| Left-atom normalized radius strictly decreases | Proved analytically | Applies to Li_a(z)-z for every a>0. |
| Gaussian values strictly negative | Proved analytically | All a,b>0, analytic/Abel convention when ordinary convergence fails. |
| Gamma-normalized negative Gaussian is strictly jointly log-convex | Proved analytically | All a,b>0 by strict Holder inequality. |
| Transport, elementary critical series, normalized Hurwitz identities | Proved analytically | Hypotheses stated in article; classical ingredients credited. |
| Parameter-dependent Euler enclosures | Proved analytically | a+b >=1; ordinary sum only for a+b>1, Abel at equality. |
| Extension of universal Euler constant one to all a+b>=1 | Disproved | Exact rational counterexamples a=1/10 with b=9/10 (Abel) and b=1 (ordinary), at N=1. |
| Existing constant-one theorem with a>=1 | Retained as valid prior result | Not contradicted by the counterexample. |
| Eight Gaussian numerical intervals | Certified finite computations | Standard-library-only exact rational replay. |
| Eleven angular brackets in a+b>=1 | Certified finite computations + analytic uniqueness | Includes nine critical and two strictly supercritical cases. |
| One angular bracket at a=b=1/4,rho=1/2 | Certified existence only | No uniqueness conclusion. |
| Nine symbolic formulas and 21 Bernoulli coefficients | Exact symbolic checks | These do not formalize the full analytic proof. |
| Quadratures and 15-point critical-constant grid | Numerical diagnostics only | No rigorous quadrature error bounds claimed. |
| Global critical optimal constant pi/4+log(2)/2 | Conjectural upper bound | Endpoint limit proves necessity; fixed-parameter optimal constant -2g is proved. |
| Strict decrease of -2g(a,1-a) in a | Conjectured | Fifteen-point diagnostic grid, not a proof. |
| Original finite-b normalized-radius conjecture | Unresolved here | Critical and left-atom cases are additional theorems, not a general solution. |
| S6 Gaussian identity | Unresolved here | Baseline status retained. |
| Global slit-plane nonvanishing below threshold | Open question here | Disk result does not imply it. |
| Proof-assistant formalization | Not performed | Written proofs, rational certificates and symbolic checks are distinct. |

Novelty is relative to the inspected repository baseline. No exhaustive worldwide priority claim is made. No mathematical error in the inspected, correctly scoped a>=1 theorems was established; the article records necessary corrections to unqualified extensions.
