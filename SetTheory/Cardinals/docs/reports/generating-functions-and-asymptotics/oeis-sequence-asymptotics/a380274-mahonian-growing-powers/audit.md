# Independent mathematical audit

Date: 1 October 2026.

## Verdict

The mathematics in the audited version of `mahonian_crossover.tex` is internally consistent. No unresolved mathematical error was found. The leading crossover, both adjacent regimes, exact first-shell equivalent, collision-location corollary, arbitrary finite expansion, displayed fourth-order correction, unnormalized multiplicative equivalent, and fixed-path inverse formulas are supported by the arguments given.

Audited TeX SHA-256:

`dc2d592d5347e41ecb2e94027aa195bb54340438c6157937034c705fc0ccc3ce`

This audit checks the proof and independently checks its algebra and numerical values. It does not certify novelty or independently verify the bibliographic claims.

One minor rigor clarification was requested and has been applied: symmetry and log concavity alone do not exclude a longer modal plateau. The text now first identifies the central sites as modes and then invokes the proved strict inequality q_n < 1 to exclude additional modes for sufficiently large n.

## Proof checks

### Fourier estimates and microscopic cancellation

The small-arc bound follows from the log-sinc expansion, with all factors satisfying |jt| <= 1. The middle arc 1/n <= |t| <= A/n can retain the factors j <= floor(1/|t|), giving exp(-c/|t|) <= exp(-cn/A). For A/n <= |t| <= pi, the last half of the factors are bounded by 2pi/(n|t|), which is uniformly below one for fixed A > 4pi. Both tail estimates are sufficient after multiplication by any fixed standardized Fourier-moment weight.

The exact cumulant identity and the scaling lambda_(2m) = O(n^(1-m)) are correct. Gaussian integration of a finite cumulant expansion yields the asserted fixed-derivative expansions. Positivity on each bounded standardized interval then justifies the logarithmic derivative estimates. Integrating the second logarithmic derivative preserves the essential factor (x^2-delta^2)/V in the local-profile error; this avoids the n^3 amplification that would invalidate a bare relative local central limit estimate.

### Domination and endpoint regimes

Closure of interval-supported log-concave sequences under convolution is valid. The first ratio outside the mode(s) satisfies

log q_n = -(1+2delta)/(2V) (1+O(n^-1)).

Consequently b_m <= q_n^m is a valid global bound. On compact positive rho intervals it supplies the summable geometric majorant needed for dominated convergence. In the supercritical regime, the exact inequality bounding the remainder after the first shell by 2q_n^(2r)/(1-q_n^r) is correct. Keeping q_n exact is essential when rho grows arbitrarily fast.

In the subcritical regime, the central quadratic squeeze and the log-concavity tail extension prove the result for every r -> infinity with r/V -> 0. No additional restriction such as r >> log n is hidden in the argument: after division by sigma/sqrt(r), the outer-tail bound is at most a constant times

exp(-cr) (sqrt(r)/sigma + 1/sqrt(r)),

which vanishes. Gaussian Riemann sums then give the stated normalization. Compactness of the extended rho-line and separation of the two lattice shifts justify the full sequential theorem.

### Collision-location corollary

The conditional mass is exactly M_n(mu+x)^r/S_n(r). In the critical window, pointwise convergence plus the same summable geometric majorant gives total-variation convergence to the normalized lattice Gaussian. In the subcritical window, the quadratic squeeze and vanishing tails give weak convergence of sqrt(r)Y_n/sigma to the standard normal. The corollary correctly says convergence in distribution here; total-variation convergence from a discrete law to a continuous normal law would be false. Symmetry plus the modal tail estimate gives uniform mass on the one or two modes in the supercritical regime.

### Arbitrary-order remainder

The formal generator is well defined: lambda_(2m) begins at z^(m-1), V^-1 begins at z^3, and each coefficient uses finitely many terms. The leading quadratic contribution cancels in P, so P has zero constant term.

Taylor expansion of log F through degree 2H, using evenness and 3H >= L+1, produces a remainder which becomes O(n^(-L-1)(1+|x|^(2H+2))) after multiplication by r. Expanding the finite set of retained Fourier moments to sufficient order preserves this polynomially weighted error; the quadratic term does not lose n^3 because its V^-1 factor cancels that growth. On |x| <= A log n the correction tends uniformly to zero, so exponentiation preserves a polynomially weighted remainder. Summation against the geometric majorant introduces no logarithmic loss. Taking A sufficiently large handles the actual tail; approximating polynomial-Gaussian tails are smaller still.

### Explicit and unnormalized formulas

The quartic exponent coefficient is rho b_n/(24V). Since b_n = -54/(25n)+O(n^-2) and V^-1 = 36n^-3(1+O(n^-1)), this is -81rho/(25n^4)+O(n^-5). The displayed correction therefore has the correct sign and coefficient. The identity Psi_delta = 4Theta_delta''-4delta^2 Theta_delta' is also correct.

The reported logarithmic normalization coefficients imply

V log J_0 = -3n^2/400 - 5883n/490000 - 13963/500000 + O(n^-1).

The shift-normalization factor cancels to produce Z_delta rather than Theta_delta in the unnormalized theorem. Using the actual rho_n is necessary and is correctly emphasized. Retaining log J_0 through order n^(-L-3) leaves an O(n^(-L-1)) error after multiplication by r = O(n^3), as claimed.

## Independent symbolic recomputation

`audit_independent.py` constructs density Edgeworth corrections using probabilists' Hermite polynomials. It does not call or reuse the original `derive_coefficients.py` weighted-Fourier-moment calculation. The independent calculation reproduces:

- Every displayed a_n coefficient through n^-4, and the existing n^-5 coefficient
- b_n through n^-5, including the required leading value -54/(25n)
- J_0 through n^-5
- log J_0 through n^-3 and all three unnormalized exponential constants

Complete rational output is in `audit_symbolic.txt` and in the `symbolic` section of `audit_independent_results.json`.

## Independent numerical verification

The same independent program builds Mahonian rows by exact integer recurrence, then evaluates powers at 85 decimal digits. It tests odd n = 21, 23, 61, 63, 121, 123, 241, 243, 481, 483, with rho = 0.2, 1, 5. These exercise the two residue classes absent from the original even-n examples. The analytic log-concavity geometric bound for numerical truncation, evaluated at 85-digit precision, is below 10^-75 in each reference sum. These are high-precision checks, not interval-arithmetic certificates.

At rho = 1, the scaled relative fourth-order residual n^5(T/approximation-1) is:

| n | delta | scaled residual | predicted limiting value |
|---:|---:|---:|---:|
| 21 | 0 | 27.6887498977 | 34.4256041561 |
| 121 | 0 | 33.0881443898 | 34.4256041561 |
| 481 | 0 | 34.0817342761 | 34.4256041561 |
| 23 | 1/2 | 23.1209312392 | 28.3087755820 |
| 123 | 1/2 | 27.2091769319 | 28.3087755820 |
| 483 | 1/2 | 28.0225185003 | 28.3087755820 |

The limiting values are predictions from the independently computed next coefficient, not numerical fits. Writing D_j=x^j-delta^j, w=exp(-rho D_2/2), and Phi_j=sum D_j w, Phi_24=sum D_2 D_4 w, the omitted absolute n^-5 coefficient is

-(rho a_5/2) Phi_2 + (341091rho/30625) Phi_4 - (2187rho^2/1250) Phi_24,

where a_5 = -418195109644373223/7671570156250000. Dividing this by Theta_delta(rho) gives the predicted scaled relative-error limits. All thirty numerical test records and their reference-tail bounds are in `audit_independent_results.json`.

## Fixed-path inverse audit and independent checks

The added inverse section is correct for the explicitly fixed path r_n = rho V_n. The Lambert W expression solves f(X)=y exactly on its large positive branch. Stirling gives

log S_n(rho V_n) = rho n^4(log n-1)/36 + rho n^3(log n+2log 6-3)/72 + O_rho(n^2 log n).

The leading relation first establishes X/n -> 1, then X-n = O(1). Taylor expansion of the explicit functions f and g, without assuming that the original integer-indexed sequence has a smooth continuation, yields the displayed O(1/X) corrected inversion remainder. Quadratic Taylor terms and the forward O(n^2 log n) remainder both have this size after division by f'(X), which is of order X^3 log X. Eventual nearest-integer recovery at exact index inputs is therefore justified, with no certified finite onset claimed.

The stronger real model F_(delta,L) has forward error O(n^(-L-1)), an eventually positive lattice factor, and derivative asymptotic to rho n^3 log n/9. Its large real inverse consequently has error O(n^(-L-4)/log n) at the correct parity-class inputs. The parity-specific model is explicitly chosen, rather than implicitly attributed to the original sum. The proof's treatment of arbitrary threshold inputs avoids the invalid claim that a vanishing continuous error determines a ceiling uniformly next to integer thresholds. Monotonicity of Y_n follows from coefficientwise convolution growth, positive new support, and increasing powers.

The independent program now includes two inverse diagnostics for every numerical row. Exact forward inputs are computed as r log C_n + log T, using the exact integer modal coefficient.

1. With B(X)=(log X+2log 6-3)/(2(4log X-3)), the error n-X+B(X) is O(1/X). At rho=1:

| n | n-X+B(X) | n times this error |
|---:|---:|---:|
| 21 | 0.0416149959991 | 0.873914915982 |
| 121 | 0.00791426679836 | 0.957626282602 |
| 481 | 0.00203328913646 | 0.978012074635 |

The independently derived n^2 log n coefficient is -rho/9. Combining it with the quadratic Taylor correction predicts the limit n[n-X+B(X)] -> 131/128, rather than fitting that limit from the data.

2. The program numerically solves the L=0 real model, using Gamma, the three displayed coefficients of log J_0, and Z_delta. Its inverse errors at rho=1 are:

| n | L=0 root minus n | n^4 log n times this error |
|---:|---:|---:|
| 21 | 1.23014946255e-5 | 7.28373671938 |
| 121 | 6.41527074011e-9 | 6.59502851789 |
| 481 | 1.92157641053e-11 | 6.35237192755 |

The predicted scaled limit is ell_4/4+(243/50) E_(rho,delta)[x^2] under the normalized lattice Gaussian, where ell_4=10558544422977/3631512500000. At rho=1 this is 5.58686859199 for delta=0 and 5.58687064517 for delta=1/2. The slow approach is consistent with inverse-logarithmic corrections. All inverse errors, scaled values, and predicted limits appear in `audit_independent_results.json`.

## Reproduction and file paths

All paths below are relative to `/workspace/shared/oeis-mahonian-crossover/`:

- Audited proof: `mahonian_crossover.tex`
- Original coefficient code/output: `derive_coefficients.py`, `coefficients.txt`
- Original numerical code/output: `check_crossover.py`, `numerical_checks.json`
- Independent reproducible audit: `audit_independent.py`
- Independent symbolic results: `audit_symbolic.txt`
- Independent numerical and symbolic results: `audit_independent_results.json`
- This report: `audit.md`

Reproduce with `python /workspace/shared/oeis-mahonian-crossover/audit_independent.py`. Runtime in the audit environment was approximately ten seconds.
