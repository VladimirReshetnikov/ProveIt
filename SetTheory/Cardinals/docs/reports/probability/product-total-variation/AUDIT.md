# Research audit

Date: October 8, 2026.

## Scope and status

This package presents independently derived mathematical results with full
written proofs. The results are not externally peer-reviewed, and no Lean or
other proof-assistant verification is claimed. Numerical tests check the code,
not the universal theorem or bibliographic novelty. No famous open conjecture
is claimed to have been resolved.

The principal proposed strengthening is deterministic **relative** approximation
of product-distribution total variation with a linear marginal-input factor,
subject to explicit logarithmic distance/accuracy factors. This is stronger
than the initial additive-only route considered in developing the argument.

## Proof dependencies

1. **Classical identity, not claimed new:** Fourier representation of the
   intersection kernel min(p,q) through sqrt(pq) exp(-|log(p/q)|/2).
2. **Elementary moment lemma:** M1 <= 2*d and M2 <= 6*d for common-support
   Hellinger weights. Singular mass is included in d.
3. **Principal relative variation lemma:** total variation of the integrand on
   log frequency is <= d times (1 + a logarithmic frequency factor).
4. **Midpoint quadrature and tails:** low tail <= epsilon*d/48, high tail <=
   epsilon*ell/12, midpoint error <= epsilon*d/8. These imply the explicit
   relative-error theorem and interval formula.
5. **Structural oracle:** products factor into local transforms; fully observed
   Markov paths factor into contractive complex transfer matrices.
6. **Bit implementation:** positive rational singleton-cylinder discrepancy
   supplies ell0 >= 2^(-2b) for products; elementary-function argument lengths
   and guard precision remain polynomial, and logarithmic in N beyond b.
7. **Independent additive route:** positive periodized kernel with normalization-
   weighted alias error and an absolutely summable Fourier tail.
8. **Extensions:** exact alias identity, positive spectral form, and the uniform
   normalized Bayes-risk curve follow from the additive route.

The results do not depend on the correctness of any openai/math claimed result.

## Source audit

Primary sources consulted include:

- Weiming Feng, Liqiang Liu, Tianren Liu, *On Deterministically Approximating
  Total Variation Distance*, SODA 2024, pp. 1766-1791; arXiv:2309.14696.
  Cited relative bound: O(q*n^2/epsilon * log(q) * log(n/(epsilon*d))).
- Konrad Anand, Alistair Benford, Heng Guo, *Linear Time Approximation of the TV
  Distance between Product Distributions*, arXiv:2607.27088, 2026; author-hosted
  manuscript. Cited randomized relative bound: O(q*n/epsilon^2 * log(1/delta)).
- Weiming Feng, Heng Guo, Mark Jerrum, Jiaheng Wang, *A Simple Polynomial-Time
  Approximation Algorithm for the Total Variation Distance between Two Product
  Distributions*, TheoretiCS 2, Article 8, 2023. The publisher identifies the
  article as 8; some later bibliographies label it 7.
- Arnab Bhattacharyya et al., *On Approximating Total Variation Distance*,
  IJCAI 2023, for exact-computation hardness and earlier deterministic special
  cases.
- Andrea Vedaldi and Andrew Zisserman, *Efficient Additive Kernels via Explicit
  Feature Maps*, CVPR 2010. Their intersection-kernel Fourier feature map and
  periodic sampling framework are prior art, not an invention of this package.
- Antti Koskela et al., AISTATS 2021; Koskela and Honkela, arXiv:2102.12412;
  and Gopi, Lee, Wutschitz, NeurIPS 2021, for earlier Fourier privacy-loss
  composition and error analysis.

Searches for deterministic Fourier/Mellin/log-frequency product-TV approximation
were not sufficient to certify global priority. The claim is a proved bound in
this manuscript and an explicit comparison with the cited bounds, not a claim
that every related paper has been exhausted.

## Repository inspiration

Repository: https://github.com/openai/math

Inspected motivating manuscript:
`preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/`

Source files inspected through the GitHub connector:

- `build/paper.tex`, blob SHA
  `4901e171afa6e8b22487e45aa779fb8e52d42c61`.
- `build/sections/01-introduction.tex`, blob SHA
  `8b648d07393132d95d365fd408e0967809199e1c`.

The introduction's distinction between relaxation and total-variation mixing,
and its independent-spin endpoint, motivated the computational question. The
manuscript's interacting-spin claims were not independently audited here and
are not cited as proven inputs. No copyrighted external manuscript is bundled.

## Assumptions and limits that must stay attached to the claims

- Elementary real operation counts include log, exp, sqrt, sin, and cos.
  They are not claimed to be unit-cost rational arithmetic in a bit model.
- The separate polynomial-bit proof makes the near-linear dimension improvement
  valid for bounded-logarithmic-precision rational product inputs.
- The relative node count still depends logarithmically on d. No uniform
  deterministic O(N*poly(1/epsilon)) bound independent of d is proved.
- The prior deterministic comparison is not a uniform parameterwise dominance
  statement. The newer randomized linear-time result is acknowledged.
- Markov paths are fully observed. Hidden-state marginalization destroys the
  simple complex-power factorization in general.
- All formulas explicitly exclude zero-probability logarithms and preserve
  singular support mass.
- The exact alias identity uses common-support submeasures, not the full
  probability laws when supports differ.
- The Bayes-risk theorem is additive and normalized; it is not a uniform
  relative guarantee near zero risk or a uniform unnormalized privacy-profile
  guarantee at extreme thresholds.
- The fixed-frequency obstruction concerns a specified positive quadrature
  formula, not arbitrary adaptive or nonlinear Fourier-oracle algorithms.

## Numerical trust boundary

The interval reference implementation trusts mpmath.iv 1.3.0's directed
arithmetic and implemented elementary interval functions. Endpoints are
extracted as exact dyadic fractions. The proof of the mathematical algorithm
does not rely on this particular software. A verified elementary-function
checker is proposed as further work.

The NumPy prototype is explicitly uncertified. Exact enumeration uses Python
Fraction and is independent of the Fourier formula. Alias identity checks use
70-digit arithmetic, not formal proofs. Scaling references use an 80-digit
binomial calculation. Hardware-dependent timings are descriptive only.

See `data/verification.json` for the actual counts, exact certificates, tolerances,
and recorded success status. It is the authoritative computational log; the
manuscript's printed decimal endpoints are rounded display values.
