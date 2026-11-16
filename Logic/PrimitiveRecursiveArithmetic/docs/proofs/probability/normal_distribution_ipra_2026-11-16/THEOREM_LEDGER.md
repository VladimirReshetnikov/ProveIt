# Statement-by-statement coverage ledger

Status codes:

- **P** — proved in the manuscript as a finite quantitative theorem schema directly arithmetizable in iPRA.
- **E** — proved for an effective presentation with explicit primitive-recursive moduli/certificates.
- **R** — reused from a specified ProveIt packet, with its formalization status preserved.
- **C** — the source wording needs a correction or extra hypothesis; the corrected result is proved.
- **D** — deferred; the manuscript explains the genuinely additional theorem required.

“Proved in iPRA” here describes the mathematical arithmetization and target derivation. It does **not** mean that this archive already contains a kernel-checked inhabitant of every `Prf PRAAx` target.

| # | Source statement family | Status | Constructive result / qualification | Manuscript location |
|---:|---|:---:|---|---|
| 1 | Density with parameters `μ,σ²` | P | Fixed rational names with a positive lower bound for `σ`; explicit density evaluator. | §3 |
| 2 | Standard normal density | P | Specialization `μ=0,σ=1`. | §3 |
| 3 | Standardization `(X-μ)/σ` | P | Effective affine change of variables with apartness for `σ`. | Thm. 3.1 |
| 4 | Gaussian integral / normalization | P/R | Gamma substitution plus the existing effective `Γ(1/2)=√π` contract. | §3, §2 |
| 5 | CDF integral formula | P | Improper integral replaced by finite quadrature plus Gaussian tail modulus. | §3 |
| 6 | Error-function formula | P | `Φ(x)=1/2[1+erf(x/√2)]`, as equality of fast names. | Cor. 3.2 |
| 7 | Quantile function | E | Interval-valued primitive-recursive inverse by monotone bisection; no real trichotomy. | Thm. 4.6 |
| 8 | Support is all of `R` | E | Every rational interval has a computable positive mass lower bound. | Cor. 3.8 |
| 9 | Mean `μ` | P | Odd integrand cancellation after standardization. | Thm. 3.3 |
| 10 | Median `μ` | P | Symmetry and strict effective monotonicity of the CDF. | Thm. 3.3 |
| 11 | Mode `μ` | P | Square completion / monotonicity of the exponential. | Thm. 3.3 |
| 12 | Variance `σ²` | P | One finite integration-by-parts identity. | Thm. 3.3 |
| 13 | Mean absolute deviation | P | `σ√(2/π)` by a one-step substitution. | Cor. 3.4 |
| 14 | Median absolute deviation | P/E | `σ Φ⁻¹(3/4)` using the effective quantile. | Cor. 3.4 |
| 15 | Skewness | P | Zero by symmetry. | Cor. 3.4 |
| 16 | Kurtosis / excess kurtosis | P | `3` / `0` from the moment recurrence. | Cor. 3.4, §5 |
| 17 | Symmetry of density and CDF | P | Exact finite identities under `x↦-x`. | §3 |
| 18 | Unimodality | P | Sign of the first derivative. | Prop. 3.5 |
| 19 | Inflection points | P | Second derivative `((x-μ)²/σ⁴-1/σ²)f`. | Prop. 3.5 |
| 20 | Log-concavity | P | Constant negative second derivative of `log f`. | Prop. 3.5 |
| 21 | Density and CDF ODEs | P | Differentiation contracts with explicit remainders. | Prop. 3.6 |
| 22 | Power series for `Φ` | P | Finite alternating sum with first-omitted-term bound after a computable threshold. | Thm. 4.1 |
| 23 | Density-factor series for `Φ` | C/P | Shown globally convergent; any “asymptotic only” wording is corrected. | Thm. 4.2 |
| 24 | Mills upper inequality | P | `1-Φ(x)<φ(x)/x` by finite integration by parts. | Thm. 4.3 |
| 25 | Mills lower inequality | P | `xφ(x)/(1+x²)<1-Φ(x)` by an exact derivative comparison. | Thm. 4.3 |
| 26 | Full finite Mills expansion | P | Arbitrary externally fixed depth with an explicit signed remainder. | Thm. 4.4 |
| 27 | 68–95–99.7 rule | P | Exact rational enclosures at `1,…,6`; executable widths ≈`1.2e-63`. | Cor. 4.5, Appendix B |
| 28 | Newton iteration for quantiles | E | Safeguarded bracketed Newton with entry and quadratic-error bounds. | Alg. 4.7 |
| 29 | Inverse-CDF differential equation | E | Effective derivative formula away from endpoints. | §4 |
| 30 | Moment recurrence | P | `m_(n+2)=(n+1)m_n` by finite integration by parts. | Thm. 5.1 |
| 31 | Odd moments vanish | P | Symmetry. | Cor. 5.2 |
| 32 | Even moments `(2n-1)!!` | P | Quantifier-free induction from the recurrence. | Cor. 5.2 |
| 33 | Raw noncentral moments | P | Finite binomial expansion. | Cor. 5.3 |
| 34 | Absolute moments | P/R | `σ^r 2^(r/2)Γ((r+1)/2)/√π` with effective gamma names. | Thm. 5.4 |
| 35 | Gaussian derivatives / Rodrigues formula | P | Hermite recurrence and induction. | Thm. 5.5 |
| 36 | Hermite generating function | P | Coefficientwise finite identity with explicit tails when evaluated. | Cor. 5.6 |
| 37 | Hermite orthogonality | P | Repeated finite integration by parts with Gaussian tail discharge. | Cor. 5.7 |
| 38 | Incomplete/truncated moments | P | Boundary recurrence and finite induction. | §5.5 |
| 39 | Conditional mean on an interval | P | Boundary-density quotient with denominator apartness. | §5.5 |
| 40 | Conditional variance on an interval | P | Second incomplete moment recurrence. | §5.5 |
| 41 | Moment-generating function | P | Completion of squares: `exp(μt+σ²t²/2)`. | Thm. 6.1 |
| 42 | Characteristic function | P | Trigonometric completion/finite Fourier argument. | Thm. 6.1 |
| 43 | Fourier transform of a Gaussian | P/R | Effective ODE proof with explicit tails, reusable from the zeta packet. | Cor. 6.2 |
| 44 | Gaussian is self-Fourier after normalization | P/R | Immediate specialization of the transform. | Cor. 6.2 |
| 45 | Cumulants | P | Log-MGF is quadratic; only first two survive. | Cor. 6.3 |
| 46 | Wick/Isserlis moments | P | Coefficient extraction and finite pairing recursion at fixed order. | §6.3 |
| 47 | Stein identity | P | One integration by parts. | Thm. 6.4 |
| 48 | Stein characterization | E | Effective test family solves the CDF comparison; no unrestricted function quantifier. | Thm. 6.5 |
| 49 | Quadratic log-MGF criterion | E/P | Analytic effective MGF with quadratic logarithm is Gaussian. | §6.5 |
| 50 | Differential entropy | P | Direct expectation of the quadratic log density. | Thm. 7.1 |
| 51 | Gaussian maximum entropy | E | KL proof for represented densities with explicit `p log p` integrability. | Thm. 7.2 |
| 52 | KL divergence between normals | P | Closed formula and finite square completion. | Thm. 7.3 |
| 53 | Nonnegativity of KL | P | Finite log-sum/Jensen inequality with rational approximation. | §7.3 |
| 54 | Hellinger distance | P | Closed affinity integral by square completion. | Thm. 7.4 |
| 55 | Total variation for equal variances | P | Crossing point at the midpoint; two CDF evaluations. | §7.4 |
| 56 | Fisher information `(μ,σ)` | P | Exact expectations of score polynomials. | Thm. 7.5 |
| 57 | Fisher information `(μ,σ²)` | P | Reparameterization of the previous matrix. | Thm. 7.5 |
| 58 | Expected maximum bound | P | Log-sum-exp plus Gaussian MGF; independence not required. | Thm. 7.6 |
| 59 | Affine closure | P | Change of variables / transform identity. | §8.1 |
| 60 | Sum of independent normals | P | MGF/CF multiplication with finite product spaces. | Thm. 8.1 |
| 61 | Stability | P | Exact parameter addition. | Cor. 8.2 |
| 62 | Infinite divisibility | P | For each finite `n`, explicit `n`th Gaussian convolution root. | Cor. 8.3 |
| 63 | Product of Gaussian densities | P | Precision-weighted mean and variance after square completion. | Prop. 8.4 |
| 64 | Multivariate normal density | E/P | Rational positive-definite matrices with explicit factorization/apartness certificate. | Thm. 8.5 |
| 65 | Linear projections and marginals | P | Matrix multiplication and scalar Gaussian closure. | Cor. 8.6 |
| 66 | Mahalanobis ellipsoids / chi-square radius | P | Orthogonalization plus sum of squares. | §8.3, §9 |
| 67 | Joint normal + zero covariance ⇒ independence | P | Block-diagonal covariance factorization. | Thm. 8.7 |
| 68 | Sum and difference independence | P | Covariance zero plus joint normality. | Cor. 8.8 |
| 69 | Bivariate conditional normal | E/P | Completion of squares, assuming explicit `1-ρ²>0`. | Thm. 8.9 |
| 70 | Folded normal | P | Sum of two density branches. | Thm. 9.1 |
| 71 | Half-normal | P | Centered specialization. | Cor. 9.2 |
| 72 | Square of a normal | P | Central and one-dimensional noncentral formulas by two-branch substitution. | Thm. 9.3 |
| 73 | Chi-square law | P/R | Finite convolution / gamma-beta algebra. | Thm. 9.4 |
| 74 | Chi, Rayleigh, Maxwell laws | P | Monotone square-root substitution. | Cor. 9.5 |
| 75 | Ratio of centered independent normals | C/P | Cauchy law; centering is essential and stated. | Thm. 9.6 |
| 76 | Product of centered normals | P | CF `(1+t²)^(-1/2)` and `K₀` density via a defining effective integral. | Thm. 9.7 |
| 77 | Lognormal transformation | P | Density, moments, and closure under products/powers. | Thm. 9.8 |
| 78 | Sample mean of normal observations | P | Exact `N(μ,σ²/n)` law. | §10.1 |
| 79 | Orthogonal sample decomposition | P/E | Fixed-dimension rational orthogonal approximation plus invariant Gaussian law. | Thm. 10.1 |
| 80 | Sample mean independent of sample variance | P | Joint normal block independence. | Thm. 10.1 |
| 81 | Scaled sample variance is chi-square | P | Sum of squares of `n-1` standard normals. | Thm. 10.1 |
| 82 | Bias of MLE variance / unbiased variance | P | Exact expectation identities. | Cor. 10.2 |
| 83 | Variances of sample-variance estimators | P | Chi-square moments. | Cor. 10.2 |
| 84 | Maximum-likelihood estimators | C/P | Mean and variance formulas; identical-data boundary handled explicitly. | Thm. 10.3 |
| 85 | Sufficient statistics | E/P | Finite factorization identity for fixed sample size. | §10.3 |
| 86 | Student t law | P/R | Normal/chi-square ratio with beta-gamma normalization. | Thm. 10.4 |
| 87 | Fisher F law | P/R | Ratio of independent scaled chi-squares. | Thm. 10.5 |
| 88 | Exact confidence pivots | E/P | Effective quantiles and explicit tail probabilities. | Cor. 10.6 |
| 89 | Inverse-CDF random generation | E/P | Finite-bit uniform source and interval-valued quantile; explicit boundary error. | Thm. 10.7 |
| 90 | Box–Muller generation | E/P | Truncated uniform inputs, Jacobian proof, and explicit omitted-boundary probability. | Thm. 10.8 |
| 91 | Zero-variance normal | C/P | Treated as a Dirac weak limit; CDF convergence excludes the discontinuity point. | Thm. 10.9 |
| 92 | CLT / Berry–Esseen | R | Reuses `central_limit_ipra_2026-11-15` with constant and effectivity status unchanged. | §10.8 |
| 93 | Arbitrary sample averages are exactly normal | C | False unless summands are normal; corrected to quantitative asymptotic normality. | Cor. 10.11 |
| 94 | Marcinkiewicz polynomial-cumulant converse | D | Forward Gaussian cumulants and effective quadratic-MGF criterion proved; full theorem requires separate complex analysis. | §6.5 |
| 95 | Cramér decomposition theorem | D | Requires factorization of entire characteristic functions. | §13 |
| 96 | Kac–Bernstein theorem | D | Requires a separate characteristic-function functional equation. | §13 |
| 97 | Geary converse characterization | D | Forward mean/variance independence proved; converse not reconstructed. | §13 |
| 98 | Information-geometric curvature | D | Fisher metric computed; global curvature theory not developed. | §13 |
| 99 | Exact high-order variances of sample skewness/kurtosis | D | Finite Wick enumeration is available in principle; long closed simplifications omitted. | §13 |
| 100 | Non-elementarity of the CDF | D | A differential-algebra theorem, irrelevant to effective computation. | §13 |

## Net result

The packet gives complete or effective constructive proofs for 93 of the 100 listed mathematical families, counting corrected and reused statements with their qualifications. Seven deep converse, global-geometric, or differential-algebraic families are left visible as separate research obligations.
