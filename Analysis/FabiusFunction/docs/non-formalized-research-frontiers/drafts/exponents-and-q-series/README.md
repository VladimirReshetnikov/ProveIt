# Exponents and q-series

Generalizations of the dyadic construction to arbitrary exponent
sequences and the q-series calculus that organizes them: the
exponent-sequence convolution monoid with its Newton-basis frontiers, and
q-binomial Richardson acceleration of geometric sinc products. The
denominator-free Gaussian/q-binomial core used by both is formalized at arbitrary
ratio. The normalized geometric-Lagrange and analytic Lagrange layers additionally
assume injectivity of `j |-> q^j` on the finite node set (see the status boxes and
crosswalk paragraphs inside the documents). `AnalyticSeriesFilter.lean` carries the core to exact
diagonal and Gaussian-tail identities for unconditionally summable sampled
series. Its hypotheses are sharp at zero-weight nodes, but it does not cover
conditionally convergent boundary series, uniform estimates, signs or bounds,
or the concrete sinc-product/Bell-series instantiation.

The documents also cross-reference the independent real fractional-Volterra
layer. `FractionalVolterraCalculus.lean` proves positive affine covariance on
ordered intervals for arbitrary real order. For `alpha <= 0`, this covariance is
an identity for the totalized Lean interval-integral definition; a classical
Riemann--Liouville/integrability interpretation is asserted only for positive
order. Gamma-normalized order raising holds for real `alpha > 0` from a continuous Banach-valued primitive with an
interval-integrable right derivative. `FabiusFractionalVolterra.lean`
specializes this to the signed Fabius extension for `x >= 0`, the bounded
Fabius function for `0 <= x <= 1`, and the Up-to-Fabius bridge for `x >= -1`.
Complex orders, Caputo/Riemann--Liouville derivatives, weighted-monomial or iterated
shifts, negative-branch and hierarchy formulas, and inverse/quantile versions
remain research frontiers. These API claims were checked at source checkpoint
`22f801337`.

Member: `Exponents_and_q_Series_Frontiers` (168 pp, six parts) — the
2026-08-28 consolidation of the two former drafts (Part I:
Newton-basis frontiers; Part II: q-binomial Richardson), joined the
same day by the eighth-wave report as **Part III** — *Finite Dyadic
Sinc Products and Piecewise-Polynomial Approximants to Rvachev's
Up-Function* (formerly `finite_sinc_products_report/`): the exact
truncated-power formula for the prefix densities `p_n` with signed
Thue–Morse top-derivative jumps on a uniform dyadic knot grid, sharp
derivative plateaux, the exact error law
`||p_n^(r) − up^(r)||_∞ = 2^(C(r+3,2)−1)/(9·4^n)` with exact
Kolmogorov distance `1/(9·4^n)`, the Bell–Bernoulli all-orders
expansion, stable `q = 1/4` Richardson weights in closed q-binomial
form (extending Part II), a uniform scale-mixture representation
`X = R·U` of the up law, and a positive Gauss/Radau/Lobatto tail
quadrature hierarchy with exact constants — including the
variance-matched positive `16^{-n}` scheme that the frontier corpus
had proposed without construction, and a sixth-order exact-support
Radau rule — and by the two ninth-wave same-topic reports, **merged
editorially** (shared core stated once, constants cross-checked,
unique layers of each kept) as **Part IV** — *Fourier Images of the
Repeated-Integration Approximants* (formerly
`Rvachev_Piecewise_Approximation_Fourier_Images/` and
`rvachev_fourier_frontier_report/`): the master factorization
`f̂_n = Φ · A(2^{-n} t)` with the universal tail-transfer function
`A = sinc z / Φ(z)`, its cotangent and valuation-weighted canonical
products with signed divisor `1 − v₂(m)`, digit-sum zero counts and
the Thue–Morse sign law, exact Taylor radius `4π` with dominant-pole
coefficient asymptotics and an arithmetic Darboux hierarchy, the
complete finite/limit zero-multiplicity filtration, the sharp
`o(2^n)` relative-convergence window with forward/inverse
conditioning thresholds at `4π·2^n` and `π·2^n`, the impossibility of
globally stable convolutional deconvolution, weighted-`L^p` and
Sobolev all-orders norm laws with explicit leading constants, exact
algebraic mean-square Fourier tails with the sharp threshold
`f_n ∈ H^s ⟺ s < n + 1/2`, and positive moment-matched atomic,
dyadic-atomic, and polynomial-density closure menus at rates
`16^{-n}`–`256^{-n}`, compared as a family against Part III's box
mixtures.  A fifth part arrived with the tenth wave (formerly
`fabius_finite_products_frontier/`) — **Part V**, *Finite Dyadic Sinc
Products and Exact Transport Geometry of Rvachev Spline Approximants*:
convex-order and peakedness chains for the prefix laws, the exact
absolute moment `E|X_N| = 5/18 - 4^{-N}/9`, the fixed single crossing
of the density error at `x = +-1/2` for every stage, the exact metric
collapse `W_1 = d_K = 4^{-N}/9`, `TV = 2*4^{-N}/9`, stop-loss =
second-order Zolotarev = `4^{-N}/18`, `W_inf = 2^{-N}` with the
synchronous coupling optimal only at `p = inf`, the exact Thue-Morse
call-potential spline, the positive-mixture no-go theorem (no convex
combination of stages can cancel the leading error in any of these
metrics — signed Richardson weights are structurally necessary),
entropy/Fisher monotonicity with the exact criterion
`I(u_N) < inf iff N >= 3` and `KL(u || u_N) = inf`, and carefully
flagged conjectural weighted expansions (entropy, forward KL, Fisher,
fixed-p Wasserstein, and the `p ~ 2N` transport crossover with its
lower-Lambert phase).  The thirteenth wave added **Part VI** —
*Atomic Sinc-Product Splines Beyond the Binary Point* (formerly
`atomic_sinc_splines_report_package/`): an English translation and
frontier expansion of Rvachev's Chapter 3, treating the geometric
family `h_a` as a genuine deformation of `up = h_2` — the general
atomic-equation zero-matching criterion, closed Bernoulli cumulants
`κ_2m = 2^2m B_2m/(2m(a^2m − 1))` with Bell/Lambert moment calculus,
weighted Prouhet identities, exact derivative norms for `a ≥ 2`, the
fractal polynomial-gap atlas for `a > 2` with the complete
Taylor-germ trichotomy, the rational-power Strang–Fix reproduction
theorem, the all-orders prefix expansion with leading profile
`−h_a''/(6(a²−1))` (specializing at `a = 2` to the binary
constants of Parts III–V), the critical `a ↓ 2` collapse, the
reconstructed uniqueness theorem, and a conjecture register
(periodic-Lambert endpoint expansion, critical double scaling,
lattice obstruction without rational powers, strict log-concavity for
`1 < a < 2`).  The fourteenth wave brought a twin — *Atomic Functions
Beyond the Critical Dyadic Case* (formerly
`Atomic_Functions_Beyond_Dyadic_Report/`), a second independent
reconstruction of the same chapter — which was **merged editorially
into Part VI** (2026-08-28): the shared translation and `h_a` core are
stated once (both editions agreed on every commonly transcribed
equation), and its distinctive layers became dedicated sections — the
fractal-string geometry of `K_a` (geometric zeta
`ℓ₀^s/(1 − 2a^{−s})`, complex dimensions `D_a + 2πik/log a`, an exact
tube formula with continuous nonconstant one-periodic profile, hence
Minkowski non-measurability, with explicit logarithmic average), the
geometric local-degree law `P(N_a = r) = ((a−2)/a)(2/a)^r` with
`(a−2)/2 · N_a → Exp(1)` as `a ↓ 2` (the first marginal of the
critical double-scaling program), quantitative Gaussian (`a ↓ 1`) and
uniform (`a → ∞`) parameter limits with exact rates and an exactly
uniform expanding core, the exact general-base negative-Laplace
decomposition with real-analytic one-periodic correction whose
Fourier modes are `−Γ(−χ_k)ζ(1−χ_k)/log a` (settling the
transform-level half of the periodic-Lambert conjecture and pinning
the Lambert normalization `c_a = √a·log a/2`), the divisor-polynomial
form of `log M_a`, the canonical Fup ladder `G_n → 2·up(2x)`, and
three new register entries (overlap-regime nowhere analyticity,
algebraic-breakpoint arithmetic, a bridge between the two periodic
profiles).  The eighth-wave fold also repaired the volume's
part-boundary section numbering (Part II had rendered with
`\appendix` letters G–N).  Supporting files under `assets/`,
provenance with SHA-256 in the document itself.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.

A fourteenth-wave arrival, `Atomic_Functions_Beyond_Dyadic_Report/` (*Atomic Functions
Beyond the Critical Dyadic Case*), joins the group as a separate member: an English
reconstruction and expansion of Rvachev atomic-function material on the geometric
family h_a beyond the binary point — same subject as the volume's Part VI, written
independently — with gap-hierarchy/fractal-string geometry, Gaussian cumulant limits,
periodic correction bases, and reproducible experiments. It stays separate until
deliberately merged into the volume.
