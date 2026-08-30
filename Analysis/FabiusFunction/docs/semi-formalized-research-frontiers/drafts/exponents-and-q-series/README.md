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
series. Its hypotheses are sharp at zero-weight nodes. The current
`AnalyticMoments.lean` and `RvachevQBinomialFilter.lean` close the actual
infinite Rvachev-product specialization: for complex `c,z`, natural order `p`,
and Gaussian base `q = c^2`, only injectivity of `j |-> q^j` on
`range (p+1)` is assumed; `c = 1/2`, `q = 1/4` is assumption-free.
This does not formalize the reports' finite prefixes `P_(b,n)`, their
quotient or Bell coefficients, conditionally convergent boundary series, or
the analytic signs, error bounds, uniform/derivative convergence, and
asymptotics. `QBinomialVandermonde.lean` separately proves both
q-Vandermonde orientations, both the full-range and exact-min-support central
identities, the total natural
positive shift, and two negative-shift forms under exactly `k <= N`, all
over arbitrary commutative semirings.

The documents also cross-reference the independent real fractional-Volterra
layer. `FractionalVolterraCalculus.lean` proves positive affine covariance on
ordered intervals for arbitrary real order. For `alpha <= 0`, this covariance is
an identity for the totalized Lean interval-integral definition; a classical
Riemann--Liouville/integrability interpretation is asserted only for positive
order. Gamma-normalized order raising holds for real `alpha > 0` from a continuous Banach-valued primitive with an
interval-integrable right derivative. `FabiusFractionalVolterra.lean`
defines the total causal Rvachev fractional primitive, proves its support cutoff,
positive-natural bridge, and positive-order semigroup on `x >= -1`, and
specializes order raising to the signed Fabius extension for `x >= 0`, the
bounded Fabius function for `0 <= x <= 1`, and the Up-to-Fabius bridge for
`x >= -1`.
Complex orders, Caputo/Riemann--Liouville derivatives, weighted-monomial or iterated
shifts, negative-branch, shifted-lattice, endpoint-moment, transform/tail,
piecewise/refinement, and inverse/quantile formulas
remain research frontiers. These API claims were checked at source checkpoint
`149332f9d`.

Member: `Exponents_and_q_Series_Frontiers`
(currently 227 pp, seven parts) — the
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
profiles).  The fifteenth wave brought a third reconstruction of the
same chapter — *Atomic Functions, Rvachev's up-Function, and Smooth
Cantor Splines* (formerly `Rvachev_Atomic_Functions_Report/`) — which
was likewise **merged editorially into Part VI** (2026-08-28),
contributing the signed leading coefficient
`L_ω = (−1)^{N₊(ω)} a^{(r+1)(r+2)/2}/(2^{r+1} r!)` on every gap, the
derivative equimeasurability theorem with the full `L^p` ladder
`‖h_a^{(n)}‖_p = (a^{n(n+3)/2}/2^n)(2/a)^{n/p} ‖h_a‖_p` and the exact
derivative-value mixture law, the endpoint jet-reduction form of the
one-branch formula (the exact
Bernoulli→cumulants→moments→jets→gap-polynomials engine), the
classical `Fup_n` hierarchy with its exact triangular reconstruction
of `up` by `n(n+1)/2` dyadic averaging steps, closed cumulants
(`σ_n² = 4^{−n}(3n+4)/36`), and quantitative central-limit regime
(Berry–Esseen `O(n^{−1/2})`), the edge pantograph equations
generalizing `F′ = 2F(2·)` to every base, and further register
entries (`Fup_n` Edgeworth, graph-directed atomic splines,
pressure-function Taylor multifractal).  The sixteenth and seventeenth
waves arrived as same-topic twins on the signed and reciprocal
parameter orbit `{q, −q, 1/q, −1/q}` of the geometric-uniform family
and were **merged editorially as Part VII** — *Signed and Reciprocal
q-Fabius Frontiers* (formerly `Fabius_Q_Connections_Report/`, *Beyond
the Dyadic Fabius Web*, and `Signed_Reciprocal_q_Fabius_Frontiers/`):
affine sign conjugacy (negative q creates no new normalized shapes),
the reciprocal moment germ with `M_q(t)·M_{1/q}(−t) = 1` and finite
digit-reversal duality giving `q = ±2, ±4` exact meaning, geometric
multisection (the Fabius law as an explicit convolution of two
quarter-base laws), the spectral q²-Pochhammer factorization, the
Bernoulli cumulant dictionary with closed spectral zeta, log-concavity
with the exact plateau phase `|q| ≤ 1/2`, the positive Laplace
representation of reciprocal germs (vertical-line moments, Hankel
signature `(−1)^C(n,2)`, orthogonal polynomials on `Re z = 1/2`), the
q-Fabius–Bernoulli Appell deconvolution family, the moment polynomial
`𝒫_n(q)` with its odd-q-integer divisor conjecture, the two-nome
Pochhammer–Prouhet partition function and digit-position master
product, the exact q-Prouhet moment transfer, the
Grassmannian/Hermitian finite-geometry square, box-spline derivative
combs with the dimension-1/2 quartic Cantor skeleton, reciprocal
q-Lagrange row reversal, the exact inverse-geometric endpoint lattice
`G_q(qⁿ) = q^C(n+1,2)·𝒫_n/(q;q)_n` with all jets and new
inverse-quartic values, the uniform two-term endpoint asymptotic with
its square-root/log-log inversion, and the resolution of the
sixteenth wave's periodic-cocycle conjecture by Part VI's exact
Gamma–zeta Laplace decomposition.  The eighth-wave fold also
repaired the volume's part-boundary section numbering (Part II had
rendered with `\appendix` letters G–N).  Supporting files under
`assets/`, provenance with SHA-256 in the document itself.

See [`../MANIFEST.md`](../MANIFEST.md) for titles and the previous paths.

The two revised fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Report-2/`, `-3/`) were merged into Part VI
(2026-08-28): the Orlicz/rearrangement form of derivative equimeasurability,
the spectral Stieltjes–Wigert bridge (squared-frequency moments
`a^{n(n+2)}/2^n`, an explicit non-lognormal representing measure with closed
Hankel determinants and orthogonal polynomials), the Mellin law of the
distance to `K_a` (complex dimensions shifted by −1; distribution function =
the exact tube formula), and — for provenance — the eleven-page Russian
source scan itself, against which the translation layers were checked (the
scan and the raw OCR were both deleted once their recoverable content was
merged and verified; SHA-256 hashes stay in the volume's provenance list,
the repair ledger lives in Part VI's concordance appendix, and git history
archives the files).  The revised fifteenth-wave
edition (`Atomic_Functions_Rvachev_Report_Package/`) followed: the
q-Gaussian derivative Gram kernel `q^{(j−k)²}` with Pochhammer determinants
and sharp Jacobi-theta Riesz bounds, the log-Weibull jet-intermittency law,
and the proof of the uniform all-orders `Fup_n` Edgeworth expansion
(resolving that register conjecture).  An expanded fifteenth-wave edition
(`Atomic_Functions_Rvachev_Expanded_Report/`, audit-aware — it marks the
previously merged layers as inherited baseline) closed the Gram geometry:
the Gaussian-binomial Gram–Schmidt theorem
`ψ*_n = Σ_j q^{n−j}·[n,j]_{q²}·e_j` with norms `(q²;q²)_n`, explicit
Cholesky and inverse Gram, the Rogers–Szegő identification of the
orthogonalizers, the uniform-innovation corollary (each new derivative
keeps an innovation of norm at least `(q²;q²)_∞^{1/2}`), the
wrapped-heat-kernel circle model (each parity tower is unitarily the
monomial sequence against `ϑ₄(θ/2, 1/a)` — heat time `log a`), the
MacMahon determinant constant `𝔐(a⁻²)` with parity-factored full-sequence
determinants and triple-product Riesz forms with a verified numeric table,
and the overlap-regime theta conjecture for `1 < a < 2`; its figures and
data live under `assets/Atomic_Functions_Rvachev_Expanded_Report/`.  Two
expanded fourteenth-wave editions
(`Atomic_Functions_Beyond_Dyadic_Expanded/`,
`Atomic_Functions_Beyond_Dyadic_Frontiers/`; both audit-aware, both
re-shipping byte-identical copies of the source scan/OCR, again not
retained) closed the round with disjoint layers: the physical-space
Stieltjes–Wigert differential ladder `Υ_{a,n} = P_{a,n}(−d²/dx²) h_a`
(compactly supported orthogonal system, closed norms, q-binomial
derivative expansion, three-term operator recurrence) — identified during
the merge with the fifteenth wave's Gram–Schmidt vectors,
`Υ_{a,n} = (−1)^n ‖h^{(2n)}‖₂ ψ*_n`, a check that also caught and repaired
a sign-convention slip in the closed Gram–Schmidt theorem's first
printing — plus both parity derivative-jet Gram determinants, the
autocorrelation germ `a^{n(n+2)}/2^n` with zero Taylor radius and provable
ladder incompleteness, and the explicit-null-modes conjecture; and the
exact derivative-energy factorization
`μ_{a,n,p} = Law(S_{a,n} + a^{−n} Y_{a,p})` with `W∞ ≤ 2a^{−n}/(a−1)`
convergence to the symmetric Bernoulli convolution (Cantor measure on
`K_a` for `a > 2`, uniform at `a = 2`), exact Hausdorff support rate, the
Rényi/Shannon entropy laws `H_β(n) = H_β(0) + n log(2/a)` with the
information-dimension reading, and the overlap-regime energy conjecture;
their figures and data live under the matching `assets/` directories.
Two expanded fifteenth-wave editions
(`Atomic_Functions_Rvachev_Report_Expanded/`,
`Atomic_Functions_Rvachev_qBinomial_Frontiers/`; both audit-aware; the
first also re-shipped the two previous editions of its lineage alongside
the scan/OCR — all byte-identical to recorded files, none retained)
completed the orthogonalization and jet theory: the nodal-polynomial
reading of the Gram–Schmidt residuals (interpolation at geometric nodes;
pivot = value at the next node), the exact inverse transform with the
entrywise-positive Cholesky factorization, the minimum-phase theta
whitening filter `A_q(z) = 1/(−qz;q²)_∞` with
`|A_q|²·ϑ₃ = (q²;q²)_∞` (the Szegő factor of the q-Gaussian covariance),
Schur-minor strict total positivity of the kernel with
oscillation/checkerboard consequences, the two-term jet tail with the
sharp exponential-Orlicz threshold, and the highest-jet partial-theta law
with the joint jet–distance transform (the distance-Mellin pole lattice
deforms into an entire partial theta series for `s > 0`); five register
conjectures were added and the algebraic-breakpoint conjecture gained its
transcendental-dichotomy sharpening; figures and data live under the
matching `assets/` directories.
(The q-orbit reports `Fabius_Q_Connections_Report/` and
`Signed_Reciprocal_q_Fabius_Frontiers/` were merged editorially as the
volume's Part VII; their figures/data are likewise under `assets/`.)

Second member: `q_pochhammer_q_binomial_monograph/` (191 pp, book class) —
*q-Pochhammer Symbols and q-Binomial Coefficients*, a standalone
proof-oriented reference monograph on the q-machinery itself, filed
2026-08-28 per the Lambert-W precedent (a reference companion rather
than a research report, so it is kept as its own document instead of
being merged into the frontier volume).  Its corpus role: Parts II, VI,
and VII of the frontier volume, and the repository's formalized
Gaussian-binomial core, consume exactly this machinery — shifted
factorials, Gaussian coefficients with their cyclotomic structure,
q-binomial theorems, q-Gauss summation, Jacobi's triple product, theta
functions, Bailey pairs, q-Lucas congruences, q-Newton interpolation at
geometric nodes, and Bernoulli asymptotics of Gaussian coefficients all
appear in the frontier volume's q-Gaussian derivative-tower,
Stieltjes–Wigert, and q-orbit chapters, and the monograph proves each
from first principles with a formula atlas, a limit dictionary, a
proof-dependency guide, and a formalization-architecture chapter.  It
was audited on arrival (ten core theorems re-verified symbolically; the
Chern–Dilcher–Jiu deleted-singularity identity and Ramanujan's ₁ψ₁
verified numerically to 30 digits; one dominated-convergence majorant
repaired with an `% ed.:` note).

Its current formalization ledger has 183 labelled results: 20 exact, 29
partial, 131 with no counterpart, and 3 interface-only. Both orientations
of q-Vandermonde and both central-support presentations are exact in
`QBinomialVandermonde.lean`; the monograph's single signed shifted-central
formula is partial because Lean exposes a total natural positive shift and
two natural negative forms under `k <= N`. The ledger also now records the
genuine real infinite product `qPochhammerInf` and its contractive-base
convergence/positivity layer, replacing the stale claim that every infinite
q-Pochhammer in the development was merely a finite `Finset.range` product.
`CompleteHomogeneousGenerating.lean` makes the complete-homogeneous half of
the weighted generating-product theorem partial rather than open: the finite
formal reciprocal-product identity is proved, while the elementary product
and analytic-convergence clause are not.  The same denominator-cleared theorem
partially covers elementary--complete orthogonality; the explicit coefficient
formula in terms of the book's `C_j^n` has no named Lean counterpart.

The wave volumes' central probabilistic object — the normalized
geometric-uniform law `Y_q = (1-q)·∑ qʲU_j`, with `q = 1/2` the
Fabius case and `q = 1/a` the atomic family `h_a` — now carries the
kernel-verified four-face geometric-tail dictionary at every ratio
`|q| < 1`: `GeometricUniformDictionary.lean` converts the corpus's
product-form self-similarity into convolution form and instantiates
`geometric_tail_dictionary` — the measure, characteristic-product,
moment, and cumulant faces of the `m`-digit tail in one statement.
The characteristic-product face is now closed in elementary terms:
`GeometricSincFactorization.lean` computes the digit,
`φ_digit(t) = e^{i(1-q)t/2}·sinc((1-q)t/2)`
(`Fabius.charFun_geometricUniformDigit`), and proves the **finite sinc
factorization at every ratio**
`φ_q(t) = e^{i(1-q^m)t/2}·∏_{k<m} sinc((1-q)q^k t/2)·φ_q(q^m t)`
(`Fabius.charFun_geometricUniformDistribution_prefix_sinc`, with the
raw closed-factor form `_prefix`) — the finite half of Part IV's master
factorization `F̂ₙ = Φ·A(2⁻ⁿs)` at `q = 1/2` and of Part VI's `ĥ_a`
sinc products at `q = 1/a`, kernel-verified.
