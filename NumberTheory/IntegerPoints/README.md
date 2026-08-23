# Integer points in circles

Formal Lean statements of the results of two papers on the **primitive
circle problem**: the asymptotic count `V(x)` of coprime integer pairs
`(a, b)` with `a² + b² ≤ x`, whose main term is `(6/π) x`.

- W. Zhai and X. Cao, *On the number of coprime integer pairs within a
  circle*, Acta Arith. 90 (1999), 1–16: under RH,
  `V(x) = (6/π) x + O(x^{11/30 + ε})`.
- J. Wu, *On the primitive circle problem*, Monatsh. Math. 135 (2002),
  69–81: under RH, `V(x) = (6/π) x + O(x^{221/608 + ε})`.

## Layout

- [`Papers/`](Papers/) — OCR transcriptions of the two papers as LaTeX.
  The Zhai–Cao transcription was compared page by page with the original
  Acta Arithmetica PDF; its statements match the print.  The Wu original
  could not be retrieved; the one correction made there (the signs in the
  Vaughan identity (4.1)) is annotated in the source.
- [`Lean/`](Lean/) — the Lake library `IntegerPoints`
  (`lake build IntegerPoints` from the repository root), namespace
  `LeanProofs.IntegerPoints`:
  - `IntegerPoints.Basic` — `P(x)`, `E(x)`, `V(x)`, `E_P(x) = Δ(x)`, `r(n)`,
    `e(t)`, dyadic ranges, the bilinear sum `ℛ(M, N)`.
  - `IntegerPoints.ExponentialSums` — Zhai–Cao Lemmas 1–8 (Kuz'min–Landau,
    Perron, Krätzel, Weyl–van der Corput, Bombieri–Iwaniec,
    Fouvry–Iwaniec, Min's B-process, Srinivasan) and Wu Lemma 2.1,
    Theorem 2, Lemmas 2.5–2.7 (triple and double monomial exponential
    sums), with the Graham–Kolesnik definition of exponent pairs
    (`f^{(p+1)} ≈ (−1)^p (s)_p y t^{−s−p}`, so `f' ≈ y t^{−s}`; the bound
    is `≪ (yN^{−s})^κ N^λ + y⁻¹N^s` for all `y > 0`, exactly as in
    Graham–Kolesnik §3.3, which is the form the A-process needs).
  - `IntegerPoints.ZhaiCao` — (1.1)–(1.4), Lemmas 9–10, Propositions 1–2.
  - `IntegerPoints.GKLemma31`, `GKLemma32`, `GKLemma33` — **proved**:
    Graham–Kolesnik Lemmas 3.1–3.3 (`gk_lemma31_holds`, `gk_lemma32_holds`,
    `gk_lemma33_holds`): the first-derivative test for integrals
    (integration by parts with `u = g/f'`, `∫|u'| = |u(b) − u(a)|` by
    monotonicity), the second-derivative test (split at `f' = ±√λ₂` by the
    intermediate value theorem), and the Fresnel integral
    `∫_{-X}^{X} e(Ax²) = e(1/8)/√(2A) + O(1/(AX))` (by Gaussian regularisation
    `b = ε − 2πiA → −2πiA` with Mathlib's complex Gaussian integral, tails
    `≤ 1/(|b|X)` by parts, and the value `(i/(2A))^{1/2}` from `cpow`).
  - `IntegerPoints.GKLemma35` — **proved**: Graham–Kolesnik Lemma 3.5
    (truncated Poisson summation, `gk_lemma35_holds`, absolute constant 55),
    on top of `IntegerPoints.Sawtooth` (the truncated Fourier series
    `S_N(x) = Σ_{h≤N} sin(2πhx)/(πh)` of the sawtooth, with the explicit error
    `|ψ(x) + S_N(x)| ≤ 4/(N·min(x, 1−x))` via the Dirichlet kernel and `Si`),
    `IntegerPoints.EulerMaclaurin` (the first-order Euler–Maclaurin formula
    `Σ_{a<n≤b} F(n) = ∫F + ψ(a)F(a) − ψ(b)F(b) + ∫ψF'`),
    `IntegerPoints.Poisson` (the exact identity
    `Σ_{a<n≤b} e(f(n)) = Σ_{|k|≤N} ∫ e(f − kx) + boundary_N + error_N`),
    `IntegerPoints.PoissonBounds` (`|S_N| ≤ 4`, the Dirichlet kernel bounds
    `‖K‖ ≤ H + 1`, `‖K(x)‖ ≤ 2/‖x‖`, alternating series, `Σ 1/(k+u)²`),
    `IntegerPoints.PoissonIntegrals` (`∫_0^1 |ψ + S_N| ≤ (9 + 8 log N)/N`, the
    `L¹` bound `4 + 4 log(H+1)` of the kernel over a unit window, the sign of
    `f''`, integration by parts for `∫ e(φ)`), and `IntegerPoints.PoissonTail`
    (the tail `Σ_{h ∉ [H₁,H₂]} ∫ e(f − hx) ≤ 4/π + (2/π) log(H+1)` at
    half-integer endpoints).  The proof trims `[a, b]` to half-integer
    endpoints so that the conditionally convergent boundary sums become
    alternating series — the textbook argument does not give `O(log H)`
    uniformly near integer endpoints.
  - `IntegerPoints.GKLemma34` — **proved**: both curvature forms of
    Graham–Kolesnik Lemma 3.4, the stationary-phase estimate
    (`gk_lemma34_holds`, `gk_lemma34_neg_holds`).  The internal
    `SP1Taylor`–`SP5Core` chain normalises the critical point, proves sharp
    Taylor bounds for the cubic remainder, controls the two integration-by-parts
    error integrals, assembles them across the singular point, and compares the
    quadratic integral with the Fresnel main term.  The public wrapper translates
    back to `x₀`, uses Lemma 3.2 when an endpoint is closer than `λ₂⁻¹⁄²`, and
    obtains the case `g'' ≤ −λ₂` by complex conjugation.
  - `IntegerPoints.GKLemma36` — **proved**: Graham–Kolesnik Lemma 3.6, the
    B-process transformation (`gk_lemma36_holds`).  The proof combines the
    truncated Poisson formula with Lemmas 3.2 and 3.4, controls the stationary
    indices by derivative monotonicity, sums the endpoint errors harmonically,
    and normalises the result to
    `log(F N⁻¹ + 2) + F⁻¹⁄² N`; a separate `F < 1` argument closes the
    scale where the raw asymptotic estimate alone is too coarse.
  - `IntegerPoints.GKLemma37` — **proved**: Graham–Kolesnik Lemma 3.7 in its
    exact book range (`gk_lemma37_holds`).  The A-process proof integrates the
    affine tangent bound for `u⁻ᵠ` exactly, retaining the factor `1/2` in the
    quadratic remainder and hence allowing `h < 2εN/(s+P)`.
  - `IntegerPoints.GKEq234` — **proved**: Graham–Kolesnik equation (2.3.4),
    the Weyl–van der Corput inequality in the integer-shift form used by §3.3
    (`gk_eq234_holds`).  It specializes the general differencing engine,
    separates the zero correlation, and reindexes the remaining shifts as
    `1 ≤ h ≤ H`.
  - `IntegerPoints.GKTheorem21` — **proved**: Graham–Kolesnik Theorem 2.1 in
    the form invoked in §3.3 (`gk_theorem21_invoked_holds`).  The `p = 0`
    class estimate keeps `f'` uniformly away from the integers, the `p = 1`
    estimate makes it antitone, and Kuz'min–Landau gives
    `≪ y⁻¹Nˢ` when `yN⁻ˢ < 1/2`.
  - `IntegerPoints.GKHighCurvature`, `GKTheorem22` — **proved**:
    Graham–Kolesnik Theorem 2.2 in both forms invoked by the chapter
    (`gk_theorem22_invoked_sec33_holds`,
    `gk_theorem22_invoked_sec34_holds`).  A shared arbitrary-`ε`
    second-derivative estimate gives `≪ √L√N` for `L = yN⁻ˢ ≥ 1/2`; the
    ranges `L < 1` and `L < log N` yield `≪ √N` and `≪ √(N log N)`.
    `IntegerPoints.ExponentPairHalf` now reuses the same high-curvature core.
  - `IntegerPoints.FiniteHilbert`, `GKAppendixATheorem2` — **proved**:
    the sharp finite Hilbert inequality and Graham–Kolesnik Appendix A,
    Theorem 2 (`gk_appendixA_theorem2_invoked_holds`).  The Hilbert inequality
    follows from finite Parseval and the exact Fourier coefficients of
    `1/2 - x` on `[0,1]`; the Appendix proof expands
    `∫_T^{2T} |Σ_{N<n≤2N} e(t/n)|² dt`, retains the diagonal `TN`, writes
    the residual as a difference of two Hilbert forms, and uses
    `Σ_{N<n≤2N} n² ≤ 4N³` to obtain `(T - 4N²)N` with the book's
    exact constant.
  - `IntegerPoints.GKSec33LGeHalf` — **proved**: Graham–Kolesnik's §3.3
    restriction `gk_sec33_l_ge_half_holds`.  A smooth phase equal to `-t/x`
    on `[N,2N]` belongs to the exponent-pair class at every finite derivative
    order.  Its bound on `8N² ≤ t ≤ 16N²`, combined with Appendix A, forces
    `N ≤ K(N^(2l) + 1)`; real-power decay rules this out when `l < 1/2`.
  - `IntegerPoints.GKSec33KNonneg` — **proved**: the remaining coordinate
    restriction `gk_sec33_k_nonneg_holds`: `k ≥ 0`, with `k = 0` forcing
    `l ≥ 1`.  At the factorial scales `t = (2N)!ν`, every reciprocal phase
    is integral and the exponential sum is exactly `N`; multiplier limits
    rule out `k < 0` and then remove the error term in the boundary case.
  - `IntegerPoints.GKSec33Boundary` — **proved**: the square-root boundary
    restriction `gk_sec33_k_eq_half_of_l_eq_half_holds`: an exponent pair
    `(k, 1/2)` has `k = 1/2`.  The proof specializes the exponent-pair bound
    to `f(x) = 2HR√x` at `H = Q²`, `N = R²`, applies the exact Lemma 3.6
    transform, and takes `R` to be a multiple of `H!`.  Every dual phase then
    equals `e(-1/8)`, the dual interval has at least `H/4` terms, and its norm
    is at least `RQ/4`; a diagonal choice of `Q` and the factorial multiplier
    contradicts every `k < 1/2`.
  - `IntegerPoints.GKLemma39`, `GKLemma39Class` — **proved**:
    Graham–Kolesnik's Lemma 3.9 (`gk_lemma39_holds`) and its class-form
    corollary (`gk_lemma39_class_holds`).  The proof constructs the local
    inverse calculus from negative curvature, derives the exact normalized
    Faà di Bruno recurrence, proves finite-order inverse-jet stability, and
    compares the inverse point with the power-model scale.  The derivative
    estimate is extended from the open frequency interval to both endpoints
    by continuity; restricting it to `[J, 2J]` then gives the dual phase class
    needed by the B-process.
  - `IntegerPoints.GKBProcessTheorem`, `GKProcessWords` — **proved**:
    Graham–Kolesnik's Theorem 3.10 (`gk_theorem310_holds`), the exponent-pair
    B-process `(k, l) ↦ (l - 1/2, k + 1/2)`, and its §3.1 finite-word
    consequence (`gk_sec31_words_holds`).  The proof isolates the boundary
    pair, transports uniform class parameters through Lemma 3.9, applies the
    exact Lemma 3.6 transform, bounds the stationary main term by dyadic
    inverse-phase blocks, and absorbs both logarithmic and curvature errors
    into the transformed exponent-pair model.  Induction then closes `(0, 1)`
    under every finite word in the proved A- and B-processes.
  - Statement modules for the other papers in `Papers/` (statements and
    auxiliary definitions only): `IntegerPoints.FouvryIwaniecStatements`
    (Fouvry–Iwaniec 1989: Proposition 1, Corollary 1, Theorems 1–7,
    Lemmas 2–9), `IntegerPoints.GKStatements` (Graham–Kolesnik Ch. 3:
    the statement definitions and remaining unproved material),
    `IntegerPoints.Kolesnik` (Kolesnik 1985: the classes `E_n`, Lemmas 1–2,
    A, B, Theorems 1–5, the numerical corollaries),
    `IntegerPoints.HeathBrown` (Heath-Brown 1992: Theorems 1–6, Lemmas 1–6,
    the truncated Voronoi formulas), `IntegerPoints.HuxleyStatements`
    (Huxley 2003: Hypothesis H, Propositions 1–6, Theorems 1–6, Lemmas
    2.3–2.5), `IntegerPoints.IwaniecMozzochi` (Iwaniec–Mozzochi 1988:
    the main theorems, the reductions, Lemma 11.1, Theorems 4.1 and 14.1,
    the §6–§14 definitions), `IntegerPoints.Hirschhorn` (the four classical
    theorems and the partial-fraction identities),
    `IntegerPoints.LittlewoodWalfisz` (the theorem `37/112`, Lemmas 1–6,
    Landau's note), `IntegerPoints.BerndtKimZaharescu` (the survey's
    identities, Ω-results, moment asymptotics and the table of exponents).
  - `IntegerPoints.Wu` — Theorem 1, Nowak's formula, the reduction to
    `ℛ(M, N)`, the regions `𝒜, ℬ, 𝒞, 𝒟`, Propositions 1–4, and the exact
    Vaughan identity behind Lemma 4.1.
  - `IntegerPoints.Consequences` — **proved**: Wu's Theorem 1 ⇒ Zhai–Cao's
    Theorem ⇒ Nowak's bound; Wu's unconditional (1.1) ⇒ Zhai–Cao's (1.2);
    Nowak's formula ⇒ Zhai–Cao Proposition 2; the regions cover the square,
    so Propositions 1–4 plus the reduction give Wu's Theorem 1
    (`wu_theorem1_of_props`).
  - `IntegerPoints.Vaughan` — **proved**: both forms of the Vaughan identity
    (`wu_vaughanIdentity_pointwise_holds`, `wu_vaughanIdentity_holds`) via
    Dirichlet convolution with the truncated Möbius function.
  - `IntegerPoints.Srinivasan` — **proved**: Zhai–Cao Lemma 8
    (`zhaiCao_lemma8_holds`) by an intermediate-value crossing argument.
  - `IntegerPoints.ExponentPairs` — **proved**: `(0, 1)` is an exponent pair.
  - `IntegerPoints.ExponentPairHalf` — **proved**: `(1/2, 1/2)` is an exponent
    pair (`isExponentPair_half_half`), from the second-derivative test.
  - `IntegerPoints.SineIntegral` — **proved**: the sine integral
    `Si y = ∫₀^y sin v/v`, its tail bound `|Si y' − Si y| ≤ 2/y`, and the
    Dirichlet integral `Si y → π/2` (`tendsto_Si`,
    `abs_Si_sub_pi_div_two_le`) via the Dirichlet kernel and the
    Riemann–Lebesgue lemma — machinery for Lemma 2 (Perron).
  - `IntegerPoints.Perron` — **proved**: Zhai–Cao Lemma 2, the truncated
    Perron formula for a finite sum (`zhaiCao_lemma2_holds`): the integral
    is `Σ_l a_l (Si(T log N/l) − Si(T log M/l))/π`, the weights are within
    `(2/πT)(1/|log N/l| + 1/|log M/l|)` of the indicator, and the sums over
    `l` are bounded by shells around `round M`, `round N` (giving the
    `min(1, L/(T‖M‖))` edge terms) plus a harmonic sum.
  - `IntegerPoints.BombieriIwaniec` — **proved**: Zhai–Cao Lemma 5, the
    Bombieri–Iwaniec inequality (`zhaiCao_lemma5_holds`): the trapezoid
    `τ = 1_{(⌊N⌋+½, ⌊N₁⌋+½)} ∗ 1_{(−½,½)}` is the indicator of `(N, N₁]` on
    integers, `|𝓕τ| ≤ K` by the convolution theorem, Fourier inversion at
    integers gives `Σ a_n = ∫ 𝓕τ(θ) Σ a_m e(mθ) dθ`, and `∫K = (2/π)(2 + log W)`
    explicitly (with `π > 3` from `sin(½) < ½` and `log 2 > 4/7`).
  - `IntegerPoints.FouvryIwaniec` — **proved**: Zhai–Cao Lemma 6, the
    Fouvry–Iwaniec counting lemma (`zhaiCao_lemma6_holds`, *Exponential
    sums with monomials*, Lemma 1): quadruples are sorted by
    `μ = gcd(m, m̃)`, `ν = gcd(n, ñ)`; distinct fractions with a fixed gcd are
    `μ²/(4M²)`-spaced and the mean value theorem spaces their `α`-th
    powers by `c(α) μ²/(4M²)`, so the box principle bounds each class by
    `4 min(M²/μ², N²/ν²) + 32Δ M²N²/(c μ²ν²)`; the sums over `μ, ν` use
    `Σ_ν min(a, N²/ν²) ≤ 4√a N`, `Σ 1/ν² ≤ 3` and the harmonic bound.
  - `IntegerPoints.AProcess` — **proved**: the shifted core of
    Graham–Kolesnik Lemma 3.7 (`AP.lemma37_sharp`): if
    `f ∈ F(N, P+1, s, y, ε)`, `0 < h ≤ b − a`, and
    `h < 2εN/(s+P+1)`, then
    `f(x) − f(x+h) ∈ F(N, P, s+1, shy, 3ε)` on `[a, b−h]`.
    `AP.lemma37` preserves the former narrower-range API for existing callers.
  - `IntegerPoints.AProcessTheorem` — **proved**: Graham–Kolesnik Theorem
    3.8, the A-process (`AP.isExponentPair_A`): `(k, l)` exponent pair ⇒
    `(k/(2k+2), (k+l+1)/(2k+2))` exponent pair.  Weyl differencing (Lemma 4
    with an indicator-weighted sequence), Lemma 3.7 and the pair `(k, l)`
    at parameter `s+1` give `|S|² ≪ N²/Q + Q^k L^k N^{l−k+1}`; the explicit
    `Q₀ = N^{(1+k−l)/(k+1)} L^{−k/(k+1)}` balances the terms with
    `N²/Q₀ = (L^κ N^λ)²`, the range `L < 1 + log N` is handled by the pair
    `(1/2, 1/2)`, and `Q₀ < 1` or `Q₀ > cN` reduce to trivial bounds.
    Corollary: `(1/6, 2/3)` is an exponent pair.
  - `IntegerPoints.Lemma9` (+ `Lemma9Tools`, `Lemma9Core`, `Lemma9Sum`) —
    **proved**: Zhai–Cao Lemma 9 (`zhaiCao_lemma9_holds`) by Heath-Brown's
    method: the pairs `(v, n)` are sorted into `Q` classes by `√n/v`,
    Cauchy–Schwarz over `(u, class)` and expansion give
    `‖S‖² ≪ U Q Σ_{|λ| ≤ 2√N/(VQ)} |Σ_u e(√x λ/u)|` with
    `λ = √n₁/v₁ − √n₂/v₂`; the inner sum is bounded by Lemma 1 (for
    `f(u) = √xλ/u`, smoothly extended below `1/2`), the number of pairs with
    `|λ| ≤ t` by Lemma 6 (`α = 1/2, β = 1`), dyadic shells in `|λ|` give
    `‖S‖² ≪ (log x)² (U²QNV + x^{1/4}U^{1/2}N^{9/4}V^{3/2}Q^{-1/2})`, and
    `Q₀ = x^{1/6}U^{-1}N^{5/6}V^{1/3}` (or `Q = 1`, or the trivial bound
    when `Q₀ > VN`) finishes, with all exponents handled through twelfth
    roots.
  - `IntegerPoints.WeylVanDerCorput` — **proved**: Zhai–Cao Lemma 4, the
    Weyl–van der Corput inequality with real shift length `Q`
    (`zhaiCao_lemma4_holds`, implied constant `6c`), by a fully discrete
    window-sum argument.
  - `IntegerPoints.LargeSieve` — **proved**: Wu Lemma 2.1, the Fejér-weighted
    large-sieve inequality (`wu_lemma21_holds`), by Cauchy–Schwarz on the
    step function `Σ zₙ 1_{[xₙ, xₙ+1/Q)}` (Bochner integrals).
  - `IntegerPoints.KuzminLandau` — **proved**: the Kuz'min–Landau inequality
    `‖Σ_{A<n≤B} e(F(n))‖ ≤ 4/λ` for `F'` monotone with `‖F'‖ ≥ λ`
    (`KL.kuzmin_landau`), by summation by parts against
    `w(g) = −½ − (i/2)cot(πg)`.
  - `IntegerPoints.VanDerCorput` — **proved**: the second-derivative test
    `‖Σ e(f(n))‖ ≤ 12α(B−A)√λ₂ + 24/√λ₂` for `λ₂ ≤ f'' ≤ αλ₂`
    (`VdC.second_derivative`), by splitting into `round(f')`-windows.
  - `IntegerPoints.Lemma1` — **proved**: Zhai–Cao Lemma 1
    (`zhaiCao_lemma1_holds`) from the two results above.
  - `IntegerPoints.Lemma3` — **proved**: Zhai–Cao Lemma 3, Krätzel's bound for
    `Σ min(D, 1/‖f(n)‖)` (`zhaiCao_lemma3_holds`), by grouping on
    `round(f(n))` and counting `δ`-separated values in shells.

## Status

Every result is a `Prop`-valued definition (e.g. `zhaiCao_theorem`,
`wu_theorem1`); the ones proved so far have a companion `…_holds` theorem
(or an implication between statements), listed above.  The library compiles
with no `sorry` and no axioms beyond Mathlib's.  The remaining analytic core —
the unproved exponential-sum estimates (Zhai–Cao Lemmas 7 and 10 and
Proposition 1; Wu Theorem 2, Lemmas 2.5–2.7 and Propositions 1–4), Nowak's
formula, and the RH-conditional main theorems — remains unproved.

## Conventions worth knowing

- `≪` with an implied constant depending on parameters `p` is rendered
  `∀ p, ∃ C, ∀ …, ‖·‖ ≤ C * …`; `∼`/`≪`/`≫` hypotheses carry explicit
  constants quantified before `C`.
- `m ∼ M` is the dyadic block `M < m ≤ 2M` (Wu's convention) in both papers.
- Functions of a real variable are globally `C^k` on `ℝ` with hypotheses on
  the relevant interval.
- `min(D, 1/‖t‖)` and `min(1, L/(T‖M‖))` use helpers that return the
  intended `+∞` branch when `‖t‖ = 0`, since `1/0 = 0` in Lean.
- Zhai–Cao Lemma 7 is stated with `f'' > 0` (the `f'' < 0` case follows by
  conjugation) and with the `u`-sum over all integers in `[α, β]`.
- Wu's reduction "(1.3) suffices for Theorem 1" is stated for any
  `1/3 ≤ θ < 1/2`, the range in which his derivation is uniform.
