# BCH — Lean 4 formalization

A Lean 4 / Mathlib library formalizing theorems of the article in
`../docs/combined` (the Baker–Campbell–Hausdorff formula). Every formal
statement is meant to coincide with the article's statement, in the
article's setting of real or complex unital Banach algebras, with no
additional hypotheses. Appendix D of the article records the correspondence.

## Modules

- `BCH/Commuting.lean` — Proposition 9.1: `[X,Y] = 0 ⇒ e^X e^Y = e^{X+Y}`.
- `BCH/Central.lean` — Theorem 9.2: central commutator; identities (9.2)–(9.4).
- `BCH/Campbell.lean` — Theorem 5.1: `e^{sX} Y e^{-sX} = e^{s ad_X} Y`, the
  series form, the norm bound, and the braiding identities (5.3), (5.4).
- `BCH/Eigen.lean` — Theorem 9.4: `[X,Y] = sY`; identities (9.5)–(9.7).
- `BCH/Log.lean` — Proposition 7.1 (Mercator logarithm): for `‖U‖ < 1`,
  `log(1+U) = Σ (-1)^{k-1} U^k / k` converges, `‖log(1+U)‖ ≤ -log(1-‖U‖)`,
  and `exp(log(1+U)) = 1 + U`; Corollary 7.2: for `‖X‖ + ‖Y‖ < log 2`,
  `Z = log(e^X e^Y)` satisfies `e^Z = e^X e^Y` and `‖Z‖ ≤ -log(2 - e^{‖X‖+‖Y‖})`.
- `BCH/Series.lean` — the homogeneous BCH components `Zₙ(X,Y)` (`bchHom`, by the
  degree recursion (2.7) of the article) and Theorem 7.3 (i), (ii): for
  `‖X‖ + ‖Y‖ < log 2`, `∑ ‖Zₙ‖ < ∞`, `∑ ρⁿ ‖Zₙ‖ ≤ -log(2 - e^{ρ(‖X‖+‖Y‖)})`,
  `∑ Zₙ = log(e^X e^Y)` (Mercator), `exp(∑ Zₙ) = e^X e^Y`, and the tail bound (7.4).
- `BCH/LowDegree.lean` — `Z₁ = X + Y`, `Z₂ = ½[X,Y]`, `Z₃ = 1/12([X,[X,Y]] + [Y,[Y,X]])`,
  `Z₄ = -1/24 [Y,[X,[X,Y]]]` and their associative expansions, and the nested-commutator
  forms of `Z₅` (six brackets) and `Z₆` (five brackets) (Proposition 4.3, degrees one to
  six; `bchHom_five_lie`, `bchHom_six_lie`).
- `BCH/Remainder.lean` — `‖e^C‖ ≤ ‖1‖ e^{‖C‖}`, `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`,
  and the exponential remainder estimate (7.5) of Theorem 7.3 (ii).
- `BCH/Trotter.lean` — Lemma 11.1 (two factors) and Theorem 11.2: the Lie–Trotter
  product formula `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}`, the exact expansion
  `(e^{tX/n} e^{tY/n})^n = exp(t(X+Y) + Σ_{k≥2} t^k n^{1-k} Z_k(X,Y))`, and the
  explicit `O(1/n)` error bound (for `‖1‖ = 1`).
- `BCH/Unique.lean` — Proposition 7.4: `log(e^W) = W` for `‖W‖ < log 2` (Mercator
  logarithm), hence for `‖X‖+‖Y‖ < log 2` and `‖Z₀‖ < log 2`: `e^{Z₀} = e^X e^Y` iff
  `Z₀ = Σ Zₙ(X,Y)`.
- `BCH/Duhamel.lean`, `BCH/DuhamelSeries.lean` — Theorem 5.2 (Duhamel differential):
  `exp` is Fréchet differentiable at every `A` with differential `(dexp)_A = e^A ∘ φ(ad_A)`,
  `φ(ad_A) = Σ (-1)^n/(n+1)! ad_A^n`; the chain rule `d/dt e^{A(t)} = (dexp)_{A(t)}(A'(t))`;
  and the series forms `(dexp)_A H = Σ_{p,q} A^p H A^q/(p+q+1)!`,
  `e^{-A} (dexp)_A H = φ(ad_A) H`, `(dexp)_A H e^{-A} = φ(-ad_A) H`.
- `BCH/Bernoulli.lean` — the coefficients `b⁺ₙ = B⁺ₙ/n!` of `β(z) = z/(1-e^{-z})` defined by
  the recursion of Proposition 5.3, `|b⁺ₙ| ≤ 1`, and `φ(ad_A) β(ad_A) = β(ad_A) φ(ad_A) = 1`
  for `‖A‖ < 1/2`.
- `BCH/BernoulliNumbers.lean` — `bplus n = bernoulli' n / n!`: the recursion-defined
  coefficients are the Bernoulli numbers (convention `B⁺₁ = +1/2`) divided by `n!`.
- `BCH/ODE.lean` — Theorem 6.1 (logarithmic differential equation): there is `δ > 0` such
  that for `‖X‖ + ‖Y‖ < δ` the curve `Z(t) = log(e^X e^{tY})` satisfies `Z(0) = X` and
  `Z'(t) = β(ad_{Z(t)}) Y` for `|t| ≤ 1` (via the inverse function theorem and
  Proposition 7.4); conversely (`bch_ode_unique`) a solution of this initial value
  problem with `‖Z(t)‖ < 1/2` on a disc of radius `> 1` equals `log(e^X e^{tY})`.
- `BCH/LieClosed.lean` — Proposition 8.1 (the BCH logarithm is a Lie element, analytic
  form): there is `δ > 0` such that for every closed `𝕂`-subspace `𝔤 ⊆ 𝔸` closed under
  the commutator and all `X, Y ∈ 𝔤` with `‖X‖ + ‖Y‖ < δ`, `log(e^X e^Y) ∈ 𝔤` (Lipschitz
  estimate for `W ↦ β(ad_W) Y`, invariance of `𝔤` under it, and Gronwall's inequality
  for `dist(Z(t), 𝔤)`); for matrix Lie algebras this is the local BCH multiplication law.
- `BCH/LieCoeff.lean` — Proposition 8.1, homogeneous form: for every closed Lie subalgebra
  `𝔤` and all `X, Y ∈ 𝔤`, every component `Zₙ(X,Y)` lies in `𝔤` (no smallness): scaling and
  extraction of the coefficients of `t ↦ Σ tⁿ Zₙ(X,Y) ∈ 𝔤` (`mem_of_tsum_smul_mem`).
- `BCH/Formal/Free.lean` — the free algebra `𝕂⟨X,Y⟩` as the monoid algebra of the free
  monoid on two letters (`FreeTwo`, generators `genX`, `genY`), homogeneity, the degree
  projections, homogeneity of the formal `Zₙ`, and the grading of the Lie polynomials
  `lieGen` (`proj_mem_lieSpan`).
- `BCH/Formal/Trunc.lean` — the truncated regular representation `rho` of `𝕂⟨X,Y⟩` on the
  finite-dimensional space of words of length `≤ N`, faithful in degrees `≤ N`.
- `BCH/Formal/LieSeries.lean` — **Theorem 3.6 (formal BCH theorem)**: every `Zₙ(X,Y)` is a
  Lie polynomial (`bchHom_mem_lieGen`), deduced from Proposition 8.1 in the operator algebra
  of the truncated representation.
- `BCH/Formal/WordCut.lean` — **Theorem 2.2 (every associative BCH coefficient)**: the
  tuples of blocks `blockTuples k n` (`mem_blockTuples`), the block words and weights, the
  nonrecursive expansion `Zₙ = Σ_k (-1)^{k-1}/k Σ X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k}/∏ rᵢ!sᵢ!` in any
  algebra (`bchHom_eq_sum_blockTuples`), and the word coefficients `c(w)` of the formal `Zₙ`
  as a finite sum over cuts of `w` into blocks (`coeff_bchHom`, `wordCoeff_eq`).
- `BCH/Formal/Dynkin.lean` — the right Dynkin operator `R` (right-nested bracketing of
  words), the identity `R(ab) = φ(a) R(b) + ε(b) R(a)` with `φ` the adjoint representation of
  the free algebra, **Lemma 3.4 (Dynkin–Specht–Wever)** `R(P) = n P` for homogeneous Lie
  polynomials of degree `n` (`R_of_mem_lieGen`), and **Theorem 4.1 (Dynkin's formula)**
  `Zₙ = (1/n) Σ_w c(w) R(w)` (`bchHom_eq_dynkin`) and its all-terms form
  `Zₙ = (1/n) Σ_k (-1)^{k-1}/k Σ R(X^{r₁}Y^{s₁}⋯)/∏ rᵢ!sᵢ!` (`bchHom_eq_dynkin_blocks`).
- `BCH/CentralMany.lean` — **Corollary 9.3 (several factors with central pairwise
  commutators)**: `e^{X₀} ⋯ e^{X_{m-1}} = exp(Σⱼ Xⱼ + ½ Σ_{i<j} ⁅Xᵢ,Xⱼ⁆)`
  (`exp_prod_range_of_central`), by induction on the number of factors from the two-factor
  central identity.
- `BCH/LinearY.lean` — **Corollary 6.4 (all single-`Y` terms)**: for `‖X‖ + ‖Y‖` small,
  `t ↦ Z(X, tY)` is differentiable at `0` with derivative `β(ad_X) Y = Σₙ (Bₙ⁺/n!) ad_Xⁿ Y`
  (`exists_delta_hasDerivAt_bch_linearY`), from the logarithmic ODE at `t = 0` and the
  Bernoulli identification.
- `BCH/Symmetric.lean` — **Proposition 11.3 (symmetric splitting)**: two nested applications
  of the BCH theorem give `L = Z(Z(A,B), A)` with `e^L = e^A e^B e^A` and
  `‖L - (2A + B)‖ ≤ c₂ (‖A‖+‖B‖)³` (the degree-two terms cancel; `symmetric_log_bound`,
  using `-log(2 - e^σ) ≤ 2σ` for `σ ≤ 1/4`), hence
  `S₂(t/n)^n = exp(t(X+Y) + Eₙ)` with `‖Eₙ‖ ≤ c₂|t|³a³/n²` (`symmetric_expansion`), the
  explicit `O(n⁻²)` error bound (`symmetric_error`) and the limit (`symmetric_limit`).
- `BCH/DynkinSeries.lean` — **Theorem 7.3 (iii), (iv) (absolute convergence of Dynkin's Lie
  series)**: the right-nested brackets `rbEval` evaluated in a normed space with a bracket
  bound `‖⁅u,v⁆‖ ≤ κ‖u‖‖v‖`, the estimate `‖[x₁,[x₂,…,xₙ]]‖ ≤ κ^{n-1} ∏‖xᵢ‖`, the Dynkin
  series `dynkinTerm` and the sum of the norms of its summands `dynkinNormSum`; absolute
  summability with the bound `κ⁻¹[-log(2 - e^{κs})]` and tails `ρ^{-(N+1)} κ⁻¹[-log(2 - e^{κρs})]`
  (`tsum_dynkinNormSum_le`, `tsum_dynkinNormSum_tail_le`); the associative case `κ = 2` with
  `M_D(s) = -½ log(2 - e^{2s})` (`tsum_dynkinNormSum_le_of_lt`), and `Zₙ = dynkinTerm ![X,Y] n`
  (`bchHom_eq_dynkinTerm`).
- `BCH/Trace.lean` — **Proposition 7.5 (trace identity)**: the evaluation homomorphism
  `evalHom` of `𝕂⟨X,Y⟩`, vanishing of any tracial linear functional on `Zₙ(X,Y)` for `n ≥ 2`
  (`tracial_bchHom`, via Dynkin–Specht–Wever), `τ(Σ Zₙ) = τ X + τ Y` for continuous tracial
  functionals when the series converges (`tracial_tsum_bchHom`), and the matrix case
  `tr Z(X,Y) = tr X + tr Y` (`trace_tsum_bchHom`, ℓ∞-operator norm).

## Building

The package depends on Mathlib (rev `v4.32.0`, toolchain `leanprover/lean4:v4.32.0`).
On the development machine the package cache is not vendored:
`lean/.lake/packages` is a directory junction to an already built cache
(`C:\ProveIt\.lake\packages`), which `.gitignore` excludes. Elsewhere, run
`lake exe cache get` (or `lake update`) once to obtain Mathlib.

```sh
cd lean
LAKE_JOBS=1 lake build BCH
```

## Conventions

- Scalars: `[RCLike 𝕂]`; algebra: `[NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]`.
- Bracket: `⁅X, Y⁆ = X * Y - Y * X` (`Ring.lie_def`).
- Exponential: `NormedSpace.exp`. The `ℚ`- (and where needed `ℝ`-) algebra
  structures Mathlib's exponential and derivative lemmas require are obtained
  inside proofs by `NormedAlgebra.restrictScalars`, never as hypotheses.
- Proofs of exponential identities use a zero-derivative argument
  (`is_const_of_deriv_eq_zero`) in place of ODE uniqueness.
