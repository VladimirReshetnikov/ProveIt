/-
# Baker–Campbell–Hausdorff: formalization root

This library accompanies the article in `docs/combined`. It formalizes,
in Lean 4 with Mathlib, results of the article with statements matching
the article's own, in the article's setting of real or complex unital
Banach algebras:

* `BCH.Commuting` — Proposition 9.1 (commuting case);
* `BCH.Central`   — Theorem 9.2 (central commutator), identities (9.2)–(9.4);
* `BCH.Campbell`  — Theorem 5.1 (Campbell's identity) and the braiding
  identities (5.3), (5.4);
* `BCH.Eigen`     — Theorem 9.4 (the relation `[X, Y] = sY`), identities
  (9.5)–(9.7);
* `BCH.Log`       — Proposition 7.1 (the Mercator logarithm `log(1 + U)` for
  `‖U‖ < 1`, `exp(log(1 + U)) = 1 + U`) and Corollary 7.2 (the BCH logarithm
  `Z = log(e^X e^Y)` with `e^Z = e^X e^Y` for `‖X‖ + ‖Y‖ < log 2`);
* `BCH.Series`    — the homogeneous BCH series `Zₙ(X, Y)` and Theorem 7.3 (i), (ii):
  for `‖X‖ + ‖Y‖ < log 2` the series `∑ₙ Zₙ(X, Y)` converges absolutely with
  the majorant `-log(2 - e^{ρ s})`, its sum `Z` satisfies `e^Z = e^X e^Y`, and
  the tail after degree `N` is at most `ρ^{-(N+1)} (-log(2 - e^{ρ s}))`;
* `BCH.LowDegree` — the components `Z₁, …, Z₆` in closed (nested-commutator) form
  (Proposition 4.3, equations (4.9)–(4.14), and the associative expansions (4.15)–(4.17));
* `BCH.Remainder` — `‖e^C‖ ≤ ‖1‖ e^{‖C‖}`, the Lipschitz estimate
  `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`, and the exponential remainder
  estimate (7.5) of Theorem 7.3 (ii);
* `BCH.Trotter`   — Lemma 11.1 (tail bounds `c₀ σ²`, `c₀' σ³`) and Theorem 11.2: the
  Lie–Trotter formula `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}` with its complete
  logarithmic error `∑_{k ≥ 2} t^k n^{1-k} Zₖ(X, Y)` and the explicit `O(1/n)`
  bound;
* `BCH.Unique`    — Proposition 7.4: `log(e^W) = W` for `‖W‖ < log 2`, and the BCH
  sum is the unique logarithm `Z₀` of `e^X e^Y` with `‖Z₀‖ < log 2`;
* `BCH.Duhamel`, `BCH.DuhamelSeries` — Theorem 5.2 (Duhamel): `exp` is Fréchet
  differentiable with `(dexp)_A = e^A ∘ φ(ad_A)`, `d/dt e^{A(t)} = (dexp)_{A(t)}(A'(t))`,
  and the three series forms (5.5)–(5.7);
* `BCH.Bernoulli` — the coefficients `b⁺ₙ` of `β(z) = z/(1 - e^{-z})` by the recursion of
  Proposition 5.3, their bound `|b⁺ₙ| ≤ 1`, and the operator identities
  `φ(ad_A) β(ad_A) = β(ad_A) φ(ad_A) = 1` for `‖A‖ < 1/2`; `BCH.BernoulliNumbers`
  identifies `b⁺ₙ = B⁺ₙ/n!` with Mathlib's Bernoulli numbers `bernoulli'`;
* `BCH.ODE`       — Theorem 6.1 (logarithmic differential equation): for `X, Y` small,
  `Z(t) = log(e^X e^{tY})` satisfies `Z'(t) = β(ad_{Z(t)}) Y`, `Z(0) = X`, and conversely
  a small solution of this initial value problem is `log(e^X e^{tY})`;
* `BCH.LieClosed` — Proposition 8.1: for `X, Y` small in a closed Lie subalgebra `𝔤` of
  `𝔸` (closed subspace closed under the commutator), `log(e^X e^Y) ∈ 𝔤`; in particular the
  local BCH multiplication law of matrix Lie algebras;
* `BCH.LieCoeff`  — Proposition 8.1, homogeneous form: `Zₙ(X, Y) ∈ 𝔤` for all `X, Y ∈ 𝔤`
  and all `n`, without smallness (coefficient extraction from `∑ₙ tⁿ Zₙ(X, Y) ∈ 𝔤`);
* `BCH.Formal.Free`, `BCH.Formal.Trunc`, `BCH.Formal.LieSeries` — **Theorem 3.6, the formal
  BCH theorem**: in the free algebra `𝕂⟨X, Y⟩` every homogeneous component `Zₙ(X, Y)` is a
  Lie polynomial (`bchHom_mem_lieGen`), proved from the analytic Lie-series property through
  the truncated regular representation and the grading of the Lie polynomials;
* `BCH.Formal.WordCut` — Theorem 2.2: the nonrecursive block expansion
  `Zₙ = ∑_k (-1)^{k-1}/k ∑ X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k} / ∏ rᵢ!sᵢ!` in any algebra
  (`bchHom_eq_sum_blockTuples`) and the word-coefficient formula `c(w) = ∑_k (-1)^{k-1}/k
  ∑_{cuts of w into blocks} ∏ (rᵢ!sᵢ!)⁻¹` (`coeff_bchHom`, `wordCoeff_eq`);
* `BCH.Formal.Dynkin` — Lemma 3.4 (Dynkin–Specht–Wever), `R(P) = n P` for homogeneous Lie
  polynomials `P` of degree `n` (`R_of_mem_lieGen`), and Theorem 4.1 (Dynkin's formula) in
  the forms `Zₙ = (1/n) ∑_w c(w) R(w)` (`bchHom_eq_dynkin`) and
  `Zₙ = (1/n) ∑_k (-1)^{k-1}/k ∑ R(X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k}) / ∏ rᵢ!sᵢ!`
  (`bchHom_eq_dynkin_blocks`);
* `BCH.Symmetric` — Proposition 11.3, the symmetric (Strang) splitting: for
  `n > 6 |t| a / log 2`, `(e^{tX/(2n)} e^{tY/n} e^{tX/(2n)})^n = exp(t(X+Y) + Eₙ)` with
  `‖Eₙ‖ ≤ c₂ |t|³ a³ / n²` (`symmetric_expansion`; the degree-two terms cancel,
  `symmetric_log_bound`), the error bound `symmetric_error`, and the limit `symmetric_limit`;
* `BCH.DynkinSeries` — Theorem 7.3 (iii), (iv): in a normed space with a bracket satisfying
  `‖⁅u, v⁆‖ ≤ κ ‖u‖ ‖v‖` (a normed Lie algebra; `κ = 2` for associative algebras), the
  right-nested commutator summands of Dynkin's formula are absolutely summable when
  `κ (‖X‖ + ‖Y‖) < log 2`, with absolute sum at most `κ⁻¹ [-log (2 - e^{κ s})]` and tails
  `ρ^{-(N+1)} κ⁻¹ [-log (2 - e^{κ ρ s})]` (`tsum_dynkinNormSum_le`, `tsum_dynkinNormSum_tail_le`,
  `tsum_dynkinNormSum_le_of_lt` with `M_D(s) = -½ log (2 - e^{2s})`), and `Zₙ(X, Y)` is the
  degree-`n` part of the evaluated Dynkin series (`bchHom_eq_dynkinTerm`);
* `BCH.Trace`     — Proposition 7.5: a tracial linear functional vanishes on `Zₙ(X, Y)` for
  `n ≥ 2` (`tracial_bchHom`), so `τ(Z) = τ X + τ Y` for continuous tracial functionals
  whenever the series converges (`tracial_tsum_bchHom`); for matrices,
  `tr Z(X, Y) = tr X + tr Y` (`trace_tsum_bchHom`).
-/
import BCH.Commuting
import BCH.Central
import BCH.Campbell
import BCH.Eigen
import BCH.Log
import BCH.Series
import BCH.LowDegree
import BCH.Remainder
import BCH.Trotter
import BCH.Unique
import BCH.Duhamel
import BCH.DuhamelSeries
import BCH.Bernoulli
import BCH.BernoulliNumbers
import BCH.ODE
import BCH.LieClosed
import BCH.LieCoeff
import BCH.Formal.Free
import BCH.Formal.Trunc
import BCH.Formal.LieSeries
import BCH.Formal.WordCut
import BCH.Formal.Dynkin
import BCH.Trace
import BCH.DynkinSeries
import BCH.Symmetric
