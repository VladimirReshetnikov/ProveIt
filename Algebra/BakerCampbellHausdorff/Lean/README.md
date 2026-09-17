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
  `Z₄ = -1/24 [Y,[X,[X,Y]]]` and their associative expansions (Proposition 4.3,
  degrees one to four).
- `BCH/Remainder.lean` — `‖e^C‖ ≤ ‖1‖ e^{‖C‖}`, `‖e^B - e^A‖ ≤ ‖1‖² e^{max(‖A‖,‖B‖)} ‖B - A‖`,
  and the exponential remainder estimate (7.5) of Theorem 7.3 (ii).
- `BCH/Trotter.lean` — Lemma 11.1 (two factors) and Theorem 11.2: the Lie–Trotter
  product formula `(e^{tX/n} e^{tY/n})^n → e^{t(X+Y)}`, the exact expansion
  `(e^{tX/n} e^{tY/n})^n = exp(t(X+Y) + Σ_{k≥2} t^k n^{1-k} Z_k(X,Y))`, and the
  explicit `O(1/n)` error bound (for `‖1‖ = 1`).
- `BCH/Unique.lean` — Proposition 7.4: `log(e^W) = W` for `‖W‖ < log 2` (Mercator
  logarithm), hence for `‖X‖+‖Y‖ < log 2` and `‖Z₀‖ < log 2`: `e^{Z₀} = e^X e^Y` iff
  `Z₀ = Σ Zₙ(X,Y)`.

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
