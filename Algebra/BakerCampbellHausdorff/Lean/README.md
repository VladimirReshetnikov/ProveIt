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
