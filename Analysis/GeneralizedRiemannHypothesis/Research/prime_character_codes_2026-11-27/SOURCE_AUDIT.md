# Source audit — 27 November 2026

The requested two directories were accessed through the GitHub connector, read-only. No repository files were changed. The `main` branch returned commit `2f43dd5a5add67a4d8a4661810e5cb70d468349a` during the inspection. Directory tree identifiers returned by the connector:

- `Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean/grh`: `2e133df63d7f4da6b3059c4195324f8e9187ba73`
- `Analysis/GeneralizedRiemannHypothesis/Article/sections`: `5ea418a24081239fe126bb25757cd4897d31e74a`

The vendor README says the 818 files in `grh/` are byte-identical to upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`. This note did not independently compare all 818 files. The source is a separate Lake package with Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The ProveIt root build does not build it.

## Inspected text files (Git blob SHA returned by connector)

Paths relative to `Analysis/GeneralizedRiemannHypothesis/`:

| Path | Blob SHA | Use |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Provenance and separate package |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Build, theorem statements, reported axioms |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact definitions |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorems |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | Upstream audit entry point |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | Functional-equation symmetry |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | Main GRH interface, declaration scan |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | 131 reports, 914 results, status |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Article section map |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Overview and distinctions |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Heading scan of mechanism |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | Smoothed prime sums, distinct samples, product-support and partition comparison |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Prime Gram estimate, reconstruction titles, keyword scan |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Theorem-heading scan |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | Theorem-heading scan |
| `Article/sections/gra.tex` | `48797ee87d3cb1c92114438476950d4a976fea0d` | Theorem-heading scan |
| `Article/remarkable-results.tex` | `e7ce20d0eed0f0d0aa03656b1ba80243e746daa6` | Targeted keyword scan |

This is a selective analysis of the relevant source and comparison results, not a line-by-line audit of the entire 723-page article or 300,000 lines of Lean. The `.tex` sources, rather than the article PDF, were used.

## Exact theorem interface

`Statements.lean` defines `DirichletLZerosOnLine` as follows (the following is a short source excerpt):

```lean
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

`Main.lean` exports `LFunction_eq_zero_re : DirichletLZerosOnLine`, `riemannHypothesis : RiemannHypothesis`, and `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`. The source shows the latter is `New.grh`, while `New.zeros_on_line New.grh` proves the critical-strip statement. These are the only zero-location inputs needed. The classical functional equation and explicit formula are used in the mathematical paper.

The pinned readable upstream's own README reports the axioms `propext`, `Classical.choice`, `Quot.sound`; independent checks of this commit are reported by Andrew Sutherland at https://klein.mit.edu/~drew/shortgrh/ (26 Nov 2026). We did not run Lean or the comparator in this environment. `InputAudit.lean` is a small untested interface file, not a formalization of the new results.

## Comparison and novelty

The merged Article explicitly treats Dirichlet GRH as input. It contains a fixed-bias small-prime sampling result (`dir:lem:oneset`), the smoothed estimates (`dir:lem:smooth`, `rec:lem:gram`), squarefree product support after deletions (`dir:thm:quotient`), and simultaneous factorization (`dir:thm:factorization`, `dir:thm:minority`). Those techniques are acknowledged and adapted. The new target is linear combinations and their near-minimum empirical support, not products. Targeted searches for Donoho–Stark, Hamming distance, sparse character mixtures, error-correcting and uncertainty principle in the relevant reconstruction and highlights source did not identify a matching theorem. The external uncertainty-principle literature already proves the uniform-measure equality cases; we do not claim these are new. No exhaustive priority search was possible.
