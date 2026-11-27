# Source audit

Repository: https://github.com/VladimirReshetnikov/ProveIt
Branch requested: `main`. Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. Retrieved through the GitHub connector on 27 November 2026. Blob SHA values identify the individual file contents fetched; we did not pin or retrieve an entire ProveIt commit.

| Source | Git blob SHA | Use |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Vendoring provenance, upstream commit and isolated build |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported checks, axiom list and build instructions |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Actual exported theorem statements |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Exact quantified propositions |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | Final one-sided ramp bound and GRH reduction |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Scope of 131-report merge and verification caveat |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Article structure |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Scope and status marks |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Source theorem and ramp mechanism |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Headings and detailed filter section: `rec:thm:finitefilter`, `rec:thm:logfilter`, `rec:lem:jensensupport`, `rec:thm:uniformavg`, `rec:thm:polylogavg` |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Headings and detailed `zer:lem:ramp`, `zer:eq:Zexp` |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | Headings and targeted kernel search |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Headings and targeted kernel search |

Upstream Lean commit reported by the vendor README: `72fead102f663d5c7a407964a13dc0cf9d977207`. Reported toolchain: Lean v4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Reported axiom set: `propext`, `Classical.choice`, `Quot.sound`. These are source claims, not independently verified in this task.

The exact scope imported is RH and Dirichlet GRH. There is no assumption of zero simplicity, zero disjointness, linear independence of ordinates, GRH for nonabelian fields, or GRH for general automorphic L-functions. The underlying positive quadrature theorem does not require any RH input.

The relevant prior upper bound is O(log B), while the cited Jensen lower bound gives a leading constant of d/2 for d completed functions. The new proof obtains a matching leading constant for the specified positive-kernel functions. Only selected article sections and theorem headings were inspected, not every result in the full collection. A targeted public literature search on positive Fourier quadrature, compact support for Xi kernels and exponential-polynomial extrapolation did not establish exact theorem priority; the note does not certify worldwide novelty.
