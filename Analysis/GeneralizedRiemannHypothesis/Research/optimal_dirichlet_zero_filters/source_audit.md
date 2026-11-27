# Repository source audit

Retrieved with the GitHub connector on 2026-11-27, from `VladimirReshetnikov/ProveIt` at ref `main`. Paths relative to `Analysis/GeneralizedRiemannHypothesis/`. These are Git blob identifiers from retrieved contents, not independent build attestations. Upstream commit is as reported by the vendored README.

| Path | Git blob SHA |
|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 |
| vendor/grh-lean/grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 |
| vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean | 5c06362a50e044d491423fb3d830bae6a50c0075 |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 |

`Article/sections/rec.tex` was retrieved and inspected for `rec:thm:twofreq`, `rec:thm:logfilter`, `rec:thm:uniformavg`, `rec:sec:open`, and the theorem inventory. The relevant `zer.tex` material is `zer:lem:ramp` and `zer:eq:Zexp`. For the longer files, inspection was targeted, not an exhaustive line-by-line audit.

Upstream reported commit: `72fead102f663d5c7a407964a13dc0cf9d977207`.

Related engineering prior art: https://doi.org/10.3390/act14020097 (section 2.4) and https://www.researchgate.net/publication/37605267_Command_generation_for_flexible_systems (chapter 3). The five-impulse low-ratio shaper is known. The candidate extensions in this note are the general cluster optimality/uniqueness and analytic-deformation arguments, stability, and the explicit arithmetic transfer.
