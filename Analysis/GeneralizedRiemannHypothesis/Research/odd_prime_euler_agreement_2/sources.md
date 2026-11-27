# Source audit

GitHub connector inspected these two requested directories on branch `main`.
The branch API returned commit `5643009d2e76fb6c235f023e515fc64ef57cb3f3`
(2026-11-27T19:17:09Z). File blob IDs below identify the fetched versions.

Base: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis

| File | Git blob | Use |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Upstream commit and isolation from root build |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Reported checks, toolchain, scope |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact Dirichlet GRH interface |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Exported theorem statements |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | Scope and review limitation |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | Merged article organization |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Source-theorem section headings |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 | Topic screening (headings) |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | Topic screening (headings) |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | Topic screening (headings) |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | Prime Gram lemma (near line 141), quadratic agreement (near line 4143), open question (near line 4670) |

The vendor README identifies upstream commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, imported November 27, 2026.
It reports that the vendored `grh/` subtree was byte-identical to the upstream
readable edition, but not compiled during import. The upstream README reports
Lean compilation, independent checker acceptance, and Comparator acceptance.
These reports were not independently reproduced here. The source theorem covers
Dirichlet L-functions, not arbitrary automorphic L-functions.

The Article README describes a merge of 131 reports, not an independent review.
The present work specifically follows and extends the quadratic agreement
subsection, rather than rechecking every one of the 914 listed results.

## Literature verification

- A. B. Sørensen, Projective Reed-Muller codes, IEEE Trans. Inform. Theory 37
  (1991), 1567–1576, https://doi.org/10.1109/18.104317.
- S. R. Ghorpade and R. Ludhani, On the minimum distance, minimum weight
  codewords, and the dimension of projective Reed-Muller codes, Adv. Math.
  Commun. 18 (2024), 360–382, https://doi.org/10.3934/amc.2023035.
- M. G. Sarabia et al., On the generalized Hamming weights of certain
  Reed–Muller-type codes, Theorem 3.3 reproduces the minimum-distance formula:
  https://doi.org/10.2478/auom-2020-0014.
- Related finite-plane uncertainty literature: A. Biró and V. F. Lev,
  Uncertainty in finite planes, https://real.mtak.hu/138965/2/1808.pdf.

A targeted search located the classical code distance formula and related
uncertainty/tomography research; no comprehensive priority search was done.
The new candidate contribution is the cyclotomic lifting argument in the
packet setting, its digit-sensitive consequence and constructions, and the
signed finite-prime test. No claim is made of a named-conjecture resolution.
