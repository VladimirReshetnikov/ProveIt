# Source audit

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis

The following Git blob identifiers were returned from GitHub when inspecting main on 2026-11-27. Paths are relative to Analysis/GeneralizedRiemannHypothesis/.

| File | Blob SHA | Use |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Upstream pin; build scope |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Reported checking and axioms |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact Dirichlet GRH proposition |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Exported theorems |
| vendor/grh-lean/grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 | Half-plane to line by symmetry |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | One-sided bound, New.grh |
| vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean | 5c06362a50e044d491423fb3d830bae6a50c0075 | Analytic criterion |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | Scope and status of merged material |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Input statement and mechanism |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | rec:thm:qmatch, rec:thm:qmatchfinite, rec:lem:gram, rec:sec:open (item 6) |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | Related character-sign and prime estimates |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 | Related reconstruction results |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | Related prime and Euler results |

Upstream pin reported by vendor: 72fead102f663d5c7a407964a13dc0cf9d977207; Lean v4.35.0; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Readable edition. Source files were inspected selectively; a full 818-file audit and independent Lean replay were not performed.

External coding theorem: A. B. Sørensen, Projective Reed-Muller codes, DOI 10.1109/18.104317; S. R. Ghorpade and R. Ludhani, On the minimum distance, minimum weight codewords, and the dimension of projective Reed-Muller codes, DOI 10.3934/amc.2023035, Corollary 3.3 and Theorem 4.3, https://arxiv.org/abs/2309.10196. The latter is essential for the equality reduction. The subsequent conic classification is proved in the note.
