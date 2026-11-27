# Source snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Main ref resolved during this task: `a4404ca0247c31b8760589015b7eb6ab4efb6f92`.
Base: `Analysis/GeneralizedRiemannHypothesis/`.

| Inspected file | Git blob SHA |
|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 |

The primary mathematical source is `rec.tex`, subsection `rec:sec:dilation`, especially `rec:thm:hblock`, `rec:thm:twofreq`, and the open questions. The source README pins upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Lean v4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The source reports independent checks; this task did not rerun them. We used the GitHub connector and read relevant source text rather than extracting the merged PDF.

Other references: https://doi.org/10.1016/S0005-1098(03)00024-4 (time-optimal input shaping); https://www.sciencedirect.com/science/article/abs/pii/S0005109807001264 (discrete command shaping with derivative constraints); https://flintlib.org/doc/tutorials/numerics/zeta.html (documented first zeta zero ordinates).
