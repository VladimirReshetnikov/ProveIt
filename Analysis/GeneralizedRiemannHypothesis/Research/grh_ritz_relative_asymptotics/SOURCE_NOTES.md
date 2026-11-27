# Source provenance and scope

GitHub connector reads of `VladimirReshetnikov/ProveIt`, branch `main`, performed on 2026-11-27. All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. The connector returned these blob SHA identifiers, not a repository HEAD commit; there was no full checkout. The article's root README says it merges 131 reports and 914 stated results; it expressly does not constitute independent review. The vendor README states that the readable edition is copied from upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207` and that the import was not rebuilt. The vendored proof README reports a pinned Lean v4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and independent checker acceptance. These are source reports, not checks repeated here.

| Path | Blob SHA | Use |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | provenance and build scope |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | theorem interfaces, reported axioms and checks |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | mathematical quantifiers |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | exported theorem names |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | corpus and status |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | structure |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | source mechanism and theorem scope, initial 100 lines |
| Article/sections/li.tex | 87871b581808b4388135617b7d38cae1438bece5 | detailed Ritz section, open questions and headings |
| Article/sections/ana.tex | f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce | headings and open questions |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | headings and selected open questions/positive filters |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | headings and selected open questions/transport |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | headings |

The exact research target is `li:thm:ritz`, `li:thm:ritzcert`, `li:cor:ritzdir`, `li:q:ritz`. The article is not exhaustively audited; comparisons are to inspected portions. The quoted leading rate for Dirichlet distance spectra is taken from the article; its abstract moment proof is independent of the article's packing argument. The arithmetic next-correction hierarchy uses those earlier rate theorems in addition to RH/GRH, not an independent proof of the rate.

Targeted literature searches found standard related work by Voros, Lasserre, Zemke, and Malejki (references in paper). This is not an exhaustive literature review. No claim of globally established priority is made.
