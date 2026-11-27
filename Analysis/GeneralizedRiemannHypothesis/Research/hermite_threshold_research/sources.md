# Repository provenance

Retrieved via GitHub connector from `VladimirReshetnikov/ProveIt`, ref `main`, 27 November 2026. The following blob SHAs identify the retrieved versions of key files (not commit SHAs).

Base: https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/

| Relative path | Blob SHA | Use |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | upstream pin and build separation |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | theorem and reported verification scope |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | exact mathematical statement |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | exported declarations |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | inventory and status |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | mechanism and quantifiers |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | main antecedents and open question |
| Article/remarkable-results.tex | e7ce20d0eed0f0d0aa03656b1ba80243e746daa6 | assessment, initial sections |

Source README pins upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean v4.35.0.

Target: Article/sections/dir.tex, lines 3538–3846 (Hermite thresholds, parity bias, prime application) and lines 3847–3927 (open questions), especially `dir:lem:hamming`, `dir:lem:radau`, `dir:prop:hammingdual`, `dir:thm:signs`, and Open Question 14. The heading inventories of the rec, zer, dir, li, gra, tors, cost and lub sections were also inspected to select the research direction. This is not a comprehensive audit of all article claims or all Lean files.

Related literature checked by public search: Bellaïche, https://doi.org/10.24033/asens.2291 ; Derksen–Ivanov–Lee–Viola, https://arxiv.org/abs/2407.12110 . The search was limited and does not establish global originality.
