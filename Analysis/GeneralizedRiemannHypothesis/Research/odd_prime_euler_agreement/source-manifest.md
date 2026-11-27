# Source manifest and dependency audit

Read via the GitHub connector on 27 November 2026. These are Git blob SHA-1 identifiers returned by GitHub for individual files (not commit identifiers). The branch was `main`; the upstream commit is the one explicitly recorded in the vendor README. The selected article files were examined at the level of source text, including the relevant theorem and open-question sections. The full 723-page merged article and the entire 818-file vendored Lean tree were not exhaustively audited.

Repository: https://github.com/VladimirReshetnikov/ProveIt

Base path: `Analysis/GeneralizedRiemannHypothesis/`

| Relative path | Blob SHA | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Pin, vendor status and build separation |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported build and independent checker status |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Actual statements of the zero hypotheses |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorem declarations |
| `vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` | Opening and main theorem: corrected-covolume comparison |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | Opening and reduction lemmas: smoothed prime remainder |
| `vendor/grh-lean/grh/GUIDE.md` | `c2acf9584b58efcb39ac1d668d25c107c3e76a0b` | Opening reading guide and architecture |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | Scope and status of merged article |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Input theorem, labels and organization |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Input theorem and transferable architecture |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Quadratic matching theorem, prime Gram lemma, and odd-prime open question |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Surveyed related open questions |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Surveyed related open questions |

The vendor README pins upstream `lsernau/grh-lean` to commit `72fead102f663d5c7a407964a13dc0cf9d977207` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean v4.35.0. The mathematical input is the Dirichlet zero theorem, not any general Artin or automorphic RH. No build was run in the current environment; Lean was not installed in the working container.

## Exact article anchors

- `rec:lem:gram` — uniform smoothed prime Gram estimate.
- `rec:sec:qmatch`, `rec:lem:walsh`, `rec:thm:qmatch` — binary case, including exact minimum and a high-agreement spectrum.
- `rec:thm:qmatchfinite` — finite detection and density measurement.
- `rec:sec:open` — question concerning products of characters of odd prime order.

## Independent mathematical references

- Ghorpade–Ludhani, *On the minimum distance, minimum weight codewords, and the dimension of projective Reed-Muller codes*, Adv. Math. Commun. 18 (2024), 360–382, Theorem 4.3. https://doi.org/10.3934/amc.2023035; https://arxiv.org/abs/2309.10196. Used for the minimum-support **classification**, not the lower bound (which is reproved).
- Blokhuis–Korchmáros–Mazzocca, *On the structure of 3-nets embedded in a projective plane*, JCTA 118 (2011), 1228–1238, Theorem 5.1 and ensuing affine conic analysis. https://doi.org/10.1016/j.jcta.2010.11.007. Used to exclude nondivisor digits in the equality problem. The original text was retrieved; the PDF screenshot endpoint returned HTTP 403, so that particular visual check was unavailable.
- Classical PNT in progressions and the smoothed explicit formula with Dirichlet GRH; see Davenport, *Multiplicative Number Theory*, third edition, and the article's `rec:lem:gram`.

The references support the ingredients. The connection between the cyclotomic leading digit and the code/net classifications, the derived extremal theorem, and the finite recovery statement are the contributions of this note relative to the inspected article. Literature search is not an exhaustive priority search.
