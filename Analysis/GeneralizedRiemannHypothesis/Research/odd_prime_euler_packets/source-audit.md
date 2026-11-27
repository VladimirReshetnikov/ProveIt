# Source audit (27 November 2026)

All listed paths are under `Analysis/GeneralizedRiemannHypothesis/` of [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt). Directory listings and text were obtained using the GitHub connector, at ref `main`. Blob SHAs identify the inspected texts independently of subsequent updates; the whole branch was not pinned to a single commit during retrieval.

| Path | Inspected blob SHA | Use |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Identifies upstream revision and separate build |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Claimed kernel and independent checks, Lean/mathlib requirements |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Formal Dirichlet GRH statement |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exported theorem interface |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | `New.grh`, main one-sided proof endpoint |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | Audit command source, not independently executed |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | 131 merged reports and scope limits |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Source theorem and architecture headings |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | Prime Gram lemma, quadratic packet theorem and explicit open question |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` | Small-bias prime pool and comparison |
| `Article/sections/spn.tex` | `886e8716472aa82fd45ff68da03be946e9dbd3da` | Related headings on selection and matrix statistics |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | Related headings on zeros and prime races |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | Related headings on moment pencils |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | Related headings on one-sided analytic methods |
| `Article/remarkable-results.tex` | `e7ce20d0eed0f0d0aa03656b1ba80243e746daa6` | Keyword screen for overlap |

The vendor README pins upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`, Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. It reports the axioms `propext`, `Classical.choice`, `Quot.sound` and independent checkers. No rebuild was performed here. The merged article README expressly warns that it merges prior reports without rechecking their mathematics.

## Exact research dependency

`rec:lem:gram` gives a smoothed prime estimate for primitive character pairs with error `O_w(sqrt(x) log(2qf))`. The proof in the article uses the smoothed explicit formula, GRH, local zero counts and removal of prime powers. Specializing to the primitive character of conductor 1 and passing to common modulus Q gives the new note's transfer lemma. `rec:thm:qmatch` classifies quadratic packet agreement, with the companion `rec:thm:qmatchfinite` for finite detection. The open question at approximately lines 4670–4672 in `rec.tex` asks whether odd-prime-order products have similarly explicit ranges. The new proof answers the minimum and two smallest positive disagreement levels in the stated ranges, not the entire spectrum.

## Literature check

A limited web search examined the finite uncertainty principle (Meshulam, DOI 10.1016/j.ejc.2004.07.009), discrete tomography (Matousek–Privetivy–Skron, DOI 10.1137/080715706), and finite-field exceptional projections (Fraser–Rakhmonov, arXiv:2503.15072), plus work on special directions. The refined uncertainty inequality already gives the numerical lower bound at prime-power packet sizes. The projection-energy proof strengthens that numerical estimate at general sizes and classifies equality; no independent priority claim is made for the finite geometry or for the complete combination. This is a new extension relative to the relevant inspected article sections, not a comprehensive novelty search across all 914 results or the literature.
