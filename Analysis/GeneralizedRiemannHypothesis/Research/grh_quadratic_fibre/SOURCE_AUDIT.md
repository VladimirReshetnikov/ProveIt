# Source audit

Retrieved using the GitHub connector, from `VladimirReshetnikov/ProveIt`, ref `main`, on 27 November 2026. Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. Blob identifiers identify the retrieved source versions independently of subsequent changes to main. The inspection was targeted, not a line-by-line audit of the entire proof or the 914-result article.

## Vendored Lean

| Path | Git blob SHA-1 | Role |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Vendor provenance and build separation |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Reported proof/check status and toolchain |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact definitions in Mathlib terms |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Five exported theorem statements |
| vendor/grh-lean/grh/src/New/Main.lean | fc0ae69627d2e66c3d1d57815d42f0aac5823432 | Reflection to critical line |
| vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 | Corrected-covolume comparison |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | Prime remainder and half-plane theorem |
| vendor/grh-lean/grh/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | Axiom inspection script |

Vendored `grh/` tree: `2e133df63d7f4da6b3059c4195324f8e9187ba73`.

The vendor README identifies upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207` and reports a byte-identical import. We did not compare all 818 files. Upstream identifies Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The relevant declarations are `LFunction_ne_zero_of_half_lt_re` and `LFunction_eq_zero_re`, with propositions `DirichletLNonvanishingRightOfHalf` and `DirichletLZerosOnLine`. The former is `New.grh`. The upstream README reports independent checks and dependence only on `propext`, `Classical.choice`, `Quot.sound`. See also Andrew Sutherland's independent verification record: https://klein.mit.edu/~drew/shortgrh/. We did not execute the Lean proof or its axiom script locally. No stronger zero hypothesis is used.

## Merged article

| Path | Git blob SHA-1 | Role |
|---|---|---|
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | 131 reports, 723 pages, 914 statements; merged, not reviewed |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | Article organization |
| Article/sections/abstract.tex | 649adf939b67e9807d87854cec0668016868c2d6 | Summary |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c | Scope and status labels |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Input theorem, proof architecture |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | Main related results and open question |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | Heading-level comparison |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | Heading-level comparison |

Article sections tree: `5ea418a24081239fe126bb25757cd4897d31e74a`. Used TeX sources rather than the article PDF. Relevant labels: `src:thm:dgrh`, `dir:lem:bias`, `dir:lem:circle`, `dir:thm:quotient`, `dir:cor:squarefree`, `dir:prop:explicit`, and `dir:sec:open` (near-half retention question, item 12). The prior article supplies a uniform bounded quotient and an exact parity coefficient; the present note proves an approximation with uniform relative error on rare fibres, a necessary-and-sufficient asymptotic equidistribution criterion for sparse quotas, and a sharp correction. The separate short-quota and optimal-constant questions remain open here.

Source links:
- https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/vendor/grh-lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/Article/sections/dir.tex
- https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh

The paper's bibliography records the targeted external literature comparison. The statement is a candidate new contribution, not a certificate of global novelty.
