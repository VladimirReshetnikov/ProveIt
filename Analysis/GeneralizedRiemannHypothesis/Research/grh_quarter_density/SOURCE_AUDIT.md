# Source audit — 2026-11-27

Fetched using the GitHub connector from `VladimirReshetnikov/ProveIt`, ref `main`. Paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. These are the exact blob SHAs returned for inspected files, not a claim of having checked the full repository or a pinned ProveIt tree commit.

| File | Git blob SHA | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Vendoring provenance, separate toolchain |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | Reported build, axioms and independent replays |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Actual definitions of the exported propositions |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Actual wrapper theorems |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | Functional equation reduction |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | One-sided prime-remainder estimate and `New.grh` (selected excerpts inspected) |
| `vendor/grh-lean/grh/Challenge.lean` | `4230ff8fe8b0265a44db348c22cd5f03a7c3f3fe` | Comparator challenge, deliberately contains `sorry`; not the proof file |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | Audit commands |
| `Article/README.md` | `334d9c48c2bf44f1b9083f133f6c46cc4b96b208` | Scope and status of merged article |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | Article assembly |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | Scope and status of results |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | Input and proof architecture (selected sections) |
| `Article/sections/dir.tex` | `5b090c0707c0e6a61642053d4ed9043b6b0e1124` | Small-bias lemma, quotient, growing disjoint products, open question |

The upstream commit pinned by vendor README is `72fead102f663d5c7a407964a13dc0cf9d977207` (25 Nov 2026). The inner package declares Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` in its README. We did not independently build or replay the upstream proof. We did not inspect every file or verify the full merged article. No GitHub writes were performed.

## Article connection

The relevant source is [`Article/sections/dir.tex`](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Analysis/GeneralizedRiemannHypothesis/Article/sections/dir.tex), especially `dir:lem:bias`, `dir:thm:quotient`, `dir:lem:partition`, `dir:lem:repair`, `dir:thm:disjoint-growing`, `dir:thm:disjoint-support`, and `dir:sec:open` (Density one quarter). The new note answers the support portion of that open question and gives a sparse-exception approximation; the complete growing-dimensional mixing question remains open here. The analytic lifting is rederived, not claimed novel.

## Literature scope

Focused web searches on small-prime products, GRH character-sum bounds, and zero-sum-free sequences supplied background references listed in the paper. No exhaustive novelty or priority search was performed.
