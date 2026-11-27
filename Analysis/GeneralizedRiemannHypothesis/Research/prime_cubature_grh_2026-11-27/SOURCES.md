# Source inspection, 2026-11-27

The GitHub connector returned both requested directory listings and these files. The branch was read live; this is a record of returned file blob hashes, not a claim of a complete immutable checkout or independent byte comparison. The branch API returned `adc82b6b50abae288ff08ae8c63e2c4aa43ac8af` during the inspection. The source file listings and some later file reads returned different blob hashes; the hashes below are from actual file-content reads rather than the tree listing.

Base: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

| File | Blob SHA from file read | Role |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Upstream import metadata |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Statements, axioms and checks reported by upstream |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact theorem types |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Main theorem declarations |
| vendor/grh-lean/grh/scripts/PrintAxioms.lean | ec5adcfd7baeff36130db9a763720ba1a6567c57 | Axiom audit commands |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | Scope and status of merged article |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | Structure |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c | Overview |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Theorem headings and architecture |
| Article/sections/dir.tex | 5b090c0707c0e6a61642053d4ed9043b6b0e1124 | Relevant theorem headings and proofs: smoothed prime sum, prescribed majority signs, squarefree product mixing |
| Article/sections/spn.tex | e5f321f49431156eeaad10ee72b2f7db4cfbbcde | Heading scan |
| Article/sections/zer.tex | f6ee5613745e2abda444fde15cf3e826979e5141 | Heading scan |

The upstream README pins the readable edition to `72fead102f663d5c7a407964a13dc0cf9d977207` (25 Nov 2026) and records Lean v4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. We did not run its build or kernel checker. Independent verification reports:

- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ (reports completed independent checks of original and compact edition)
- https://leanprover-community.github.io/blog/posts/riemann-hypothesis/ (Lean FRO and Mathlib Initiative, RH verification)

External related work consulted through a targeted literature search: see the references in paper.tex. This is not an exhaustive novelty audit or a review of every result of the merged article. All new theorems have human-readable proofs; only finite certificates were machine checked here. No Lean toolchain was available locally.
