# Source inspection record

Fetched directly via the GitHub connector from `VladimirReshetnikov/ProveIt`,
ref `main`, 2026-11-27. Root path for all entries below is
`Analysis/GeneralizedRiemannHypothesis/`. The two directory listings and
relevant file sources were inspected. Long article sections were inspected
by theorem-heading and keyword extraction, with targeted full passages
read; this was not a complete audit of all 723 article pages or 818 vendored
files. No repository writes were performed.

| Relative file | Git blob SHA | Role |
|---|---|---|
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Upstream pin and build separation |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Theorems, checks, toolchain |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Exact input propositions |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Exported proofs |
| vendor/grh-lean/grh/src/New/Reduction/MainInequality.lean | 97f83ab52b2feb420e952a2722b4cef454b9e579 | Covolume comparison |
| vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean | 99e5240de112527b739068b692e5007720d310c1 | One-sided prime estimate |
| vendor/grh-lean/grh/src/New/Reduction/Zeros/Criterion.lean | 5c06362a50e044d491423fb3d830bae6a50c0075 | Quadratic twist and Landau |
| Article/README.md | 7f3286088c94a8df3d8b9846112ea83dbbbbfa25 | Scope, status, section inventory |
| Article/article.tex | 2d95d3db42756d4dcea77ecd304c92ded01ad7c6 | Structure |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Input theorem and architecture |
| Article/sections/dir.tex | da58d506e24a05e1b888da2802398f277d9ea727 | Prime bias, especially lines 2758–2888 |
| Article/sections/rec.tex | da56d6ad5a1a699e335dcfd327bcdc9492c64017 | Reconstruction theorem inventory |
| Article/sections/zer.tex | 1f1e31367ea4fdd259786e3997d46ecd279d5cbc | Targeted keyword scan |
| Article/sections/spn.tex | 886e8716472aa82fd45ff68da03be946e9dbd3da | Targeted keyword scan |
| Article/sections/intro.tex | b68b38b12772e23ffae3a25a1d449881435a4e5c | Targeted keyword scan |

The vendored README reports byte identity of the readable edition with
upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
Independent check reports consulted:
- https://math.mit.edu/~drew/shortgrh/
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/

The upstream verification is not replicated here. The new paper's assumption
is precisely Dirichlet GRH, with classical standard explicit-formula and
zero-counting facts. The unconditional finite-group theory does not require
it. The source article has a related small-bias lemma (dir:lem:bias), but
its use is squarefree products; the new paper treats sparse character sums
and arbitrary adversarial sample errors. Literature search found general
coherence-based corrupted-signal recovery (Studer et al., arXiv:1102.1621),
so the general area is not new; novelty of the exact arithmetic combination
is not guaranteed by a targeted search.
