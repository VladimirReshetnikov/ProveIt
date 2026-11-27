# Source audit (27 November 2026)

Repository: `VladimirReshetnikov/ProveIt`, branch `main`, read through GitHub. All paths below are relative to `Analysis/GeneralizedRiemannHypothesis/`. No repository writes were made.

## Pinned source interface

The vendored README identifies the upstream readable edition at commit `72fead102f663d5c7a407964a13dc0cf9d977207`. It reports byte-identical vendoring of 818 files. The vendor package is separate from ProveIt's root build. The vendor pins Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, as stated in its own README.

| File | Git blob SHA | Role |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | upstream pin and import status |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | statement and build/check reports |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | Mathlib-level propositions |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | exports |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | functional-equation reduction |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | terminal proof of `New.grh`; examined concluding lines |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | audit commands, not their locally run outputs |

The input required by this paper is `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` and its critical-line consequence `LFunction_eq_zero_re : DirichletLZerosOnLine`. Classical RH is also exported as `riemannHypothesis`. The source `New.grh` handles the point 1 separately, induces to level `18480*q`, and applies the one-sided prime remainder criterion to exclude a putative right-half-plane zero. The ordinary strip follows using `New.zeros_on_line`. The proof here does not depend on any non-Dirichlet GRH.

No independent rebuild or full review of 300,000 lines of Lean code was performed. The vendor's three-standard-axiom and independent-checker claims are reports, corroborated by publicly available verification reports, not commands executed locally.

## Article

| File | Git blob SHA |
|---|---|
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` |
| `Article/sections/dir.tex` | `da58d506e24a05e1b888da2802398f277d9ea727` |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` |

The requested article is a merge, not an independent proof review, as its README explicitly says. Its section directory tree is `5ea418a24081239fe126bb25757cd4897d31e74a`.

The main reused analytic input is `dir:lem:bias` in `sections/dir.tex` (subsection `dir:sec:products`, around line 2760 onward). It supplies uniform small bias for the complete prime pool both at log-power cutoff and at sufficiently large constant times log-squared cutoff. The paper reproduces its analytic reasoning using the classical GRH explicit formula, rather than using the article's other novel results as black boxes.

Closest results inspected:

- `dir:thm:quotient`: exact support and relative counts after global prime deletion.
- `dir:cor:squarefree`: fixed-cardinality squarefree representation under a retained majority.
- `dir:prop:explicit` and `dir:thm:short`: quantitative fixed-pool character estimates and short products.
- `dir:cor:list`: one common list for many moduli.
- `dir:thm:factorization`, `dir:thm:minority`: simultaneous factorization under global deletions, quotas and congruences.

These are global retained sets and/or factor assignments. The new paper instead requires each directed transition to be independently allowed at its current residue and demands both globally distinct prime labels and disjoint vertices across many ordered pairs. A keyword scan of the 19 substantive section sources (`src, ana, li, nab, grp, hec, zer, rec, dir, cls, smd, gpp, gpi, gra, tors, cost, lub, sel, spn`) for rainbow, local resilience, routing, prime-disjoint, vertex-disjoint, and Cayley found no matching routing result. Matches in `gra`, `li`, `rec`, `nab`, `gpp`, `sel` concern other subjects (Cayley angles, graph tower questions, disjoint triples, Cayley-Hamilton, etc.). This was a targeted comparison, not verification of every one of the article's 914 results.

## External context and literature

- Jao, Miller, Venkatesan (2009): https://arxiv.org/abs/0811.0647 — classical GRH Cayley expansion precedent, not claimed as new here.
- Montgomery and Vaughan, *Multiplicative Number Theory I*, Ch. 13 — sharp and integrated prime character sums, also the references in `dir:lem:bias`.
- Sutherland's verification reports: https://math.mit.edu/~drew/
- Rubinstein's verification reports: https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/
- Clay status page: https://www.claymath.org/millennium/Riemann-Hypothesis/ — lists RH as active at the time of this note; independent kernel acceptance is distinct from prize recognition and human peer review.

Focused searches for GRH small-prime Cayley graphs, rainbow connectivity under local resilience and prime-disjoint routing found the expansion precedent, not the exact combined theorem. This is not a comprehensive priority search. The novelty claim is provisional and relative to the supplied article and inspected literature.
