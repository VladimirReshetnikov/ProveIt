# Source audit and scope

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

Read using the GitHub connector, branch `main`, on 2026-11-27. Blob identities below are Git blob SHAs from the retrieved snapshot, not independently computed SHA-256 hashes. These allow later readers to distinguish changing versions of the merged article.

| Path relative to project | Blob SHA |
|---|---|
| README.md | `9aa123f3c17f3e8056d64d3c2bc7823e583fa82d` |
| Article/README.md | `b986fb54c6e641e9241439476bb5579e234fecd6` |
| Article/sections/src.tex | `b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8` |
| Article/sections/gpp.tex | `29c75c077d43ddcea05f9d68fd47e569c33ee69e` |
| vendor/grh-lean/README.md | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` |
| vendor/grh-lean/grh/src/Statements.lean | `1cd1bce93344065936b2b392b23306254e0785ef` |
| vendor/grh-lean/grh/src/Main.lean | `1adf4187a938510363cdb0dde0a6d628ff39c600` |
| Lean/README.md | `67865c311b9464acc067616879fa238782d42a1c` |

The project README describes 209 merged research reports. The Article README describes a 982-page merge with 1,321 labeled results, and explicitly says it is a merge rather than an independent check. The vendored project is pinned to `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207`, with a separate Lean toolchain from ProveIt's root package. Its source statement restricts GRH to Dirichlet L-functions over Q. `Main.lean` delegates the proof to `New.Main`. `Challenge.lean` has sorry placeholders for comparison and is not imported by the claimed proof; it is not itself the proof. We did not rebuild the upstream package, verify all 818 vendored files, check its reported axioms, or independently establish the status of the announcement.

The `src.tex` architecture is: short integral forms with controlled index; enough independent forms; a lower bound on the same corrected Gram determinant; one-sided ramp-prime estimates; separation via auxiliary quadratic twists; a Mellin/Landau argument. The article transfers these mechanisms into various mathematical domains. We inspected the section headings in `ana`, `nab`, `grp`, `hec`, `dir`, `zer`, `rec`, `fil`, `spn`, `gpi`, `gpp`, and `smd`, and the relevant open questions. We did not audit every one of the 1,321 results.

## Chosen open question

`Article/sections/gpp.tex`, label `gpp:q:cube`, asks which invariant controls the density loss for a local ring with cube-zero but nonzero square of its radical, and asks more generally for the growing-product criterion. The preceding theorem `gpp:thm:local` covers square-zero radicals, with a loss scale Q^-2 for even residue characteristic, using elimination, finite disjoint triples, degree-block gluing, and density Hales–Jewett. Those last two arguments are reproduced in the note for completeness, not claimed as new.

New ingredient: retain the even-degree structure of the polynomial square of a radical polynomial rather than dropping the entire square contribution. The high-coefficient parity and two-term alignment conditions give a loss scale |S|/Q², rather than the naive |S|²/Q² obtained by merely reducing modulo S. A socle correction gives exact sufficiency for actual triple starts when m³=0. A low-coefficient marker in the ratio makes the progression packing injective despite varying the ratio with the square-image element. The new scale then feeds the existing product argument. The paired ring families show it is essential to know the multiplication law, not just the dimensions of its radical layers.

The results are unconditional. No new analytic L-function estimate is claimed. The restriction 2m=0 and mS=0 is essential to the proof given, so the general cube-zero mixed-characteristic case with 2m nonzero and the odd-characteristic case remain open here. Exact single-ring extremal densities are not determined. The paper's novelty claim is relative to the inspected article and a targeted literature search; it does not assert that a comprehensive global priority check has been performed. The general proof was checked by hand and the small-ring examples by exhaustive code, not by a Lean kernel.

## Published references

- Asada, Fourakis, Manski, McNew, Miller, Moreland, *Subsets of F_q[x] free of 3-term geometric progressions*, Finite Fields and Their Applications 44 (2017), 135–147. Question 6.5 in arXiv:1512.01932v2. https://doi.org/10.1016/j.ffa.2016.10.002 ; https://arxiv.org/abs/1512.01932
- D. H. J. Polymath, *A new proof of the density Hales–Jewett theorem*, Annals of Mathematics 175 (2012), 1283–1327. https://doi.org/10.4007/annals.2012.175.3.6
