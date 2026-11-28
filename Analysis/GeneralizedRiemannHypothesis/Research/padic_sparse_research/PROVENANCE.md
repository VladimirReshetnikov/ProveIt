# Repository provenance and research scope

Source: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

Inspected using the GitHub connector on 2026-11-27. Blob SHA identifiers below identify the inspected versions, rather than claiming that the moving `main` branch is immutable.

| Relative path | Blob SHA |
|---|---|
| README.md | 9aa123f3c17f3e8056d64d3c2bc7823e583fa82d |
| Article/README.md | b986fb54c6e641e9241439476bb5579e234fecd6 |
| Lean/README.md | 67865c311b9464acc067616879fa238782d42a1c |
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa |
| Article/sections/src.tex | b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8 |
| Article/sections/smd.tex | 790993c6656d292056ac5eadc893061fa7a19002 |
| Article/sections/nab.tex | 7390a4bceb51e7ba358f3062398da5891c25db71 |
| Article/sections/grp.tex | 13b04893c551c0af59a006caeecb50722fa994ae |

Other article sections inspected selectively for headings and/or open problems included gpi, gpp, fil, rec, zer, dir, spn, and hec. This was a targeted review, not an exhaustive validation of the 982-page article or an independent check of the upstream Lean proof.

The direct mathematical anchors are `smd:thm:rankrule`, `smd:thm:fixedsupport`, `smd:thm:opendisk`, `smd:thm:jump`, and the open question `smd:q:roots`. The article's existing method uses integral recurrences for moments, residue algebras and Newton polygons. The new proof introduces precision determined by the maximum base-p digit sum of the initial moments, followed by exact determinant-lattice optimization and a two-residue extremal construction. The paper generalizes further to confluent exponential-polynomial spaces.

An alternative route examined the questions `nab:q:un` and `grp:q:vn` about positive monomial decompositions for symmetric groups in arbitrary degree. The attempted uniform argument was not completed; no claimed result depends on it. No new named global conjecture is claimed resolved. Related literature is cited in the manuscript; the targeted search was not a proof of worldwide novelty.

The repository's upstream RH/Dirichlet-GRH proof is pinned to commit 72fead102f663d5c7a407964a13dc0cf9d977207 in lsernau/grh-lean. It is not needed for the new results. No repository files were modified.
