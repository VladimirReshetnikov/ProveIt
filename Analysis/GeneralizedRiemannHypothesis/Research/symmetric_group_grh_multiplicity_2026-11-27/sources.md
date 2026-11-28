# Source and dependency audit

Inspected via the GitHub connector, main branch, 27 November 2026.

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

Relevant returned blobs:

| File (relative to GRH directory) | Blob SHA | Role |
|---|---|---|
| README.md | 9aa123f3c17f3e8056d64d3c2bc7823e583fa82d | Corpus provenance; 209 reports |
| Article/README.md | b986fb54c6e641e9241439476bb5579e234fecd6 | Scope and status of 982-page merge |
| Article/sections/intro.tex | d68752790cb7989a9ea58d35afefb7cdfe56b279 | Transfer mechanisms and status conventions |
| Article/sections/src.tex | b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8 | Source theorem and prime-ramp mechanism |
| Article/sections/nab.tex | 7390a4bceb51e7ba358f3062398da5891c25db71 | Exact prior n<=12 result, uniform bound, open question nab:q:un |
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Separate unbuilt vendored package |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Dirichlet GRH statement |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Exported theorem names |
| vendor/grh-lean/grh/README.md | 68cd862687bac1dadf3f14dc7266365e5c8b1ec4 | Reported checks and build requirements |

The upstream development is pinned to commit
`72fead102f663d5c7a407964a13dc0cf9d977207` of lsernau/grh-lean.
The prior finite certificate was located in historical commit `10802a6b36`,
`Research/grh_method_transfers_2026-11-26/checks/reflection/certificates.json`
(blob `f3f323e19e9a7ecd4bae3e414fb1d6fe3774ffb2`); its structure and degree
range were inspected, but the prior certificates were not independently rerun.

## External literature

- S. Gun, S. Hazra and D. Sahu, *On holomorphy and non-vanishing of Artin
  L-functions*, Monatshefte fuer Mathematik 206 (2025), 853–883.
  https://doi.org/10.1007/s00605-025-02060-7 (Heilbronn-character context).
- P. Erdős, A. Ivić and C. Pomerance, *On sums involving reciprocals of the
  largest prime factor of an integer*, Glasnik Matematički 21(41) (1986),
  283–300, Theorem 1 and equation (1.1).
  https://www.renyi.hu/~p_erdos/1986-10.pdf (verified statement and scanned
  pages 283–284; supplies the optional sharper asymptotic).

The comparison and exact identities are new relative to the specific
repository question as inspected. A focused literature search is not a
comprehensive novelty or priority certification. No claimed upstream proof
has been independently kernel-replayed in this task.
