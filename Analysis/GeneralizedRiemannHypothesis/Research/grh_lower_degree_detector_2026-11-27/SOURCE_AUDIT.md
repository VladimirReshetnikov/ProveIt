# Repository source audit

Inspected through the GitHub connector, 27 November 2026. The references identify the specific blobs returned from `main`; they do not assert an atomic checkout. Only relevant portions of the merged article and vendored proof were inspected, not every report or the complete formal proof.

Base path: <https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis>.

| File (relative to base path) | Git blob SHA | Relevance |
|---|---|---|
| `Article/README.md` | `c9fe005bd5cbdee34dbcfacf1d5127a59ba46d0d` | Describes the 209-report merged article, 982 pages, 1321 result headings; warns that the merge is not independent verification. |
| `Article/sections/src.tex` | `b0ac2147291b7da3a74cdf6072cc557b1e1f5ee8` | Input theorem, covolume amplification, prime-sum/Landau mechanism, Dirichlet GRH scope. |
| `Article/sections/nab.tex` | `7390a4bceb51e7ba358f3062398da5891c25db71` | `nab:q:lowdegree` asks for smaller detecting fields without Artin holomorphy; `nab:cor:sn` gives the degree-n!/2 reflection detector; `nab:thm:snsharp` sharpens its multiplicity constant for n<=12; `nab:prop:dedekind` gives the one-sided prime criterion; `nab:lem:heilbronn` gives local restrictions. |
| `Article/sections/grp.tex` | `13b04893c551c0af59a006caeecb50722fa994ae` | `grp:sec:a5`: positive character detectors, A5 subgroup data. `grp:sec:s5`: separate S5 transposition identity and S8 cyclic-generator test (`grp:ex:s8`). Neither is the shared-spare-letter tower proved here. |
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | Upstream revision `72fead102f663d5c7a407964a13dc0cf9d977207`; separate Lake package not checked by the root build. |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | Exports RH and Dirichlet GRH, not arbitrary Artin or Dedekind GRH. |

## Dependency audit

- A5 identity, A4 refinement and S4 two-detector identity: direct class counts.
- Arbitrary n: tensor with a trivial character of the preceding subgroup and induce in stages. All subgroups are explicit. No numerical interpolation or unstated group classification.
- Analytic quotient: standard multiplicativity and induction of Artin L-functions, abelian reciprocity and holomorphy of nontrivial finite-order Hecke L-functions, simple pole of Dedekind zeta at 1. These are classical theorems, not Artin's general conjecture. See Foote, Ginsberg and Murty, DOI [10.1090/bull/1492](https://doi.org/10.1090/bull/1492).
- Artin exclusion: cyclic-subgroup Heilbronn argument using Brauer meromorphic continuation.
- One-sided test: classical prime ideal theorem, Landau's theorem on nonnegative transforms, integrated explicit formula conditional on RH for the detecting field. See Grenié and Molteni, DOI [10.1090/mcom3039](https://doi.org/10.1090/mcom3039). This is an equivalence, not an established nonabelian estimate.
- Only the optional exact S4 off-line order formula assumes Dirichlet GRH over Q. The S4 detector equivalence and all main compression statements are unconditional.

## Limits

The source question is answered for n>=5 by one field, with degree reduction exponential in n, and for n=4 by two fields. The separate n-1 optimal transposition-bound question is not answered. The result is novel relative to the inspected source sections; no exhaustive literature or all-reports priority check was conducted. Searches on Heilbronn characters, zeta quotients and symmetric-group zero detectors were not an independent review. The vendored Lean proof was not rebuilt. The submitted proof is not Lean-formalized. Exact finite arithmetic was independently checked by the supplied Python code; this does not constitute an independent validation of the analytic input theorem or establish RH for a nonabelian field.

No repository files were edited.
