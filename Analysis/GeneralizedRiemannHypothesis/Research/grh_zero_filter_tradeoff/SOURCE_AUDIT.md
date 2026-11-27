# Source audit (27 November 2026)

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/

Files fetched via the GitHub connector on `main`. IDs below are blob SHAs, not commit SHAs. The retrieved README files had inconsistent report counts: the root README described 131 merged and 11 placed reports, whereas the article README described 142 merged reports. The mathematical comparison uses the retrieved article section content, identified by its blob SHA, not the report count.

| Path relative to the GRH directory | Blob SHA | Scope reviewed |
|---|---|---|
| README.md | ef805e4e61c6f19846907c7a181feb157ba7d480 | Overall structure and provenance |
| Article/README.md | 334d9c48c2bf44f1b9083f133f6c46cc4b96b208 | Section inventory; merge is not independent verification |
| Article/sections/rec.tex | 29cec9b8cbcbf499ffecd52343bfd622ea3974d7 | Reconstruction headings; full separated-filter lemma, finite construction, logarithmic filter, Jensen bound, prime averaging, open questions |
| Article/sections/zer.tex | not recorded | Ramp formula and proof, section headings |
| Article/sections/ana.tex | f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce | Theorem headings |
| Article/sections/dir.tex | 5b090c0707c0e6a61642053d4ed9043b6b0e1124 | Theorem headings |
| Article/sections/src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 | Theorem headings |
| Article/sections/spn.tex | e5f321f49431156eeaad10ee72b2f7db4cfbbcde | Theorem headings |
| vendor/grh-lean/README.md | a04f66a62af93fc0757f2aa573f3b053fde51bfa | Vendor status and upstream pin |
| vendor/grh-lean/grh/src/Statements.lean | 1cd1bce93344065936b2b392b23306254e0785ef | Mathematical statements |
| vendor/grh-lean/grh/src/Main.lean | 1adf4187a938510363cdb0dde0a6d628ff39c600 | Proof entry points |
| Lean/README.md | 7f778b86e08847a29ce845c49c83a653e7ce3a35 | Formalization scope |

Upstream commit as documented by the vendor: `72fead102f663d5c7a407964a13dc0cf9d977207`.

The crucial comparison is to `rec:lem:sepfilter`, `rec:thm:finitefilter`, `rec:thm:logfilter`, `rec:lem:jensensupport`, `rec:thm:uniformavg`, `rec:thm:polylogavg`, and the open question about the optimal logarithmic support constant. The construction here changes the taper, chooses a separation scale growing with height, handles the initial low zeros separately, and replaces the sinc-power tail with a positive continuous Chebyshev-type kernel. The lower bound uses disk Jensen after a slit-plane conformal map and adds the harmonic-measure average of attenuation to the zero cost. The article's lower bound uses circular Jensen without a tail term.

External references checked: Bennett–Martin–O'Bryant–Rechnitzer, *Counting zeros of Dirichlet L-functions*, https://doi.org/10.1090/mcom/3599; P. Lynch, *The Dolph–Chebyshev Window: A Simple Optimal Filter*, https://journals.ametsoc.org/view/journals/mwre/125/4/1520-0493_1997_125_0655_tdcwas_2.0.co_2.xml. Standard analytic tools are identified in the paper. No exhaustive priority search, full repository audit, or Lean build was performed. The result is a candidate new extension relative to the inspected article. The filter theorems are unconditional and the prime-race application assumes Dirichlet GRH. The exact optimum with prescribed zeros remains open.
