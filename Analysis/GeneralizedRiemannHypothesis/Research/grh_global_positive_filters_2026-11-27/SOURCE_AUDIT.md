# Source inspection and dependency ledger

Read through the GitHub connector on 27 November 2026. The requested paths were accessible. The vendored README identifies upstream `lsernau/grh-lean` commit `72fead102f663d5c7a407964a13dc0cf9d977207` (25 November 2026). Blob identifiers below are from the `main` branch responses. The article directory contains 723 pages by its own README, merging 131 reports with 914 labeled results. This audit is selective, not a line-by-line verification of all 723 pages or all 818 vendored files.

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis

| Relative path | Git blob SHA | Inspection |
|---|---|---|
| `vendor/grh-lean/README.md` | `a04f66a62af93fc0757f2aa573f3b053fde51bfa` | full; vendor provenance and separate build |
| `vendor/grh-lean/grh/README.md` | `68cd862687bac1dadf3f14dc7266365e5c8b1ec4` | full; five exports and reported checking procedure |
| `vendor/grh-lean/grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | full; exact Mathlib-based types |
| `vendor/grh-lean/grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | full; public theorem proofs via `New.grh` |
| `vendor/grh-lean/grh/src/New/Main.lean` | `fc0ae69627d2e66c3d1d57815d42f0aac5823432` | full; functional-equation reduction to the critical line |
| `vendor/grh-lean/grh/src/New/Reduction/OneSidedBound.lean` | `99e5240de112527b739068b692e5007720d310c1` | lines 1–85; prime remainder estimate and admissible scales |
| `vendor/grh-lean/grh/Challenge.lean` | `4230ff8fe8b0265a44db348c22cd5f03a7c3f3fe` | full; comparator challenge with `sorry`, separate from Main |
| `vendor/grh-lean/grh/scripts/PrintAxioms.lean` | `ec5adcfd7baeff36130db9a763720ba1a6567c57` | full; five axiom print commands |
| `vendor/grh-lean/grh/lean-toolchain` | `a6aff065db2882c535684f8c5bcd4f16e9a23915` | Lean v4.35.0 |
| `Article/README.md` | `7f3286088c94a8df3d8b9846112ea83dbbbbfa25` | full; article size, scope and caveats |
| `Article/article.tex` | `2d95d3db42756d4dcea77ecd304c92ded01ad7c6` | full; article organization |
| `Article/sections/intro.tex` | `b68b38b12772e23ffae3a25a1d449881435a4e5c` | full; classification of results and source methodology |
| `Article/sections/src.tex` | `f69668b2f95261630bb1282c2cc1f9c172b7e530` | lines 1–150; exact theorem and transfer mechanism |
| `Article/sections/rec.tex` | `da56d6ad5a1a699e335dcfd327bcdc9492c64017` | retrieved; selective headings, finite and logarithmic positive filter statements/proofs, open questions, keyword search |
| `Article/sections/zer.tex` | `1f1e31367ea4fdd259786e3997d46ecd279d5cbc` | retrieved; headings, keyword search, lines 2920–3005 (eta-product positivity and cubic race) |
| `Article/sections/ana.tex` | `f05f1cbf50dee52273e72b76f7b0f5aa2f3e51ce` | headings and targeted keyword search |
| `Article/sections/li.tex` | `87871b581808b4388135617b7d38cae1438bece5` | headings and targeted keyword search |

Other sections (`dir`, `spn`, `tors`, `cost`) were sampled via headings and in `dir` selected theorem text to help choose a non-overlapping direction. The analysis used article LaTeX source, not its compiled PDFs.

## Exact interface and dependency boundary

- `Statements.lean`: `DirichletLNonvanishingRightOfHalf` and `DirichletLZerosOnLine` quantify over every nonzero modulus and character, not general automorphic/Artin functions.
- `Main.lean`: the former is exported as `LFunction_ne_zero_of_half_lt_re := New.grh`; the latter as `LFunction_eq_zero_re := New.zeros_on_line New.grh`. The zeta theorem is also explicitly exported. The principal pole is excluded, and zeros at the central point can have arbitrary multiplicity.
- `New/Main.lean`: symmetry and the gamma factor convert one-sided nonvanishing into the critical-line statement.
- `OneSidedBound.lean`: the ramp sum is `sum lambda(n)(1/n-1/x) - log x / phi(q) - c_q`; the one-sided estimate is combined with the analytic criterion. No arithmetic covolume argument is assumed applicable to other L-functions here.
- The README reports the axioms `propext`, `Classical.choice`, and `Quot.sound`, independent checking with nanoda/con-leche/con-ron, and successful Comparator runs. These reports were not independently replayed in this session. The local environment did not have `lean` or `lake` on PATH. No Lean certificate for the new theorem is claimed.

## Relation of the new result to the article

`rec:thm:finitefilter`, `rec:thm:logfilter`, `rec:lem:jensensupport`, `rec:thm:uniformavg`, `rec:thm:polylogavg`: finite-band cancellation, finite support and approximate arithmetic averaging. Our result treats a single positive kernel with exact cancellation at all noncentral ordinates, including their aggregate multiplicity, and proves the optimal exponent of its doubly exponential moment. The positive kernel may have additional zeros. Exact compact support is impossible; its finite-range truncation need only approximate cancellation. The explicit coefficient of the truncation half-width is an upper bound only.

The classical positive xi Fourier kernel is known; targeted literature lookup found Polson's survey (https://ssrn.com/abstract=7277559) and related work on the xi distribution. No exhaustive novelty or priority search is asserted. The main claimed extension is the compact-smoothing lemma and its application to arbitrary finite conjugation-closed families, including possible central zeros. The mathematical proof does not depend on any finite numerical tests or other unverified results from the merged article.
