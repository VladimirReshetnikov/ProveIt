# Source map

## Lean repository

Pinned revision of lsernau/grh-lean: `72fead102f663d5c7a407964a13dc0cf9d977207`. The release describes the readable and compact editions as rewritings of the Alpöge–Claude argument. The analysis used the readable edition. The authors report Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and three standard axioms. This project inspected source and did not rebuild the upstream project or run a Lean kernel on the present papers.

| Source | Use |
| --- | --- |
| [Statements and domains](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean) and [Main](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean) | The five public declarations cover the zeta function and Dirichlet characters. |
| [Data/Existence, lines 80 onward](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Data/Existence.lean#L80) | A sphere of digit vectors avoids weighted three-term congruences. It supplies the combinatorial idea for the polynomial-ring counterexample. |
| [Main inequality](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean#L87) and [one-sided bound](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean#L200) | Lattice index and determinant bounds control the smoothed quadratic-twist prime sum. |
| [Poles of the prime remainder](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/PrimeError.lean#L414) | The numerator of a residue is a signed sum of zero multiplicities. |
| [Zero criterion](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean#L37) and [Landau's theorem](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Landau.lean#L217) | Choice of a twist and the signs of real residues convert a one-sided upper bound to a zero-free half-plane. The same last step motivates the Gaussian angular test. |
| [Reading guide](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md) | Glossary, theorem names, scales and diagram of the proof. |

## Earlier ProveIt reports

The directory [docs/incoming at d31039a4](https://github.com/VladimirReshetnikov/ProveIt/tree/d31039a48d963692e5a5176f47b6603fc9e9d9cf/docs/incoming) contained 35 ZIP archives. The included TSV identifies their Git blobs and the number of directly enclosed TeX files. The search for references to Asada or Fourakis looked in those TeX members. The directly relevant report on progression densities addresses Questions 6.1, 6.2 and the existence clause of 6.4. It explicitly leaves Conjecture 6.3 open. Its two-prime upper bound applies alongside the new strict lower bound. The earlier torsion-and-zero-data report uses the signed residues to infer conductor information. Our supplementary paper studies their signs within height intervals. References to primary publications and comparisons with existing theorems appear in the corresponding sections of the papers.
