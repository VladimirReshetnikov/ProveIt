# Sources and contribution boundary

## Immediate research source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `d18416ec7e187a0948248cb3077e37d7b089a8f9`.

Source:
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions/article.tex`

Pinned link:
https://github.com/VladimirReshetnikov/ProveIt/blob/d18416ec7e187a0948248cb3077e37d7b089a8f9/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a261781-matrix-compositions/article.tex

The source is the merged October 3, 2026 report, *Matrix Compositions:
Exact Spectra, Hankel Products, and Uniform Asymptotics*.

The existing maximal determinant theorem has label `mxc:thm:hankel`.
Its factorization has label `mxc:eq:weighted-hankel-product`.
The question answered here is titled **The limiting distribution of
determinant zeros**. It asks for the limit after removing 0 and -1,
tail estimates, contributions of small-order roots, and an explicit
normalization convention.

## Published and OEIS foundations

- Emanuele Munarini, Maddalena Poneti, Simone Rinaldi,
  *Matrix Compositions*, Journal of Integer Sequences 12 (2009), Article 09.4.8.
  https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.pdf
- László Tóth, *A Survey of Gcd-Sum Functions*, Journal of Integer Sequences
  13 (2010), Article 10.8.1.
  https://cs.uwaterloo.ca/journals/JIS/VOL13/Toth/toth10.pdf
- OEIS A261781: https://oeis.org/A261781
- OEIS A261784: https://oeis.org/A261784
- OEIS A001615 (Dedekind psi): https://oeis.org/A001615

Sources were inspected on October 4–5, 2026.

## Attribution

The enumeration and recurrence existence are published background.
The exact maximal Hankel product is prior repository mathematics and is
rederived in the article for self-containment.

The contribution is the zero theory developed from that product:
the Cauchy limit and exact discrepancy constant; Dedekind-psi multiplicities;
smooth, rational, and moving-endpoint corrections; the arithmetic edge law;
edge-to-bulk matching; the moment transition with critical constant;
and shift-dependent full normalization.

These statements were derived and cross-checked by independent mathematical
reviews in this session. Integration review corrected the range of a primitive
angle, the absolute-value convention for Kolmogorov distance, the nearest-integer
notation, and the domain of the primitive triangle count.

The work is unrefereed. No exhaustive literature-priority claim, Lean/Rocq
formalization, or OEIS submission is asserted.

The numerical package was written for this article. It computes rows directly
from the counting recurrence before verifying the determinant product.
It does not copy or redistribute a third-party article or an OEIS term table.
