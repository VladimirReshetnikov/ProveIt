# Sources and attribution

The finite Fourier model, real-phase Perron simplicity, atomic spectrum and Taylor cancellation are prior results in the ProveIt manuscript:
https://github.com/VladimirReshetnikov/ProveIt/blob/63a7a325109ba611a1816b61dfd0eb072b896a7a/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/thue-morse/Thue_Morse_Integer_Pressure/article.tex

Commit: 63a7a325109ba611a1816b61dfd0eb072b896a7a
Git blob: 1444c01b4b30020f727172f0ee0060cab644f444
SHA256: 3f0e157c4d79664a65c06eee76f7619e8777ac5c70e4849f482cda6963283fa8
Inspected: 1 October 2026

The relevant Perron proof is reproduced and credited in the report, including the one-zero backward-tree argument and exceptional atomic phase. The inspected source does not state the infinite-sign conclusion.

Classical analytic input:
Philippe Flajolet and Robert Sedgewick, Analytic Combinatorics lecture-note draft, Chapter IV, Theorem IV.3(ii), printed page 15:
https://algo.inria.fr/flajolet/Teach/fascII.pdf

Primary pressure context:
Philipp Gohlke, Marc Kesseböhmer and Tanja I. Schindler, Generalized Thue–Morse measures: spectral and fractal analysis, arXiv:2509.22109v1:
https://arxiv.org/abs/2509.22109
Theorem 2.7 proves order-two real-phase analyticity.

Prior companion:
The Full Pressure Positivity Range at Every Integer Order,1 October 2026, delivered as report 63. It supplies the separate lower bound N_m>=6m. The infinite-sign theorem itself does not depend on that positive-window theorem.

The exact table producer extends the previously audited rational Fourier recurrence by retaining the full formal logarithm, rather than truncating at two feedback orders. Independent characteristic-polynomial calculations verify all 105 coefficients for m=2–6.

The claimed contribution is a source-relative application of classical complex-analytic mechanisms. A targeted search found no earlier statement of the all-integer sign conclusion; this is not an exhaustive priority claim. No external papers are redistributed.

