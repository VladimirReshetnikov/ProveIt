# Verification scope

The mathematical article received an independent integrated review of its exact chamber/orbit proof, smooth-point hypotheses, residue normalization and contour change, finite generator, first and second corrections, rational dependence on dimension, D-finite consequence, and specified-model inverse/threshold qualifications. This is ordinary mathematical review, not a proof-assistant certificate or a novelty certification.

The executable checks cover:

- 45 direct rook versus weighted-unit-word cases: k=1 through5, n=0 through8
- 15 direct rook versus unsymmetric coefficient cases: k=2 through4, n=0 through4
- 22 direct rook versus symmetric coefficient cases: k=2, n=0 through6; k=3, n=0 through5; k=4, n=0 through4; k=5, n=0 through3
- Symbolic all-k first and second corrections, with distinct Wick pairing and Gaussian integration-by-parts calculations
- Root equation substitution through t^6 and amplitude verification through t^4
- Independent k=2 algebraic generating-function and k=3 eliminated-chart checks through the second correction
- Arbitrary-order generator replay for k=2, k=3 and symbolic k through order2
- Formal inverse cancellation through degree4
- Twelve larger, recurrence-free exact counts through n=100 for k2, n=80 for k3, n=30 for k4, and n=15 for k5
- PDF rebuild, extracted-text checks, and visual inspection of every rendered page

The package is also safely extracted into a fresh directory, its manifest checked, and `bash replay.sh` run there. The deterministic build settings permit a byte-identical PDF rebuild in the verification environment. Other TeX distributions may produce different bytes despite equivalent content; exact-data checks can still be run separately from PDF comparison.

Numerical agreement is supplementary. The article's theorem provides fixed-dimension, fixed-order big-O statements, not effective finite-n error constants. A finite correction polynomial may give poor or even negative approximations at moderate n. The integer threshold cannot be uniquely rounded from an asymptotic approximation when its uncertainty interval meets an integer.
