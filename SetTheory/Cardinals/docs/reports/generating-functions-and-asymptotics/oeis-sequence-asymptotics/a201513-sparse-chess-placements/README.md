# Sparse nonattacking chess placements

A complete exact-arithmetic derivation of every fixed asymptotic order for n nonattacking kings or knights on an n by n board, with compact positive k/n extensions and growth-index inverses.

Main sequences: A201513 (kings) and A201540 (knights). Neighboring examples: A201511 (wazirs/grid graph), A201861 (ferses/diagonal-neighbor graph).

## Read first

`Sparse_Chess_Asymptotics.pdf` is the polished nine-page report, with editable source `Sparse_Chess_Asymptotics.tex`. `PROOF.md` provides the same core mathematics in searchable text. These contain the definitions, complete proofs, all hypotheses, explicit coefficients, source attribution, and the integer-threshold rounding qualification. The classical leading equivalent and the general cluster-expansion method are credited to prior literature. The contribution is the specialized higher-order arithmetic, explicit extraction method and controlled error for these moving-piece diagonals; no exhaustive-priority claim is made.

## Integrity

Run `sha256sum -c SHA256SUMS` before replay. The manifest covers all 19 other release files. Replays regenerate deterministic data; run the integrity check again afterward to confirm byte equality.

## Replay

Python 3.11 or later; the symbolic step uses SymPy 1.14.0. The combinatorial and finite-check programs use only the standard library.

1. `python compute_clusters.py --order 6`
2. `python derive_expansion.py`
3. `python verify_finite.py > finite_verification.txt`

Alternatively run `./replay.sh` to regenerate the connected-support producer data and run the independent symbolic check. This ordinary replay reuses the frozen `independent_verification/row_dp_counts.txt`; it does not rerun the row-mask C++ enumeration. Full row-DP regeneration is a separate check described in `independent_verification/README.md`. To rebuild the PDF, run `./build.sh` with a TeX Live installation. The build helper also handles the stripped-down TeX configuration of the preparation environment without changing global system files.

Run these commands in this folder. The first two commands regenerate the two JSON files deterministically. They enumerate exact connected supports and perform rational algebra. No OEIS coefficients, regression, nonlinear fitting, floating-point extrapolation, or external service is used by the derivation.

`compute_clusters.py --order J` computes the data required for all asymptotic corrections through order J-2; time and memory grow with J. No practical claim is made about arbitrarily high J.

## Contents

- `Sparse_Chess_Asymptotics.pdf` and `.tex`: polished report and editable source
- `build.sh`: portable PDF build helper
- `replay.sh`: producer replay and independent checks against frozen row-DP data
- `independent_verification/`: independent row-mask and Touchard-moment checks
- `PROOF.md`: complete theorem and proof
- `compute_clusters.py`: finite connected-support enumeration
- `derive_expansion.py`: exact falling-factorial operator and coefficient generator
- `verify_finite.py`: independent direct finite-board enumeration
- `cluster_coefficients.json`: exact quadratic cluster polynomials through order 6
- `asymptotic_coefficients.json`: exact relative corrections through order 4
- `finite_verification.txt`: 12 direct finite-board checks through cluster order 6
- `SOURCES.md`: primary sources and exact scope of the literature comparison

No external submission or repository change is part of this package.
