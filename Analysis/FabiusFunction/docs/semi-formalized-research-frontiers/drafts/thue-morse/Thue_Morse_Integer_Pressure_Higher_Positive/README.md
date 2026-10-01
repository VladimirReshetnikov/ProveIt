# Higher Positive Coefficients in Integer Thue Morse Pressure

This separate companion proves that the coefficient of degree 2m+4 is
strictly positive at every integer moment order m>=2. It also proves a
uniform positive region: the coefficient of degree 2m+2r is positive when
m>=3r. An exact negative degree-12 coefficient at m=2 rules out positivity
at every later even degree.

The first-coefficient report is not changed by this package. Its established
quadratic-response positivity is an explicitly cited mathematical input.

## Contents

- `article.pdf`: six-page mathematical report
- `article.tex`: editable source
- `code/run_all.py`: complete exact verification entry point
- `code/check_fourth_response.py`: rational normalized eigenfunction jets
- `code/explore_higher_pressure.py`: separate rational pressure recursion
- `code/check_m2_cubic.py`: standard-library cubic certificate for the negative coefficient
- `data/`: exact values and verification summaries
- `PROOF_STATUS.md`: scope and proof boundary
- `requirements.txt`: Python dependency
- `SHA256SUMS.txt`: file-integrity manifest

## Verify and build

Run `python3 code/run_all.py` with Python 3 and SymPy installed. All polynomial
and matrix calculations are exact; no floating-point sign decision is used.
The full check takes only a few seconds on the production environment.

A normal TeX installation can build with two runs of `pdflatex article.tex`.
`build_local.sh` reproduces the restricted-environment build used here.

The proofs are ordinary mathematics, independently reviewed and supported by
exact certificates. They are not formally verified in Lean or externally
refereed. The region m>=3r is sufficient and is not claimed optimal.
