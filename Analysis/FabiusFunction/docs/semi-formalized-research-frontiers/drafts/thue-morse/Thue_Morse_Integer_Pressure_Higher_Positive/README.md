# Higher Positive Coefficients in Integer Thue Morse Pressure

This separate companion proves that the coefficient of degree 2m+4 is
strictly positive at every integer moment order m>=2. It also proves a
uniform positive region: the coefficient of degree 2m+2r is positive when
m>=3r. An exact negative degree-12 coefficient at m=2 rules out positivity
at every later even degree.

The first-coefficient report is not changed by this package. Its established
quadratic-response positivity is an explicitly cited mathematical input.

## Contents

- `article.pdf`: seven-page mathematical report (six pages as delivered; see the editorial amendments below)
- `article.tex`: editable source
- `code/run_all.py`: complete exact verification entry point
- `code/check_fourth_response.py`: rational normalized eigenfunction jets
- `code/explore_higher_pressure.py`: separate rational pressure recursion
- `code/check_m2_cubic.py`: standard-library cubic certificate for the negative coefficient
- `data/`: exact values and verification summaries
- `PROOF_STATUS.md`: scope and proof boundary
- `requirements.txt`: Python dependency
- `SHA256SUMS.txt`: file-integrity manifest (retired on filing; not in the repository)

## Verify and build

Run `python3 code/run_all.py` with Python 3 and SymPy installed. All polynomial
and matrix calculations are exact; no floating-point sign decision is used.
The full check takes only a few seconds on the production environment.

A normal TeX installation can build with two runs of `pdflatex article.tex`.
`build_local.sh` reproduces the restricted-environment build used here.

The proofs are ordinary mathematics, independently reviewed and supported by
exact certificates. They are not formally verified in Lean or externally
refereed. The region m>=3r is sufficient and is not claimed optimal.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the second of thirteen packages of one series, filed beside the
manuscript they continue, `../Thue_Morse_Integer_Pressure/`, in logical order:
the positivity series `../Thue_Morse_Integer_Pressure_First_Positive/`,
`../Thue_Morse_Integer_Pressure_Higher_Positive/`,
`../Thue_Morse_Integer_Pressure_Positive_Triangle/`,
`../Thue_Morse_Integer_Pressure_Feedback_Boundary/`,
`../Thue_Morse_Integer_Pressure_Beyond_Boundary/`,
`../Thue_Morse_Integer_Pressure_Linear_Region/`,
`../Thue_Morse_Integer_Pressure_Full_Range/`, and the sign series, which
imports the full-range theorem,
`../Thue_Morse_Integer_Pressure_Sign_Changes/`,
`../Thue_Morse_Integer_Pressure_Sign_Densities/`,
`../Thue_Morse_Integer_Pressure_Negative_Bound/`,
`../Thue_Morse_Integer_Pressure_First_Negative/`,
`../Thue_Morse_Integer_Pressure_Cluster_Asymptotics/`, with the dataset
`../Thue_Morse_Integer_Pressure_First_Negative_Data/`. An earlier version of
`../Thue_Morse_Integer_Pressure_Full_Range/`, *The Full Pressure Positivity
Range for Large Integer Orders* (`m >= 4096`), was superseded by it and not
filed; neither was a duplicate archive.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note (ProveIt,
  2026-10-01)") is defined after the theorem environments (no counter
  changes). Three notes:
  - after Theorem 1.1 and the negative `E_{2,4}`: every positivity statement
    is contained in later packages
    (`../Thue_Morse_Integer_Pressure_Positive_Triangle/` for `r < m`, which
    includes `m >= 3r`; the case `m = r = 2`, `D_2 = 536/27`,
    `E_{2,2} = 6836/189`, in
    `../Thue_Morse_Integer_Pressure_Feedback_Boundary/`; all pressure
    coefficients `1 <= r < 2m` in
    `../Thue_Morse_Integer_Pressure_Full_Range/`); the two-nearest-branch
    argument is a second route;
  - after the last paragraph of Section 7: its open questions other than the
    uniform radius are answered (pressure positive up to degree `6m - 2`,
    `E_{2,4} < 0`; responses positive for `r <= m`, `H_{2,3} = -488/27`; the
    first negative degree in the sign series);
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited (`[2]` is
    `../Thue_Morse_Integer_Pressure_First_Positive/`).
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 7 A4 pages (6 as delivered),
  320,626 bytes; all 17 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `code/run_all.py`, `code/check_fourth_response.py`,
  `code/check_m2_cubic.py`, `code/explore_higher_pressure.py`: new option
  `--output-dir` (default `data/rerun/`, which also receives the summary
  `verification.json`; `run_all.py` now reads the two results it checks from
  there), with LF line endings. As delivered, every checker overwrote its
  recorded file in `data/`, with CRLF line endings on Windows. Pass
  `--output-dir data`, on a copy, to regenerate the recorded files. A checker
  that reads another checker's record reads the recorded file, as delivered.
  On the ProveIt machine use `py` rather than `python3`/`python`. A rerun on a
  copy (2026-10-01, Python 3.14.4, SymPy 1.14.0) passed (in 5 s, not "a few
  seconds" on every machine) and wrote all four records equal to the recorded
  ones byte for byte.
- `Makefile`: kept as delivered; it calls `python3` (use `py` on the ProveIt
  machine), and its `pdf` target runs `pdflatex` here and overwrites the filed
  PDF.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `data/visual_qa.json`: `pages` set to 7; its other entries are as delivered.
- `README.md`: the page count and the retired ledger under "Contents", and
  this section.
