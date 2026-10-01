# The Full Positive Triangle in Integer Thue Morse Pressure

For every integer m>=2 and 1<=r<m, this note proves both
H_(m,r)=[a^(2r)]h_a(1/2)>0 and
E_(m,r)=[t^(2m+2r)]p_m(t/pi)>0.

Thus every even pressure coefficient strictly between degrees 2m and 4m is
positive. A new dyadic tangent-product comparison closes the full triangular
range left by the earlier sufficient region m>=3r. This is a separate report;
previously delivered papers are unchanged.

## Contents

- `article.pdf`: eight-page standalone mathematical report (seven pages as delivered; see the editorial amendments below)
- `article.tex`: editable LaTeX source
- `code/run_all.py`: complete exact verification entry point
- `code/check_triangle.py`: 91 rational response/pressure pairs, plus 28 independent direct pressure checks
- `code/check_basis_signs.py`: 36 exploratory exact eigenbasis-sign checks, explicitly separate from the proof
- `code/check_m2_cubic.py`: exact certificate for the negative later degree-twelve coefficient
- `data/`: exact reference values and verification results
- `PROOF_STATUS.md`: proved scope and remaining questions
- `SOURCES.md`: versioned source provenance
- `VISUAL_QA.md`: rendered-page verification record
- `SHA256SUMS.txt`: file-integrity manifest (retired on filing; not in the repository)

## Verification

Run `python3 code/run_all.py` with Python 3 and SymPy installed. All coefficient
and matrix calculations use exact rational arithmetic. The universal proof
uses no numerical sign test; the finite values are regression checks.

Build with two runs of `pdflatex article.tex` on a normal TeX installation,
or use `build_local.sh` for the restricted environment used for this package.
The latter builds the format locally rather than modifying a system TeX tree.

This is ordinary mathematical research, independently reviewed but unrefereed
and not formally verified in Lean. Positivity of individual eigenbasis
coefficients remains conjectural. Positivity of all subsequent pressure
coefficients is false, as shown by the included m=2 degree-twelve certificate.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the third of thirteen packages of one series, filed beside the
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
  - after Theorem 1.1 and its paragraph: it contains Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_First_Positive/` (`r = 1`; that note's
    pointwise positivity off the integers stays its own) and of
    `../Thue_Morse_Integer_Pressure_Higher_Positive/` except `m = r = 2`
    (covered by `../Thue_Morse_Integer_Pressure_Feedback_Boundary/`); its
    pressure statement is contained in Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_Full_Range/`, which cites it for `r < m`;
    the responses and the lower bounds stay its own;
  - after "Determining the general first negative degree ... remains open in
    this note": determined asymptotically by the sign series (`N_m >= 6m`,
    equal for `m = 2, 3, 4`; `N_m = gamma m - log log(2m)/Lambda + O(1)`;
    certified for `m <= 128`); the eigenbasis-coefficient conjecture is not
    treated;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited (`[2]`
    `../Thue_Morse_Integer_Pressure_First_Positive/`, `[3]`
    `../Thue_Morse_Integer_Pressure_Higher_Positive/`).
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 8 A4 pages (7 as delivered),
  385,129 bytes; all 22 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- `code/run_all.py`, `code/check_triangle.py`, `code/check_m2_cubic.py`: new
  option `--output-dir` (default `data/rerun/`), with LF line endings. As
  delivered, every checker overwrote its recorded file in `data/`, with CRLF
  line endings on Windows. Pass `--output-dir data`, on a copy, to regenerate
  the recorded files. A checker that reads another checker's record reads the
  recorded file, as delivered. On the ProveIt machine use `py` rather than
  `python3`/`python`. A rerun of `run_all.py` on a copy (2026-10-01, Python
  3.14.4, SymPy 1.14.0) passed, wrote both records equal to the recorded ones
  byte for byte, and printed exactly `data/verification.log`.
- `Makefile`: kept as delivered; it calls `python3` (use `py` on the ProveIt
  machine), and its `pdf` target runs `pdflatex` here and overwrites the filed
  PDF.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count and the retired ledger under "Contents", and
  this section.
