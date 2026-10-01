# Infinite Taylor Sign Changes in Integer Thue–Morse Pressure

The PDF proves that, for every integer m >= 2, both even degree classes modulo four contain infinitely many positive and infinitely many negative Taylor coefficients. The positive and negative coefficient subsequences have the same exponential scale, with the separate filtered radii distinguished. The proof is analytic and does not depend on a finite scan.

The finite table gives the exact first negative degree after cancellation for m=2,...,20. It does not establish a large-m scaling law.

## Contents
- infinite_pressure_sign_changes.pdf and .tex: complete seven-page report
- build.sh: ordinary pdflatex build (three passes)
- checks/first_negative_exact.cpp: exact GMP Fourier recurrence, full logarithm, all-order residual checks
- checks/m002.json,...,m020.json: exact eigenvalue and pressure coefficients through degree 10m
- checks/verify_table.py: independent rational pressure conversion and complete first-negative scan
- checks/verify_charpoly.py: independent symbolic characteristic-polynomial calculation for m=2,...,6
- checks/reproduce.py: compile and replay all 19 Fourier cases without overwriting delivered data
- checks/*validation*.json and independent_charpoly_checks.json: executed arithmetic receipts
- SOURCES.md and source_pin.json: version and attribution
- VALIDATION.md and compiler.log: validation record
- SHA256SUMS: file provenance (retired on filing; not in the repository)

## Reproduction
The analytic theorem is proved in the manuscript. For the finite table use Python 3, a C++17 compiler, and GMP development libraries:
    python checks/reproduce.py
    python checks/verify_table.py

The independent characteristic-polynomial check additionally uses SymPy:
    python checks/verify_charpoly.py

To build the PDF, use a LaTeX installation providing the packages listed in the preamble:
    sh build.sh

The reported source mathematics is not externally refereed or formally verified. No dominant complex singularity location or sign density is asserted in this report.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the eighth of thirteen packages of one series, filed beside the
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

- `infinite_pressure_sign_changes.tex`: an unnumbered environment `ednote`
  ("Editorial note (ProveIt, 2026-10-01)") is defined after the theorem
  environments (no counter changes). Three notes:
  - after Theorem 1.1: here `R_m` is the Taylor radius; in the host and every
    other package `R_m = 2(2^{2m} - 1) zeta(2m)/pi^{2m}`;
  - after the scope paragraph of Section 6:
    `../Thue_Morse_Integer_Pressure_Sign_Densities/` proves positive lower
    densities, which contain the infinite-sign statements of Theorems 1.1 and
    4.1 but not the radius bound, (1) or the corollary on `N_m`;
    `../Thue_Morse_Integer_Pressure_First_Negative/` proves the `N_m`
    asymptotic; `../Thue_Morse_Integer_Pressure_First_Negative_Data/` extends
    the table to `m <= 128` and agrees with it for `m <= 20`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited: `[Window]`, "delivered as report
    63", is `../Thue_Morse_Integer_Pressure_Full_Range/`.
- `infinite_pressure_sign_changes.pdf`: rebuilt from the amended source with
  three `pdflatex` passes (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 7 A4 pages
  (7 as delivered), 342,777 bytes; all 17 fonts embedded, none Type 3; the
  final log has no error, overfull or underfull box, undefined or multiply
  defined reference, duplicate destination, or rerun request. The pages
  carrying the notes were rendered and inspected.
- `checks/verify_table.py`, `checks/verify_charpoly.py`: new option
  `--output-dir` (default `checks/rerun/`), with LF line endings. As
  delivered, every checker overwrote its recorded file beside itself, with
  CRLF line endings on Windows. Pass `--output-dir checks`, on a copy, to
  regenerate the recorded files. A checker that reads another checker's record
  reads the recorded file, as delivered. On the ProveIt machine use `py`
  rather than `python3`/`python`. Reruns on a copy (2026-10-01, Python 3.14.4,
  SymPy 1.14.0) passed (43 s and 2 s) and wrote both records equal to the
  recorded ones byte for byte. SymPy is not pinned (no requirements file).
  `checks/reproduce.py` (C++, GMP; not run) writes `checks/replay/`.
- `build.sh`: kept as delivered; it runs `pdflatex` here, overwrites the filed
  PDF and leaves `build-pass-N.log`, `.aux` and `.out` files here: build on a
  copy. `compiler.log` is a delivered record.
- `README.md`: the retired ledger under "Contents", and this section.
