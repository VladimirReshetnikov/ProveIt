# Positivity at the First Feedback Boundary in Thue Morse Pressure

This report proves, for every integer m>=2:

- H_(m,m)=[a^(2m)]h_a(1/2)>0
- [t^(4m)]p_m(t/pi)>0

Together with the previous triangle theorem, both response and pressure
coefficients are now positive throughout 1<=r<=m. The response range cannot
uniformly extend one step: H_(2,3)=-488/27. Pressure at degree ten is still
positive, so response and pressure sharpness must be distinguished.

The proof has two explicit parts. A regularized orbit formula, strict tangent
comparison, and a Bernoulli mode bound prove every m>=70. Exact integer
reflection-block enclosures certify all 68 remaining moments m=2,...,69.
The report also proves a positive diagonal asymptotic for H_(m,m).

## Main files

- `article.pdf`: nine-page mathematical report (eight pages as delivered; see the editorial amendments below)
- `article.tex`: editable LaTeX source
- `code/run_all.py`: quick exact validation of the supplied certificates
- `code/reproduce_all.py`: full recomputation of all 68 matrix enclosures and every saved trace entry
- `code/check_boundary_parity.cpp`: primary exact GMP enclosure generator
- `code/check_trace_coverage.py`: independent standard-library trace audit
- `code/verify_cutoff.py`: exact rational analytic-cutoff certificate
- `code/check_m 2_response.py`: exact cubic proof of the response counterexample
- `code/check_m 2_pressure.py`: independent exact pressure cubic certificate
- `code/fourier_reference.py`: optional independent SymPy response comparisons
- `code/recompute_first_negatives.py`: optional exact later-sign exploration
- `data/certificates/`: per-moment rational enclosures and compressed per-order traces
- `data/`: exact cutoff, sharpness, reference, and audit data
- `PROOF_STATUS.md`, `SOURCES.md`, `VISUAL_QA.md`: scope, provenance, and inspection records
- `SHA 256SUMS.txt`: file-integrity manifest (retired on filing; not in the repository)

## Verify

The quick check requires only Python 3:

    python 3 code/run_all.py

It validates all 68 saved traces, all 4828 scalar error recurrences, the baseline
vectors, final intervals, available exact comparisons, the rational analytic
cutoff, and the two cubic certificates. The audited generator itself checks
matrix inverse identities and every outward rounding operation.

For the complete matrix-level replay, use Python 3, a C++17 compiler, and GMP
with its C++ development headers and libraries:

    python 3 code/reproduce_all.py

This compiles the included source locally, recomputes all 68 enclosures using
two processes, and compares every trace entry to the supplied certificates.
Every arithmetic decision is exact integer arithmetic. The reported runtime
is metadata only. No floating-point estimate enters a sign certificate.

Optional reference calculations require SymPy 1.14.0:

    python 3 code/fourier_reference.py
    python 3 code/recompute_first_negatives.py

The latter regenerates the first negative pressure degree above 2m for m=2,...,14.
It is exploratory finite orientation, not a claimed general formula.

## Build

A normal TeX installation can run `pdflatex article.tex` twice.
`build_local.sh` reproduces the restricted-environment build without changing
a system TeX tree. Build and replay outputs go under `build/`.

The results are ordinary mathematics with a finite computer-assisted proof
component, independently reviewed but unrefereed and not verified in Lean.
The source ZIP is approximately 45MB because it preserves every per-order
integer vector and error bound. Earlier delivered reports remain unchanged.


## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 72 of `docs/incoming/` (see
`docs/incoming/README.md`). Every change to the source is marked
`% ed. (2026-10-01)`, every change to a program `ed. (2026-10-01)`. The
mathematical text is unchanged; the byline and `pdfauthor` entry ("Research
note prepared for Vladimir Reshetnikov with OpenAI") are kept as delivered.
This is the fourth of thirteen packages of one series, filed beside the
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
  changes). Four notes:
  - after Theorem 1.1 and its paragraph: `E_{m,m} > 0` is re-proved as the
    case `r = m` of Theorem 1.1 of
    `../Thue_Morse_Integer_Pressure_Full_Range/`, so it does not hang on the
    missing traces; `H_{m,m} > 0` and the diagonal asymptotic stay this note's
    own (`m = 2` was in `../Thue_Morse_Integer_Pressure_Higher_Positive/`;
    `../Thue_Morse_Integer_Pressure_Beyond_Boundary/` extends the asymptotic
    to fixed offsets);
  - at the end of Section 7: the trace archives were not delivered (see
    below), and what the filed files show, checked on filing: all 68 interval
    records have positive lower endpoints; filed exact values of `H_{m,m}` lie
    inside them for the 35 orders `2 <= m <= 35` and `m = 50`; for
    `m = 68, 69` a full-vector enclosure overlaps; for `36 <= m <= 49` and
    `51 <= m <= 67` the intervals are the only finite evidence; `E_{m,m} > 0`
    is certified for `m <= 128` by the filed intervals of
    `../Thue_Morse_Integer_Pressure_First_Negative_Data/`;
  - after the open directions: pressure positivity for `1 <= r < 2m` is proved
    in `../Thue_Morse_Integer_Pressure_Full_Range/`; the table of first
    negative degrees agrees with
    `../Thue_Morse_Integer_Pressure_First_Negative_Data/` and
    `../Thue_Morse_Integer_Pressure_Sign_Changes/`, and
    `../Thue_Morse_Integer_Pressure_First_Negative/` proves `N_m/m -> gamma`;
  - before the bibliography, a series map: the thirteen packages in logical
    order, the superseded earlier version of the full-range article, and the
    filed directory of every source cited (`[2]` is
    `../Thue_Morse_Integer_Pressure_Positive_Triangle/`).
- `article.pdf`: rebuilt from the amended source with three `pdflatex` passes
  (MiKTeX 26.2, pdfTeX 1.40.29), on a copy: 9 A4 pages (8 as delivered),
  383,155 bytes; all 21 fonts embedded, none Type 3; the final log has no
  error, overfull or underfull box, undefined or multiply defined reference,
  duplicate destination, or rerun request. The pages carrying the notes were
  rendered and inspected.
- **Undelivered trace archives.** `DELIVERY_README.txt` describes a
  six-archive split delivery; only the source archive arrived. The 68 files
  `data/certificates/parity_mNNN.json.trace.gz` (listed in the retired ledger;
  the unsplit package was about 45 MB) are not in the repository, so the trace
  audit and `code/reproduce_all.py` (which also needs g++ and GMP) cannot run
  here; `data/trace_checks.json` is the delivered record of the audit as run
  before the split. If the five archives are delivered later, they belong in
  this directory, filed in a commit of their own.
- `code/check_trace_coverage.py` and `code/run_all.py`: as delivered, a
  missing trace was skipped in silence, `run_all.py` printed "All packaged
  certificate checks passed" after auditing no trace at all, and it overwrote
  `data/trace_checks.json` (68 moments, 4,828 orders, `complete: true`) with
  an empty record (`complete: false`). Now every checker of `run_all.py`
  (`verify_cutoff.py`, `check_trace_coverage.py`, `check_m2_response.py`,
  `check_m2_pressure.py`) has the option `--output-dir` (default
  `data/rerun/`), with LF line endings; the trace audit prints a warning when
  traces are absent, and `run_all.py` ends with "Trace audit INCOMPLETE"
  instead of the claim when the audit is incomplete (the exit status is
  unchanged). A rerun on a copy (2026-10-01, Python 3.14.4) wrote the cutoff
  and both cubic certificates equal to the recorded ones byte for byte, and an
  empty `data/rerun/trace_checks.json`.
- `code/recompute_first_negatives.py` (optional, kept as delivered) stops with
  `AttributeError` as filed: line 17 rebinds `target`, its output path (line
  3, under `build/`), to a SymPy matrix, which line 26 then tries to write.
  With that variable renamed, a scratch copy reproduced the recorded rows
  `m = 2..11` exactly (rows 12-14 were not rerun). `code/fourier_reference.py`
  was not rerun in this pass (it passed on intake).
- `README.md` as delivered has letter-digit splits:
  `code/check_m 2_response.py` and `code/check_m 2_pressure.py` are
  `code/check_m2_response.py` and `code/check_m2_pressure.py`,
  `SHA 256SUMS.txt` is `SHA256SUMS.txt` (retired on filing), and `python 3` is
  `python3`; `PROOF_STATUS.md` line 17 "weighted-l 1" means weighted-l1. "The
  source ZIP is approximately 45MB" describes the unsplit package; the
  delivered source archive was 594,390 bytes. Kept as delivered apart from the
  ledger line.
- `Makefile`: kept as delivered; it calls `python3` (use `py` on the ProveIt
  machine), and its `pdf` target runs `pdflatex` here and overwrites the filed
  PDF.
- `build_local.sh`: kept as delivered. It sets `TEXMF` to the Debian paths
  `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, writes `build/` here
  and copies the result over the filed PDF: build on a copy.
- `README.md`: the page count and the retired ledger under "Main files", and
  this section.
