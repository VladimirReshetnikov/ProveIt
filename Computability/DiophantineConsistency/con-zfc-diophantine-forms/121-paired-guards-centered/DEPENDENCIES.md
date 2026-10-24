# Exact dependency closure and calibration boundary

## Current computations

1. `integer/`: the two builders use `circuit.py` and its imported
   `five_square_norm.py`. The independent producer audit uses
   `exact_polynomial.py`, `prior_check.py` (functions only), and the complete
   `coefficients/recipe/source34_builder.py`, `k215.tm`, and `wang943_tiles.json`.
   All six compressed numerals and their binding are included. The runtime is
   Python's standard library. `SOURCE_PINS.json` authenticates the retained
   proof and license files. The separate reviewer uses SymPy, no producer imports.
2. `lowdegree/`: the two builders use the bundled DAG helper and the twelve
   variable literal specification. The fifteen-variable build regenerates its
   own specification. All six numerals are included. Its exact SymPy audits
   read the unchanged `prior/ZFC_Diophantine_Coprime_Projection/lowdegree/`
   equations, specifications, source pins, and mathematical proofs. The entire
   immutable prior release is present, not merely a selected theorem excerpt.
3. `positive/`: the builder reads `source/prior96_equation.json` and emits six
   literal evaluators. The audits load only standard-library helper functions
   from `source/prior_check.py`. Its complete **original compact44 tuple** is
   included and compared byte-for-byte to the retained prior. It is not the
   distinct BFS or newly indexed tuple. No individual coefficient is exchanged.
4. `alternative/`: `build_pairguards.py` reads the two frozen `source/` JSONs
   and the two inspected `vendor/` polynomial modules. Its paired/squared-paired
   output directories each contain the equation, full expanded polynomial,
   source transformations, sign certificates, presemantic certificates,
   factorization certificate, and all projection/restoration steps. Runtime
   is standard-library only. `CALIBRATION.md` maps the included ordinary
   C222/ZF/ZFC source proof chain under `inherited_proofs/`.
5. `report/qa/check_editorial_math.py`: portable SymPy transcription checks
   for the report-only typesetting changes, reading literal component TeX and
   the twelve-variable specification. No file writes or producer imports.
6. `review/`: independently written finite checkers, proof reviews and receipts.
   Integer and lowdegree review need SymPy 1.14.0; positive and alternative
   review use the standard library. No network or parent workspace is required.

The selected execution closure is recorded with exact file hashes in
`CODE_REVIEW.json`. Other source programs retained in `prior/`, provenance,
and `alternative/inherited_proofs/` remain **inert evidence** during this replay.
Their presence is not a claim that their entire historical build was rerun.

## Root orchestration

`reproduce.py` uses Python standard-library subprocesses with fixed argument
lists, no shell. It authenticates the root manifest before running the above
closure, creates isolated copies, writes receipts/logs only to an external destination,
runs both ordinary and optimized interpreters,
and performs exact byte comparisons. `rebuild_coefficients.py` reconstructs
integer numerals from the retained recipe and authenticates the positive tuple.
`COEFFICIENT_CHECK.json` is its deterministic certificate; it is compared exactly
in both modes. No compiler, machine, proof enumerator, or consistency search is
executed. `seal_release.py` is a maintainer action, not part of verification.

## Source closure versus a newly mechanized theorem

This release supplies the ordinary arithmetic dependency documents used by its
reductions, complete explicit equation and coefficient data, provenance pins,
and the complete preceding release. It does not claim to ship or rebuild every
external Lean/Mathlib dependency or establish a new kernel-checked theorem all
the way from a formalized ZFC syntax to each new polynomial. All calibration,
exceptional-case and existence-direction obligations remain explicitly stated
in the proofs and independent reviews. A finite test cannot discharge an
unbounded existence theorem or decide consistency.

## Baseline evidence

`baseline/BASELINE_CHECKS.json` authenticates the **larger original research
snapshot**, not just the subset distributed here. `baseline/SELECTED_EVIDENCE.json`
records the actual included subset and its exact bytes. The omission of most
baseline archives, historical graphs and tools is intentional: they are not
runtime inputs or the retained mathematical dependency closure. Dated late-head
credit is retained separately under `baseline/late/` and component provenance.

## Documents

TeX sources and PDFs are included. TeX rebuilds require a standard pdflatex
installation and the packages declared by each manuscript. TeX compilation and
visual review are not implied by a Python replay pass; consult the report and
component QA records for what was actually performed.

`make_release_zip.py` is a reviewed release-maintainer tool. It reads the sealed
tree, creates two independent fixed-metadata ZIPs outside it, requires exact
byte identity, and writes an external archive hash/CRC receipt.
