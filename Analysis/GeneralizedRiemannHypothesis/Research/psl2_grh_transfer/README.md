# Beyond Dirichlet GRH: sharp PSL2 transfer

**Start with `report.pdf` (13 pages).** `report.tex` is the complete typesetting source. The report proves a uniform optimal nonnegative-character detector, sharp subfield-degree thresholds, and a precise one-sided prime-only criterion equivalent to Dedekind RH for splitting fields with group PSL2(2^r). It does **not** establish that new prime-sum inequality or prove nonabelian RH. No full new conjecture is claimed solved.

## Contents

- `report.tex`, `report.pdf`: mathematical exposition, proofs, limitations, citations, and further research questions.
- `check.py`: exact group computations with standard-library Python 3.10 or newer. Generates `checks.json`.
- `checks.json`: computed conjugacy-class data for q=4,8,16; complete subgroup searches up to conjugacy for q=4,8.
- `verification.txt`: actual execution results.
- `source_manifest.tsv`: upstream Git revision, selected source blobs, and prior-report blobs reviewed or inaccessible.
- `SHA256SUMS`: integrity hashes of all deliverables except itself.

## Reproduce

Run from the extracted directory:

```sh
python3 check.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The Python computation requires no Sage, GAP, or PARI. It checks finite instances, not the analytic theorem, and is not a Lean proof. The general theorems are justified in the text. A local Lean build was not performed. The prior-report review was selective; no priority or worldwide novelty claim is made.
