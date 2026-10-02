# Log periodic factors in radix layer partition asymptotics

The 14-page article proves the corrected equivalent and all fixed-order terms for F_b(z) = product over j >= 0, i >= 1 of (1 + z^(i b^j)), integer b >= 2. It corrects the constant-only formulas in the retrieved OEIS A174065 and A393565 versions, gives an exact positive-real reciprocal identity, and derives inverse and regularity consequences.

## Contents

- `radix_partition_report.pdf`: complete article
- `radix_partition_report.tex`, `numerical_tables.tex`: editable TeX source
- `checks/`: exact enumeration and high-precision verification scripts
- `recorded/`: supplied numerical JSON results
- `provenance/`: factual OEIS snapshot, source links and bounded literature/repository search scope
- `requirements.txt`: Python calculation dependencies
- `build_pdf.sh`: portable PDF build
- `replay.sh`: complete verification and clean rebuild
- `SHA256SUMS`: SHA-256 values for all immutable supplied files

## Requirements

Python 3.10 or newer; mpmath 1.3.0; SymPy 1.14.0; Bash; and a TeX Live or comparable installation providing `pdflatex`, `pdftex`, `kpsewhich`, Latin Modern, AMS-LaTeX, mathtools, booktabs, microtype, hyperref, enumitem and geometry. The validation environment used Python 3.12, mpmath 1.3.0, SymPy 1.14.0, and pdfTeX 1.40.26 (TeX Live 2025/dev/Debian).

If the Python packages are not already installed, install them in a virtual environment with `python3 -m pip install -r requirements.txt`. No network access is needed for the replay once its dependencies are present. The build script bootstraps TeX format/font caches in its own directory when necessary; it does not modify the system TeX installation.

## Portable extraction and complete replay

Executable permission bits are not required. For example, from a directory containing the ZIP:

```bash
python3 - <<'PY'
from zipfile import ZipFile
with ZipFile('radix-partition-reproducibility.zip') as z:
    z.extractall('clean-extract')
PY
cd clean-extract/radix-partition-report
bash replay.sh
```

The replay verifies the frozen hashes, copies scripts to a new `replay-output` directory, recomputes all five JSON outputs, compares  numerical results, regenerates the TeX tables, and builds the PDF in a clean staging directory. It deliberately stops if its output directory already exists. Use a new extraction or set `RADIX_REPLAY_DIR` to a new absolute directory for another run.

The computation-only commands, in their dependency order, are:

```bash
python3 checks/check_exact.py
python3 checks/check_radix.py
python3 checks/check_coefficients.py
python3 checks/check_inverse.py
python3 checks/check_reciprocity.py
python3 checks/verify_results.py recorded checks
```

These commands write JSON beside the copied scripts. `check_inverse.py` depends on the coefficient JSON. The exact dynamic programs run through n=10000 for b=4 and b=8. The smaller three-way identity check runs through n=400 for b=2,3,4,8,16.

To rebuild the supplied article directly, use `bash build_pdf.sh`. The replay is preferred because it isolates all generated files. The build uses a fixed source date and suppresses volatile PDF date/trailer fields. Identical dependencies in the validation environment produced byte-identical PDFs; a different TeX installation can legitimately produce different bytes.

## What is and is not verified

The exact checks use integer arithmetic and compare independent constructions. Floating checks use 60–90 decimal working precision, finite Fourier sums, and non-interval arithmetic. The replay compares numeric records to absolute-plus-relative tolerance 1e-40, compares exact integers exactly, checks fourth-order count errors at n=10000 below 1e-9 and inverse errors below 1e-6, and requires reciprocity residuals below 1e-80. These are computational sanity checks, not rigorous remainder certificates.

The analytic nonvanishing proof is exact and does not depend on numerical amplitudes. The integer inverse brackets are asymptotic: explicit coefficient-error constants and starting thresholds are not supplied. Exact positive-real radial completion does not establish exponentially complete coefficient asymptotics. A bounded literature search is not a worldwide priority claim. Full third-party papers are not redistributed.
