# Report194: binary matrices with zero row and column slopes

This package studies the square diagonal C_n of [OEIS A222959](https://oeis.org/A222959): n by n binary matrices M with Mw=M^T w=0, where w_j=j-(n+1)/2 for odd n and w_j=2j-n-1 for even n. The convention at n=1 is C_1=2.

For S_n=n(n^2-1)/12 in the odd case and n(n^2-1)/3 in the even case, the report proves

    C_n = 2^(n^2) exp(-7/5) sqrt(2/pi) (2/(pi S_n))^(n-1)
          (1 + 171/(350 n) + 483051/(245000 n^2) + O(n^-3)).

The report gives a problem-specific global Fourier localization proof, the saturated lattice and Gaussian normalization, a finite rational prescription for every fixed-order coefficient, and parity-aware inverse expansions. The supplied code evaluates c0=1, c1=171/350 and c2=483051/245000. No all-order Wick engine, practical onset, convergence of the formal series, or absolute priority claim is supplied. Exact small counts are strongly preasymptotic and do not validate the asymptotic error term.

## Contents

- `Report194.tex` and, in a release, `Report194.pdf`: the proof and source comparison
- `code/matrix_exact.py`, `code/check_exact.py`: standard-library exact arithmetic and bounded enumeration
- `code/derive_second_correction.py`, `code/verify_second_correction.py`: finite connected-Wick contraction and independent raw-moment verification of c2
- `data/reference.json`: the finite count and row-alphabet reference values, including a separately labeled n=9 computation
- `reproduce.py`: normal and optimized isolated-Python replay with byte comparison
- `build.py`, `verify_manifest.py`, `test_build.py`: offline reproducible publication and fail-closed guards
- `DATA_SOURCES.md`: primary-source scope and limitations
- `README_REPRODUCIBILITY.md`: commands, dependencies, inventory, and trust boundary

## Quick start

With Python 3.11 or later, from the package directory:

    python -B reproduce.py --output-dir /tmp/Report194-replay
    python -B test_build.py
    python -O -B test_build.py

These are Linux examples. Choose fresh output names under an existing parent such as `/tmp`; existing output is rejected. On macOS, use `/private/tmp` rather than the symlink `/tmp`. On Windows, substitute absolute paths whose parent already exists. Every path component must be a real directory, not a symlink. Output paths must contain no `.` or `..` components. The mandatory replay uses only the Python standard library and no network. It recomputes counts through n=8, full rational projector identities through n=12, and row alphabets/ranks and structural checks through n=14. The n=9 count 1,808,243,216 is recorded independent enumeration evidence from 7,311,616 positive-row tuples, not a default rerun. An explicitly requested expensive replay is available:

    python -I -S -B code/check_exact.py --max-n9 --output /tmp/Report194-with-n9.json

Building the PDF additionally requires an installed TeX distribution:

    python -B build.py --output /tmp/Report194-release

The result is a PDF, TeX source, deterministic code ZIP containing all sources and generated receipts, and a SHA-256 artifact receipt. Existing output is never overwritten. For an extracted release, run `python -B verify_manifest.py` before replaying or rebuilding.
