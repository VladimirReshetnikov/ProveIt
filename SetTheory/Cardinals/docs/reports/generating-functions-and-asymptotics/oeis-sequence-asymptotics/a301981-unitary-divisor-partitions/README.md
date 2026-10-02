# Unitary divisor sum colored partitions

This package accompanies the research article on A301981 and A301982. It contains the editable TeX source, rendered PDF, original coefficient and asymptotic-check programs, numerical data and replay instructions.

The central conclusions are sequence-specific corrections of the two recorded pure equivalents, a logarithmic-error criterion equivalent to RH for either sequence separately, an unconditional corrected equivalent at an explicit point, all-fixed-order centered and off-center expansions, and qualified inverse-threshold brackets. An equivalence to RH is not a proof or disproof of RH.

## Files

- `unitary-partitions.tex` and `unitary-partitions.pdf`: complete article, proofs and bibliography
- `build.sh`: rebuild the PDF with pdfLaTeX
- `reproduce.sh`: verify pinned sources, recompute all diagnostics in a fresh working directory, compare reference JSON and rebuild the PDF
- `requirements.txt`: mpmath version pin
- `SOURCE-MANIFEST.sha256`: hashes of sources and reference data
- `MANIFEST.sha256`: hashes of all delivered files except itself
- `code/package_release.py`: deterministic manifest and ZIP creation for the final files
- `code/`: original coefficient, saddle, explicit-point, inverse, precision and safety checks
- `data/`: recorded numerical results and inspected OEIS prefixes
- `receipts/`: compact execution and rendering verification records

No external account, network access, private notes or third-party full-paper copy is needed for replay.

## Environment and replay

Reference numerical environment: Python 3.12.14 and mpmath 1.3.0. The code uses only the standard library and mpmath. Python 3.10 or later should run it; the pinned reference environment is the basis for exact JSON comparisons. The tested TeX engine is pdfTeX 1.40.26, TeX Live 2025/dev/Debian. A normal TeX installation needs article, Latin Modern fonts, geometry, amsmath, amssymb, amsthm, mathtools, booktabs, longtable, microtype, hyperref and enumitem. Poppler `pdftotext` checks the rebuilt PDF text.

If necessary, install the dependency in a virtual environment with `python3 -m pip install -r requirements.txt`. Installation is separate from replay and may use the network. The supplied scripts install nothing.

From the extracted package directory:

```sh
python3 code/verify_manifest.py MANIFEST.sha256
bash reproduce.sh
```

The full replay can take several minutes. It creates a fresh `.replay/run-*` directory, leaves reference numerical files unchanged, and rebuilds the PDF. It compares every reference numerical JSON value, including high-precision/cutoff replays. A different dependency environment may change floating residuals; investigate any mismatch rather than silently discarding it.

For only a PDF rebuild:

```sh
bash build.sh
```

Invoke shell scripts with `bash`; executable mode bits are unnecessary. The TeX build has a local-cache fallback for installations whose TeX sources/fonts exist but generated formats/maps are missing. It writes only inside the package. PDF creation timestamps are fixed for reproducibility within one installation. Different engines can produce different PDF bytes; replay also compares extracted text and checks the final TeX log for warnings and box defects.

## Independent computations

The numerical entry scripts share `code/numerics_core.py`; keep that module with them.

- `check_oeis_prefixes.py`: direct unitary-divisor enumeration and finite binomial products match the 36/37 recorded OEIS terms, including degree zero
- `check_unitary.py`: integer logarithmic-product recurrence through 1000, independent trial-divisor checks, principal Mellin-residue and old-model diagnostics
- `check_saddle.py`: exact-cumulant centered formulas for M = 0, 1, 2
- `check_fixed_saddle.py`: explicit leading point and stationary-exponent comparisons
- `check_cutoff_precision.py`: cutoff 1000 / 60 digits versus 2000 / 80 digits, with rational tail bounds through derivative order 6
- `check_inverse.py`: centered model inverse tests at exact coefficient and geometric-midpoint targets
- `check_offcenter.py`: independent binomial products versus recurrence through 500, Gaussian Fourier sign checks, Hermite grades and deliberate odd-grade-deletion diagnostics
- `check_offcenter_replay.py`: cutoff 1200 / 70 digits versus 1800 / 90 digits, with rational tail bounds through order 7
- `check_offcenter_inverse.py`: outer-only inverse checks with explicit points and no inner saddle solve; uses the shared numerical core

No numerical first-zeta-zero residue illustration is included. No zero computation or zero-simplicity assumption supports the article or replay.

## Exactness and numerical limits

Coefficients and binomial/recurrence equalities use exact integer arithmetic. Rational tail majorants exactly bound omitted product terms. Floating evaluations, Newton/root-finder results and final ratios are not interval enclosures. A larger-cutoff/higher-precision match checks stability; it does not certify all rounding error.

The cutoff replay proves that all tested exact saddles exceed 1/10 using an exact rational lower bound on the tilted mean there. The plus model has the smaller mean; its block lower bound exceeds 1036, hence 1000. For t >= 1/10 and r >= 1, a discarded derivative tail beyond L is bounded by

(r-1)! (1-e^-1)^(-r) sum_{m>L} m^(r+2) e^(-m t).

For r = 0, use (1-e^-1)^(-1) and power 2. Integration of (x+1)^p e^(-t x) on [L,infinity) bounds the remaining sum by

e^(-t L) sum_{i=0}^p binom(p,i) (L+1)^(p-i) i! / t^(i+1).

The code proves 27/10 < e < 68/25 by rational Taylor estimates and replaces the exponential terms with rational upper bounds. Numerator/denominator pairs are recorded in the replay reports. These conservative bounds do not certify floating roots.

The threshold theorems give eventual existence constants and shrinking two-ceiling brackets. They do not provide numerical global starting cutoffs or unconditional exact-ceiling formulas. Midpoint checks exercise stable rounding away from integer boundaries; exact coefficient targets expose near-integer ambiguity.

## Sources and scope

The article links the inspected OEIS records and primary references. Tóth's ordinary unitary-divisor Dirichlet series is unnumbered in Section 4.9 on printed page 28, not equation (50). Bureaux–Enriquez, Bodini et al., Dong et al. and general partition expansions receive explicit methodological credit. The literature search was targeted, not exhaustive, and no universal priority claim is made.

## Safe extraction

The ZIP has one top-level `unitary-partition-report/` directory and only regular files. Inspect entries before using an archive. The standalone utility extracts it to a destination that does not yet exist:

```sh
python3 code/safe_extract.py path/to/unitary-partition-report.zip path/to/new-directory
```

For first extraction, obtain the utility from a trusted copy or use a ZIP tool with traversal and symlink protections. The utility rejects absolute paths, parent components, backslashes, drive-like prefixes, duplicate names, symlinks and nonregular entries, and limits expanded size to 100 MB.
