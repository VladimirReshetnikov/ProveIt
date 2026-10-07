# Report186: rounded running means

Exact amplitude selection and all-order asymptotics for OEIS A065094 (floor) and
A065095 (ceiling). The archive contains the manuscript, compiled report, attributed
short source data, exact replay programs, mathematical corruption checks, and an
isolated deterministic offline builder.

## Start here

From an extracted release, using Python 3.10 or newer:

```
python3 -B verify_manifest.py
python3 -B reproduce.py --output-dir /existing/parent/new-replay
python3 -B build.py --output /existing/parent/new-release
```

The requested output directory must not exist and must be outside the package.
The builder additionally requires an installed working pdfLaTeX stack with the
packages used in the manuscript. See `README_REPRODUCIBILITY.md` for dependencies,
independent rebuild instructions, and the exact guarantee. No network is used.

The build publishes exactly `Report186.pdf`, `Report186.tex`,
`Report186_code.zip`, and `ARTIFACTS.json`. It does not overwrite existing outputs.
The ZIP's PDF and TeX are byte-identical to their separately published versions.
All temporary caches, certificates and TeX intermediates remain outside the
source tree. An intact extracted ZIP is itself a valid build source.

## Mandatory exact replay

`reproduce.py` runs every mathematical script in normal and optimized Python,
with isolated standard-library-only interpreters. Both outputs must equal the
shipped reference files byte for byte.

- `code/certify_amplitudes.py`: N=10000 integer/Fraction amplitude intervals;
  rational Machin pi, exponential, square-root and outward decimal bounds
- `code/check_common_truncations.py`: exact endpoint floor-equality proof of 69
  common truncated places for all six A/C/c constants
- `code/check_exact.py`: both official 1000-term b-files and complete stored
  prefixes; finite Laguerre sums, sum identity and symbolic Casoratian through 150
- `code/formal_series.py`: arbitrary fixed-order truncated Fraction polynomial
  arithmetic; c0 through c9, logarithmic and inverse coefficients, independently
  checked via logarithmic recurrence ratios and direct inverse composition
- `code/audit_positive_sum.py`: independent N=10000 positive finite-sum P and T,
  separate division-with-remainder trajectories and exact amplitude checks
- `code/test_mathematical_guards.py`: deliberate certificate, data and formal
  coefficient corruption, malformed arithmetic parameters and provenance changes
- `test_build.py`: isolated builder, no-overwrite, symlink/traversal, complete
  inventory, strict JSON, deterministic archive and TeX-log guards

All guards use explicit exceptions. They remain active with `python3 -O`.
Reference certificates are in `certificates/`; integrity receipts are in `data/`.

## Interpretation

The all-orders classical Laguerre expansion is credited prior work. This report
uses exact bounded-forcing control to transfer it to rounded recurrences and
certify their amplitudes. The narrow rational intervals certify 69 common truncated digits. The displayed
70-place endpoints share 69 fractional digits except for ceiling A, whose two
printed endpoints share 68; its 69-place result uses the separate exact check. No finite onset is certified for log-concavity, asymptotic
bounds or arbitrary-threshold inversion. The exact range inverse and the two
ceiling threshold envelope are distinct conclusions.

Optional `optional/diagnostics_mpmath.py`, `optional/diagnostics_sympy.py` and
`optional/derive_coeffs_sympy.py` require mpmath or SymPy. They are not needed for
building or verifying this report and do not replace interval certificates.
See `DATA_SOURCES.md` and the manuscript bibliography for attribution.
