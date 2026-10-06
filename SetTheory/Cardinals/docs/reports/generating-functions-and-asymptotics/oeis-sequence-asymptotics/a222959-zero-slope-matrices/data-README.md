# Finite reference data

`reference.json` records square counts C_n for 1<=n<=9 and row alphabet sizes/ranks for 2<=n<=14. Its bytes are SHA-256 pinned by `code/check_exact.py`.

The official OEIS A222959 page's displayed array was inspected on 4 October 2026. A direct b-file retrieval was unavailable (HTTP 403); it is neither bundled nor represented as retrieved. All nine diagonal values were independently checked by a C++ positive/negative-row meet-in-the-middle implementation. The n=9 computation used an alphabet of size 52, 52^4=7,311,616 positive-row tuples, and yielded 1,808,243,216 matrices. That independent computation is recorded evidence, not an executable dependency or a default rerun in this package. The authored Python implementation recomputes n<=8 on every normal and optimized mandatory replay; n=9 is an optional explicit run.

The row alphabet reference and rational ranks originated in a separate symbolic computation. The package independently recomputes them by complete binary-word enumeration and Fraction elimination through n=14; no symbolic package is required.

No numerical values for asymptotic higher-order coefficients are inferred from or fitted to the counts. For primary sources and scope, see `DATA_SOURCES.md`.
