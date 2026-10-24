# Positive-gap shared taps

Primary: gapN86_source.json, gapN86_code.json, gapN86_kernels.json.
The source is strictly positive in31 coordinates. Fixed four-port constants
are actual payloads under coefficients/, in the original31 tuple.

Run `python audit.py` (or `python -O audit.py`) for read-only artifact audit,
actual coefficient bounds, and negative controls. `python verify.py`
reconstructs the kernels from search input and frozen target logs and checks
all target identities. No upstream program is executed or imported.

The newly authored optional search uses `prepare.py` and `search.cpp`;
prepare.py needs the sibling frozen round9/review data and is not necessary
for a standalone replay. The complete input JSON is supplied. Compilation
and search are not needed for the proof certificate. Only source65's exact
target vector, not the heuristic search result, is primary.

PROOF.md states the positive-coordinate bijection, shared-tap lemma,
positivity/carry bounds and integer-finalizer ports. This is supporting work;
it does not claim an independently materialized complete Con(ZFC) equation.
