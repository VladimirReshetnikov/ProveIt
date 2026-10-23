# Selective positive-source guards and sparse carry interfaces

The proven source transformation shifts only twelve of the original thirty-one
positive variables. All nineteen remaining coordinates are forced positive by
literal source equations. It lowers 136 coefficient records / 71 active
monomials to 109 / 62, without changing 31 variables or 22 quadratic equations.

Primary files:

- `SELECTIVE_POSITIVITY_PROOF.md`: complete elementary zero-set bijection.
- `selective12_source.json`: all transformed residuals and factorial weights.
- `selective12_row_pairs.txt`, `selective12_support_pairs.txt`: packing input.
- `data/source_system60.json`: byte-pinned inert parent source.
- `build_selective_source.py`: generator (requires SymPy).
- `verify_selective_source.py`: independent exact standard-library verifier.
- `SELECTIVE_SOURCE_VERIFICATION.json`: native coefficient and source audit.
- `SPARSE_POPCOUNT_SOURCE_PROOF.md`: signed-borrow sparse padding and separate
  natural-square / integer-nonsquare threshold contracts.
- `check_sparse_popcount.py`, `SPARSE_POPCOUNT_CHECKS.json`: finite diagnostics.

The coherent native coefficient tuple is in `../native`. Positional certificates
are independently checked in `../packing`. Complete nine-variable circuits,
materialized signed fixed leaves, exact source checks, and ratio-tail proofs are
in `../nine`.

Reproduce from this directory's parent or any working directory:

    python source/build_selective_source.py
    python source/verify_selective_source.py
    python source/check_sparse_popcount.py

Do not interpret the finite checks as an end-to-end proof-assistant
formalization or a proof of consistency. The inherited compiler/refutation
and Jones/Sun bridge dependencies remain explicit.

Exploratory affine-search logs are research notes only. They are not used in
any recommended source or circuit and need not be included in a release.
