# Joint positivity, free Lucas coordinates, and commutative proof certificates

Research packet for ProveIt, 23 October 2026. Reviewed main pin:
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.

Start with `report/report.pdf`; its TeX and local build script are included.

## Completed consistency equations

- `integer_system/octic28.json`: 28 unrestricted integers, 14 residuals,
  degree-eight single sum of squares.
- `integer_system/degree16_26.json`: 26 unrestricted integers, 13 residuals,
  degree-sixteen single sum of squares.
- `norm/final10/`: ten-integer free-coordinate finalizer. Consult that
  directory's README, exact circuit and metrics: 481 operations and exact
  total degree 1,576,864. Superseded prototype/fallback circuits are omitted.

Each has a mathematical equivalence proof using the named inherited source
calibration and Pell results. No new Lean/Rocq certificate is claimed.

## New architecture, not a completed global record

`direct/` and `alternative/` prove a different source representation:
single-conclusion proof flows, pairwise coprime affine factors, a one-stream
accumulator, and 17-witness branch-shared local formulas. The supplied
23-local-witness accumulator constructor is UNCOMPILED; its final ordinary
polynomial is UNMATERIALIZED and UNCOUNTED. Local counts cannot be compared
with the variable counts of completed consistency equations.

`disjointness/` proves a standalone 12-nonnegative-witness, five-equation
asymmetric parity interface of exact degree 504. Its missing binary-base
integration is stated explicitly. The 13-witness degree-368 form is a
separate tradeoff. The general three-Pell method is credited to JSWW (1976).

## Offline reproduction

Requires Python 3 and SymPy (tested with 1.14.0); the other checkers use only
the standard library. From this directory:

    python verify.py
    python negative_controls.py

The verifier authenticates the file manifest and retained source hashes,
copies the release into a temporary directory, executes ONLY authored
checkers/builders, and compares generated outputs byte for byte. Incoming
programs are inert; no incoming code is imported or executed. Some inherited
proofs refer to transitive repository imports; they are not represented as
newly self-contained proof-assistant derivations.

To rebuild the report on a TeX Live system:

    bash report/build.sh

No repository is modified. The checks establish finite identities,
regressions and reproducibility, not universal arithmetic proofs. No global
minimality or decision of ZFC consistency is asserted.
