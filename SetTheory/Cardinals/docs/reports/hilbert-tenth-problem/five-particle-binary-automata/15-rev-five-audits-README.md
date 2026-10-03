# Independent executable audits

The tests here are independently written implementations of the stated checks. They are finite regression evidence and human-readable proof review, not proof-assistant formalizations.

## Reversible compiler

`audit_api.py` runs ten suites, both normally and under Python optimization. Per run: 27,412 systematic source/image checks, 4,448 home semantics checks, 1,080 isolated-gate oracle inputs, 835 malformed finite inputs with both inverse identities and conservation. It tests runtime schema/numeric validation and immutable snapshots.

The original audited compiler is included exactly once, as `compiler/reversible_binary.py`. Its SHA256 is f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f. The original independent auditor had SHA256 d7a65937b271d6b2f21cf542007b7804c6ffbcb443bf6adec9d5fc92818868c4. In the portable copy only its default compiler path and its receipt's module-name metadata were adapted; no test or mathematical logic was changed.

## Fixed-horizon certificates

`audit_certificate.py` runs six suites normally and with optimization: 384 variants, 7,008 residual rows, 43,318 expanded coefficients, 6,274 bounded complete witness tuples and 556 single-coordinate witness mutations. It also validates the cleanup example and the paid-real selector-norm requirement.

The audited emitter is included exactly once, as `certificates/certificate.py`. Its SHA256 is 07241d3bc43c9fddf24665b8c91c628e64f3c8e865b891cd1d6f31c3cf04f296. The original auditor had SHA256 b797f3a2c6749f8482f592d29c754799f5f800d6473500a99a3883bb7afcdfdc. Only default relative paths and module-name receipt metadata were adapted for this archive.

An earlier immutable-record implementation allowed a second explicit initialization to mutate retained source records. This was fixed before release; the audit explicitly verifies rejection of Branch, Machine, CellBranch and Certificate reinitialization before any mutation. Source JSON and deep/cyclic Boolean AST behavior were also aligned with the strict shared schema. The final algebraic formulas and counts passed independent comparison.

## How to replay

Run `python replay.py` from the release root. It copies the package to a temporary directory, executes all tests there, compares fresh fixtures, and prints a short receipt. Optimization runs are limited to suites whose checks do not disappear under `-O`. The ring, geometric and producer trace tests run normally with assertions active. No network or nonstandard Python modules are needed.

The two independent raw-fixture checkers retain their mathematical logic unchanged; only their generated receipt destination was changed from the development audit directory to the relative `compiler/checks` directory.
