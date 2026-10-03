# Direct primitive certificates

A finite-source-horizon quartic SOS family using original primitive row selectors, shifted postcounters, and two shared positive-test offsets per step. It accepts the frozen literal reversible source without allocating normalized branch/cell copies or a giant horizon-one polynomial.

## Contents and status

- `PROOF.md`: complete natural and paid nonnegative-real fiber proofs, precise domains, raw/expanded cost accounting, literal specialization and conditional periodicity corollaries
- `certificate.py`: standalone immutable indexed implementation, Python 3.10+, standard library only
- `test_certificate.py`: exact-domain, all-coordinate small fiber, arithmetic, ledger, snapshot and bounded-allocation tests
- `example-source.json`, `example-materialized.json`, `example-witness.json`: a fully emitted five-step small example; expanded degree 4 polynomial with 1100 monomials, unique witness, clock 3115
- `test-receipt.json`, `test.log`, `test.optimized.log`: local implementation checks
- `universal-h1-ledger.json`: numerical ledger specialized to clean empty tape START(1,0), nonaccepting horizon 1; no witness or universal polynomial materialized
- `source-ledger-receipt.json`: source audit and symbolic-horizon allocation checks

Core universal counts for K≥1: 141565K witnesses, 23435K+1 squares, 566225K written residual slots. Clock: +1 witness, +1 square; paid real norm: +K squares. Exact full-fiber uniqueness is proved. No fixed unbounded single-fold theorem is claimed.

## Replay

Run from this directory:

    python test_certificate.py
    python -O test_certificate.py
    python audit_source.py ../source/source.json
    python certificate.py ../source/source.json 1 --left 1 --right 0 --clock --real --require-reversible

The relative default and these commands locate the bundled `source/source.json`; an explicit source argument may override that location. The source SHA-256 must be 38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a. Source files outside this directory are read-only dependencies; no command above modifies them.

The CLI defaults to a ledger. `--export-small PATH` is bounded and rejected for the universal table. Explicit all-source polynomial expansion is intentionally not performed. The small sample is fully materialized and verified by the test replay.
