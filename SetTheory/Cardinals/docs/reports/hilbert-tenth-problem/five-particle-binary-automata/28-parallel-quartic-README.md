# Parallel CA finite-horizon quartic certificate research

A concrete deterministic compiler for the **new parallel two-involution rule**.
Fix a schema-valid source, mass n, horizon T, and direction. The emitted ordinary
integer polynomial has degree at most four and exactly one complete natural
witness for an accepted exact endpoint pair, and no natural witness otherwise.
Canonical external signed pairs and strict sortedness are checked internally.

This is bounded research software and a source-level mathematical audit, not a
proof-assistant verification, an unbounded-time fixed-arity representation, or a
real-witness uniqueness result. It does not claim a practical universal-source
polynomial or an improvement over differently scoped earlier certificates.

## Files

- `compiler.py`: direct source-record/pair/marker/orientation emitter, paid raw
  predicates, fixed bitonic isolation, deterministic lane compaction, full
  hypothetical rediscovery, simultaneous writes, and horizon composition
- `circuit.py`: exact signed/Boolean/comparison gates and quadratic residuals
- `PROOF.md`: all-input semantics, unique natural witnesses, and resource bounds
- `audit-design.md`: earlier independent geometric design analysis; its quadratic
  isolation estimate is superseded by the concrete bitonic network
- `audit-emitter.md`: independent final code audit and finite audit evidence
- `resource-ledger.json`: exact emitted sizes, sparse-residual coefficient costs,
  and exact expanded pair-example coefficient costs
- `example-source.json`, `example-pair-sos.json`, `example-pair-quartic.json`,
  `example-pair-witness.json`: concrete source, residual system, fully expanded
  ordinary quartic, and accepted witness for X={0,5}, Y={1,6}, n=2, T=1
- `verify_example.py`: independent parser/expansion/evaluation check without
  importing the compiler, including schema/arity/input-metadata binding and every upward witness-coordinate mutation
- `test_example_validation.py`: 37 negative schema/arity/metadata binding cases
- `fixtures.json`: independent pinned-oracle snapshots and finite-domain cases
- `test_certificate.py`, `test_supplement.py`, `test_multisource.py`: regression
  and witness-binding checks, with exact normal/optimized receipts and logs
- `audit_emitter.py`: independent raw, descriptor, sorting, and compaction checks
- `references/`: byte-identical prior mathematical/source-schema dependencies
- `PROVENANCE.json`, `MANIFEST.json`, `verify_bundle.py`: dependency provenance and
  reproducibility/integrity checks

## Run

Python standard library only. From this directory:

    python -B verify_bundle.py
    python -B verify_example.py
    python -B -O verify_example.py
    python -B test_certificate.py
    python -B -O test_certificate.py
    python -B test_supplement.py
    python -B -O test_supplement.py
    python -B test_multisource.py
    python -B -O test_multisource.py
    python -B audit_emitter.py

The larger n=5 whole-step certificate is intentionally not serialized as one
expanded polynomial. Its actual emitted residual counts are measured in tests;
its fixed compiler regenerates all residuals. The fully expanded concrete pair
example is small enough to inspect and independently evaluate.

## External replay without source writes

The four regression/audit runners accept `--output-dir`. Inputs always remain
rooted adjacent to the scripts. For example, from any working directory:

    python -B <source>/test_certificate.py --output-dir <replay>/normal
    python -B -O <source>/test_certificate.py --output-dir <replay>/optimized

The same option is supported by test_supplement.py, test_multisource.py, and
audit_emitter.py. The optimized audit writes audit-emitter-receipt-optimized.json.
Use -B to suppress Python bytecode writes. verify_example.py is stdout-only.
The sealed pre-revision manifest is retained in lineage/v1-MANIFEST.json.
See REPLAY.md for the replay protocol and external evidence reference.

## API and acceptance

    from compiler import Certificate
    cert = Certificate(source_data, n=2, T=1, inverse=False)
    natural_assignment = cert.witness([0,5], [1,6])
    residuals = cert.circuit.rows
    polynomial = cert.polynomial()

`witness` checks every residual by default and raises on a rejected endpoint.
`witness(...,check=False)` and `result(x)` are **unchecked diagnostic helpers**;
calling them is not acceptance or input validation. The definitive acceptance
condition is that all assigned variables are natural and every residual is zero
(equivalently, the emitted quartic is zero). Verification of a supplied algebraic
assignment does not require trusting the witness evaluator.

`serialize()` emits the explicit finite SOS syntax. `polynomial()` combines like
terms into the ordinary sparse integer polynomial and may consume much more
memory. Variable indices 0 through 4n-1 are external x/y signed pairs; all later
indices are the complete witness. Each signed pair is plus,minus in coordinate
order, with all x coordinates first and then all y coordinates.

## Important measured example

For the one-increment source m=2,p=1,a=0,J=0, T=1:

| n | Witnesses W | Residuals M | All polynomial variables 4n+W |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | 0 | 3 | 4 |
| 2 | 1,494 | 1,502 | 1,502 |
| 3 | 47,080 | 47,093 | 47,092 |
| 5 | 784,928 | 784,951 | 784,948 |

The expanded n=2 example has 12,595 nonzero monomials, degree 4, 29,413 total
coefficient-magnitude bits, maximum coefficient bit length 23, and 220,969
serialized bytes. These are concrete implementation costs, not minimality claims.
A counts signed assignment registers, rather than uniformly bounded-fan-in
arithmetic additions; the full residual-monomial and coefficient ledgers are
part of every cost statement.

The five-particle malformed cascade is particularly important: X={-118,-112,0,18,23}
is fixed by the new rule, while its old ordered image {-119,-113,0,19,24} is
rejected. Each block has a genuine isolated raw key that fails prospective
rediscovery because the hypothetical swap creates a different nearby key.

No frozen dependency source was modified. No upstream repository was run,
no package was installed, and no material was published or uploaded.
