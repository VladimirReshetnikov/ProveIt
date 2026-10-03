# External-output replay revision

The original packet is preserved as
`parallel-diophantine-certificate-research-20261003-v1`.
Its manifest, SHA-256
`dc2106553312d36cbcd655e5e3551e52771682de0a1f7f27e91798561ecf90a0`,
is copied byte-for-byte at `lineage/v1-MANIFEST.json`.
The backup's file/directory modes and nanosecond mtimes were also checked equal.

Only four test scripts' output plumbing changed. Each now accepts optional
`--output-dir`; its default remains the script directory. Fixture inputs and
compiler imports remain adjacent to the source script. All receipt/artifact
writes honor the selected output directory. Audit under `-O` now explicitly
writes `audit-emitter-receipt-optimized.json`. The compiler, arithmetic circuit,
mathematical test logic, fixture data, and concrete polynomial are unchanged.
Before/after script hashes are in `PROVENANCE.json`.

For each script in
`test_certificate.py`, `test_supplement.py`, `test_multisource.py`, `audit_emitter.py`,
run these commands, replacing `<source>` and `<replay>` with their directories:

    python -B <source>/<script> --output-dir <replay>/normal
    python -B -O <source>/<script> --output-dir <replay>/optimized

`verify_example.py` only writes stdout:

    python -B <source>/verify_example.py
    python -B -O <source>/verify_example.py

Use `-B` so Python does not create source-side bytecode caches. Outputs may be
redirected to logs outside the source directory. No dependency or environment
installation is required.

The external evidence reference is
`parallel-diophantine-certificate-replay-20261003`.
It contains normal/optimized receipts and logs, exact per-command wall times,
a read-only whole-source snapshot comparison (bytes, modes, nanosecond mtimes),
and an independent output-routing diff audit. The test runner deliberately
uses an external working directory to exercise script-relative input resolution.

Source receipts/logs retained here are earlier successful evidence. The external
replay receipts are the fresh evidence for these output-plumbing wrappers. Their
mathematical counts and emitted ledgers must agree. The source packet is sealed
before replay and verified unchanged afterward; successful replay requires no
write into it.

## Separate standalone-verifier hardening

In addition to output plumbing, verify_example.py now validates exact artifact
schemas/formats and exact integer arities, rejects Boolean/floating-point
counts, and binds equally sized integer input/target lists to the canonical
natural prefix. test_example_validation.py exercises 37 malformed cases in
both interpreter modes and accepts --output-dir. This changes verification
metadata binding, not compiler/gadget formulas or the polynomial.

    python -B <source>/test_example_validation.py --output-dir <replay>/normal
    python -B -O <source>/test_example_validation.py --output-dir <replay>/optimized
