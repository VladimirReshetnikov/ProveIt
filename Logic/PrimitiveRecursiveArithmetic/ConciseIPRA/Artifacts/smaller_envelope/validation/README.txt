Inferred-major validation
=========================

Run from the package directory:

    python3 validation/validate_inferred.py

The script uses Python's standard library only. It runs the actual complete
programs checkers/ast.py and checkers/tokens.py, and their exact controls in
reference/checkers/, in separate processes. Every verdict comparison is
performed both normally and with Python -O. A checker accepts only when it
exits successfully and prints exactly ACCEPT followed by a newline; an
exception is rejection. Timeouts are recorded as validation failures.

The frozen fixture manifest is fixtures/manifest.json. It records the
repository, pinned commit, original path, SHA-256, declared verdict and
appropriate eigenparameter-scope profile of every inherited fixture. These
fixtures are copied from ProveIt under the accompanying upstream license.
The global token profile uses the original *_global fixtures. The local AST
profile uses the original *_local fixtures and the additional zero-neutral
fixtures. No heuristic global/local variable renaming is performed.

For every positive case with an inferred-major step, the script erases the
supplied major at each such step, retaining its subproof. It writes these
actual new certificates to fixtures/inferred/. It then records a successful
trace of the candidate, replaces the consumed major fields by the majors
actually checked, and writes the resulting old-control certificates to
fixtures/repaired/. Both the new certificates and repaired control
certificates are checked in actual subprocesses. Running the unrepaired
certificates against the controls demonstrates the changed certificate
contract; those results are reported separately from equivalence tests.

Trace observation instruments the candidate's existing functions, removing
only its top-level input/output statements and adding recording calls before
recursive major verification. It is an untrusted exporter, not a second
proof checker. The checker never imports the exporter. The exporter fails
if it does not find the exact intended instrumentation points.

Additional targeted negative certificates are written to fixtures/attacks/:
an inferred false major without a proof, an unallocated future source
parameter, a mismatched endpoint, and a deleted recursive major subproof,
each tested in both scope profiles. The inherited cases additionally cover
future-witness capture, local-context leakage, false equations, incomplete
instructions, incorrect computations and inappropriate introduction modes.

Results:

    evidence/inferred_validation.json   complete process receipts
    evidence/inferred_summary.json      counts, hashes and limitations
    evidence/trace_repair_summary.json  per-certificate repair counts/hashes

The tests are finite implementation evidence. They do not mechanize the
general accepting-trace simulation or the bi-interpretation. Some inherited
fixtures deliberately exercise administrative raw formulas outside the
canonical guarded public language. Their acceptance is not a claim that
these compact programs perform exact syntax validation.
