# Matrix factorization fibers

A focused, self-contained verification supplement for the fixed 229-generator
matrix construction. `PROOF.md` proves the exact accepting-target witness
counts, infinite unbounded fibers, rational generating function, exact
quasipolynomial, support, and counting asymptotics. The original matrix
construction and paired polynomial interface are unchanged.

The exact formula applies to a well-formed live configuration whose U15 run
halts, including all accepted main-interface tape inputs. Simple infinitude
also holds for any accepted word target, even malformed words. The separate
zero-step target X has generating function 1/(1-z^2). Counting is of generator
factorization words, equivalently canonical paired polynomial roots at each
fixed inner length, and never of distinct resulting matrices.

## Replay

Python 3 with the standard library is sufficient. From this directory:

    sha256sum -c SHA256SUMS
    python check_fibers.py > normal-run.json
    python -O check_fibers.py > optimized-run.json
    cmp normal-run.json optimized-run.json
    python audit/independent_check.py > audit/normal.json
    python -O audit/independent_check.py > audit/optimized.json
    cmp audit/normal.json audit/optimized.json

The first checker also writes `CHECKS.json`. All commands are portable;
there are no network requests, absolute source paths, or imports of earlier
compiler code. The two copied input JSON files are hash-checked before use.
The independent checker pins the matrix/tile JSON, its only input.

## Inputs and receipts

`data/semigroup.json` and `data/accepting-witness.json` are byte-for-byte
copies of the fixed matrix source's literal semigroup and accepting witness.
Their hashes and roles are recorded in `MANIFEST.json`; only data are reused.

`CHECKS.json`, `normal-run.json`, and `optimized-run.json` share one schema:
`cases` lists each word's graph size, genuine history count, machine/cleanup
parameters, minimum inner length, loop weights, degree, checked coefficient
range, sample coefficients, collision checks, and literal-matrix/canonical-SOS
sample results. Top-level totals include 33,544 distinct bounded stutter
witnesses and 12 independently evaluated matrix/SOS samples. `zero_step_X_GF`
and its checked range record the empty-history boundary case.

`audit/normal.json` and `audit/optimized.json` share the independent receipt
schema: `status`, `cases`, `coefficient_comparisons`, `actual_tape_example`,
`max_cleanup_paths`, and `method`. They record 226 accepted fixtures and
31,366 exact coefficient comparisons. `audit/REVIEW.md` records the
independent mathematical review and the checker's provenance.

Finite replay checks supplement the proof and do not decide nonhalting
inputs. The results make no claim of novelty or of a uniform, fixed-arity
unbounded Diophantine representation.
