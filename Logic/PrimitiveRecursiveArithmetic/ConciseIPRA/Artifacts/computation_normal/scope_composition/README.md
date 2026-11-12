# Scope reuse in the strict iPRA checker

This package contains a small implementation improvement of the existing
native scalar iPRA calculus. It composes two existing validation ideas and
stores only the Boolean syntax mode that remains necessary.

* `code/checker.py`: complete new standalone checker, 860 normalized bytes.
* `PROOF.md`: exact success-set preservation proof and comparison.
* `reference/typed870.py`: exact pinned complete control.
* `reference/scope881.py`: exact pinned source of scope reuse.
* `reference/compact516.py`: exact compact frontier, a different contract.
* `reference/zero_normal3095.py`: exact readable six-rule zero-normal source.
* `reference/zero_normal3029.py`: fair ergonomic refinement of that source;
  computation certificates are the terms being evaluated. This is a derived
  control, not an exact upstream copy.
* `reference/LICENSE-ProveIt.txt`: inherited MIT No Attribution license.
* `evidence/provenance.json`: pinned paths, Git blob hashes, and derived edits.
* `evidence/metrics.json`: all complete-module counts, including gzip level 9.
* `tests/cases.json`, `reproduce.py`: portable checks and measurement code.

Run `python3 reproduce.py` with Python 3.12 to reproduce the measurement and
verification. Run `python3 code/checker.py < certificate.json` to check a proof.
Acceptance means normal exit and exactly `ACCEPT` followed by a newline.

Baseline repository commit:
`d9383325b18d349b8bfdc54ef564c5784cc029ec`.

No new arithmetic or logical axiom deletion, absolute minimum, or new
proof-assistant verification is claimed for this implementation composition.
