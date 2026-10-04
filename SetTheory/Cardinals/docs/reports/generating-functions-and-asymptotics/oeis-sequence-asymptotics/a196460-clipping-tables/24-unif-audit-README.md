# Independent growing-sector audit

Verdict: PASS. Read `AUDIT.md` for the full analytic review, domains, proof checks, evidence scope, and preservation qualifications.

- `check_mathematics.py`: newly authored independent integer/rational checks through n=160 and rigorous rational exponential enclosures
- `check_algebra.py`: newly authored symbolic polynomial and geometric-series checks
- `check_integrity.py`: read-only full manifest/archive authentication and 333-object input preservation
- `seal_audit.py`: local manifest, read-only modes, archive verification and receipt
- `evidence/`: completed results, logs and input inventories

The source inputs were never executed or modified. To repeat just the portable mathematics checks, copy the two mathematical checker files to a fresh directory, create an empty `evidence` directory, and run them with ordinary Python 3 without optimization. Both refuse to overwrite their JSON result. The integrity checker instead expects the five named packets and earlier article release at the paths declared in its source; it is not a general portability interface.

The adjacent archive contains the complete dossier and its manifest. Its adjacent receipt pins the audit, manifest, archive and input-preservation result. Read-only delivery is an integrity convention, not WORM storage or external timestamping. This audit proves no growing-order logarithmic/inverse result and makes no priority claim.
