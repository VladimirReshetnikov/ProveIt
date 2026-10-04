# Frozen Jacobi addendum packet

Read `JACOBI-ADDENDUM.md` and `INDEPENDENT-AUDIT.md` first. This independently audited extension proves a cheap fixed-modulus exclusion test and infinitely many genuine reduced candidates that fail the main congruence. Full child-zero existence and global sign restoration remain open.

The entire previously frozen family packet is copied unchanged under `inherited-family/`, including the inherited Report37 theorem and source evidence. `context/` records the root proposal and its historical arithmetic receipt. The new proof supersedes only the earlier stage's unresolved-miss status; no old file was altered.

From this directory, run:

    python3 check_jacobi_addendum.py --expect expected_jacobi_receipt.json
    python3 -O check_jacobi_addendum.py --expect expected_jacobi_receipt.json
    python3 inherited-family/check_unwrapped_family.py --expect inherited-family/expected_check_results.json
    python3 -O inherited-family/check_unwrapped_family.py --expect inherited-family/expected_check_results.json
    python3 inherited-family/independent/check_audit.py --expect inherited-family/independent/expected_audit_receipt.json
    python3 -O inherited-family/independent/check_audit.py --expect inherited-family/independent/expected_audit_receipt.json

The fresh Jacobi checker needs only Python's standard library. The inherited independent checker requires SymPy 1.14.0 as specified in `inherited-family/requirements.txt`. All default outputs are deterministic JSON on stdout. The new checker can create a fresh receipt with `--output` at a path outside this packet; it rejects existing destinations and in-packet destinations. It never executes upstream source or saved schedules.

`MANIFEST.sha256` freezes every packet file except itself. `release_checks.json` records isolated normal/-O replays and safety/relocation checks; these are reproducibility checks, not a replacement for the mathematical proof.
