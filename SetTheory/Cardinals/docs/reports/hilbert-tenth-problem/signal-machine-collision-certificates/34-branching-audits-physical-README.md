# Reproduce the independent branching audit

This dossier audits the frozen `five-signal-branching64-20261004` packet. Start with `AUDIT.md` for the result and limits. `audit-results.json` is the exact static output, not a physical simulation log.

## Files

- `AUDIT.md`: independent source-bound mathematical review
- `audit_static.py`: new standard-library rational checker, independently authored and inspected before execution
- `audit-results.json`: final successful static output
- `source-inventory-before.json`: frozen content hashes and metadata recorded before substantive inspection
- `source-inventory-after.json`: final metadata and hash comparison
- `DOSSIER_MANIFEST.json`: SHA-256 binding for this audit dossier

## Run safely

1. Use Python 3.9 or later on Linux, under the owner of the source files or with existing permission to use `O_NOATIME`. No Python packages need installation.
2. Inspect `audit_static.py`. It loads no code from the packet. It prints JSON only, and opens source files read-only without access-time updates.
3. From any directory, run:

   `python3 -I /path/to/dossier/audit_static.py /path/to/five-signal-branching64-20261004 > /path/outside/the/frozen/packet/recheck.json`

4. Success is process exit code zero and `assertions_passed` equal to 4424. The output pins all six source files and reports unchanged content-file metadata. Compare the output's `audit_checker_sha256` with this dossier manifest. The actual command run here used `python -I` with the same arguments.

The checker deliberately refuses systems without `O_NOATIME`; do not weaken that safeguard against the originals. On macOS or Windows, use a Linux environment with an expendable copied packet, or review the portable standard-library algebra and expressly adapt only the inert-file reader on a copy. This preserves the original source while avoiding a false claim that ordinary reads leave access times unchanged. The mathematical checks themselves have no platform-specific dependency.

The independent checker verifies static declared rows. It does not run the packet's `static_algebra.py`, execute a counter program, ask which collision comes next, or evolve a live configuration. Do not run the author checker to reproduce this audit: it writes into the author's evidence file and is outside this audit's execution boundary.

## What a pass means

A pass checks rational identities and strict finite inequalities for the two forward/reverse words, both arithmetic updates and the two transfers; local-only label changes; source hashes; 56 primitive rules; and static assembly of a representative 118-rule table. It does not replace the mathematical proof of exact chambers, all-counter coverage, arbitrary fixed-program compilation, no accumulation, or historical scope. Those arguments and the source references are in `AUDIT.md`.
