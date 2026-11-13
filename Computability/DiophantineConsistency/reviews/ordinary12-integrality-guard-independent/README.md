# Independent review of the optimized-mode guard

Commit `c7f744b053` corrects the assert-elision issue described in the
[descent review](../ordinary12-integrality-descent-independent/README.md).
The review checker retrieves the parent and fixed files from Git and pins
their full SHA-256 hashes. It verifies that the only checker change is the
new `if not __debug__` guard placed after imports and before the class,
polynomial identities, and bounded checks. The only documentation change is
the appended note; the third changed file records the author's observed exits.

In fresh processes the fixed checker produced these observed results:

| Invocation | Exit | Result |
|---|---:|---|
| Normal Python | 0 | All five original identity checks and the bounded survey report PASS |
| `python -O` | 1 | Rejects optimized Python before the checks |
| `python -OO` | 1 | Rejects optimized Python before the checks |
| `PYTHONOPTIMIZE=1` | 1 | Rejects optimized Python before the checks |

The guard failures print no PASS output. A temporary copy with an appended
false assertion exits 1 in normal mode, confirming assertions remain active
there. The review checker itself uses explicit exceptions and exited 0 in
both normal and optimized mode. Full outputs and process exits are in
`CHECK.json`.

This reviews the finite checker's guard. It does not prove the unbounded
descent, model-level graph transport, fixed-port calibration, or an iPRA
derivation; those boundaries remain as stated in the original review.

Run from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/reviews/ordinary12-integrality-guard-independent/check.py
python3 -B -O Computability/DiophantineConsistency/reviews/ordinary12-integrality-guard-independent/check.py
```

The historical Git commit must be available locally.
