# Pending independent artifact audit of the fresh current14 base

[`audit.py`](audit.py) is a read-only, fail-closed terminal audit prepared
while the current 1,000-module project build is still running. The observed
[preterminal refusal](preterminal-refusal.json) confirms it exited 1 without
creating a success receipt when the watchdog was `RUNNING`. **It has not
validated a successful base** and no completion is implied here.

If the watchdog reports a successful terminal exit, the script is designed
to rehash all 1,000 frozen and current sources, recorded objects and logs,
recorded direct-input and companion guards, the Foundation inventory and
declared external guards; it also compares the four exact target axiom names
and reports with the target log and ledger. It checks source tracking and
current HEAD, and verifies the watchdog's recorded base-state digest. The
actual outer tool-session exit must be observed separately. A passing result
would be a single-build artifact audit, not a second Lean replay or full
package-transitive, dynamic-loading or transient-mutation authentication.

After an actual successful terminal observation, and only while the captured
paths remain available, run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-fresh-base-independent/audit.py
```

The script refuses to overwrite `receipt.json`. Its success path has not yet
run and may require correction if it encounters an unanticipated valid
record shape; any failure must be retained and investigated rather than
presented as an audit pass. Script SHA-256:
`2ff22e3a0b0116d1a609d49f5983b5a9c15a61339277583c244ed4f624591820`.
