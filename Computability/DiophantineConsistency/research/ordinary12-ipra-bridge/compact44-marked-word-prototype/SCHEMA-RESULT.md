# Matching parent receipt-schema correction

The original marked-word driver `9e44ca5cef` and inverse driver `b929bbb5c0` incorrectly expected `observed_exit` and `receipt_sha256` in the independently audited matching parent's terminal observation. The actual pinned observation records `independent_parent_rerun_exit`, `independent_review_exit`, `check_sha256`, and `lean_launched`. No paired Lean replay was launched with the original drivers.

`schema-controls.py`, run with `python3 -I -S -B`, exited 0 without launching Lean. It reconstructed both original committed drivers and observed that their actual pinned preflight rejected the matching audit observation. It then ran the corrected `pins()` for each driver successfully and exercised 12 missing, conflicting, or boolean-as-exit negative cases per driver, all rejected. `SCHEMA-CONTROLS.json` retains its output. This is a local schema check, not independent review or the full audit replay.

Both corrected drivers require exact integer-zero parent rerun and independent review exits, the pinned check hash, explicit `lean_launched: false`, and the expected parent status. Their existing full-JSON before/after parent-audit checks remain. Independent prelaunch review is required before either real paired build.
