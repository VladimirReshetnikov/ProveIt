# Development notes

The first generic proof attempt failed at the base-case disjunction:
`Tactic failure: Cannot solve this goal`. Explicitly reducing `Nat.add`
and `Allows` fixed the issue. The second attempt failed at the selector
length conversion: `Not convertible`. An explicit list-length arithmetic
rewrite, proved by `lia`, closed it. The subsequent generic source check
passed. The numeric counter adapter and indexed corollary then compiled.

The final `build.py` run is a fresh compilation from copies of the final
sources, followed by recursive `coqchk`; its raw logs and exact source
hashes are in `verification/receipt.json`. These notes describe earlier
interactive failures and do not purport to be their raw log files.

The first exact production adapter build compiled all dependencies and
its command/exec bridge, then failed because `growG` was not re-exported
by the imported compiler. Adding the explicit `Codes222` import fixed
this. The complete second build, including recursive `coqchk`, passed;
the failed and successful production receipts are both retained.
