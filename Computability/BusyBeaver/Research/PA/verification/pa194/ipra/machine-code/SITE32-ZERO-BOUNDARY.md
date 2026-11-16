# Site-32 zero branch to the dense header boundary

`PA194Site32ZeroRollback.zeroRollback` composes the pinned site-32 physical entry with the zero decision and nine-slot rollback, restoring the entire original source-file code under logical register 6 = 0. `PA194Site32ZeroToBoundary.zeroToBoundary` follows the model-length rollback scan to the dense state-11 header boundary, with an explicit endpoint and existential clock. All other model-valued registers and the full physical suffix remain arbitrary.

This is an all-PRA-model physical prefix; the source-site-34 physical frame and complete source/physical transition remain open. The exact clock of the earlier state-4 prefix and the rollback subsegment are separately available, but this composition currently existentially quantifies the combined clock.

A fresh incremental replay passed with exit 0 and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-boundary.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-boundary-replay
```

Use a fresh output directory. The checker rebuilds the two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Prior physical and general foundation stages remain prebuilt; their full transitive closures are not independently authenticated here. The fetch machine-object root is excluded from Lean's search path.
