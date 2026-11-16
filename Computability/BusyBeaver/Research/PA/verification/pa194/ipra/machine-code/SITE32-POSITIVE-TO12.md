# Site-32 positive branch to dense state 12

`PA194Site32PositiveReturnFile.returnFile` composes the positive decision and eight-slot return with the exact updated-file identity. `PA194Site32PositiveReturned.positiveReturned` connects that subrun to the pinned site-32 physical entry when logical register 6 is a successor. `PA194Site32PositiveTo12.positiveTo12` continues the positive return to dense state 12, retaining the source file with register 6 decremented, every other register and the complete arbitrary physical suffix. The total physical clock is existentially quantified; the earlier subsegment has an explicit clock.

These all-PRA-model physical prefixes do not yet establish the site-33 frame, a matched source/physical transition, or complete simulation.

A fresh incremental replay passed with exit 0 and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-positive-returned.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-positive-to12-replay
```

Use a fresh output directory. The checker rebuilds the three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audits, and records source, direct object/companion and upstream receipt hashes. Prior physical and general foundation stages remain prebuilt; their complete transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
