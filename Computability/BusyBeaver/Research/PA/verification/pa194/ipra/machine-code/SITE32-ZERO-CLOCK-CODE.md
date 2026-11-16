# Primitive-recursive clock for the site-32 zero exit

`PA194Site32ZeroClockCode.clockCode : Code 12` represents the exact zero-branch clock. `modelClock` proves its interpretation equals `PA194Site32ZeroTo24Exact.clock` in every PRA model. `PA194Site32CodedZero.zeroPath` puts this code directly into the literal stepper theorem from the site-32 physical frame to the site-34 physical frame when logical register 6 is zero. Its first input is the gap parameter and the other eleven are the full logical register file including its arbitrary suffix slot. The file and suffix are preserved, and the gap changes from `k+2` to `k+3`.

This is a coded physical instruction theorem in every PRA model. The combined restore orbit and exit, its native iPRA statement, full physical/source simulation and the consistency equivalence remain to be proved.

A fresh staged source replay passed with exit 0, both final axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-clock-code.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-exact-repo /dev/shm/pa194-site32-clock-code-repo /dev/shm/pa194-site32-positive-exact-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-clock-code-repo
```

Use a fresh output directory. The checker rebuilds two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
