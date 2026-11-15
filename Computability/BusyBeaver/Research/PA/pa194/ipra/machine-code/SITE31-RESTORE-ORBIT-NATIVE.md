# Native iPRA physical restore orbit

`PA194RestorePhysicalOrbitSentence.nativeIPRA` proves in the repository's exact `IPRAStandardTheory.standardTheory` the universal closure of an equality between explicit PR terms. The left term runs the literal PA194 stepper at the PR cumulative time for exactly the initial register-6 value of site-31→32→33→31 iterations. The right term is the site-31 physical frame after the loop: register 0 increased by that initial value, register 6 reduced to zero, gap and repeated-spare count increased by that value, and all other registers and the independent spare retained. The 13 inputs are source registers 0–8, the independent controller tail, the initial gap parameter, the model-length repeated-spare count and the spare value. The repeated-spare suffix ends in blank tape.

`modelSentence` establishes the explicit equality in every PRA model, `classicalPRA` transfers it to classical PRA, and `nativeIPRA` uses the existing equality transfer. The conclusion covers the physical loop before its subsequent site-32 zero exit; it is not yet a full physical/source simulation or a consistency implication.

A fresh staged source replay passed with exit 0, the complete-loop and three sentence axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-restore-orbit-native.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-restore-physical-orbit-repo /dev/shm/pa194-site31-fully-coded-repo /dev/shm/pa194-site31-restore-iteration-repo /dev/shm/pa194-site31-transfer-loop-repo \
  /dev/shm/pa194-site31-coded-loop-repo /dev/shm/pa194-site31-coded-clock-repo /dev/shm/pa194-site31-native-repo /dev/shm/pa194-site32-clock-code-repo /dev/shm/pa194-site32-positive-exact-repo \
  /dev/shm/pa194-site33-jump-repo /dev/shm/pa194-site32-both-physical-repo \
  /dev/shm/pa194-site32-positive-to12-repo /dev/shm/pa194-site32-positive-return-repo \
  /dev/shm/pa194-site32-zero-physical-repo /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-restore-orbit-native-repo
```

Use a fresh output directory. The checker rebuilds two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the four axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
