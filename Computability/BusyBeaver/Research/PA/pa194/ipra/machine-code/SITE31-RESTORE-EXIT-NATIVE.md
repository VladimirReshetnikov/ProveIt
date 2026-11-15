# Native iPRA restore orbit and zero exit

`PA194RestorePhysicalExitSentence.nativeIPRA` proves, in the repository's exact `IPRAStandardTheory.standardTheory`, the universally closed equality of two explicit PR terms. The left term runs the literal PA194 stepper at the sum of the PR-coded model-length restore orbit, final site-31 increment and site-32 zero-branch clocks. The right term is the resulting site-34 physical frame: register 6 is zero, register 0 increased by the initial register 6 plus one, the gap increased by the initial register 6 and the repeated-spare count by that value plus one. The remaining registers, the independent spare and controller tail are preserved. The 13 inputs are source registers 0–8, controller tail, initial gap parameter, repeated-spare count and spare. The model-length repeated-spare suffix ends in blank tape; the initial physical gap is the supplied gap parameter plus three.

`modelSentence` establishes the equation in every PRA model, `classicalPRA` transfers it to classical PRA, and `nativeIPRA` uses the existing equality transfer. This theorem establishes the complete physical restore operation through its zero exit; full machine/source simulation and the Con(PA) equivalence remain separate.

A fresh staged source replay passed with exit 0, all five requested axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-restore-exit-native.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-restore-physical-exit-repo /dev/shm/pa194-site32-zero-clock-code-repo /dev/shm/pa194-site32-zero-exact-repo /dev/shm/pa194-site31-restore-physical-orbit-repo \
  /dev/shm/pa194-site31-fully-coded-repo /dev/shm/pa194-site31-restore-iteration-repo /dev/shm/pa194-site31-transfer-loop-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-restore-exit-native-repo
```

Use a fresh output directory. The checker rebuilds three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
