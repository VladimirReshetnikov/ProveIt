# Site-31 physical restore orbit and zero exit

`PA194RestorePhysicalExit.completeExit` proves in every PRA model that the literal machine executes the entire site-31→32→33→31 restore loop for the initial register-6 value, then the final site-31 increment and the site-32 zero branch, arriving at the site-34 physical frame. Its single stepper call uses the explicit sum of the PR-coded orbit time, final increment time and zero-branch time. The output has register 6 zero, register 0 increased by the initial register 6 plus one, the gap increased by the initial register 6, the repeated-spare count increased by that value plus one, and all other registers, the spare value and independent controller tail retained. The model-length repeated-spare suffix ends in blank tape. The initial gap is `k+3`.

This is an all-PRA-model physical run through the complete restore operation and zero exit. The combined native iPRA sentence, full machine/source simulation, and either consistency implication remain separate.

A fresh staged source replay passed with exit 0, the final axiom audit and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-restore-physical-exit.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-clock-code-repo /dev/shm/pa194-site32-zero-exact-repo /dev/shm/pa194-site31-restore-physical-orbit-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-restore-physical-exit-repo
```

Use a fresh output directory. The checker rebuilds one module, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
