# Model-length physical restore orbit at site 31

`PA194RestorePhysicalOrbit.physicalOrbit` proves in every PRA model a model-length orbit of the literal PA194 physical machine through the site-31→32→33→31 restore loop, for every `steps ≤ register 6`. The cumulative physical time is the explicit PR code `timeCode (PA194ModelTransferState.next PA194ActualRestoreSource.triple) PA194RestorePhysicalCost.cost`. At that time, the physical frame is again at site 31: register 0 has increased by `steps`, register 6 has decreased by `steps`, and both the physical gap and model-length repeated-spare count have increased by `steps`. All other registers, the spare value and the independent controller tail are preserved. The repeated-spare suffix ends in blank tape; its length can be any model value. The initial gap is `k+3`.

The proof combines a kernel-checked actual controller/physical one-step match, a unary PR cost decoded from the packed state, and open induction in PRA over the model-valued iteration count. It assumes no IΣ₁ hypothesis. The source-controller orbit is identified with actual three-instruction triples. The theorem does not yet include the subsequent site-32 zero exit, establish a native iPRA sentence for this orbit, prove full machine/source simulation, or prove a consistency implication.

A fresh staged source replay passed with exit 0, the four final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-restore-physical-orbit.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-restore-physical-orbit-repo
```

Use a fresh output directory. The checker rebuilds four modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
