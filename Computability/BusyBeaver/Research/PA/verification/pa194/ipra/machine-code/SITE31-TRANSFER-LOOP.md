# Matched site-31/32/33 transfer-loop step

`PA194SourceSite31TransferLoop.oneLoop` proves one actual source/controller and physical loop 31→32→33→31 in every PRA model. When logical register 6 is `m+1`, it increments register 0, decrements register 6 to `m`, retains every other register and the independent controller tail, and adds one one-spare to the model-length physical suffix. The physical gap increases by one. The input suffix is an arbitrary model-length one-spare sequence ending in blank tape, and the independent spare value is arbitrary.

The site-31 physical segment has its explicit nested clock, the site-32 positive segment supplies an existential physical clock, and the site-33 jump takes exactly 34 steps. The theorem is one model-uniform loop step; it does not yet prove model-length iteration of this loop, a native iPRA sentence for that iteration, full physical simulation, or either consistency implication.

A fresh incremental source replay passed with exit 0, the final axiom audit, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-transfer-loop.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-transfer-loop-replay
```

Use a fresh output directory. The checker rebuilds the composition, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
