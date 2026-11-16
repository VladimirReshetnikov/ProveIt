# Both site-32 controller/physical branches

`PA194SourceSite32PositivePhysical.positiveBranch` proves in every PRA model that when logical register 6 is `m+1`, the actual encoded source controller takes its positive site-32 branch to site 33 and the pinned physical machine reaches the matching site-33 frame with that register set to `m`. All other registers, the complete physical suffix and the independent controller tail are arbitrary and preserved. The numeric gap changes from `(k+1)+1` to `((k+1)+1)+1`.

`PA194SourceSite32BothPhysical.bothBranches` combines this theorem with the previously staged site-32 zero branch to site 34, using model zero-or-successor exhaustiveness. It gives the appropriate actual controller step and matching physical frame for every PRA-model input, with an existential physical clock. The two branch destinations and corresponding file values are explicit.

This establishes both cases of one source instruction in all PRA models. It does not yet internalize this step as a native iPRA sentence, prove a complete physical simulation, or prove either consistency implication.

A fresh staged replay passed with exit 0, both final axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-positive-physical.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-positive-to12-repo /dev/shm/pa194-site32-positive-return-repo \
  /dev/shm/pa194-site32-zero-physical-repo /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-both-physical-replay
```

Use a fresh output directory. The checker rebuilds seven modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both final axiom audits, and records source, direct object/companion and upstream receipt hashes. The earlier machine and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
