# Site-32 zero controller/physical transition

`PA194SourceSite32ZeroPhysical.zeroBranch` proves in every PRA model that if logical register 6 is zero, the actual encoded source controller takes its site-32 zero branch to site 34 and the pinned physical machine runs from the matching site-32 frame to the site-34 frame. All other model-valued registers, the complete physical suffix and the separate controller tail are arbitrary and preserved. The numeric gap changes from `(k+1)+1` to `((k+1)+1)+1`, reflecting the one-bit shorter site-34 path. The physical execution clock is existentially quantified.

The proof completes the state-14-to-root execution, kernel-checks the actual site-34 path and identifies the exact returned word with its frame. It is one source instruction's zero branch; it does not prove the positive branch, a native iPRA sentence for this transition, full machine simulation, or either consistency implication.

A fresh staged replay passed with exit 0, the final axiom audit and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-physical.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-physical-replay
```

Use a fresh output directory. The checker rebuilds all seven new modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audit, and records source, direct object/companion and upstream receipt hashes. The earlier physical, controller and general foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
