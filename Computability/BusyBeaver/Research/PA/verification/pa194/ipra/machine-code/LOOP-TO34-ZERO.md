# Matched model-length loop through the site-32 zero branch

`PA194MatchedLoopTo34Zero.matched` composes the existing matched site-27 model-length loop and site-31 increment with the newly proved site-32 zero source/physical transition. For arbitrary PRA-model registers, controller tail, gap, spare count and spare, it assumes `r 6 + r 0 = 0`; this is exactly the zero condition on logical register 6 after `r 0` loop iterations. The theorem proves that the actual encoded controller and the pinned literal machine reach matching site-34 frames with the same complete file and suffix. It gives two existential physical times for the loop/exit and site-32 transition, with the intermediate site-31 segment's explicit nested clock.

This is a conditional all-PRA-model composition. It does not prove the site-32 positive branch, a native iPRA sentence for this composition, the complete physical simulation, or an implication involving Con(PA).

A fresh incremental replay passed with exit 0, the axiom audit and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-loop-to34-zero.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-physical-repo /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-loop34-zero-replay
```

Use a fresh output directory. The checker rebuilds the composition, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the axiom audit, and records source, direct object/companion and upstream receipt hashes. The earlier machine and foundation stages remain prebuilt; their complete transitive closures are not independently authenticated in this replay. The fetch machine-object root is excluded from Lean's search path.
