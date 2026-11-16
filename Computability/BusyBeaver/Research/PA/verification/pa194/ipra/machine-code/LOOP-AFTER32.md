# Matched model-length loop through both site-32 branches

`PA194MatchedLoopAfter32.matched` composes the existing matched site-27 model-length loop and site-31 increment with the exhaustive site-32 source/physical transition. For every PRA-model input it reaches either the matching site-34 frames when the post-loop register 6 is zero, or matching site-33 frames with register 6 decremented when it is a successor. The other registers, full physical suffix and independent controller tail remain arbitrary. Physical times are existentially quantified.

`PA194MatchedLoopTo33Positive.matched` separately states the positive composition under the explicit initial-value condition `r 6 + r 0 = m+1`. The zero composition has already been staged separately. These are all-PRA-model results, not native iPRA sentences for these compositions, a complete physical simulation, or either consistency implication.

A fresh incremental replay passed with exit 0, both axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-loop-to33-positive.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-loop-after32-repo-baseline-replay
```

Use a fresh output directory. The checker rebuilds both modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier machine and general foundation stages remain prebuilt, and this incremental replay does not independently authenticate their full transitive object closures. The fetch machine-object root is excluded from Lean's search path.
