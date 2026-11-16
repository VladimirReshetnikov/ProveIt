# Matched site-34 positive branch to site 35

`PA194SourceSite34PositivePhysical.positiveBranch` proves for every PRA model that if logical register 8 equals `m+1`, the actual encoded source controller takes site 34→35 and the literal PA194 physical stepper reaches its actual site-35 source frame at an explicit model-valued clock. Both preserve every other register, the entire arbitrary physical suffix, and the independent controller tail. The selected register becomes `m`, and the physical gap remains `k+2`. The source instruction and path-35 identifier are kernel checked. The final 23-step physical return is checked one row at a time, with arbitrary residual tape.

This establishes the complete positive source/physical branch. A primitive-recursive code for the whole clock and native iPRA transfer, the complete decoder, global simulation and the consistency equivalence remain separate.

The sources, in build order, are `PA194Site34PositiveReturn.lean`, `PA194Site34PositiveTo16.lean`, `PA194Site34PositiveFinish.lean`, `PA194Site34PositivePath.lean`, `PA194SourceSite34PositiveController.lean`, and `PA194SourceSite34PositivePhysical.lean`.

The fresh staged replay passed with exit 0. Replay (use a fresh output directory):

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site34-positive-physical.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site34-branch-repo /dev/shm/pa194-site34-second-pass-repo /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-positive-physical-repo
```

The checker rebuilds six modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
