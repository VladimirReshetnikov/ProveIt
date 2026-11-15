# Site-34 physical selected-register decision

`PA194Site34To4.to4` proves in every PRA model that the literal PA194 machine reaches physical state 4 from a site-34 frame with gap `k+2`, using an exact PR arithmetic clock. The selected unary block is physical slot 1, which is logical register 8, and the exact marker/left tape, complete residual file and arbitrary suffix are retained. `PA194Site34Branch.zeroTo5` and `positiveTo6` check the two actual physical decision transitions under, respectively, register 8 = 0 and register 8 = m+1, with a common explicit clock.

These are intermediate physical states 5 and 6. Returning to the source-frame destinations 42 and 35 and proving the complete site-34 source/physical branch matches remain open, as do the complete decoder, native iPRA transfer, global simulation and consistency equivalence.

A fresh staged source replay passed with exit 0, six axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site34-branch.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site34-second-pass-repo /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-branch-repo
```

Use a fresh output directory. The checker rebuilds five modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires each named axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
