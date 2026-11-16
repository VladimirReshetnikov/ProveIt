# Site-32 zero branch with an exact model clock

`PA194Site32ZeroPathExact.zeroPath` proves in every PRA model that the literal machine reaches the site-34 physical frame from the site-32 frame when logical register 6 is zero. Its explicit clock is `PA194Site32ZeroTo24Exact.clock k args`; the complete register file and arbitrary suffix are preserved, and the gap changes from `k+2` to `k+3`. The six new modules expose the exact rollback and header costs and compose them with the previously checked exact state-4 prefix.

This theorem covers one physical zero branch in every PRA model. A PR code for the entire clock, a native iPRA version, the combined restore orbit and exit, full physical/source simulation, and the consistency equivalence remain separate.

A fresh staged source replay passed with exit 0, the final axiom audit and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-exact.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-positive-exact-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-exact-repo
```

Use a fresh output directory. The checker rebuilds six modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
