# Matched site-36 zero branch to site 38

`PA194SourceSite36ZeroPhysical.zeroBranch` proves in every PRA model that when logical register 6 is zero, the actual encoded source controller takes the site-36→38 zero branch and the literal machine reaches the actual site-38 physical frame. Input and output gap are `(k+1)+1`, the whole file and arbitrary numeric suffix are unchanged, and the independent controller tail is retained. The full physical time is an explicit nested sequence of model-valued clocks. Source instruction, destination path, finite return traces and all branch transitions are kernel checked.

This matched branch requires gap at least two; gap zero and one, the positive physical branch, native iPRA transfer and global simulation remain separate. Build order: `PA194Site36ZeroRollback.lean`, `PA194Site36ZeroBoundary.lean`, `PA194Site36ZeroBoundaryTo12.lean`, `PA194Site36ZeroTo12.lean`, `PA194Site36ZeroTo16.lean`, `PA194Site36ZeroReturn.lean`, `PA194Site36ZeroPath.lean`, `PA194SourceSite36Controller.lean`, `PA194SourceSite36ZeroPhysical.lean`.

The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site36-zero-physical.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site36-branch-repo /dev/shm/pa194-site36-marked-entry-repo /dev/shm/pa194-site36-second-pass-repo /dev/shm/pa194-site36-second-to14-repo /dev/shm/pa194-site36-first-pass-repo /dev/shm/pa194-site36-gap-dispatch-repo /dev/shm/pa194-site36-to42-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site36-zero-physical-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their entire transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
