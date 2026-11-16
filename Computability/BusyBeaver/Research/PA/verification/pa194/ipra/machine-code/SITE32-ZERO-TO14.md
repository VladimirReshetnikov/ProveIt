# Site-32 zero branch to dense state 14

`PA194LeftOneWriteZero.leftOneWriteZero` proves arbitrary pinned physical table rows that read one, write zero, and move left. `PA194Site32ZeroBoundaryTo12.sevenTo12` uses it for the site-32 path-specific seven-step return from the state-11 header boundary. `PA194Site32ZeroTo12.zeroTo12` composes this with the full zero-branch physical prefix. `PA194Site32ZeroTo14.zeroTo14` follows the two model-length scans to dense state 14, preserving the original complete file code under logical register 6 = 0. All other file arguments and the suffix are arbitrary; the total clock is existentially quantified.

The final state-14-to-root execution and identification with the site-34 source frame remain open. These are all-PRA-model physical results, not yet a native iPRA source/physical transition.

A fresh incremental source replay passed with exit 0 and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-to14.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-to14-replay
```

Use a fresh output directory. The checker rebuilds the four modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audit, and records source, direct object/companion and upstream receipt hashes. The earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
