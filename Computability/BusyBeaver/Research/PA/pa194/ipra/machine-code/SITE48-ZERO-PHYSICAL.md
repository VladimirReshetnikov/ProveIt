# Site-48 matched zero source and physical branch

`PA194SourceSite48ZeroPhysical.zeroBranch` combines the actual encoded-controller step 48→3661 with the exact-clock literal physical run under `args 3 = 0`. From site-48 gap `(k+1)+1`, it reaches site-3661 gap `k+1` with the full arbitrary register file, suffix, and controller tail preserved. This is not a consistency implication.

The fresh staged source replay passed exit 0 and no sorryAx. Copy the Lean sources and checker into the indicated source directory and run from the repository root with a nonexistent output:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site48-zero-physical.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site42-positive-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
  /dev/shm/pa194-site34-branch-repo /dev/shm/pa194-site34-second-pass-repo /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-one-spare-file-roundtrip-repo \
  /dev/shm/pa194-site28-roundtrip-repo /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site48-zero-physical-repo \
  /dev/shm/pa194-site42-zero-physical-repo \
  /dev/shm/pa194-site42-branch-repo \
  /dev/shm/pa194-site42-second-pass-repo \
  /dev/shm/pa194-site42-first-pass-repo \
  /dev/shm/pa194-site38-positive-to16-replay \
  /dev/shm/pa194-site38-positive-return-repo \
  /dev/shm/pa194-site38-zero-physical-repo \
  /dev/shm/pa194-site38-branch-repo \
  /dev/shm/pa194-site38-to4-repo \
  /dev/shm/pa194-site38-to1-repo \
  /dev/shm/pa194-site38-second-pass-repo \
  /dev/shm/pa194-site38-second-to14-repo \
  /dev/shm/pa194-site38-first-pass-repo \
  /dev/shm/pa194-site38-second-to71-new \
  /dev/shm/pa194-site38-second-to95-repo \
  /dev/shm/pa194-site43-first-pass-replay \
  /dev/shm/pa194-site43-second-to14-replay2 \
  /dev/shm/pa194-site43-second-pass-repo \
  /dev/shm/pa194-site43-to2-repo \
  /dev/shm/pa194-site43-selected-repo \
  /dev/shm/pa194-site43-increment-return-repo \
  /dev/shm/pa194-site43-increment-to7-repo \
  /dev/shm/pa194-site43-output-file-repo \
  /dev/shm/pa194-site43-header-return-repo \
  /dev/shm/pa194-site43-complete-repo \
  /dev/shm/pa194-site43-source-physical-repo \
  /dev/shm/pa194-site44-source-physical-repo \
  /dev/shm/pa194-site45-first-pass-repo \
  /dev/shm/pa194-site45-second-to14-repo \
  /dev/shm/pa194-site45-second-pass-repo \
  /dev/shm/pa194-site45-branch-repo \
  /dev/shm/pa194-site45-zero-to12-repo \
  /dev/shm/pa194-site45-zero-to16-repo \
  /dev/shm/pa194-site45-zero-physical-repo \
  /dev/shm/pa194-site32-positive-exact-repo \
  /dev/shm/pa194-site45-positive-to16-repo \
  /dev/shm/pa194-site45-positive-physical-repo \
  /dev/shm/pa194-site46-first-pass-repo /dev/shm/pa194-site48-first-pass-repo /dev/shm/pa194-site46-second-to114-repo /dev/shm/pa194-site48-second-to114-repo /dev/shm/pa194-site48-second-to14-repo /dev/shm/pa194-site48-second-pass-repo /dev/shm/pa194-site48-to1-repo /dev/shm/pa194-site48-to4-repo /dev/shm/pa194-site48-zero-cell-replay /dev/shm/pa194-site48-branch-replay /dev/shm/pa194-site48-zero-rollback-full-repo /dev/shm/pa194-site48-zero-to12-repo /dev/shm/pa194-site48-zero-path-repo /dev/shm/pa194-site48-controller-repo
```

The checker pins sources and direct imports, detects nonidentical duplicate direct imports, rejects inherited Git overrides and `sorryAx`, and records hashes. Physical stages and general foundations remain prebuilt; their entire transitive closure is not rebuilt. The checker constructs `LEAN_PATH`.
