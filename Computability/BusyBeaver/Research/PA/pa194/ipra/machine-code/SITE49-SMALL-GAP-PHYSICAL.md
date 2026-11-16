# Site-49 positive header return at gaps 2–4 in the standard model

`PA194Site49SmallGapPhysical.rootMismatchTwo`, `rootMismatchThree`, and `rootMismatchFour` instantiate the actual kernel-checked 24-step physical header return `PA194Site49PositiveFinish.returnWord` in the standard natural-number model. For each respective case, starting from its explicit control-16 input with the corresponding one, two, or three zero cells followed by an odd marker, the returned root configuration cannot equal a root configuration containing the actual site-50 source path followed by *any* natural tail. `wordEq` formally connects the standalone little-endian word arithmetic to `PA194Path27Header.modelWord`, and the proof decodes both packed configurations to compare their tape words.

These are results about the immediate header-return endpoint in the standard model. They do not show that an actual blank-start run reaches these configurations, do not describe any subsequent physical behavior, and do not prove that the machine fails to simulate by some alternative representation. They do explain why the current direct source-frame theorem needs additional padding in these cases; this is not a consistency implication. Full composition from the initial site-49 frame through the control-16 stage remains separate.

The fresh source replay passed exit 0 and no sorryAx. Copy the Lean source and checker to the designated source directory and run from the repository root with a nonexistent output:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site49-small-gap-physical.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site42-positive-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site49-small-gap-physical-repo \
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
  /dev/shm/pa194-site46-first-pass-repo /dev/shm/pa194-site48-first-pass-repo /dev/shm/pa194-site46-second-to114-repo /dev/shm/pa194-site48-second-to114-replay3 /dev/shm/pa194-site49-first-pass-repo /dev/shm/pa194-site49-gap-dispatch-repo /dev/shm/pa194-site49-second-to114-repo /dev/shm/pa194-site49-second-to14-repo /dev/shm/pa194-site49-second-pass-repo-v2 /dev/shm/pa194-site49-to1-repo /dev/shm/pa194-site48-to4-replay /dev/shm/pa194-site49-to4-repo /dev/shm/pa194-site49-branch-repo /dev/shm/pa194-site48-positive-return-full-repo /dev/shm/pa194-site49-positive-to16-repo /dev/shm/pa194-site49-positive-path-repo /dev/shm/pa194-site49-controller-replay /dev/shm/pa194-site49-small-gap-arithmetic-repo
```

The checker pins sources and direct imports, detects nonidentical duplicate direct imports, rejects inherited Git overrides and `sorryAx`, and records hashes. Physical stages and general foundations remain prebuilt; their complete transitive closure is not rebuilt. The checker constructs `LEAN_PATH`. The supporting natural arithmetic module is separately documented in `SITE49-SMALL-GAP-ARITHMETIC.md`.
