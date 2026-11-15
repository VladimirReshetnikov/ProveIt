# Chained 42→45→48→49 physical execution and reachable gap

`PA194Site49ReachableGap.reaches49` proves in every PRA model an explicit literal-stepper composition: the model-length site-42 transfer and zero exit to site 45, the model-length site-45 transfer and zero exit to site 48, and the positive site-48 branch to site 49. The three parts use their exact coded or nested physical clocks and the entire repeated-spare file and independent controller tail are retained. The sole branch premise is that register 3 in the actual site-48 output file equals `m+1`.

Writing `r42` for the register file after the 42 transfer, the resulting site-49 gap is `((k + r7) + 1 + r42[6]) + 1`, where `(k+1)+1` is the initial site-42 gap. The theorem also proves it is exactly `(q+1)+1` for `q = k + r7 + r42[6]`. This establishes the site-49 first-pass input shape for this particular chained physical route; it does not assert that every site-49 configuration has this gap, or that the route is reached from blank input. It is not a consistency implication.

The fresh source replay passed exit 0 and no sorryAx. Copy the Lean source and checker into the indicated source directory and run from the repository root with a nonexistent output. Every positional machine stage below is the explicit expanded root used by the replay; these remain prebuilt:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site49-reachable-gap.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site42-positive-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site49-reachable-gap-repo \
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
  /dev/shm/pa194-site46-first-pass-repo /dev/shm/pa194-site48-first-pass-repo /dev/shm/pa194-site46-second-to114-repo /dev/shm/pa194-site48-second-to114-repo /dev/shm/pa194-site48-second-to14-repo /dev/shm/pa194-site48-second-pass-repo /dev/shm/pa194-site48-to1-replay2 /dev/shm/pa194-site48-to4-replay /dev/shm/pa194-site48-branch-replay /dev/shm/pa194-site48-positive-return-replay /dev/shm/pa194-site48-positive-cell-replay /dev/shm/pa194-site48-positive-four-replay /dev/shm/pa194-site48-positive-return-path-replay /dev/shm/pa194-site48-positive-to16-replay2 /dev/shm/pa194-site48-positive-path-repo /dev/shm/pa194-site48-controller-repo /dev/shm/pa194-site48-positive-physical-repo /dev/shm/pa194-site42-physical-exit-repo /dev/shm/pa194-site45-physical-exit-repo /dev/shm/pa194-site42-physical-orbit-repo /dev/shm/pa194-site42-model-source-repo /dev/shm/pa194-site42-actual-source-repo /dev/shm/pa194-site42-transfer-coded-step-repo /dev/shm/pa194-site42-transfer-clock-code-repo /dev/shm/pa194-site42-zero-clock-code-repo /dev/shm/pa194-site42-zero-clock-exact-repo /dev/shm/pa194-site31-native-repo /dev/shm/pa194-site31-restore-iteration-repo /dev/shm/pa194-site45-physical-orbit-repo /dev/shm/pa194-site45-physical-one-step-repo /dev/shm/pa194-site45-physical-cost-repo /dev/shm/pa194-site45-actual-source-repo /dev/shm/pa194-site45-model-source-replay /dev/shm/pa194-site45-zero-clock-code-repo /dev/shm/pa194-site45-zero-clock-exact-repo /dev/shm/pa194-site42-positive-clock-code-repo /dev/shm/pa194-site42-positive-clock-exact-repo /dev/shm/pa194-site43-clock-code-repo /dev/shm/pa194-site43-clock-exact-repo /dev/shm/pa194-site42-physical-arithmetic-repo /dev/shm/pa194-site42-transfer-step-repo /dev/shm/pa194-site38-zero-rollback-repo /dev/shm/pa194-site38-zero-to12-repo /dev/shm/pa194-site38-zero-to14-repo /dev/shm/pa194-site38-zero-to16-repo /dev/shm/pa194-site45-physical-frame-repo /dev/shm/pa194-site45-transfer-clock-code-repo /dev/shm/pa194-site45-transfer-coded-step-repo /dev/shm/pa194-site45-positive-clock-code-repo /dev/shm/pa194-site45-positive-clock-exact-repo /dev/shm/pa194-site46-clock-code-repo /dev/shm/pa194-site46-clock-exact-repo-v3 /dev/shm/pa194-site32-clock-code-repo /dev/shm/pa194-site45-transfer-step-repo /dev/shm/pa194-site46-clock-code-repo /dev/shm/pa194-site46-clock-exact-repo /dev/shm/pa194-site46-clock-exact-repo-v2 /dev/shm/pa194-site46-clock-exact-repo-v3 /dev/shm/pa194-site46-first-pass-repo /dev/shm/pa194-site46-header-return-repo /dev/shm/pa194-site46-increment-return-repo /dev/shm/pa194-site46-second-pass-repo /dev/shm/pa194-site46-second-to114-repo /dev/shm/pa194-site46-second-to14-repo /dev/shm/pa194-site46-selected-repo /dev/shm/pa194-site46-source-physical-repo /dev/shm/pa194-site46-to2-repo /dev/shm/pa194-site47-source-physical-repo /dev/shm/pa194-site45-actual-source-repo /dev/shm/pa194-site45-branch-repo /dev/shm/pa194-site45-exit-frame-repo /dev/shm/pa194-site45-first-pass-repo /dev/shm/pa194-site45-model-source-repo /dev/shm/pa194-site45-native-exit-repo /dev/shm/pa194-site45-native-orbit-repo /dev/shm/pa194-site45-physical-arithmetic-repo /dev/shm/pa194-site45-physical-cost-repo /dev/shm/pa194-site45-physical-exit-code-repo /dev/shm/pa194-site45-physical-exit-repo /dev/shm/pa194-site45-physical-frame-repo /dev/shm/pa194-site45-physical-one-step-repo /dev/shm/pa194-site45-physical-orbit-repo /dev/shm/pa194-site45-physical-zero-cost-repo /dev/shm/pa194-site45-positive-clock-code-repo /dev/shm/pa194-site45-positive-clock-exact-repo /dev/shm/pa194-site45-positive-physical-repo /dev/shm/pa194-site45-positive-to16-repo /dev/shm/pa194-site45-second-pass-repo /dev/shm/pa194-site45-second-to14-repo /dev/shm/pa194-site45-transfer-clock-code-repo /dev/shm/pa194-site45-transfer-coded-step-repo /dev/shm/pa194-site45-transfer-step-repo /dev/shm/pa194-site45-zero-clock-code-repo /dev/shm/pa194-site45-zero-clock-exact-repo /dev/shm/pa194-site45-zero-physical-repo /dev/shm/pa194-site45-zero-to12-repo /dev/shm/pa194-site45-zero-to16-repo
```

The checker pins the source and direct imports, detects conflicting duplicate direct-import objects, rejects inherited Git overrides and `sorryAx`, and records hashes. General foundations and the listed machine stages remain prebuilt; their full transitive closure is not rebuilt. The checker constructs `LEAN_PATH`.
