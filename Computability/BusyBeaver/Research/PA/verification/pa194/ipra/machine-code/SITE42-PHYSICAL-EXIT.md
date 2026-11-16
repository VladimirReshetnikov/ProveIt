# Site-42 model-length physical transfer and zero exit

`PA194Transfer42PhysicalExit.completeExit` proves in each PRA model that the literal stepper executes the model-valued register-7 count of transfers 42→43→44→42, followed by the zero branch 42→45. Its one exact clock is the sum of the primitive-recursive cumulative transfer clock and a unary coded exit cost evaluated on the intermediate frame. Register 7 ends at zero, register 8 increases by its initial value, the repeated-spare count increases by the same amount, and the gap increases by that amount plus one; other registers, spare and independent controller tail are retained. This is a physical execution theorem, not a consistency implication.

The two-source staged replay passed exit 0 with no sorryAx. Copy both Lean sources and the checker into the designated source directory, then run from the repository root with a nonexistent output:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site42-physical-exit.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-site42-positive-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site42-physical-exit-repo \
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
  /dev/shm/pa194-site46-first-pass-repo \
  /dev/shm/pa194-site46-second-to114-repo \
  /dev/shm/pa194-site46-second-to14-repo \
  /dev/shm/pa194-site46-second-pass-repo \
  /dev/shm/pa194-site46-to2-repo \
  /dev/shm/pa194-site46-selected-repo \
  /dev/shm/pa194-site46-increment-return-repo \
  /dev/shm/pa194-site46-header-return-repo \
  /dev/shm/pa194-site46-source-physical-repo \
  /dev/shm/pa194-site47-source-physical-repo \
  /dev/shm/pa194-site45-transfer-step-repo \
  /dev/shm/pa194-site46-clock-exact-repo-v3 \
  /dev/shm/pa194-site46-clock-code-repo \
  /dev/shm/pa194-site45-positive-clock-code-repo \
  /dev/shm/pa194-site45-positive-clock-exact-repo \
  /dev/shm/pa194-site32-clock-code-repo \
  /dev/shm/pa194-site45-transfer-clock-code-repo \
  /dev/shm/pa194-site45-transfer-coded-step-repo \
  /dev/shm/pa194-site45-model-source-repo \
  /dev/shm/pa194-site31-native-repo \
  /dev/shm/pa194-site45-physical-frame-repo \
  /dev/shm/pa194-site45-physical-cost-repo \
  /dev/shm/pa194-site45-actual-source-repo \
  /dev/shm/pa194-site31-restore-iteration-repo \
  /dev/shm/pa194-site45-physical-one-step-repo /dev/shm/pa194-site42-model-source-repo /dev/shm/pa194-site42-actual-source-repo /dev/shm/pa194-site42-transfer-coded-step-repo /dev/shm/pa194-site42-transfer-clock-code-repo /dev/shm/pa194-site42-positive-clock-code-repo /dev/shm/pa194-site42-positive-clock-exact-repo /dev/shm/pa194-site43-clock-code-repo /dev/shm/pa194-site43-clock-exact-repo /dev/shm/pa194-site42-transfer-step-repo /dev/shm/pa194-site42-physical-orbit-repo /dev/shm/pa194-site42-zero-clock-exact-repo /dev/shm/pa194-site42-zero-clock-code-repo /dev/shm/pa194-site38-zero-rollback-repo /dev/shm/pa194-site38-zero-to12-repo /dev/shm/pa194-site38-zero-to14-repo /dev/shm/pa194-site38-zero-to16-repo
```

The checker pins sources and direct imports, checks overlapping direct imports for byte identity, rejects inherited Git overrides and `sorryAx`, and records hashes. Physical stages and foundations are prebuilt; their full transitive closure is not rebuilt here. The checker constructs `LEAN_PATH`.
