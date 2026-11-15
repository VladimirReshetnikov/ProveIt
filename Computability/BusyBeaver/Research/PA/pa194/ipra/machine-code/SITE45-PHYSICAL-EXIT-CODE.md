# Site-45 coded physical orbit and zero exit

`PA194Transfer45PhysicalExitCode.completeExit` states the model-uniform literal-machine run for the complete site-45 transfer and zero exit as a single equality of PR-coded input/output tape frames. The time is the PR cumulative positive-orbit clock plus the unary PR zero-exit cost applied to the intermediate packed state. The output tape is the actual site-48 frame, with r6 cleared, r3 increased by initial r6, spare count increased by initial r6, and gap increased by initial r6 plus one.

The packed controller component used to recover output register values is a site-45 source state; it is a parameter of the tape-frame code and is not a claim about the actual controller PC after the exit. Native iPRA transfer remains separate. Build source: `PA194Transfer45PhysicalExitCode`. Fresh staged replay passed with exit 0. Repeat from the repository root with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site45-physical-exit-code.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site42-positive-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site45-physical-exit-code-repo \
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
  /dev/shm/pa194-site45-physical-cost-replay3 \
  /dev/shm/pa194-site45-actual-source-repo \
  /dev/shm/pa194-site31-restore-iteration-repo \
  /dev/shm/pa194-site45-physical-one-step-repo \
  /dev/shm/pa194-site45-physical-orbit-repo \
  /dev/shm/pa194-site45-physical-zero-cost-repo \
  /dev/shm/pa194-site45-zero-clock-code-repo \
  /dev/shm/pa194-site45-zero-clock-exact-repo \
  /dev/shm/pa194-site32-clock-code-repo \
  /dev/shm/pa194-site45-physical-exit-repo \
  /dev/shm/pa194-site45-exit-frame-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their complete transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
