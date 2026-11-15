# Physical site-31 increment to site 32

`PA194Site31RootStep.rootStep` proves a complete source-frame-to-source-frame physical step for the pinned literal 194-state machine, in every model of PRA. Its input is a control-24 site-31 path frame with zero-gap length `(k+1)+1`; its output is a control-24 site-32 path frame with gap `k+1`. The source file is updated by incrementing logical register 0 and replacing the physical suffix with `repeatOutput(count+1, 0)`. The other eight logical registers and the physical spare value are preserved. The controller-file tail is not mentioned in this physical-only theorem.

All register values, `k` and `count` range over arbitrary elements of the PRA model. The input suffix condition is exactly `physicalArgs args 10 = repeatOutput(count,0)`: a model-valued sequence of one-valued spare blocks followed by blank tape. The physical step uses the explicitly defined `PA194Site31AfterRun.runAfter` nesting and the explicit first-phase clock in `rootStep`; no existential clock is assumed. The gap change and appended spare matter for chaining the physical invariant.

`PA194Site31OutputFile.outputFile` is the exact all-model identity connecting the physical return-code output to `sourceFileCode` of the updated argument vector. It uses the independently checked finite-vector, six-block file split and combination lemmas. The actual path for site 32 is checked in `PA194Path32Header`.

This proves a physical source-frame step for one instruction. It does not itself prove that the encoded source controller takes the matching instruction, produce a native-iPRA sentence, prove a model-length full-program simulation, or establish either consistency implication.

From the repository root, replay using:

```sh
env -u LEAN_PATH Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-root-step.sh \
  "$PWD" /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip
```

This extends the root-to-site-32 replay with source-built `PA194Site31UpdateVector`, `PA194Site31ReplaceSimple`, `PA194Site31FileSplit`, `PA194Site31FileCombine`, `PA194Site31OutputFile`, and `PA194Site31RootStep`. It pins the listed sources and selected direct machine objects, checks the pinned input hashes before and after, rejects conflicting overlapping machine objects, and audits printed theorem axioms for `sorryAx`. The baseline machine root, two tail-stage roots and general foundations remain prebuilt; the replay does not rebuild or independently certify their entire transitive object closure.
