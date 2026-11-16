# PRA-model scheduler fetch/decode and dispatch branches

This seven-source suffix removes the prior IΣ₁ assumption from the source fetch/decode/tag-dispatch prefix. It extends the independently replayed PRA-only fetch/decode sources in `SCHEDULER-DECODE-OPEN.md`:

* `PA194Transfer42Open.lean` and `PA194Transfer42OpenComplete.lean` prove, by PRA open induction, the actual source site 42→45 transfer in exactly `3·reg7+1` steps, adding reg7 to reg8 and clearing reg7.
* `PA194Transfer45Open.lean` and `PA194Transfer45OpenComplete.lean` similarly prove source site 45→48 in `3·reg6+1` steps, adding reg6 to reg3 and clearing reg6. Both preserve other logical registers and the independent tail.
* `PA194DispatchTransfersOpen.lean`, `transferToDispatch`, composes these segments in every PRA model.
* `PA194SchedulerDispatchOpen.lean`, `fetchDecodeDispatch`, composes the actual source fetch, source Cantor decoder and transfers from site 25 to site 48. Under explicit scheduler N/L matching and initial source regs 3/6/7=0, output reg3 is the scheduler's `head`, reg8 its `tail`, reg0 its next N, and regs 6/7 are zero.
* `PA194SchedulerBranchesOpen.lean`, `fetchDecodeBranches`, additionally composes the pinned tag test: scheduler head 0, 1, or c+2 leads respectively to source site 3661, 3554, or 50, with the axiom case leaving c in reg3.

The final theorems are model-theoretic Lean results in every PRA model, including nonstandard models; they are not yet native iPRA theorems. The prefix clock is existential, the initial alignment/zero-register premises are explicit, and the result does not execute a complete scheduler step, prove global source/physical simulation, or prove a Con(PA)/machine direction.

The independent seven-source replay completed with exit 0, no `sorryAx`: `/tmp/pa194-scheduler-branches-open-replay.log`, output `/dev/shm/pa194-scheduler-branches-open-replay`. It builds the seven files in one fresh output against the separately replayed six-object PRA fetch stage, ten-object native-decoder stage, 26-object source-built dispatch stage, and 270-module source-built controller/scheduler closure. The checker validates all three object receipts, all seven source hashes, and the 270 source hashes/object presence before and after; the prior native-decoder audit independently checked the six graph objects and symlinks. The graph objects and general project/package/Lake foundations remain prebuilt, with exact provenance and limitations in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md` and `DECODER-NATIVE.md`.

From the repository root, after reproducing the staged baselines in `SCHEDULER-DECODE-OPEN.md`, select a fresh final output:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-scheduler-branches-open.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /dev/shm/pa194-decoder-native-replay /dev/shm/pa194-scheduler-decode-open-replay /tmp/pa194-scheduler-decode-open-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/dispatch-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/native-decoder-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/fetch-open-receipt.json /dev/shm/pa194-scheduler-branches-open-replay
```
