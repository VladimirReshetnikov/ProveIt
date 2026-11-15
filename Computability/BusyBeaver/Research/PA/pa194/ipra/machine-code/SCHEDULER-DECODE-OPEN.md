# PRA-model scheduler fetch and decoder prefix

This independently replayed six-module suffix removes the IΣ₁ hypothesis from the source-controller/scheduler `fetchAndDecode` theorem. The six source modules are:

1. `PA194SourceDrainOpen.lean` and `PA194SourceRestoreOpen.lean` prove the model-length source loops at sites 27 and 31 via explicit open-language induction in every PRA model.
2. `PA194SourceFetchOpen.lean` composes those loops into the exact fresh-fetch source run.
3. `PA194SchedulerFieldsOpen.lean` proves the packed scheduler's relevant next-N and fetch-field identities without inheriting the older lemmas' IΣ₁ section assumption.
4. `PA194SchedulerFetchOpen.lean`, `fetchPrefix`, handles both fresh and nonempty source-fetch branches in every PRA model.
5. `PA194SchedulerDecodeOpen.lean`, `fetchAndDecode`, combines that prefix with the previously replayed PRA-model decoder: assuming scheduler N/L match source regs 0/8 and source regs 6/7 initially equal zero, there is a model-valued source clock from site 25 to site 42; output regs 6/7 equal the scheduler's actual `head`/`tail` codes, output reg0 matches scheduler next N, and reg8 is zero. The independent file tail is arbitrary.

This is a model-theoretic Lean theorem, not yet a native iPRA theorem. Its combined fetch/decode clock is existential; the decoder portion has a PR cumulative clock. It does not execute the complete scheduler iteration, prove literal physical-machine synchronization, or prove a Con(PA)/machine direction. Its scheduler-field and zero-register premises remain explicit.

The staged six-source replay completed with exit 0, with no `sorryAx`: log `/tmp/pa194-scheduler-decode-open-replay.log`, output `/dev/shm/pa194-scheduler-decode-open-replay`. It uses the separately passed native-decoder source suffix and the earlier source-built dispatch/machine outputs. `check-scheduler-decode-open.sh` pins all six source files before and after, verifies the 10-object native-decoder and 26-object dispatch receipts and the recorded 270 machine-source hashes/object presence, and checks named axiom reports. The previous native-decoder audit separately checked the six graph namespace object hashes and symlinks. Those graph objects and the general project/package/Lake foundations remain prebuilt; their exact provenance and limitations are in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md` and `DECODER-NATIVE.md`.

From the repository root, after reproducing the staged baselines described in `DECODER-NATIVE.md`, choose a fresh final output:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-scheduler-decode-open.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /dev/shm/pa194-decoder-native-replay /tmp/pa194-decoder-native-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/dispatch-receipt.json Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/native-decoder-receipt.json /dev/shm/pa194-scheduler-decode-open-replay
```
