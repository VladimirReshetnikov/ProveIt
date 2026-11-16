# Native iPRA source tag dispatch

The independent staged replay passed with exit 0. Its log is `/tmp/pa194-dispatch-tag-native-replay.log`; the fresh output is `/dev/shm/pa194-dispatch-tag-native-replay`.

`PA194DispatchTagNative.lean` proves three closed native iPRA equalities for the pinned encoded source controller at site 48. The input tags are encoded as terms rather than hypotheses: zero gives one step to site 3661, one gives two steps to site 3554 with register 3 zero, and `(c+1)+1` gives two steps to site 50 with register 3 set to c. All other source registers and the independent file tail remain arbitrary. These are local source-controller statements; they establish neither actual physical stepping nor the global scheduler/consistency claim.

The staged checker is `check-dispatch-tag-native.sh`, which uses the same 13 positional arguments and source-built baseline as `check-fetch-native.sh`, but a distinct fresh output. It rebuilds the source, checks source/object receipts and axiom reports, and does not rebuild the pre-existing staged closure; prebuilt general foundations and six graph fallback objects remain as described in `SCHEDULER-FETCH-MODEL.md`. Its pinned source hash must be updated if the source changes.

The scratch check of source SHA-256 `99920e3d8e660647bd38ef4764ffe19aab29dcb442bfefd7a98d971cd396bf58` succeeded, and the model, classical PRA and native iPRA axiom reports all list only `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`). The independent fresh replay exited 0 and its pre- and post-build input audits passed.

From the repository root, after reproducing the cited prerequisite stages, the fresh replay command is:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-dispatch-tag-native.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /dev/shm/pa194-decoder-native-replay /dev/shm/pa194-scheduler-decode-open-replay /tmp/pa194-scheduler-decode-open-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/dispatch-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/native-decoder-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/fetch-open-receipt.json /dev/shm/pa194-dispatch-tag-native-replay
```
