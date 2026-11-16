# Native iPRA source transfers to dispatch

`PA194DispatchTransfersNative.nativeIPRA` is a universally closed native iPRA equality for the actual encoded source controller from site 42 to site 48, with arbitrary registers and independent tail. It states

```text
run((3*r7+1)+(3*r6+1), S(42,r,t))
  = S(48, r[3:=r3+r6, 6:=0, 7:=0, 8:=r8+r7], t).
```

Here the clock and output tuple are explicit repository PRA terms; the other registers are preserved. The proof uses the actual pinned source transfer theorems, PRA-model open induction, and classical-to-native-iPRA equality transfer, without IΣ₁. Its model, classical PRA and native iPRA axiom reports list only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. This is an isolated encoded-source equality, not a physical source simulation, a full scheduler-step theorem, or either consistency/halting direction.

Source SHA-256 is `75c5b785b3c781ca3f41b055894fa7ad9c598a62831fda0fcf74878ede324c95`. A scratch check passed. The repository staged source replay exited 0, with log `/tmp/pa194-dispatch-transfers-native-repo.log`. The independent replay log `/tmp/pa194-dispatch-transfers-native-replay.log` also prints PASS, although its final process status was not retained. The checker pins all seven objects of the previously replayed transfer suffix, the composed native fetch/decode object, its three native fetch inputs, and the existing dispatch/decoder/fetch receipts, and checks source/object hashes before and after compilation. Six graph fallback objects and general project/package/Lake foundations remain prebuilt as explained in `UNIFIED-FETCH-NATIVE.md`; receipts do not authenticate the whole foundational closure.

After reproducing the prerequisite staged outputs described in `SCHEDULER-BRANCHES-OPEN.md` and `FETCH-DECODE-NATIVE.md`, run from the repository root with a fresh output:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-dispatch-transfers-native.sh "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /dev/shm/pa194-decoder-native-replay /dev/shm/pa194-scheduler-decode-open-replay /tmp/pa194-scheduler-decode-open-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/dispatch-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/native-decoder-receipt.json Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/fetch-open-receipt.json /dev/shm/pa194-dispatch-transfers-native-replay /dev/shm/pa194-fetch-native-replay /dev/shm/pa194-unified-fetch-native-staged-replay /dev/shm/pa194-scheduler-branches-open-replay /dev/shm/pa194-fetch-decode-native-replay
```
