# Native iPRA source fetch and decode composition

`PA194FetchDecodeNative.nativeIPRA` proves one universally closed equality in `IPRAStandardTheory.standardTheory` for the actual pinned encoded source-controller iterator from site 25 to site 42. The input register 6 is substituted by zero in the term; all other source registers, including register 7, and the independent file tail are arbitrary. Both fetch branches are included using the primitive-recursive chooser from `PA194UnifiedFetchNative`.

Write `S(q,r,t)` for the encoded source state and `r′` for the exact site-34 registers produced by the unified fetch. Set `p = fixedCantor(r′6,r′7)+r′8`, and let `F` be the explicit unified fetch clock (fresh `7*r0+4`, positive `2`). The equality is

```text
run(F + (totalClock(r′8, S(34,r′,t)) + 1), S(25,r,t))
  = S(42, r′[6 := fixedFirst(p), 7 := fixedSecond(p), 8 := 0], t).
```

Here `r′6=0`; `fixedCantor`, `fixedFirst`, `fixedSecond`, and `totalClock` are the actual repository primitive-recursive codes. The term definitions include the full chooser, register tuple and clock; the displayed names are abbreviations. This is unconditional after the zero-register input substitution, uses PRA-model open induction, and has no IΣ₁ hypothesis. Its `modelSentence`, `classicalPRA`, and `nativeIPRA` axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`. The proof composes the checked fetch and decoder equalities with model-uniform iterator addition before transferring the closed equality to native iPRA. It does not prove the physical-machine step, a full scheduler iteration, or either consistency/halting direction.

The source SHA-256 is `e76e4fedcef9c71451fc8e055c0938e73ff77c7014e49b5312c748682cbee90a`; the independent staged replay passed with exit 0, log `/tmp/pa194-fetch-decode-native-replay.log`, fresh output `/dev/shm/pa194-fetch-decode-native-replay`. The fresh check uses the separately replayed native decoder, two native fetch branch objects and unified fetch object, pinning their hashes and source/receipt baselines. As in `UNIFIED-FETCH-NATIVE.md`, the six graph fallback objects and general project/package/Lake foundations remain prebuilt and their full transitive provenance is not independently authenticated.

After reproducing the staged prerequisites described in `UNIFIED-FETCH-NATIVE.md`, run from the repository root with a fresh output path:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-fetch-decode-native.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /dev/shm/pa194-decoder-native-replay /dev/shm/pa194-scheduler-decode-open-replay /tmp/pa194-scheduler-decode-open-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/dispatch-receipt.json Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/native-decoder-receipt.json Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/fetch-open-receipt.json /dev/shm/pa194-fetch-decode-native-replay /dev/shm/pa194-fetch-native-replay /dev/shm/pa194-unified-fetch-native-staged-replay
```
