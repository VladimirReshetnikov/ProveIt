# Native iPRA source-decoder equality

`PA194DecoderNative.nativeIPRA` is a theorem of the repository's actual `IPRAStandardTheory.standardTheory`: the universally closed native-iPRA equality `equalClosureI lhs rhs`. It concerns the pinned **encoded source controller** at site 34, not the literal physical Turing machine.

For arbitrary input register tuple `r` and independent file tail `t`, write `S(q,r,t)` for the encoded source state at site q, `p = fixedCantor(r6,r7)+r8`, and `C(n,s)` for the concrete PR `PA194DecoderClock.totalClock`. The theorem states the universally closed equality

```text
run(C(r8, S(34,r,t))+1, S(34,r,t))
  = S(42, r[6 := fixedFirst(p), 7 := fixedSecond(p), 8 := 0], t).
```

Here `run` is the actual pinned source-controller iterator, and `fixedCantor`, `fixedFirst`, and `fixedSecond` are exactly the scheduler's existing PR code symbols. There are no register-side or standardness hypotheses. Registers 0–5 and the independent tail are carried through exactly. All functions, the clock and both sides are encoded as terms of the repository's PRA language; the proof of `nativeIPRA` transfers a classical PRA derivation of that universally closed equality using `PRAEqualityToIPRA.nativeOfClassical`. Lean's axiom reports for `modelSentence`, `classicalPRA`, and `nativeIPRA` contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

The proof does not assume IΣ₁. It uses PRA-model open induction to establish the model-length source drain, actual coded-round/diagonal synchronization and cumulative clock, then uses completeness and equality stability to produce the native intuitionistic proof. This is a complete native iPRA theorem for the source decoder, not a native proof of the full scheduler iteration, a global source/physical simulation, or either Con(PA)/machine-halting direction.

The ten newly rebuilt modules are:

1. `PA194IterateAddOpen.lean`: generic source-iterator addition in PRA models.
2. `PA194UnpairDrainOpen.lean`: model-length decoder drain by open induction.
3. `PA194UnpairDrainOpenComplete.lean`: complete zero-reg6 source round.
4. `PA194DecoderRoundOpen.lean`: both actual PR-coded source rounds in PRA models.
5. `PA194SourceReconstruct.lean`: reconstructs any model-valued site-34 encoded file from its readers and ninefold tail.
6. `PA194DecoderSynchronizationOpen.lean`: arbitrary-model-length source/diagonal synchronization via an open formula.
7. `PA194DecoderClockOpen.lean`: exact PR cumulative clock via open induction.
8. `PA194DecoderCompleteOpen.lean`: explicit PRA-model source-decoder equality.
9. Repository source `Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/PRAEqualityToIPRA.lean`: classical-to-native-iPRA equality transfer.
10. `PA194DecoderNative.lean`: the exact closed formula, classical PRA proof, and native iPRA proof.

All except module 9 are in `/dev/shm/pa194-unpair-diagonal`. Their exact SHA-256 pins, including the repository transfer source, are in `check-decoder-native.sh`.

The independent staged replay completed with exit status 0: log `/tmp/pa194-decoder-native-replay.log`, fresh output `/dev/shm/pa194-decoder-native-replay`. It compiled all ten modules in one output against the 26-module source-built dispatch suffix and the independently source-built 270-module machine/controller/scheduler closure. It checked every one of the 26 dispatch-object hashes against `dispatch-receipt.json`, all 270 recorded source hashes and corresponding object presence, the six curated graph object hashes and namespace symlinks, and all ten new source hashes before and after compilation. It also checked all named axiom reports and rejected `sorryAx`. The six graph objects and the general project/package/Lake foundations remain prebuilt; their exact provenance and the preserved initial failed audit are documented in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md`. The receipts do not independently authenticate the prebuilt foundational closure.

From the repository root, after reproducing the staged 26-object baseline as described in `DISPATCH.md`, use a fresh output path:

```sh
/dev/shm/pa194-unpair-diagonal/check-decoder-native.sh "$PWD" /dev/shm/pa194-unpair-diagonal /dev/shm/pa194-fetch-coherent-full-v2 /dev/shm/pa194-dispatch-replay /tmp/pa194-dispatch-replay.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-unpair-diagonal/dispatch-receipt.json /dev/shm/pa194-decoder-native-replay
```
