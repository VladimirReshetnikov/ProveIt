# PA194 model-length source fetch and decoder

These five new Lean sources extend the eleven-source decoder round handoff in `DECODER-ROUND-CODE.md`:

* `PA194DecoderInvariant3.lean` proves that an invariant describing the actual site-34 source state, remaining reg8 countdown, and equality of regs 6/7 with the abstract diagonal iterator is Σ₁-definable. Only the three changing registers are existentially quantified; all other logical registers and the controller file tail remain fixed.
* `PA194DecoderSynchronization.lean`, `synchronization`, proves that for every model-valued round count `j ≤ initial reg8`, the actual PR-coded controller-round iterator reaches site 34 with `remaining reg8 + j = initial reg8` and regs 6/7 equal to the corresponding model-length diagonal iterator. Its proof uses the checked positive/zero controller-round theorems, the encoded exact per-round clock, and Σ₁ induction.
* `PA194DecoderClock.lean` defines the primitive-recursive `totalClock : Code 2`, the cumulative sum of the exact clock for each actual coded round, and proves `accumulate` for every model-valued round count: the literal source-controller run at that total time equals the iterated round code.
* `PA194DecoderComplete.lean`, `decode`, proves that from any site-34 register file, after the total clock for `initial reg8` rounds plus the one-step exit, the actual encoded source controller reaches site 42 with reg8=0 and regs 6/7 equal to the scheduler's fixed first/second Cantor projection codes on `cantor(initial reg6, initial reg7)+initial reg8`. `decodeFromZero` specializes initial regs 6/7 to zero, so the projected input is exactly initial reg8. Other logical registers and the independent controller file tail are unchanged.
* `PA194SchedulerDecode.lean`, `fetchAndDecode`, combines this with the previously verified actual fetch prefix. If scheduler N/L match source regs 0/8 and source regs 6/7 start at zero, there is a model-valued source clock from site 25 to site 42 whose output regs 6/7 equal the scheduler's actual `head`/`tail` codes, whose reg0 matches scheduler next N, and whose reg8 is zero. The combined fetch/decode clock is existential; the decoder portion has the explicit PR cumulative code above.

All theorems currently check in every model of PRA + IΣ₁, with no `sorryAx`. These are model-theoretic Lean results, not native iPRA proofs. They establish the fetch-and-first-decode prefix of a scheduler iteration; they do not execute the remaining scheduler branches, prove global source/physical simulation, establish a machine-specific consistency direction, or prove the desired Con(PA) equivalence. In particular, termination here is a result about the coded source controller and not yet the literal physical machine.

The independent source replay completed with exit status 0; its log is `/tmp/pa194-scheduler-decode-replay.log` and its output is `/dev/shm/pa194-scheduler-decode-replay`. It rebuilds the previous eleven decoder/diagonal sources plus these five in a fresh shared output against the independently source-built 270-module fetch/controller/scheduler baseline. Six graph objects and the general project/package/Lake foundations remain prebuilt; their exact provenance, hashes, and first failed audit are in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md`. `check-scheduler-decode.sh` pins all five new source hashes before and after compilation and audits their printed axioms; nested prerequisite checkers perform the corresponding earlier checks.

From the repository root, choosing a fresh final output path:

```sh
/dev/shm/pa194-unpair-diagonal/check-scheduler-decode.sh "$PWD" /dev/shm/pa194-scheduler-controller /dev/shm/pa194-unpair-diagonal /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-scheduler-decode-replay
```

Only the final `PASS: model-length actual source fetch and Cantor decode` line covers the entire 16-module suffix; earlier PASS lines are for proper prerequisites.

The repository-source suffix replay also passed against the independently
rebuilt fetch baseline. The graph and general foundations remain prebuilt.
