# PR-coded actual source decoder round

The new `PA194DecoderRoundCode.lean`, SHA-256 `febfc0fbd1d562e619bc33bc58d71277d07c9d40dae4739eece61f17f9642e39`, defines a primitive-recursive `roundClock` on the actual encoded source-controller state and `advance`, which runs the actual source iterator for that clock. `clockModel` proves the clock reads actual registers 6 and 7: it is five source steps for positive reg6, and `3 + (3·(reg7+1)+2)` for reg6=0. `advancePositive` and `advanceZero` prove the code reaches the exact corresponding site-34 output of the previously checked controller rounds for arbitrary model-valued registers and file tail, assuming input reg8 is positive. The variable-length zero drain and the existing `runFive` recurrence use PRA + IΣ₁ model assumptions; the clock-identification theorem itself uses PRA models.

These are model-theoretic Lean theorems, not native iPRA derivations. They give one actual source round with an explicitly coded clock; they do not yet prove arbitrary model-length synchronization with the diagonal iterator, accumulation of the round clocks, a full scheduler step, or a consistency implication.

The independent staged checker exited 0. Its source suffix includes the five source-round modules from `/dev/shm/pa194-scheduler-controller/UNPAIR-ROUNDS.md`, `PA194UnpairExit.lean` and `PA194UnpairCantor.lean` from `DECODER-CANTOR.md`, `PA194DiagonalCode.lean`, `PA194DiagonalIteration.lean`, and `PA194DiagonalLink.lean` from `DIAGONAL-ITERATION.md`, and the new `PA194DecoderRoundCode.lean`, all rebuilt in one fresh output against `/dev/shm/pa194-fetch-coherent-full-v2`. It checks source hashes and printed axiom reports for `sorryAx`. The six graph namespace objects and general project/package/Lake foundations remain prebuilt; their provenance and the original failed build are described in `SCHEDULER-FETCH-MODEL.md`. Log `/tmp/pa194-decoder-round-code-replay.log`; output `/dev/shm/pa194-decoder-round-code-replay`.

From the repository root, with a fresh last argument:

```sh
/dev/shm/pa194-unpair-diagonal/check-decoder-round-code.sh "$PWD" /dev/shm/pa194-scheduler-controller /dev/shm/pa194-unpair-diagonal /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-decoder-round-code-replay
```

The checker calls `check-diagonal-iteration.sh`, which calls `check-unpair-cantor.sh` and `check-unpair-after-fetch.sh`. Each intermediate checker prints its own PASS; the final `PASS: actual PR-coded source decoder round` line and the wrapper's exit status certify the complete 11-source suffix.

The repository-source suffix replay also passed against the independently
rebuilt fetch baseline, with the same prebuilt graph and foundation limitations.
