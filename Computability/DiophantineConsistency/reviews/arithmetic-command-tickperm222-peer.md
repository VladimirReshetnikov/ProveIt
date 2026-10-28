# Independent review of the actual C222 command-word tick

Reviewer: `circuit_reduction`; author: root. Verdict: **PASS**, no requested
source changes. The reviewer authored the reused actual parser and command
step; this review independently checks the new tick layer and its composition,
not the entire prerequisite library's independent authorship.

The complete 147-line main, 36-line checks, author driver, frozen author
metadata/bundle and the independent replay driver were read before execution.
The literal uses of `stepValue`, `tailValue`, `encodeResult`, and actual
`EnumPerm.cstep`/`decode` were checked against the accepted command-step/parser
contracts and the actual native definitions, not an old254 tick theorem.

| Frozen source | SHA-256 |
|---|---|
| `ArithmeticCommandTickPerm222.lean` | `2edee8fb7e5f5234136583ddb551222828b3c0e130415d9d76b1322e945ff348` |
| `ArithmeticCommandTickPerm222Checks.lean` | `60dc46b1a94fe81b7ce628a64e601f11ffccb63aa5fb22c07f4873ee11869ce4` |

## Mathematical findings

The positive code `1+P(word,working)` distinguishes a completed word from the
zero halting sentinel. Every nonzero internal code decodes, using the proved
predecessor identity and Cantor projections. A completed shifted word zero is
absorbing and remains positive; shifted word one executes raw command zero.
The two notions are not conflated in `Stopped`, which is explicitly their
disjunction.

`nextDef` represents the accepted actual command result. Only in the positive
result branch does it subtract one to restore the working-state code and pair
it with the actual permuted tail. All quantified intermediate values remain
unbounded. `tickDef` separately handles evaluator zero, completed word zero,
and active positive word; its `word-1` is the exact raw command passed to that
next graph. The functional representation holds for arbitrary internal IOpen
inputs, not only a native run or a purported well-formed list.

The decreasing measure is the shifted **remaining word**, not the whole
evaluator code or changing working state. For an active input it either halts,
or its new tail is at most the old raw command; adding one and restoring the
old shifted pointer gives the claimed strict decrease. The proof does not
derive any bound on command intermediates from that decreasing tail.

The Nat adapter handles every raw input and every actual working state. It
uses the accepted all-raw command-step agreement and literal tail agreement;
the `some` branch restores the full post-command state and the `none` branch
is exactly zero. No scheduling, proof invariant, or special initialization
premise is used. Focused checks retain both completed-word zero and executable
raw zero, the active measure, and the exact all-raw native one-step adapter.

## Fresh independent replay and provenance

Author summary SHA:
`5dda196edcae181a9d332f9a4d5b41080c15142ccdf7424c9468d64703f18f1f`;
author bundle SHA:
`f5edcce38c7897e263645403291f25bd4bbd8db95cff32307c17b74b03d70c1c`.
The author recorded first-attempt success for both leaves and no failed Lean
execution. The peer likewise had no failed execution or source correction.

The independent traversal reparsed every current custom import header,
validated exact dependency closure and no cached import of either fresh leaf,
and authenticated **107 cached current-source modules**, including **86
Foundation modules**, **365 cached artifacts**, and **37 explicit external
boundary names**. All **541 deduplicated pins** match before and after each
fresh command. Compiler, toolchain, manifest, frozen sources, author bundle
and logs/objects are included. This reuses the recorded package boundaries;
it does not claim a fresh Foundation or Mathlib build.

Only the two new leaves were rebuilt in
`/tmp/command-tickperm222-independent-4hl5jf5u/lib`, sequentially with Lean
4.32.0, full actual source paths, `-M6000 -j1 -DElab.async=false`, and at least
512 MiB free disk. Outputs were new private regular files.

| Fresh object | Seconds | SHA-256 |
|---|---:|---|
| Main | 7.515 | `f003db1b839446e68051c8f75beb94b4263d54090d59e80233c6be7d48966e0e` |
| Checks | 1.722 | `4a47f54e1d3261eee408564d839ca31a378a4ebc3cf323f27a6172403e2b5a7d` |

Both objects are byte-identical to the author's. The main log is empty. All
13 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
No new axiom or `sorryAx` occurs. No dependency or reviewed source was edited.

The durable twelve-file peer bundle preserves source snapshots, inputs,
commands, logs and results:

* `arithmetic-command-tickperm222-peer-replay.json`:
  `4c653e2444623c4d8b69bce334208bd0074c5c8adb9c67058bcb547d0e75b18b`.
* Bundle `FILES.json`:
  `8f8920f6aa1486ab75ab3db14e94d6bb0c2339efae24ddd904f2f8b6e4cb1d39`.
* Terminal `attempt-1793063199177654555/RESULT.json`:
  `490b0c2276059425a96418ffea849657a2f259bad9807bdb1fb3f0eba3d5f963`.
* Inputs:
  `3686650033671e4e9ce7f067b02446dd841fd9dd16a57b891c288b5018024205`.
* Peer driver:
  `e671b238d7f68286c612af2a95954346fc436e24d47a216d9ad6eacef9e696f8`.

This checkpoint does not prove that a complete command word drains in a
specified time, scheduler fairness, compiled-proof correctness, a C222 proof
invariant, 215-machine simulation, or an arithmetic/HA consistency equivalence.
It is an exact represented one-command tick with its control measure.
