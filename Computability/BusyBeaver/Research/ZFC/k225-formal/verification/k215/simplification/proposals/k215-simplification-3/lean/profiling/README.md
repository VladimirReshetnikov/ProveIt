# Further Lean simplification: measured source queries and canonical blocks

## Result and limits

The strongest new source-equivalence proposal is **a canonical 1,426-row block relation**, instantiated in the existing `RMBisim.Bisim.halts_iff`, rather than another generic machine semantics or a giant memo table. The current 2,240 certificate entries contain 814 aliases of the same actual paired test/halt sites. A data-only reconstruction from the **literal latest Lean trees** confirms that both programs have exactly the same register-count block CFG: 1,426 rows, 2,851 branches including the initial branch. This independently agrees with the Rocq-source reconstruction, without importing its results.

All checks in this directory are **Python source-data checks, not Lean kernel validation**. No Lean executable was available, no compilation was run, and no speedup is measured here. Both `.uncompiled.lean` files are proposed semantic adapters requiring compiler validation. No historical repository worktree was modified.

Everything below is pinned to `e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`; `latest/KSource215Data.lean` has SHA256 `43093f181bfdd86408a7c88bbf8c0d99ada494b5e3780ae9d93cff05502dbe67`. The earlier general signed-symmetry improvement is **already implemented** at this pin, not proposed again. Historical wall-clock measurements in the parent report remain tied to the original full build, not this pin.

## 1. What the current forward checker recomputes

`profile_forward_checks.py` strictly parses `t215`, `tD`, all sixteen forward chunks and their balanced certificate tree. It checks the branch cuts, all 2,240 zero offsets, test-register matches, all 4,479 segment-pair obligations (two branches per nonhalt row plus startup), every successor pointer and increment-count equality. Its path model preserves zero extension, truncation, wraparound, break/continue behavior, and the **original** final path returned by `seg`, not just the consumed path.

The counters are mathematical function-call counts for that straightforward evaluation, not an actual Lean evaluator trace. Lean reduction and sharing behavior can differ.

| Query | Calls | Distinct exact keys | Repeated calls |
|---|---:|---:|---:|
| Pointer decode | 13,438 | 4,332 encoded naturals | 9,106 |
| Certificate lookup | 4,479 | 2,240 entry indices | 2,239 |
| `tsite` | 24,696 | 11,216 `(program,path)` | 13,480 |
| Top-level `seg` | 8,958 | 5,702 `(program,path)` | 3,256 |
| Recursive `seg` | 20,216 | 12,520 `(program,path,fuel)` | 7,696 |

Tree traversal visits 1,570,586 internal nodes. Looking up each distinct exact `tsite` query only once would visit 719,771 internal nodes: 186,649 on the source and 533,122 on the target, versus respectively 410,837 and 1,159,749 without that sharing. Pointer decoding performs 841,623 bit-loop iterations in this model.

**The longest segment is only six visited sites.** The longest control-only chain is four instructions. The repeated traversal of deep pointer paths is the larger structural issue, not long straight-line register blocks. The target certificate really contains 176-bit pointers, so changing to `RMBisim.decode`'s 128-iteration implementation is invalid without separately fixing that bound.

A checked memo format could use:

1. 4,332 shared decoded path values with one equality/check per encoding;
2. 11,216 exact site results, keyed by program/tree identity and full input path, with checked traversal results;
3. 5,702 top-level segment results, with references to checked site/next-segment facts;
4. 2,240 certificate entries using those shared results.

This is a safe *interface design*, not an assertion that emitting all those proofs will beat the current checker. Cross-module transparent definitions can still reduce again; a reusable theorem about a checked memo table must expose results without reproving them. Segment caches keyed only by path must justify independence from the remaining fuel, or instead retain the exact fuel key. Preserve the raw final path when reusing the current checker: canonicalizing it silently would change its relation.

A second experiment, `profile_walker_sharing.py`, makes the warning concrete. Across the two syntax trees there are 427 distinct hash-consed syntax objects, but a memo of **recursive** tree-walk subqueries would still need 691,190 exact `(subtree,remainingPath,depth)` keys. Removing the depth accumulator with a generic shift theorem leaves 649,123 keys; also normalizing trailing zeros leaves 549,475. Materializing such a table is unlikely to be the first simplification to try. It is far larger than the 11,216 outer site results. None of these transformations is free merely because the source is a DAG.

## 2. Canonical block CFG: 814 redundant checkpoint aliases

`verify_lean_canonical_cfg.py` reconstructs each tree's ordered leaf occurrences, canonical consumed paths, control-eliminated primitive graph, and test/halt block graph. It rejects control/increment-only cycles rather than silently treating them as halts. It establishes:

- 4,751 expanded leaves per tree;
- 3,326 primitive occurrences after eliminating break/continue;
- equal primitive kinds and every successor ordinal, with initial ordinal zero;
- 512 differing increment labels, exactly 256 adjacent independent swaps;
- 175 pairs `p215: (7,6)` versus `dagPerm: (6,7)`;
- 81 pairs `p215: (1,6)` versus `dagPerm: (6,1)`;
- no other predecessor enters the second member of any swapped pair, and none is initial;
- identical **register-count block graphs**, including the initial block;
- 2,240 raw certificate entries map to precisely 1,426 canonical paired sites, leaving 814 aliases, or 36.34% of the original entries.

The existing checker may not simply drop those aliases: its `ORel` names exact raw path pairs. The relation must change deliberately.

### Minimal semantic route in actual Lean interfaces

Use a finite row with boundary kind (halt or test register), canonical left/right paths, and two successor row indices. Define

`Related P1 P2 := ∃ row, tsite t1 P1 = some (row.edge,row.left) ∧ tsite t2 P2 = some (row.edge,row.right)`.

A checked row provides either halt or two existing `BranchGood` facts starting at `incPath` and `breakPath 1` of those canonical paths. Its segment endpoints are accepted by their `tsite` results matching the chosen successor row, not by literal raw-path equality.

Then `Bisim.step` follows immediately by unpacking the row. The existing `EntryGood` already uses exactly these consumed-path equations. `seg_run`, `seg_hn`, and `Bisim.halts_iff` already justify finite control/increment segments, increment-count commutation and halting transport. There is no need to reprove a general CFG executor's semantics merely to use this canonical relation. `CanonicalRows.uncompiled.lean` sketches this semantic adapter.

The remaining work is real: implement a small finite Boolean checker with a soundness theorem producing those row contracts and the initial `BranchGood`; kernel-check its data; retain 512-bit pointer decoding or store paths directly; profile the new checker. If its endpoint site checks repeat the long traversals, combine it with checked sharing. Fewer rows alone is not a proven time improvement.

### Alternative: normalize two structured nodes first

The separate Rocq provenance audit identifies the expanded swaps as just two original `dagPerm` templates: nodes 188 and 190. Reversing these two increment pairs makes the complete ordered primitive CFG identical. That provenance result is not independently reproved by this Lean tree-only script.

The actual latest Lean library already has the local tools:

- `RMDag.seq` (line 160): compose normal runs;
- `RMDag.upd_comm` (line 220): distinct register updates commute;
- `RMTransfer.contract`: identical total deterministic effects imply arbitrary-run transfer;
- `RMTransfer.closed_of_contract`: one changed contract node inside an otherwise agreeing closed region;
- `RMTransfer.iter_transfer`: lift the node contracts to root iteration.

Use two successive overlays, first 188 then 190, each with the same root and `ok n := decide (n < 487)`. Apply the one-exception theorem twice, in both directions, rather than inventing a two-exception induction. `IncrementPairSwap.uncompiled.lean` sketches the reusable increment-pair contract. Actual finite closure checks and program overlays remain unimplemented in Lean. The canonical count-block route above can avoid even these swaps because the existing segment semantics already permits reordered independent increments.

## 3. Site coverage: sharing requires continuation contexts

For **Lean's** current `p215`, the data header and definition give 179 internal DAG nodes, not 201. Hash-consing the literal tree confirms 179 distinct internal subtrees plus 23 distinct leaf constructors, or 202 syntax objects. Do not conflate these with a separately encoded Rocq/source DAG or the structured `dagPerm` program bounded by 487.

The expanded coverage has 4,750 internal occurrences and 4,751 leaves. There are 9,501 exact `(subtree,prefix)` occurrences; the most reused internal subtree appears under 267 distinct prefixes. Even grouping by `(edge,depth)` leaves 488 classes. Grouping by exact edge and successor paths leaves all 4,751 leaves distinct.

Factoring out the common unchanged prefix of a leaf's input and all its successor paths leaves 56 boundary-effect patterns. This is promising for a parameterized prefix theorem, but it is **not** yet a quotient of the TM simulation: `KSim.start` physically encodes the prefix on the tape, and the checker may scan through it. One must prove the runtime's prefix/frame behavior for arbitrary prefix, register tails and branch outcomes before checking one representative. A proof over 179 syntax nodes with unspecified continuation behavior is unsound.

The lower-risk runtime improvement investigated separately is to replace linear transition-table lookup by the already proved balanced lookup while keeping the exact 4,751 site obligations. That is complementary to this audit and should be evaluated before introducing general continuation-parametric symbolic execution.

## Reproduce and inspect

From this directory, run:

```
python profile_forward_checks.py
python verify_lean_canonical_cfg.py
python profile_walker_sharing.py
python build_canonical_rows.py
```

`build_canonical_rows.py` additionally writes a concrete1,426-row certificate and rechecks all branches against the literal trees. Its161,429-byte JSON passes; four mutations (initial row, stored path, successor target and test register) are rejected. This prototype uses2,851 branch checks,5,702 segment calls and21,096 site calls including redundant row self-checks, versus24,696 in the old raw-path profile. This is a more modest site-query reduction than the row reduction, not a runtime benchmark.

These scripts require only the adjacent pinned `../latest/KSource215Data.lean`; no network, git checkout, Rocq, Lean or third-party Python package is used. All reject `-O`/`-OO`, and the parser verifies the pinned input SHA256. The second and third scripts reuse the first script's strict parser and path definitions. Normal runs passed. Optimized-mode rejection was checked and recorded in `optimized_run.log`.

Primary sources: [latest checker](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMOffsetBisim.lean), [existing segment semantics and bisimulation](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMBisim.lean), [literal data](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSource215Data.lean), [structured contracts](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMDag.lean), [closed transfer](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RMTransfer.lean), [context-carrying coverage](https://github.com/VladimirReshetnikov/ProveIt/blob/e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SiteCoverage.lean).
