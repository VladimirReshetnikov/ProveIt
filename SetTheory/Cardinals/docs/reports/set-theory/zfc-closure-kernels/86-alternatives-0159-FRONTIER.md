# Result and frontier

No sub-246 machine was obtained. All jobs in this branch are terminal.

## Useful positive work

1. A different **246-state** machine, `reuse_control8.tm`, SHA256 `40136b784bc8facb44b17b9383f775d454ad86d1681d9050669c7c85271eefe7`.
   - All nine exterior-independent detector cylinders pass literal replay.
   - All 8,391 arbitrary-parameter symbolic instruction contracts pass, and all 42 macro-induction rows are unchanged.
   - Independent dense blank startup takes 411,243 steps and reaches exactly the baseline's complete tape: state 96, head -5, 351 ones. This is stronger than comparing only decoded registers.
   - Reproduce with `python check_reuse_control.py` and `python replay_detector.py reuse_control8.json` from this directory.
2. Stronger universal caller invariant, checked at all 191,434 scanner entries across the symbolic cases: distance-six and distance-seven leftward delimiters imply respectively ten and eleven additional rightward ones; the long case contains a rightward zero by cell +13. See `verify_deeper_entry_guard.py` and `deeper_entry_guard.json`. The inherited nine-cell long-zero guard is explicitly reasserted.

## Most informative negative results

- Deleting 74 while keeping the first six scanner states fixed and allowing **both rows of 58 to target any retained state** yields 960,400 recipes. None meets the exact restoring interface, even with four arbitrary borrowed cells on each side. The 3,328 affected cylinders were universally covered as needed. An independent Python enumeration has no fuel bound and detects exact cycles; zero survivors, maximum observed execution 761 moves. This is a finite-window, fixed-prefix result, not a global lower bound.
- Restoration-aware seven-state synthesis with 28 existing helper states, the first four scanner states fixed, and 64 moves is UNSAT. Earlier first-return-only results are labeled separately; positive models remain sound.
- No-prefix seven-state, 64-move synthesis and its first-write-one restriction timed out: **UNKNOWN**, not UNSAT.
- The new 246 control exposes no inherited uniform/mixed protected-row fold: 54,390 uniform and 49,702 mixed recipes, no survivors. These use a bounded symbolic proof search.
- L84/R84 plus one-row-repair families also have no survivors; their unsupported and fuel rejections are not semantic impossibility results.

## What remains open

A seven-state detector may still exist with a changed prefix, more helpers, longer execution, larger/restored scratch, or a different complete simulation interface. The new rightward delimiter invariant and source-path helpers offer concrete design information, but neither is a 245-state construction. Repeating the completed fixed-prefix and one-row-repair families is unlikely to be useful.

The intended theorem remains nonhalting iff Con(ZFC), provable in ZFC. The positive control inherits an ordinary simulation argument through the verified local substitution and exact initialization. This work does not complete an exact-machine Lean/PA endpoint or establish unconditional nonhalting.

Full scopes and commands: `REPORT.md`. Terminal SAT statuses: `run_status.json`. Source pin: ProveIt `7ba1598461c6e485c5aeb8f673c0b1d571f8012b`.
