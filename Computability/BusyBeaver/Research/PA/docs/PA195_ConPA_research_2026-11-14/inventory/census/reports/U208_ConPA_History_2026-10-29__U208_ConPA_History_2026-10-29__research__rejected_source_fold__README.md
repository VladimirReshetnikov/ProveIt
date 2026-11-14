# Rejected grammar shortcut: a concrete simulation counterexample

This is a rejected research attempt, not the delivered U208 candidate. It is
kept to prevent an attractive but unsound compression from being reused.

## Proposed shortcut

Start from the Plain proposal's `u209.native.tm`, SHA-256
`891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4`.
Write a pure decoder's two successors as an ordered pair. The relevant old
fragments are

```
155 = (85,150), 85  = (98,12)
52  = (154,150), 154 = (166,12).
```

Reassociate `((A,B),C)` to `(A,(B,C))` at both roots. In the source, each of
the three factors is closed and nonhalting, with 26, 26, and 28 primitive
instructions respectively. Update every occurrence of each matching source
subtree: five occurrences of the first root, three of the second. The complete
3,909-instruction word and all 5,083 ordinal control edges are unchanged.

The proposed decoder becomes

```
155 = (98,85), 85 = (12,150)
52  = (166,154), 154 = (12,150).
```

States 85 and 154 now have identical rows, so merge 154 into 85. The resulting
table has 208 working states. Its six changed retained rows are:

| State | Read | Old transition | New transition |
| --- | --- | --- | --- |
| 52 | 0 | `0 R 154` | `0 R 166` |
| 52 | 1 | `1 R 150` | `1 R 85` |
| 85 | 0 | `0 R 98` | `0 R 12` |
| 85 | 1 | `1 R 12` | `1 R 150` |
| 155 | 0 | `0 R 85` | `0 R 98` |
| 155 | 1 | `1 R 150` | `1 R 85` |

Delete both rows of state 154. The exact row-equality merge is sound relative
to the already modified table; the preceding reassociation of a shared
runtime fragment is the invalid step.

## Why source control preservation does not suffice

The literal machine uses some apparent source decoder states as part of its
arithmetic runtime. On the zero branch of source instruction 25 (`CD 1`), the
original runtime traverses

```
152/0 -> 159/1 -> 118/0 -> 155/0 -> 85/0 -> 98/0 -> ...
```

The reassociation changes the number and meaning of cells read along this
runtime path. It is not enough that the affected states have bit-preserving
right-moving rows, that the inner decoder has only one incoming edge, or that
the source control graph is unchanged. The same physical graph is serving a
second purpose.

The arbitrary-register symbolic checker rejects the attempt at instruction
25, zero branch, with an `Unknown run may be empty` failure. The finite check
below independently shows an actual wrong return, so this is not merely an
incompleteness of the symbolic checker.

## Finite witness

Use the canonical dispatcher configuration:

- state 84, head position 0;
- source instruction ordinal 25, address `0011001000000`, opcode `CD 1`;
- nine registers all zero, header gap zero, spare list `[0]`;
- exactly the tape positions
  `[-1,2,3,6,56,58,60,62,64,66,68,70,72,74,76]` contain 1;
- every other tape position contains 0.

The expected zero-decrement successor is source ordinal 28,
`00110010000100`, opcode `CD 2`. The baseline reaches the corresponding
canonical frame after **494** literal steps. The rejected table instead
reaches a canonical frame for source ordinal **44**, `0011001000100`, opcode
`CD 4`, after **526** steps. Its registers, spare list, head position, and
header gap are again unchanged. The differing program-counter cells are 10
and 11: the rejected return has the extra 1 at position 10; the expected
return has it at position 11.

The script records every literal transition in both runs, checks the complete
source graph, checks the exact equal-row merge, and reproduces these specific
results without assertions, third-party packages, or the symbolic engine:

```
python3 replay_rejected.py
python3 -O replay_rejected.py --output results_optimized
```

Output `results/rejection.json` contains the source occurrence ledger, patch,
input hashes, and full finite traces. Files named `rejected208.*` are expressly
rejected exploratory artifacts. This witness refutes the claimed canonical
primitive simulation. It does **not** prove anything about this exploratory
machine's eventual behavior from the blank tape.

## Search boundary

A random closed-rotation search produced the shortcut above; its 40-step
discovery path simplifies to the two rotations just described. Subsequent
runtime-filtered exploratory rotations were stopped when the separate,
history-guarded U208 construction met the research target. No minimality or
exhaustiveness claim is made for the grammar search.
