# Removing the delayed Shift halt: a failed shortcut and a 197-state auxiliary

This is auxiliary research. **Neither construction improves the 194-state bound.**
The rejected table has 196 working controls and fails both its intended source
semantics and a physical simulation contract. The corrected, invariant-based
197-state construction retains only the immediate successful-MP halt in its
source program. It is supplied to make the precise cost and the obstruction
reviewable, not as the requested state-count result.

## Parent and scope

The parent is the MP196 prototype in `docs/incoming/pa_sub194_research.zip`
at ProveIt commit `2337ce611a26e308697ccbddb2a1636f989f01c3`.
Its primitive source and physical runtime are derived from primary PA194.
The three input files, compiler, symbolic engine and license notices are
unchanged copies from that packet. The new driver, evidence, and mathematical
explanation are the work of this investigation. The inherited generic
arithmetic-box lemmas remain a proof dependency; this is not a new
independent arithmetic-box audit or end-to-end Lean/Rocq theorem.

Both tables start in native state 74, halt at terminal label 254, and use a
blank two-way binary tape. All transitions move L or R. Every working control
is reachable in the pointed transition graph; this does not mean every
control is visited in the blank run.

## Why the tempting deletion is wrong

The original Shift uses `node21 = (node7, node20)` and
`node7 = (node6, halt)`. The comparator `node6` has an ancestor-sensitive
`breakTo 1` on mismatch. Replacing `node21` by `(node6, node20)` removes the
wrapper that the mismatch branch is supposed to escape. The branch now
escapes all of `node21`, skipping the stack pop in `node20`.

This fails even on a one-free store: `t = h = 0`, `w = 3 = pair(2,0)`.
The proper Shift returns `t = 0`, `h = 2`, `w = 0`, while the shortcut
returns `t = h = 0`, `w = 3`. This counterexample has no contradiction code
1 among its visible or stacked formulas. No consistency assumption is used.
The physical checker separately fails at site 130, on the zero branch of
logical decrement 8 (physical register 1), after 174 completed contracts.
A 200,000-step startup probe does not reach the designated clean frame;
that bounded observation is not a nonhalting claim.

## The corrected 197-state construction

Retain the two-child wrapper, but replace its old halt leaf by `dec H`:

```
node21 = ((node6, dec 5), node20)
```

The immediate-MP occurrence of `node7` remains unchanged. One additional
reader, native control 402, implements the new Shift-only wrapper:

| Row | New action |
| --- | --- |
| `(53,0)` | `0 R 402` |
| `(402,0)` | `0 R 77` |
| `(402,1)` | `1 R 45` |

All other rows equal MP196. The changed leaf is unreachable from initialized
command boundaries by the one-free invariant explained in `proof.tex`.
Consequently the corrected machine and MP196 have equivalent blank halting
behavior under the inherited source calibration. The Shift operation of this
new machine need not match total Shift on arbitrary stores containing 1;
the equivalence is deliberately restricted to the invariant that is proved
for all reachable command boundaries.

The corrected source has 3,663 sites and 4,769 branch-sensitive primitive
contracts. All pass, with 1,476,396 symbolic executor operations and maximum
497 per contract. Complete blank initialization reaches source site 25,
control 84, head -2 after 58,154 transitions. This is whole-tape equality,
including the primary registers and 26 spare registers.

## Reproduction and artifacts

Run with Python 3.10 or later, standard library only, with assertions enabled:

```
python3 -B verify.py --output /absolute/path/to/new-evidence
```

The command reconstructs both tables, checks the explicit source
counterexample, verifies the corrected one's physical contracts and exact
startup, and writes a receipt. It expects the first candidate to fail and
reports that failure as a rejected diagnostic. A successful verifier exit
never certifies that rejected table.

`evidence/receipt.json` contains exact counts, hashes, the source
counterexample, the failed physical contract, and startup evidence. The
adjacent `.native.tm` files are exact transition tables; the JSON instruction
maps make the ancestor-sensitive branch issue inspectable. The bounded
command cases are supporting cross-checks, not the universal source proof.
No general impossibility result or global state lower bound is claimed.
