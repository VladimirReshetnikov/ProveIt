# Comparison of the eight incoming U213 proposals

Prepared against the extracted files at ProveIt commit
`6b3145c0bbbf7563bd7bce44c974b4515656a5b0`. The inventory's literal-table,
source-tree, and guarded-control-flow fingerprints are in `catalog.json`.
The individual tables, sources, and original
readmes are retained under `inputs/A` through `inputs/H`.

## Literal comparison

All eight native tables are distinct. Every one has 213 working states,
426 binary transition rows, native halt 254, and all 213 states reachable
in its transition graph. Graph reachability does not imply visitation on
the blank run.

The primitive count is the expanded source length. The subtree count
includes leaves. The table delta is measured against the supplied primary
U214 native table, not against whichever intermediate an individual report
uses for its own delta.

| ID | Incoming archive | Main saving | Primitives | Subtrees | Cases | Retained rows changed vs U214 |
|---|---|---|---:|---:|---:|---:|
| A | `U213_ConPA_2026-10-28.zip` | Exchange implication antecedents; allocate on a U217 return-helper table; repair known-zero arithmetic entry | 3,928 | 198 | 5,109 | 68 |
| B | `U213_ConPA_2026-10-28 (1).zip` | Direct-transfer source; contextual arithmetic repair; shorten origin detector to seven zeros | 3,909 | 197 | 5,084 | 67 |
| C | `U213_ConPA_2026-10-28 (2).zip` | Reassociate emitter, reallocate, repair arithmetic entry, fold native167 into172 | 3,928 | 198 | 5,109 | 70 |
| D | `U213_ConPA_2026-10-28 (3).zip` | One closed reassociation outside the emitter; reallocate decoder roles and remove215 | 3,928 | 198 | 5,109 | 36 |
| E | `U213_ConPA_Reduction_2026-10-28.zip` | Another emitter reassociation/allocation, known-zero repair, and fold167 into172 | 3,928 | 198 | 5,109 | 70 |
| F | `U213_ConPA_Reduction_2026-10-28 (1).zip` | Six source rotations; use preceding tag and helper155 to fold214 into211 | 3,928 | 199 | 5,109 | 15 |
| G | `U213_ConU_2026-10-28.zip` | Eight source rotations; use preceding tag and helper155 to fold115 into214 | 3,928 | 199 | 5,109 | 10 |
| H | `u213_from_u214_2026-10-28.zip` | Bypass a redundant entry to172, then redirect172/0 and remove112 | 3,928 | 198 | 5,109 | 2 |

C, D, E, F, G, and H preserve U214's ordered opcode/operand word and
its complete guarded ordinal control-flow graph. H also preserves all
source addresses literally. C and E are different allocations of different
parenthesizations, with maximum depths 51 and 50 respectively; they are
closely related ideas, not duplicate tables. A changes the logical emitter
word and uses an explicit numerical exchange certificate. B changes the
source program to direct transfer and uses a distinct interior-startup
calibration. Its source is shorter, and its dirty startup proof cannot be
silently replaced with U214's root-startup proof.

The comparison distinguishes source size from physical state count.
F and G increase the source DAG from 198 to199 nodes while decreasing the
machine from214 to213 states. Their saving comes from tape-context reuse.

## Why the successful stack uses B and H

H's idea is a local machine theorem, independent of the source instruction
layout. Its old helper167 has rows `(0,R,218)` and `(1,R,184)`. In B, those
exact rows belong to native211. Reusing211 transports H's bypass to B
without changing B's source or requiring a new logical-calibration argument.

The accepted patch to B is exactly:

| Native row | B | New table |
|---|---|---|
| 180/1 | `(1,R,172)` | `(1,R,211)` |
| 172/0 | `(0,L,112)` | `(0,L,67)` |

Delete both rows sourced at112. There are212 working states and424 rows.
No state is added. The source and theory stay exactly those of B.

The state-number translation matters: copying H's literal target167 into
B is incorrect, because B repurposes167. The independent checker explicitly
rejects that damaged control.

Other tempting combinations are not immediate. For example, D's
outside-emitter rotation and F/G's emitter rotations have disjoint changed
row keys and deleted states. Nevertheless D's repair sends180/1 into167,
whereas F/G repurpose167. Their patches interfere through a destination
state, so the union is not justified by disjoint row keys alone. C/E remove
the old helper167 entirely. These observations do not prove that those
ideas cannot be combined with further changes.

## Independent audit of the U212 reduction

`../code/check_local_independent.py` was implemented separately from the builder. It checks the
complete literal delta, every incoming row to172 and112, four exact path
identities, and six semantic negative controls. Each local execution uses
a partial tape dictionary and fails on any read outside the stated cells.
Thus success proves that the unspecified exterior is never read or changed.
This avoids substituting a finite radius sample for a universal statement.

Let P be B's original213-state table, J the intermediate with only
180/1 changed, and Q the212-state table. Use `(state,head)` pairs, with the
head initially at coordinate0.

For cells `(0,1)=(1,1)`:

- P: `(180,0),(172,1),(184,2)`.
- J: `(180,0),(211,1),(184,2)`.

For cells `(0,1,2)=(1,0,0)`:

- P: `(180,0),(172,1),(112,0),(209,1),(157,2),(67,1),(151,2),(90,3)`.
- J: `(180,0),(211,1),(218,2),(90,3)`.

For cells `(0,1,2)=(1,0,1)`:

- P: `(180,0),(172,1),(112,0),(209,1),(157,2),(148,1),(186,2),(86,3)`.
- J: `(180,0),(211,1),(218,2),(86,3)`.

All paths leave the entire tape unchanged. These cover every possible tape
at180 scanning1, and no displayed internal state is halt.

In J the complete incoming inventory of172 is only116/0, whose action is
`(0,R,172)`. Thus every visit to172 in a run from state0 has a zero directly
to its left. The only entry into112 is172/0. Consequently the fourth
identity, on cells `(-1,0)=(0,0)`, always applies:

- J: `(172,0),(112,-1),(157,0),(67,-1),(151,0)`.
- Q: `(172,0),(67,-1),(151,0)`.

This is a four-step versus two-step tape-preserving block. The invariant
uses the complete incoming-edge list, not a bounded run or source sampling.

## Formalization and time bound

One may compare P directly with Q at equal-state, equal-head,
equal-entire-tape checkpoints. Handle180/1 by the first three blocks.
Their endpoints are184,90,86, so they never create a checkpoint at172 or112.
At every other checkpoint entry to172, the preceding transition is116/0,
which supplies the needed zero marker. Handle172/0 by the fourth block.
No checkpoint is112. Every remaining step is identical in P and Q.

Every matched block has positive bounded length and no internal halt.
Induction on a finite halting trace therefore translates the trace in both
directions. The proof uses only fixed finite transition checks, coding of
finite configurations/traces, and ordinary natural-number induction. It
is formalizable in PA without a consistency assumption. In particular,

`PA proves Halt(P,blank) iff Halt(Q,blank)`.

The same ordinary mathematical argument works from state0 on any common
initial tape; the PA version can be stated for arithmetically represented
tapes and runs. Avoid asserting a PA quantification over arbitrary
uncoded functions from the integers to bits.

For any halting run, write TP and TQ for the literal times. The old/new
block lengths are1/1,2/2,7/3, or4/2, so

`TQ <= TP <= (7/3) TQ`.

More exactly `TP - TQ = 4r + 2s`, with r counting the100/101 bypass blocks
and s counting the two-zero fold blocks in the common checkpoint sequence.
These are conditional running-time comparisons; they do not assert that
the blank machine halts.

The direct machine equivalence is independent of Theory U. Its Con(PA)
corollary composes with B's explicitly retained conventional numerical
calculus, startup, and U/PA calibration. Neither this checker nor the new
package is a compiled Lean/Rocq/MM0 proof of that complete endpoint.

## Blank initialization audit

A separate literal sparse-tape run of each table for48,140 steps yields
the same complete tape: native state84, head−2,120 one-cells, and zero
exterior. None of180/1,172/0,112/0,112/1 is visited in that prefix, so the
prefixes in fact agree step for step. This preserves B's interior AX
frame and its existing protected-tail/credit calibration.

The first visit to native84 occurs at step34. The calibrated48,140-step
frame occurs after335 earlier dispatcher visits. It must not be described
as the first entry to the dispatcher or as U214's clean root frame.

## Files and exact identities

- New native table:
  `386ce16259d4c97e4af31b3ba494feaff11a0a1a066e0235dddc154b4cea38c4`.
- Parent B native table:
  `bb4f5ac12b29d07d1080109af9bb564e9e11a4783efc48cd73b8f826789d01f7`.
- Literal/source catalog: `catalog.json`.
- Independent local/blank audit receipt: `../evidence/independent_audit.json`.

This is a sound stacking of two supplied ideas with an explicit translated
helper role. It establishes a candidate below213. It supplies no lower bound
or discovery-priority claim.

## Run the independent local audit

From the package root:

```sh
python3 -B code/check_local_independent.py
```

By default this prints a compact result and writes no files. Use
`--output /chosen/path/local-audit.json` to retain a complete new receipt
outside the sealed package. The callable `run(parent_path, child_path)`
returns the complete receipt without writing files.
