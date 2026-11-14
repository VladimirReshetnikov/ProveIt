# The new U209-to-U208 reduction

This file records the local result only. The parent U209's connection to the
unary theory U and PA is inherited and is not re-proved here.

## Exact modification (Plain parent, native labels)

Delete native state 211. Redirect every target 211 to native 172. Replace
the zero row of 172 by `172 0 0 L 214`. There are exactly three changed
retained rows: 163/0, 163/1, and 172/0. No source address changes.

The dense machine has 208 working states (0 through 207) and separate halt
label 208, on a two-way infinite binary tape, blank symbol zero, initial
state zero, initial head position zero. Initialization is included.

## Guards derived from complete incoming-edge inventories

All guards below concern configurations of the **old** U209 run.

1. At native 172, the tape bits at offsets -2,-1 are respectively 1,0.
   Its only incoming edge is 116/0, which writes 0 and moves right. Native
   116's only incoming edge is 216/1, which writes 1 and moves right.
   Neither 172 nor 116 is the initial state, so these predecessors exist.

2. At native 211 scanning 0, the bit at offset -1 is 1. Its incoming edges
   are exactly 163/1 (write 1, move right) and 163/0 (write 0, move left).
   The former gives the guard immediately. In the latter case, 163 was
   entered through 132/1, 199/1, or 214/0; all move right. The first two
   write 1 in the cell that 211 will scan and cannot yield a scanned 0.
   Thus the predecessor was 214/0. State 214 is entered only by 204/1,
   which leaves the required 1 one cell further left. None of 211,163,214
   is initial, so the at-most-three predecessors exist.

## Exhaustive macro cases

Let rho map 211 to 172 and fix all other states, including the halt label.
Ordinary old states other than 172 and 211 are simulated by one new step
because their rows are exactly the quotient under rho (414 rows).

On a scanned 1, old 172 and 211 both execute `1 R 184`, as does new 172.

At old 211 scanning 0, the old transition is `0 R 157`. With the guard
left=1, new 172 takes the following three steps (coordinates relative to
the old head):

| State | Head | Read | Write | Move | Next |
|---|---:|---:|---:|---|---:|
| 172 | 0 | 0 | 0 | L | 214 |
| 214 | -1 | 1 | 1 | R | 216 |
| 216 | 0 | 0 | 0 | R | 157 |

At old 172 scanning 0, the old transition is `0 L 67`. With guard bits
at offsets -2,-1 equal to 1,0, new 172 takes seven steps:

| State | Head | Read | Write | Move | Next |
|---|---:|---:|---:|---|---:|
| 172 | 0 | 0 | 0 | L | 214 |
| 214 | -1 | 0 | 0 | R | 163 |
| 163 | 0 | 0 | 0 | L | 172 |
| 172 | -1 | 0 | 0 | L | 214 |
| 214 | -2 | 1 | 1 | R | 216 |
| 216 | -1 | 0 | 0 | R | 157 |
| 157 | 0 | 0 | 0 | L | 67 |

Every cell has its original value at the endpoint; each macro leaves the
head at the old endpoint and the state at rho(old endpoint). Exterior
cells are never read, so they remain arbitrary. No macro visits the halt
state internally, and each has positive length at most seven.

## Global theorem and formalization boundary

For every common initial tape at state 0, the old and new machines halt
equivalently. The run proof inductively concatenates the positive macro
blocks above. A terminating old run of T steps is matched by a terminating
new run of between T and 7T steps; an infinite old run produces an infinite
new run. The deterministic nature of the machine gives the converse
halting implication. On finitely coded tapes, including blank tape, this
argument is elementary and formalizable in PA. No proof-assistant kernel
certificate of the full Con(PA) endpoint is claimed here.

## Why a previous one-bit search missed the fold

State 211 has entrances from both directions. Its zero-read left-bit
invariant is visible only after resolving the last three transitions, and
state 172 needs two predecessor bits. The new macro also re-enters 172
before returning: its finite recursion terminates on the previous 1.
Restricting every candidate to a single immediate predecessor tag or
disallowing such temporary re-entry excludes this fold.

## Portability

The same construction works on every supplied main U209 table after
substituting three structural roles:

| Proposal | Entry E | Selector H | Follower F |
|---|---:|---:|---:|
| Plain | 163 | 214 | 216 |
| Compatibility | 216 | 214 | 163 |
| Compatible Folds | 163 | 217 | 215 |
| Composed | 163 | 216 | 215 |
| Joint | 163 | 217 | 215 |

Set the new 172/0 row to `0 L H`, delete 211, and redirect its incoming
targets. H/0 leads right to E, H/1 leads right to F, and F/0 leads right to
157. E/0 and E/1 are the two entrances to old 211. Complete incoming
inventories supply the same guards. `../portable_fold.py` derives these
roles from the tables and replays all four cases for each variant.

## Reproduction

Run `python3 build_and_check.py`, or run the same command with Python's `-O`
flag. All requirements use explicit exceptions rather than assertions.
Both checks passed; all eleven corrupted-input controls were rejected.
The checker verifies the parent and candidate SHA-256 identities, literal
tables, totality, graph reachability, dense bijection, complete incoming
inventories, all ordinary rows, and every special macro endpoint.
