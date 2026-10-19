# The selected 226-state extension

The final selected machine is **K226**, with 226 working states over two symbols,
start state 0, dispatcher 82, and halt state 226. The public table is
`selected/k226.tm`, SHA-256:

```
b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599
```

Its numbering preserves ascending original K230 labels after deleting
65, 79, 140 and 175. Complete bijections and the inherited-label representation
are supplied beside the public table. This extension depends on the frozen
`native227_evidence` packet for the K230 input, inherited arithmetic proofs,
source H context proof, and exact symbolic engines. It preserves that packet
unchanged as a fully proved checkpoint.

## Fourth state saving

A closed source reassociation at original K230 states 85/65 makes the two rows
of state 65 identical to state 98:

| Read | Write | Move | Next state |
|---|---|---|---|
| 0 | 0 | R | 19 |
| 1 | 1 | R | 114 |

State 65 can therefore be deleted and every incoming edge retargeted to 98.
`verification/verify_duplicate.py` checks all 454 old rows, not just the two
identical rows. The quotient commutes with one literal TM step on **every
binary tape**, with the exact same head position and entire tape. It fixes start
and halt, and no working control maps to halt. The two tables consequently have
identical halting times from corresponding configurations.

The source reassociation is performed at all ten occurrences of the relevant
closed subtree. It reduces the source DAG from 212 to 211 distinct nodes while
retaining 5,121 leaf occurrences and all 6,656 guarded source cases. Five more
closed reassociations repair seven-zero address runs, preserving the earlier
227-state role assignments:

| Outer state | Inner state | Direction |
|---|---|---|
| 101 | 209 | Left |
| 101 | 208 | Left |
| 226 | 224 | Right |
| 205 | 134 | Left |
| 207 | 205 | Right |

The final source has maximum depth 41 and maximum zero run 6.
`selected/construction_chain.json` records all six rotations, every literal row
change, their required old values, source positions and closed-context data.
The accompanying source packet proves the source transformations; the final
native protocol is checked directly on the completed table.

## Complete selected-table result

The independent full proof in `evidence/runtime226/verification.json` passed:

- all 5,121 leaves and 6,656 guarded instruction cases;
- 1,615,284 symbolic rules, with minimum constant duration 13;
- all four exact-table finite-list induction schemas;
- all 452 transition rows, with no unused-row assumption;
- arbitrary natural primary registers and gap, arbitrary first spare and finite spare tail;
- exact entire-tape and head-position successors;
- exact blank startup in 409,835 steps and a second dense canonical replay.

Every full case, the block schemas, the runtime row census and the complete
startup tape are retained. The checksum reported by the native runtime checker
for its own dense table uses inherited-label order. The public table above uses
ascending original K230 order; exact row-by-row bijections relate them.

These executable mathematical proofs combine with the frozen K230 consistency
calibration and the independently proved closed source replacements. They are
ordinary finite proofs and induction arguments that can be formalized in ZFC.
The selected 226-state endpoint is not described as a fresh proof-assistant
kernel check; any separately supplied Rocq endpoint must be read with its exact
machine and source scope.

## Portable replay

Use Python 3 with assertions enabled and a C++17 compiler. No new third-party
Python dependencies or network access are needed.

```
python reproduce.py --base /path/to/native227_evidence --output /path/to/fresh-replay
```

This reconstructs all selected tables from the frozen227 bytes; independently
replays the 454-row all-tape quotient proof; reproduces the rejected scanner
counterexample; checks 26,624 finite instruction fixtures and exact startup;
and checks the full selected source graph and exact blank tape.

To freshly reprove all 6,656 universally quantified native instruction frames:

```
python reproduce.py --full --base /path/to/native227_evidence --output /path/to/fresh-full-replay
```

The quotient itself is replayed by:

```
python verification/verify_duplicate.py controls/prequotient227_k230labels.tm controls/postquotient226_k230labels.tm --output quotient_replay.json
```

`build.py` checks all selected representations byte for byte. `SHA256SUMS` pins
every file. The inherited base packet can be replayed independently, including
its full H delayed-erasure guard proof.

## Rejected intermediate

The immediate unrepaired226 layout fails at site 650, address
`1110100100111000010000000`, on the zero outcome of `CD1` with all logical
registers zero, first spare zero, and gap zero. After 658 steps it returns to a
clean dispatcher with wrong cells 20 and 23: actual/expected values are 1/0 and
0/1, respectively. `rejected/scanner_witness.json` contains the exact initial
tape, entire literal trace, actual and required final tapes. The rejected table
and source are retained. The five subsequent source rotations repair the
encoding, and the full final proof above verifies the corrected table.

The explicit quotient theorem applies even to the intermediate table; it does
not claim that the intermediate table correctly implements its seven-zero
source layout. The final source and native proof establish the completed
construction's correctness without assuming that failed protocol.
