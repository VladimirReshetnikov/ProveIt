# Independent literal audit of the 216-state candidate, branch order 210

This directory binds the exact native table and its complete canonical
transition table to a literal blank-tape initialization and a local helper
proof. The source calibration and the unbounded implementation of all source
primitives are supplied separately by the enclosing research packet.

## Exact machine

- Binary alphabet `{0,1}`; blank symbol `0`; one two-way infinite tape.
- Exactly **216 working states** and **432 transitions**. Every working state
  is reachable from the initial state in the directed transition graph.
- `k216.native.tm` retains the research labels, starts in `0`, and halts on
  entering label `254`, which has no outgoing transitions.
- `k216.tm` renames the working states in increasing native-label order to
  `0,...,215`. Its start is `0`, its unique halting label is `216`, and its
  dispatcher is `83`. The state-by-state bijection is in
  `canonicalization.json`. This is only a change of names.

The native table SHA-256 is
`eff4f5a3e2c81a674d1a799f634ee4606708b79899e65e8c3cb688dc87c954a3`.
The canonical table SHA-256 is
`b0cf986df02fc0383c788f3d06ac46ac179ed81b3f1546115668c13bf72eeaea`.
The compact source-site file SHA-256 is
`8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc`.

## Blank prefix

Starting at head position `0` in native state `0` on the all-zero tape, the
machine reaches the following exact complete frame after **95,674** literal
transitions:

- Native dispatcher `84` (canonical dispatcher `83`), head `-8`.
- Sole control marker at `-9`; every control-address bit is zero.
- Register-file header at `57`, so the distance from the head is `65` and
  the frame's extra gap is `1`.
- Logical registers `[4,0,0,0,0,0,0,0,0]`, in the inherited register order.
- Exactly 40 spare blocks, each with value `1`.
- Exactly 95 one-cells; every other tape cell is zero.

`blank-seed.json` lists all 95 one-cell coordinates. During this prefix the
head remains in `[-18,199]`. The marker, primary registers, and complete
finite spare list are checked against a frame constructed independently
from those data. The three formula registers are zero, so this is within
the dirty-root initialization contract used by the source proof.

`blank-prefix.json.gz` retains every transition of the native prefix. Its
uncompressed JSON SHA-256 is
`3d937db98b2fa82201db2ddcfc186ed5c398c00ca9e0b9ffcf998fb7bd0a33f8`.
`audit.py` independently executes both the native and canonical tables and
checks that the two complete traces correspond at every step under the
renaming. It uses a sparse dictionary for the tape. `blank_replay.cpp` uses
a separate, bounds-checked array implementation, simulates exactly the
specified number of transitions without an endpoint-selection heuristic,
and reproduces both complete endpoint tapes. The two implementations were
written in this audit task; they are separate implementations, not separate
authorship claims.

## Local helper proof

`local81-proof.json` and `local81-proof.tex` prove the arbitrary-context
three-step equality behind native `81/0 = 0 L 111`. When the cell immediately
to the left is zero, both old and new routes finish in state `123`; when it
is one, both finish in state `21`. In both cases the head moves one cell to
the right and the entire tape is unchanged. The proof reads only the two
specified cells and is independent of unary counter bounds. It permits
this engine use to avoid the old `92/1` row.

## Reproduce

With Python 3.10 or later, from this directory:

```sh
python3 -B audit.py
```

This regenerates the canonical table, canonicalization map, complete
compressed blank trace, exact seed, local proof certificate, full table in
LaTeX, and `audit.json`. If the two saved C++ output files are present, it
also checks them against the Python endpoints.

For an independent implementation of the literal replay, a C++17 compiler
can regenerate those two small outputs:

```sh
g++ -O2 -std=c++17 blank_replay.cpp -o /tmp/k216-blank-replay
/tmp/k216-blank-replay k216.native.tm 95674 254 > blank-cpp-native.json
/tmp/k216-blank-replay k216.tm 95674 216 > blank-cpp-canonical.json
python3 -B audit.py
```

The transition-table format is one row `state read write direction next`,
with directions `L` and `R`; lines starting with `#` are comments. The halt
label has no rows. `full_table.tex` requires the standard `longtable` and
`booktabs` packages.

This finite audit establishes the literal bootstrap, table census, renaming,
and the stated local macro equality. It does not replace the enclosing
packet's unbounded primitive certificate or its proof-theoretic calibration.
