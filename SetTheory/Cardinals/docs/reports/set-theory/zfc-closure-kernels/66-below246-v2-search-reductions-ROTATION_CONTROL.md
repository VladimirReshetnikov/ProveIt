# Bounded control repairs for the one-state source reassociation

The source transformation studied here replaces the closed sequence
`(23, (24, 206))` at state178 by `((23, 24), 206)`, reusing state16.
The transformed program has the same ordered 6,460 instruction leaves.
Its register-program bisimulation is supplied by the separate grammar audit.
At the transition-table level the initial proposal is:

| Change | New row |
|---|---|
| 178 / 0 | `0 R 16` |
| 178 / 1 | `1 R 206` |
| Delete state | 208 |

This table has 245 working states, but it **does not correctly simulate the
transformed program**. The folded partial decoder entered by `218 / 0`
still assumes the old parenthesization. These experiments search for a repair
of that interface without adding a state. No full survivor was found, and no
table in this directory is presented as a consistency machine.

## Reproducible results

| Search | Proposals tested | Initial survivors | Full survivors |
|---|---:|---:|---:|
| Every action at 218 / 0 | 980 | — | 0 |
| 218 / 0 jointly with 154 / 0 | 960,400 | — | 0 |
| 218 / 0 jointly with 154 / 1 | 960,400 | — | 0 |
| 218 / 0 plus any row retained by failed-trace intersection | 76,777,120 second-row proposals, over all 980 first edits | 2,880 | 0 |
| One more row around the best near-candidate | 90,160 | 239 | 0 |
| Explicit additional 244 / 0 repair around the near-candidate | 980 | — | 0 |
| Explicit additional 244 / 1 repair around the near-candidate | 980 | — | 0 |

An action has either write symbol, either direction, and any of the 245
working states as its target. A target may equal the old target. The halt state
is not included in this action family.

The main two-row search tries every action at `218 / 0`. It runs the resulting
table on 24 fixtures and intersects the sets of rows visited by failed tests.
Only a row in this intersection can change every one of those bounded traces.
For every retained second row it tries all 980 actions. It reruns the 24-case
screen, then tests each survivor on all 8,391 guarded instruction fixtures.

The first screen allows 2,000 transitions per fixture; the full stage allows
10,000. Both stop after the sixteenth incorrect dispatcher visit. The checked
tape window is the 4,096 cells at coordinates -1,024 through 3,071. A pass
requires the exact expected head position and tape at dispatcher state96;
halting is accepted only on a halt fixture. Thus the searches allow some
intermediate dispatcher visits, but do not exhaust arbitrary retimings.
Fuel, tape, and dispatcher-visit cutoffs are bounded evidence. No resulting
claim rules out an eventual rejoining after these cutoffs or a more general
change to the encoding or source program.

Each fixture starts with header distance40, spare suffix `[0]`, and physical
register `i` equal to `(3*i)%7`, except that a tested CD register is set to0 or1.
The exact expected frame is calculated directly from the instruction semantics;
it is not obtained by running the unverified table. The two first problematic
source paths, each with both CD guards, are placed first. The portable generator
reproduces the stored fixture text and metadata byte for byte.

## The strongest near-candidate and its recorded failure

Starting from the reassociated table, the best two-row attempt is

```text
218 / 0 -> 0 L 246
246 / 1 -> 1 L 193
```

It passes the first 7,651 reordered guarded fixtures, then fails on source
instruction index5,895:

```text
pc = 111010010010111111001000000
instruction = CD logical register1, zero guard
physical values = [0,3,0,2,5,1,4,0,3]
spares = [0]
head = 0
header distance = 40
```

The file `results/rotation-control/failed-near7651.tm` is the exact failed
table, SHA-256
`fb45847113d8c79801704bc2c1677f5fcf552e6898952261ef64648a9910518d`.
Its accompanying `near7651_failure.json` records all 2,204 literal transitions,
all sixteen incorrect dispatcher visits, the expected support, and each visit's
extra and missing one-cells. Its outcome is explicitly
`dispatch_visit_limit`, not a theorem of divergence.

The same first failure remains after replacing the register values by witnesses
admitted by the new interval invariant. Those values are
`[6,3,0,5,2,0,1,1,4]`; the result is in `near7651_interval-test.json`.
The interval restriction therefore does not rescue this near-candidate.

For the third-row search, 24 fixtures beginning at the failure are moved to the
front. Of 90,160 proposals, 239 pass this new initial screen and none passes all
fixtures. The best third edit breaks an earlier original fixture7,617; it does
not improve the frontier. Every action at `244 / 0`, and separately every
action at `244 / 1`, also fails the first frontier fixture. That branch was
stopped after the absence of progress was established at these bounds.

## Reproduction

Run from the search package root. Supply the pinned context246 directory:

```sh
CONTEXT246=/path/to/vendor/context246
ROT=results/rotation-control
```

Regenerate the source/target fixtures and the shifted frontier fixtures:

```sh
python code/capture_rotation_cases.py --baseline "$CONTEXT246" --logical-sites "$ROT/rotation178-sites-logical.json" --output "$ROT"
python code/capture_rotation_cases.py --baseline "$CONTEXT246" --logical-sites "$ROT/rotation178-sites-logical.json" --frontier 7651 --output "$ROT"
```

Compile the simple one-row or two-row search and reproduce its scopes:

```sh
c++ -O3 -std=c++17 code/search_control.cpp -o /tmp/zfc-rotation-control
/tmp/zfc-rotation-control "$ROT/unrepaired-rotation178.tm" "$ROT/rotation-fixtures.txt" 10000 218 0
/tmp/zfc-rotation-control "$ROT/unrepaired-rotation178.tm" "$ROT/rotation-fixtures.txt" 10000 218 0 154 0
/tmp/zfc-rotation-control "$ROT/unrepaired-rotation178.tm" "$ROT/rotation-fixtures.txt" 10000 218 0 154 1
```

Reproduce the expanded synthesis, its optional focused near-candidate recovery,
and the third-row search:

```sh
c++ -O3 -std=c++17 code/search_control_pruned.cpp -o /tmp/zfc-rotation-pruned
/tmp/zfc-rotation-pruned "$ROT/unrepaired-rotation178.tm" "$ROT/rotation-fixtures.txt" 2000 24 > "$ROT/two-row-survivors.txt" 2> "$ROT/two-row-progress.txt"
/tmp/zfc-rotation-pruned "$ROT/unrepaired-rotation178.tm" "$ROT/rotation-fixtures.txt" 2000 24 -1 0 0 201 300
/tmp/zfc-rotation-pruned "$ROT/failed-near7651.tm" "$ROT/near7651-fixtures.txt" 2000 24 246 0 -1 > "$ROT/third-survivors.txt" 2> "$ROT/third-progress.txt"
/tmp/zfc-rotation-control "$ROT/failed-near7651.tm" "$ROT/near7651-fixtures.txt" 10000 244 0
/tmp/zfc-rotation-control "$ROT/failed-near7651.tm" "$ROT/near7651-fixtures.txt" 10000 244 1
```

Optional arguments after the sample count select a fixed first-row target,
write symbol, and displacement (-1 for left, +1 for right). A negative target
disables that selector. Two further integers restrict the one-based ordinal
range of the 980 first actions. The delivered source additionally logs each
new best failed-fixture index with its edits; this logging was added while the
initial full search was running, so its original progress file contains only
the milestone counts. The focused recovery log retains the best edits.

Reproduce the complete failing literal trace:

```sh
python code/capture_rotation_failure.py --baseline "$CONTEXT246" --table "$ROT/failed-near7651.tm" --fixtures "$ROT/rotation-fixtures.json" --fixture 7651 --output "$ROT/near7651_failure.json"
```

The transformed sites and unrepaired table are inputs from the grammar audit;
their hashes and final search counts are recorded in
`results/rotation-control/summary.json`. All machines with failed compositions
are deliberately named `failed` or `unrepaired`.
