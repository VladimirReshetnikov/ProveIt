# State 122 cannot be freed by this entry-substitution check

The proposed [marker relay](../README.md) still needs the old state-16
bit-flip-and-return operation along `108/1 → 10/0 → 16/1`. State 122 already
has the right read-one action. Giving it the old read-zero action would make
it a complete replacement for state 16, but would destroy six decoder uses.
This small diagnostic tests whether existing entry states can take over
those uses. It finds no match in the stated family; it does not rule out
multi-row routing, changed source syntax, or a different simulation relation.

## The six decoder roles

An independent literal traversal of the accepted K218 source and table finds
four `(CD5, CC1)` occurrences and two `(CD1, CC1)` occurrences at state 122.
The exact prefixes and source ordinals are in
[census.json](evidence/census.json). The corresponding decrement ordinals are
4572, 4590, 4604, 4713 and 4577, 4595, respectively.

Originally, `88/0 = 0 R 122` supplies the four CD5 occurrences, while
`196/1 = 1 R 122` supplies the two CD1 occurrences. The delete-301 core changes
`88/0` to `0 L 51`, but this does **not** remove the CD5 uses of 122:
the preceding `77/1` wrote one, so the new route passes through `51/1`,
then `51/0`, and still enters 122. State 51 also has its arithmetic scan
role. Redirecting only state 196 would therefore leave an actual conflict.

For a decoder prefix `p`, let `h = length(p)` and append the selected leaf
bit at `h`. These are exact original endpoints:

| Caller class | Read zero | Read one |
| --- | --- | --- |
| Four CD5 prefixes, ending in 0 | state 45, head `h+1`, tape unchanged | state 1, head `h-1`, only cell `h` cleared |
| Two CD1 prefixes, ending in 1 | state 41, head `h+1`, tape unchanged | state 1, head `h-1`, only cell `h` cleared |

The zero endpoint takes three original steps; the one endpoint takes one.
All 12 original endpoint controls pass.

## Completed bounded diagnostic

[entry-routes.json](evidence/entry-routes.json) tests all 217 existing entry
states separately for each caller class, at the unchanged head and prefix.
The speculative table sets `122/0 = 1 L 1` and `10/0 = 0 L 122`, in addition
to the existing relay changes. No other helper rows are synthesized.

Each attempt must make a positive exact join with the old endpoint within
97 steps. Only the known prefix, leaf bit and leading sentinel may be read;
an attempt that reaches another cell is rejected as unresolved. Encounters
with the future caller substitutions `51/0` or `196/1` are also unresolved.
The program stops on the first rejection for each entry state. Both classes
have zero surviving entries. State 30 matches the first CD5 zero branch;
states 28 and 70 match the first CD1 zero branch. Their one branches take
different decoder routes.

These rejections are incomplete filters, not semantic counterexamples.
In particular, a route using known properties of the following register
area, changing a caller's write or direction, or changing more rows is
outside this test. The test proves no global runtime or bootstrap theorem.

## Reproduce

From the repository root, with fresh output paths:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/return-122/census.py --repo . --output /tmp/return122-fresh/census.json
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/return-122/entry_routes.py --repo . --census /tmp/return122-fresh/census.json --output /tmp/return122-fresh/entry-routes.json
```

The actual scratch scripts, records and narrow portable-path diffs are
preserved. An initial missing-space syntax error occurred before execution;
its source and failure receipt remain in `history/`. The successful successor
is retained separately. The publication audit checks metadata and source
structure without repeating the machine diagnostic.
The actual entry record omitted the relay table from its input hash map.
The additive publication audit binds the unchanged parent packet's exact
table; the portable successor also records this input explicitly. The raw
actual record is retained unchanged.

`drop_contract` authored this diagnostic and its role analysis. It uses the
accepted Source 144 source/table and the previously published failed relay;
it does not claim an independent peer review of this new packet.
