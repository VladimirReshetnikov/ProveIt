# PA194: the complete binary Turing machine

The primary table is `tables/pa194.tm`. It has exactly **194 working
states**, numbered 0 through 193, with start state 0 and separate terminal
halt label 194. It runs on a two-way infinite binary tape, initially all
zero, with the head at cell zero. Every row has the format

```text
current_state read_bit write_bit direction next_state
```

A transition writes, moves one cell left or right, and enters its target.
There are 388 rows. The terminal halt control has no rows and is excluded
from the working-state count. All 194 working states are reachable in the
pointed transition graph; this does not assert that they all occur on the
blank execution.

## Reproduce the primary certificate

From this directory, using Python 3.10 or later and its standard library:

```sh
python3 build194.py
python3 rotation194.py
```

The first command reconstructs and checks the raw 201-state table, the
seven simultaneous folds, the complete dense table, and its dense-to-native
bijection. It also reconstructs the supplied 195S parent and checks exact
equality of the 190-token macro word and all 3,673 resolved source
instructions. Both the new and parent tables pass all 4,780 symbolic
instruction contracts, including arbitrary register values and both
decrement branches. The complete blank-start tape reaches the expected
clean source frame after 58,154 transitions.

The local quotient check covers 23 incoming rows and 28 two-cell cases in
the final simultaneous table: ten take one transition, sixteen take three,
and two take five. These local checks leave the exterior tape arbitrary.
The state count is `134 fixed + 67 readers - 7 folds = 194`.

`rotation194.py` constructs and replays 369 occurrence-level associativity
moves between the parent and new macro trees. Intermediate trees are used
only as an algebraic witness; the endpoint source maps and physical runtime
are verified separately.

To write an additional reconstructed copy of the primary tables:

```sh
python3 build194.py --output rebuilt
```

Run without Python's `-O` flag. Assertions are certificate checks, and the
builder explicitly rejects that flag. No network access, source checkout,
optimization search, or proof-assistant installation is required.

## Exact file identities

The primary dense table's SHA-256 is

```text
4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f
```

The native table's SHA-256 is

```text
e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54
```

In native labels the initial control is 74 and the halt control is 254.
`tables/pa194.labels.json` lists the native images of dense states 0 through
194, including halt. `tables/unfolded201.native.tm` is the new raw table
before the seven folds. `source/pa194.grammar.json` and
`source/pa194.folds.json` are the frozen construction witness.

## Proof scope

The mathematical proof in the report transfers the supplied 195S source
program's PA-consistency calibration to this literal table. The source
program is unchanged; only its binary reader allocation and contextual
quotient change. The primary machine needs no physical register permutation
or change of numerical calculus.

The builder's symbolic executor uses the unchanged imported arithmetic-block
contracts, documented in `reference/M6/Runtime.lean`. The separate
independent verification directory supplies an additional literal-tape
symbolic audit that rederives its list lemmas from actual transition rows.
The executable certificates and the ordinary mathematical PA-provability
argument should not be mistaken for a newly compiled end-to-end Lean or
Rocq theorem.

`PROVENANCE.json` records the source archive, parent and imported files.
Original licenses are included in `licenses/`. Optional discovery code and
actual run logs are under `../search/`; the retained construction can be
checked without repeating those searches.
