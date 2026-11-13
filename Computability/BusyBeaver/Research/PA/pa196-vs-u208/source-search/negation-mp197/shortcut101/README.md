# A blank-start reader shortcut

This is a **197-working-state** variant of the experimental
[combined negation and MP machine](../README.md). It makes no reduction in
state count. Its sole changed native transition is

```
101 0 0 L 26     ->     101 0 0 R 17
```

The [native table](machine.native.tm) starts in state 74 and halts at 254.
All 197 working states remain graph reachable. This shortcut removes two
physical steps whenever that row occurs on the blank run, while preserving the
complete tape, head and control at the next matched boundary.

## Blank-start invariant and local argument

The replay densely renames the **unmodified** combined table, placing native
state 74 at dense state 0 and mapping halt 254 to dense halt 197. A radius-six
window closure starts at the all-zero window and, after every transition,
allows either value for the newly exposed cell. This is an overapproximation
of every concrete blank-start window. It contains 266,771 state/windows and
2,767 projected five-cell state/windows; the abstract closure can reach halt.
The script independently checks initial inclusion and every successor edge,
and separately compares its complete five-cell projection to the existing
`blank_window_contexts` implementation.

At native state 101 reading 0, the admitted five-cell masks are `0, 8, 16,
24`; in all four, the cell immediately to the left of the head is 0. Hence
on any such original-machine boundary the original table executes

```
101/0: write 0, move L, state 26
 26/0: write 0, move R, state 194
194/0: write 0, move R, state 17
```

These three transitions make the same tape change and end at the same head and
state as the candidate's single `101/0` transition. The replay explicitly
compares the complete five-cell tapes for all four masks. Cells outside that
window are untouched. Every other row is unchanged; the original three-step
block has no intermediate halt. Induction over matched boundaries therefore
gives the same blank-input halting behavior for the two literal tables, as an
ordinary finite-invariant argument. The closure also applies to a later visit
to state 101 because the original machine's entire blank run stays inside it.

The checked invariant and finite stuttering argument have **not** been
encoded or proved inside PA. Moreover, the combined machine's own proposed
PA-consistency equivalence remains unproved. Thus this experiment supplies no
PA-provable biconditional or machine below 196 states.

## Executable checks

From the repository root, with Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/negation-mp197/shortcut101/replay.py --output /tmp/shortcut101-receipt.json --out-dir /tmp/shortcut101
```

The command verifies the input archive/table/source hashes, reconstructs the
candidate byte for byte, audits the radius-six closure, and checks the four
local windows. It uses the incoming symbolic checker to validate the same
3,573 source primitives and all 4,641 branch cases. Blank startup reaches the
same exact source frame after 58,142 transitions, compared with 58,154 for the
original table. Output matches [receipt.json](receipt.json). Do not use
Python `-O`: the inherited symbolic checker uses assertions. This executable
check is not a proof-assistant certificate.

After generating the combined source sites using the
[parent replay](../README.md), the separate U208-derived runtime checker can
be run on `/tmp/shortcut101/machine-with-start.native.tm` with the same
command and mapping given there. Its 4,641 passing cases and 394 covered rows are recorded in
[runtime48-receipt.json](runtime48-receipt.json). Both runtime engines retain their archive licenses and provenance.

A [second independent shortcut](../shortcut26/README.md) applies after this
one, with its own blank-start closure and explicit stuttering check.
