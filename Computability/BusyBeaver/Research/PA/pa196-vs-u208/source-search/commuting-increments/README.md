# Commuting adjacent increments in the PA196 source

The source contains 207 disjoint adjacent pairs of increments of distinct
registers where the second instruction has only the first as a predecessor.
They comprise one pair `(8,6)`, 139 pairs `(7,6)`, and 67 pairs `(1,6)`, with
register numbers in execution order. The clean seed is site 25, never the
second instruction of a pair. None of these swaps gives a smaller source DAG
in the experiments below, and no smaller machine is obtained.

For such a pair, exchanging the two instructions leaves both registers and
the program counter unchanged after two steps. Other registers are untouched.
Because the only incoming edge of the second instruction is from the first,
a run starting at the seed cannot enter a changed pair halfway through. The
pairs are disjoint, so induction over blocks of one or two steps gives equal
source halting behavior for any subset of these swaps. This is a finite
mathematical source argument, not an exported Lean or PA theorem. Relating a
new table to this source and proving the missing reverse consistency direction
remain separate obligations.

[`replay.py`](replay.py) pins the imported program and seed definitions. It
checks the predecessor and seed conditions, independently resolves each
candidate graph by the existing path and interval resolvers, and compares all
3,812 rows with the original graph after exchanging exactly the intended
increment arguments. Its deterministic output is [receipt.json](receipt.json).

The original has 159 distinct internal nodes. Swapping only one eligible pair
increases this count to at least 160. Swapping *all* pairs of one of the three
ordered types gives 160 nodes; combining two or all three types gives 161 or
162. For each global candidate, the replay also applies every eligible single
global directional rotation. None improves on 159 nodes. This is a bounded
family of source edits; DAG-node count is not machine-state count, and another
allocation or more general source rewrite could behave differently.

## Reproduce

From the repository root, using Python 3.10 or later:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/commuting-increments/replay.py --output /tmp/pa196-commuting-receipt.json --write-sources /tmp/pa196-commuting-sources
```

The exported JSON files use the existing allocator's source format. To
reproduce the exploratory allocation calls, install `z3-solver==4.15.8.0` in
a disposable environment and run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/allocate_current.py /tmp/pa196-commuting-sources/swap-8-6.json /tmp/pa196-commute-86-alloc --protected Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/protected-core.txt --seconds 10 --feasible-only --fresh 0
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/allocate_current.py /tmp/pa196-commuting-sources/swap-7-6.json /tmp/pa196-commute-76-alloc --protected Computability/BusyBeaver/Research/PA/pa196-vs-u208/source-search/allocator-screen/protected-core.txt --seconds 20 --feasible-only --fresh 0
```

In the recorded run, the `(8,6)` candidate returned `unsat` within this
allocator's fixed-node and protected-row model; the `(7,6)` candidate returned
`unknown` after the 20-second solver limit. Solver timeouts and assignments
may vary. These results do not rule out another allocation, or prove any
halting property. The [allocator documentation](../allocator-screen/README.md)
explains its model, the need for separate runtime checks, and its scope.
