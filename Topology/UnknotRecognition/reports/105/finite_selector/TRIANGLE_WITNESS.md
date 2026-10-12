# Triangle columns do not imply dual-tree invariance

`triangle_tree_sensitivity.json` records a connected simple graph on nine
vertices with 25 edges and a Boolean row/column incidence matrix with 17
columns. Rows label graph edges. Every column consists of exactly the
three edges of a graph triangle. Thus its total occurrence is three and
its odd support is an even-degree subgraph. The example satisfies both
the three-occurrence bound and the dual parity condition of native core
matrices. These are necessary constraints only: no realization by a native
triangulated source is claimed.

The packet contains two explicit spanning trees, each with eight edges.
Deleting the first tree's rows leaves 17 rows and a complete 17-step
unit-column peeling certificate. Deleting the second tree's rows permits
eight recorded unit-column peels, then leaves the nine rows

`[0, 4, 6, 7, 13, 17, 21, 22, 23]`.

Their column totals, in the packet's column order, are

`[2, 3, 0, 0, 2, 0, 2, 2, 0, 0, 2, 0, 0, 2, 0, 2, 2]`.

This nonempty row set is a stopping set: no column has total one. The
previously established persistence theorem therefore excludes every
complete positive raw cancellation schedule for this second tree,
including schedules with positive fill. The difference is about complete
raw cancellation, not merely the displayed pivot order.

Every claim used in this finite witness can be checked directly. The
standalone `check_triangle_witness.py` imports no solver or topology code.
It verifies that each support is a graph triangle, that both selected
edge sets are spanning trees, that every recorded pivot has actual live
column sum one, that the successful trace removes every surviving row,
and that the failed trace ends in the stated stopping set.

```bash
python check_triangle_witness.py
```

The witness arose from a seeded search (`931`, iteration `13`) on graphs
with selected triangle columns. One redundant column was removed while
preserving the two recorded trees' different outcomes. The remaining 17
columns are irredundant for a complete 17-row peel, since distinct pivots
must use distinct columns. No minimum vertex or edge count is claimed.

This refutes the proposal that dual-cycle parity plus native column
sparsity alone makes all dual trees equivalent for raw completion. It
does not refute stronger invariance claims for more restricted,
geometrically authenticated source families.
