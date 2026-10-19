# Marked unary field copying with 30 working states

This is a component theorem, not a consistency machine. Its literal table has 29 operational states and one totalizing invariant-failure state, with one separate return label. A larger machine may share the failure state only after checking its exact transition convention.

## Contract

There is a counter sentinel 1 at coordinate c, then g zero cells, then the anchor 10, followed by a finite sequence of fields of the form 1^(a+1)0. The first 1 of exactly the selected source field has been erased. Its value is v, and g >= v+2. All preceding fields are nonempty unary fields. Start on the erased first cell.

The machine terminates with the entire source and field stream restored, the counter replaced by 1^(v+1), and the head on the rightmost counter 1. Every other tape cell is unchanged. Exterior tape may be arbitrary: the machine never reads to the left of c or to the right of the source's terminating separator.

## Small values

The initial transition restores the erased cell. Inspection of the next two cells distinguishes v=0, v=1, and v>=2. For v=0 the source is already restored and the done-return scan reaches the existing counter. For v=1 the source is also already restored; the finish-one scan appends one counter 1 and returns there.

## Movable two-zero marker

For v>=2, erase the second and third source ones, leaving its first 1 intact. Transfer to the counter and append two ones. At the subsequent source check the invariant is:

- 2 <= k <= v units have been copied;
- the counter contains exactly k+1 ones;
- the only altered source cells are zeros at p+k-1 and p+k, where p is the original source start;
- all other field cells retain their original values;
- the remaining blank counter gap has length g-k >= 2.

The marker's left neighbor is a 1 because p+k-2 >= p. Consequently, while scanning fields rightwards from the anchor, the first pair of consecutive zeros is precisely the marker. An ordinary field separator is a single zero. The source-end separator may be a third zero after the marker, but does not change the position of its first pair.

If the cell after the marker is 1, erase it, restore the left marker cell to 1, and shuttle to the counter. The marker has shifted one cell right. Append one counter 1. This establishes the invariant with k+1.

If the cell after the marker is 0, it is the original source terminator and k=v. Restore both marker cells and make the done-return scan. This restores the complete original field stream.

## Shuttle correctness

A leftward shuttle begins strictly left of the marker. Between this point and the anchor, all field separators are isolated zeros. Thus the first two consecutive zeros encountered leftwards belong to the counter gap. The gap-left loop reaches exactly the rightmost counter 1 and stops before reading the exterior on its left.

The return shuttle scans the remaining counter-gap zeros to the anchor 1, crosses its following zero, and searches the field stream as described above. The inequality g-k>=2 preserves the gap detector throughout. The terminal return adapter moves right once from the counter, reads the adjacent zero, and moves left to the separate return label; the final head is therefore exactly the counter's rightmost 1.

Each scan crosses a finite interval. Each productive cycle increases k, bounded by v, so the machine terminates. The proofs for the three value cases establish the stated universal whole-tape contract by induction on v-2 in the large case. This argument is finitary and formalizable in ordinary arithmetic and hence ZFC; no proof-assistant compilation is claimed.

## Checks

`marked_unary_copy.py` constructs the table and checks 5,756 deterministic exhaustive-small and seeded-random whole-tape fixtures, with arbitrary exterior bits in the random cases. The largest observed fixture took 297,763 transitions. The script rejects Python assertion-disabled mode. Tests supplement, rather than replace, the invariant proof.

Table SHA-256: 50c006e5bda4dee7eb2530c4f33e56ce3d98798a53fe8cf12d66b34a811aef72.
