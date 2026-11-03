# Sharp bounds toward clearing the high-mask padding

`CompactCellSharpSize.packedCell_lt_twice_top` proves that, in every model
of IΣ₁, a represented cell `packedCell a d` with `a ≠ 1` and Boolean dummy
`d ≤ 1` is strictly below `2 * 2^(67*3296)`. The earlier support bound clears
all slots above 3296, and the digit at 3296 is at most one. This applies to
either Boolean dummy value and hence can be used for base and pulsed cells
once the separate pulse-to-cell identity is supplied.

`CompactLowerKernelMass.lower_le` proves for every natural radix `r ≥ 1`
that the exact lower-kernel term sum is at most `2^62 * r^5495`. It uses a
generic weighted-list bound, the fixed term count and per-term weight bound;
it does not evaluate the row table or expand the very large kernel numeral.

The cell check, session `2267`, and corrected mass check, session `70436`,
exited 0 without warnings or `sorryAx`. Their named axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; each run's sampled direct
dependency and companion guards were unchanged. The mass run additionally
guards the mixed project overlay, including all recorded overlap hashes.
Two earlier mass attempts failed due to local elaboration/simplification;
their exact failed sources and compiler logs are retained under
`observations/`. These checks are single-author incremental results with
inherited project, package, transitive, dynamic-loading and
between-observation ancestry; no independent replay or full closure audit is
claimed, and `/tmp` provider paths may disappear.

`CompactHighPaddingSize.block_lt_padding` combines these estimates in every
IΣ₁ model: for any positive `N`, if every cell at an index below `N` is
less than `2^(67*3296+1)`, then every normalized transport block at such an
index is below `2^(67*8792)`. The cyclic predecessor and stride neighbors
are in range by positivity of `N`. The argument handles the exact symbolic
kernel; it implies that all 67-bit digits at positions 8792 and above are
zero. The generic statement explicitly retains the sharp-cell hypothesis.

`CompactMarkedHighPadding.marked_padding` supplies that hypothesis for the
actual base word `packedCell (row j) 0` and its Boolean-pulsed version, using
`CompactWord` and the checked single-pulse cell identity. For each `j<N`,
all their normalized-block digits at positions `p ≥ 8792` vanish. This
clears the actual high-mask padding slots 8792 through 8805 without assuming
high-mask safety; it does not clear the other constrained phases.

The generic combined check, session `69237`, exited 0 without warnings or
`sorryAx`. All four named reports contain only `propext`, `Classical.choice`
and `Quot.sound`; its three-provider project overlay, overlap hashes and
sampled direct/companion guards were unchanged. Its runner and records are
under `observations/padding-attempt01` and share the inherited single-author
and ancestry limits above.

The marked specialization, session `2761`, also exited 0 without warnings
or `sorryAx`; its two named reports list the same three metatheoretic axioms.
Its guarded project overlay covered 524 names, including 339 overlapping
names and 338 present in all three providers; all overlapping hashes matched
and the overlay and sampled direct/companion guards were unchanged. Its
runner and records are under `observations/marked-attempt01` with the same
ancestry limitations.

Other high-mask phases, complete packing, graph zero, retained literal-byte
binding and an iPRA theorem remain open.
