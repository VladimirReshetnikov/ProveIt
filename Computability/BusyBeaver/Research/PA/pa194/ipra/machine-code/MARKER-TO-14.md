# PA194 marker path through seven remaining file blocks

`PA194MarkerTo14.markerTo14` extends the genuine non-first marker path in
`MARKER-TO-106.md` through the seven-control file traversal in
`FILE-TRAVERSAL.md` to dense state 14. It covers all eight non-first marker
positions in every candidate PRA model, including nonstandard register
values and runtime clocks. It retains the exact initial `k=1` header and
delimiter/file assumptions, a positive selected register, and first
physical value `k+7`. The additional condition `idx+n=7` states that, after
the first physical block, the specified updated file contains exactly nine
ordinary blocks, including the selected block and the following spare.
The first-value-six, selected-zero, state-42 zero-residual and other header
cases remain separate.

`PA194UpdatedSevenMatch.matchSeven` proves the exact match for every one of
the eight physical marker positions: the first seven ordinary blocks form
an eight-entry vector whose last entry is the even code for the remaining
two blocks. The composed theorem supplies this vector, its even-tail
witness, the full model-valued clock, and both final tape halves. The left
half is the explicit `PA194FileTraversal.leftCode 7` fold of the seven
register blocks onto the earlier header-derived left half; the right half
is half the remaining two-block file code.

The packet's pinned state-label metadata maps dense state 14 to native state
16, whereas the existing canonical `M6.Source.rootFrame` has native control
84 (dense 24 according to that metadata). This is an external metadata
lookup, not a Lean-proved full-table conjugacy. The endpoint is therefore an
intermediate physical configuration; the theorem does not prove that the
numeric left fold is a source-frame tape, establish blank-tape reachability,
or prove either PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-to-14.sh
```

An independent suffix replay rebuilt the new module(s) against separately
checked controller objects and preserved prerequisite/scratch overlays. The
reported theorem axioms did not include `sorryAx`. The shared comprehensive
prerequisite replay is running separately.
