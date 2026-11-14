# Meaning of the seven-block left fold

`PA194FileTraversalMeaning.leftSevenMeaning` proves in every candidate PRA
model that the exact left-half fold at the dense-14 endpoint is the ordinary
seven-block `fileCode` of the traversed register values in reverse order,
with the earlier header-derived left half as its tail. The reversal is the
one expected when the head moves right and the left tape is read away from
the head. In the standard-natural interpretation, the existing
`PA194RegisterFileStandard.sourceFile` relates ordinary `fileCode` to
`M6.Runtime.sepsR`.

`leftSevenEven` and `leftSevenNotOne` prove that this left half is even and
cannot equal 1 in any candidate PRA model. The existing
`M6.Source.rootFrame_concrete` says a canonical source root frame has the
singleton left tape `[true]`; its standard numeric tape code is 1. Thus the
present dense-14 endpoint itself is not that canonical full source-root tape.
The pinned label metadata also maps dense 14 to native 16 and the canonical
native-84 control to dense 24; that metadata lookup is external to Lean's
full-table conjugacy. These facts do not preclude the machine from reaching a
root frame later, and they do not establish source-instruction simulation,
blank-tape reachability, or either PA consistency direction.

The all-model equality concerns only the specified seven-block endpoint; the
link to `M6.Runtime.sepsR` and the singleton-list comparison are standard
natural-number source-tape facts, not a transfer of standard runs to
nonstandard runs.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-file-traversal-meaning.sh
```

An independent suffix replay recompiled the meaning module against separately
checked traversal objects and preserved prerequisite/scratch overlays. The
reported theorem axioms did not include `sorryAx`; the full nested replay has
not been independently completed.
