# Dense 113 to an already-marked source increment

`PA194FirstMarkIncrement.firstMarkToIncrement` proves that a configuration at
dense state 113 with halves `1024*u+3` and `256*r+158` reaches the physical
increment entry, dense state 2, after 30 physical steps. The resulting halves
are `262144*u+824` and `r`. The theorem holds for arbitrary model elements
`u` and `r` in every candidate PRA model, including nonstandard models.

`PA194FirstMarkIncrementSource.firstMarkSourceIncrement` instantiates `r`
with the existing nine-register increment-input encoding and composes this path
with the source-register increment box. The resulting state is dense 7, and
the output file has the specified logical register incremented, other source
registers unchanged, a one-valued spare, and a blank suffix. Exact tape and
clock terms are given in Lean.

**The embedded increment file is already marked in the starting layout.** The
q113 marker action occurs in the preceding prefix; this package does not show
that it produced the mark in the embedded file, or that the q113 marker and
the selected file slot refer to the same source instruction. It also does not
prove that a blank-tape run reaches the layout, or either PA consistency
direction. The controller and source-layout invariants remain open.

Replay from the repository root using the pinned iPRA/Foundation overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-first-mark-increment.sh
```

The script rebuilds the controller, source increment box, dispatch composition,
and the two new modules in a private temporary directory and rejects `sorryAx`
in their reported dependencies.

The complete author replay passed using the audited overlays. An independent
suffix replay also rebuilt both new modules against separately checked dispatch
objects and preserved increment prerequisites, with no `sorryAx` reported.
