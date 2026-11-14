# PA194 marker-exit dispatch and marked increment

`PA194IncrementDispatch.markerToIncrement` proves a physical path from either
marking-exit control (dense 15 or 17) to the marked-increment entry (dense 2).
The start has left half `512*u+1` and right half `512*r+313`; after 27 steps
it has left half `262144*u+824` and right half `r`. The path through dense 24
reads, from the low bit upward, `1,0,0,1,1,1,0,0,1`; its last transition
writes zero. The right half after the prefix is preserved exactly.

`PA194DispatchIncrementSource.markerSourceIncrement` instantiates `r` with the
existing marked physical register-file code for any of the nine logical source
registers, and composes the dispatch with `modelSourceIncrement`. The input
file is the nine-block marked layout with a blank suffix; the spare and suffix
values in the eleven-element source argument are replaced by the layout's
specified zero suffix. The resulting control is dense 7. If `A` is the left
half at the increment entry and `out` is the output file, the output halves
are `half(A)` and `parity(A)+2*out`. The file has the selected logical register
incremented, all other logical registers unchanged, a one-valued spare, and a
blank suffix. The Lean theorem records the full source/file terms and clock.
All register values, the tail `u`, and the clock values may be nonstandard in
any candidate PRA model.

The theorem assumes the complete displayed intermediate tape layout, including
the nine-bit dispatch prefix directly before the marked file. It does **not**
show that source dispatch or the earlier marking routine produces that combined
layout, that a blank-tape run reaches it, or either PA consistency direction.
The source-controller and layout invariants remain open. In fact, the
[marker-layout conflict](MARKER-LAYOUT-CONFLICT.md) proves that the existing
non-first marking output cannot immediately satisfy this route's input pattern;
a different continuation or layout argument is required for those positions.

Replay from the repository root using the pinned iPRA/Foundation overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-dispatch-increment-source.sh
```

The script rebuilds both the header controller and the marked-increment source
box in a private temporary directory, then checks the three new modules and
rejects `sorryAx` dependencies in the reported theorems.

An independent suffix replay rebuilt the eight controller and dispatch modules
in order in a fresh tmpfs overlay, reusing the preserved marker and increment
prerequisites. The reported theorem dependencies did not include `sorryAx`.
The complete nested replay described above is running separately.
