# PA194 non-first marker output follows state 35 for k = 1

`PA194PositiveMarkerRoute.positiveMarkTo35` follows the **actual output** of
`modelMarkAllPositive` for each non-first physical register. Under that
marking theorem's selected-delimiter condition and the explicit padded-header
layout, it takes the `k = 1` case of `positiveMarkTo24`. The returned regular
prefix supplies controller bits `1,0,1`, so the next three transitions are
24 → 26 → 29 → 35. This is the branch compatible with that marking output,
unlike the `1,0,0,…` conditional increment route ruled out in
`MARKER-LAYOUT-CONFLICT.md`.

The start has the specified marker control and file code, with left tape half
`1024*u+3`. The theorem records an exact model clock and ends at control 35
with left half `4096*u+13`. Its right half is the remaining one-run
`ones(j 1,w)` from the leading unmarked register block, where `j` and `w` are
the explicit file-code arguments in the Lean statement. All tape and
register values may be nonstandard model elements; the selected index is one
of the eight non-first physical positions.

This proves the stated physical segment only. It does not cover other header
run lengths, identify the controller path with a source instruction, reach an
arithmetic entry, or prove either PA consistency direction. In particular,
the original source/file layout invariant and its reachability remain open.

To replay from the repository root:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-positive-marker-route.sh
```

The script rebuilds the dispatch, marking, and header prerequisites before
checking this module in a private temporary directory; it rejects `sorryAx` in
the reported theorem dependencies.

An independent suffix replay recompiled the new module in a fresh tmpfs
overlay against the separately checked controller and dispatch objects, with
no `sorryAx` in the reported theorem dependencies. The complete author standalone
replay also passed with the audited overlays.
