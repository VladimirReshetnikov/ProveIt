# PA194 marker path through the dense-84 scanner

`PA194MarkerFrom84.markerTo15` extends the genuine marker-entry path in
`MARKER-TO-84.md` through dense 84 to dense 15. It keeps the exact `k=1`
header and delimiter/file assumptions, covers all non-first marker
positions, requires a positive selected register and an initial first
physical value `k+7`, and works in every candidate PRA model including
nonstandard values and scan lengths. The first-value-six, selected-zero,
state-42 zero-residual and other header cases are separate.

The dense-84 right half is `zeros(2,zeros(k,1+4*r))`, where `2*r` is the
exact updated file after the first block. Dense 84 scans those `k+2` zeros,
writes ones as it moves right, then reads the following one and enters dense
15. After exactly `k+3` additional physical steps its left half is
`ones(k+1,L)` and its right half is `3+8*r`, where `L` is the previous
dense-84 left half. The full marker-to-15 theorem includes the complete
clock. `PA194GenericZeroToOneScan` proves the general rightward zero-to-one
scan by open induction in candidate PRA models; it does not rely on external
induction over model elements.

Dense 84 is native control 35 according to the pinned external label metadata,
and native source-root control 84 is dense 24. The metadata lookup has not
been proved as a full table conjugacy in Lean. The state-15 result is still
an intermediate physical configuration, with source-frame meaning and
blank-tape reachability unproved. No PA consistency direction follows yet.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-from-84.sh
```

An independent ordered suffix replay rebuilt the four new modules in a fresh
tmpfs overlay against separately checked controller objects and preserved
prerequisite/scratch overlays. Their reported theorem axioms did not include
`sorryAx`. The redundant full nested replay was stopped to reduce I/O; a
shared `check-file-traversal.sh` replay subsequently passed.
