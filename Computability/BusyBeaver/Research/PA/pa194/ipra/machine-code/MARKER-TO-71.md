# PA194 marker path through the forced state-106 scan

`PA194MarkerTo71.markerTo71` extends the genuine marker-entry path in
`MARKER-TO-106.md` to dense 71. The theorem keeps the exact initial `k=1`
header and delimiter/file assumptions, positive selected value, and first
physical value `k+7`; it covers every non-first marker position in every
candidate PRA model, including nonstandard values. The first-value-six,
selected-zero, state-42 zero-residual and other header cases are separate.

The generic state-106 contract permits an arbitrary right half. In the actual
composed layout, `PA194UpdatedHead.updatedHeadEvenTail` proves that the
updated remaining file is `block(head,2*tail)` and its half is
`ones(head+1,2*tail)`. A following physical block supplies the even tail;
this holds whether the selected block is first or follows a prefix. Hence
the first state-106 transition is forced to read one. The machine scans the
entire possibly nonstandard one-run, then reads the following zero and
enters state 71. Its right half is exactly `tail`; its left half and full
clock are given explicitly in the composed theorem.

`PA194State106Scan.scanExit` proves the reusable all-model scan and exit.
The theorem concerns an intermediate physical configuration; blank-tape
reachability, source-frame and source-instruction correspondence, and both
PA consistency directions remain open.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marker-to-71.sh
```

An independent suffix replay rebuilt the new module(s) against separately
checked controller objects and preserved prerequisite/scratch overlays. The
reported theorem axioms did not include `sorryAx`. The shared comprehensive
prerequisite replay is running separately.
