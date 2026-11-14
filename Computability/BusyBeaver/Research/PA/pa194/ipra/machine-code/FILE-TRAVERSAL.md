# PA194 finite-control register-file traversal

`PA194FileTraversal.scanFile` proves a reusable physical-file invariant for
any fixed finite sequence of pinned controls whose one rows copy a one and
loop right and whose zero rows copy a zero and advance right. The input is
the half-code of a finite ordinary register file whose final tail is even.
For each physical block the machine scans its `value+1` ones, crosses the
zero delimiter, and advances to the next supplied control. The number of
blocks is a fixed natural number used to select finite code and table rows;
all register values, file tails, and clock values may be nonstandard
candidate-PRA model elements. The theorem gives an explicit finite
primitive-recursive cost and an exact left-half fold using ordinary block
codes; the final right half is half of the original even tail.

`scanSeven` instantiates the checked controls
106 → 71 → 95 → 114 → 68 → 93 → 113 → 14. It requires seven explicit
physical block values and an even final tail. This is a physical run
contract, not yet a proof that the actual updated marker file has that
seven-block shape, a source-frame invariant, a blank-tape reachability fact,
or either PA consistency direction.

Replay from the repository root with pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-file-traversal.sh
```

An independent suffix replay rebuilt the new module(s) against separately
checked controller objects and preserved prerequisite/scratch overlays. The
reported theorem axioms did not include `sorryAx`. The shared comprehensive
`check-file-traversal.sh` replay subsequently passed.
