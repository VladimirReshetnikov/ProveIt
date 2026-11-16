# Marker-control unary scans

`PA194MarkerScan.modelMarkerScan` proves the rightward one-scan for each of the
nine actual PA194 marker-entry controls. The model length, tape halves, and
register values may be nonstandard. The proof checks the exact write, move,
and target of each corresponding pinned dense-table row and invokes open
induction for the variable-length scan. The nine control choices are finite
Lean indices, not a claim about nonstandardly many controls.

`PA194MarkerScanSentence.nativeIPRA` provides the corresponding universally
closed primitive-recursive equality in native intuitionistic PRA for each
control, using the existing equality transfer. `PA194GenericRightScan` contains
the reusable all-model induction with its one-row premise stated explicitly;
the PA194 specialization discharges that premise by checking the actual rows.

These scans are components of the prefix-selection stage. They do not yet
establish a complete skip over a register block, the marker's return through
an arbitrary prefix, the transition to the increment engine, or either
consistency direction.

Run `check-marker-scan.sh` with the pinned iPRA and Foundation overlays used
by `check-increment-return.sh`. It rebuilds dependencies in temporary storage
and rejects any `sorryAx` in printed theorem dependencies. Set
`TMPDIR=/dev/shm` when root-disk space is limited.
