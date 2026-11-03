# Independent review of the 91-operation Lean algebra packet

The recorded Lean source proves three equalities over an arbitrary
commutative ring, for arbitrary integer ports and valuations. The 92-graph's
first, main and ordinary residuals at the valuation with coordinate 5 changed
from `w` to `(1+J*beta)*w` equal the respective residuals of the 91-graph.
Small general ring identities handle the two factorizations. The theorem
statements do not require positivity, fixed ports or standard valuations, and
do not establish positive-zero existence, a machine-halt equivalence, or an
internal iPRA proof.

A separate source reconstruction matched all 12 variable indices, all four
port indices, every one of the 91 ordered Lean operations and all four
output projections against the pinned JSON graph. The author's graph and
Lean-source checks both reran successfully, with three mutation controls in
the latter; both refuse optimized Python. The earlier independent 91-graph
review also reran and checked the rewrite, liveness and external degree
calculation. These are external source and data checks, not Lean file or PDF
semantics theorems.

The captured author algebra run exited zero with empty stderr, no warning
and no `sorryAx`. The first identity reports Lean metatheory axioms
`[propext, Quot.sound]`; the other two report `[propext]`. Its source
snapshot, output object and logs match the receipt. All 75 files found by
the selected-provider traversal were rehashed with their resolved paths;
they include the exact 92-algebra object from the earlier accepted run and
all 74 files in that run's selected inventory. Two captured resource samples
saw two Lean processes and at least 18,257,092 KiB available memory.

Run `python3 -I -S -B check.py` from this directory, or pass the script path
from another directory. The read-only check pins source, receipts and logs,
rechecks the selected files before and after, and reruns the external graph
reviews. Its captured execution exited zero with empty stderr; see
`observations/stdout`. It needs the retained absolute `/tmp` provider and
object paths. No Lean process was started for this review.

The selected traversal does not cover all symlinked directories or full
transitive, package and dynamic ancestry; historical source-to-object
provenance remains inherited. Resource samples are not continuous. The
recorded run is a single-author kernel check, not a fresh independent
replay. The fixed-port positive-existence bridge and all later end-to-end
iPRA, coefficient-file and PDF bindings remain separate work.
