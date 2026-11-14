# Internal Foundation universal-introduction fields

`PA194AllFields.lean` gives fixed candidate-PRA codes for the conclusion set,
rule tag, body and child of Foundation's encoded `allIntro` node. `fields_all`
proves their values are exactly `s`, `4`, `p` and `dp`, respectively, on an
input `allIntro s p dp`. The equalities hold throughout every candidate-PRA
model with an IΣ₁ arithmetic reduct, including nonstandard arguments.

`nodeChoice` combines the decoded conclusion set with the universal-premise
selector. `all_node_choice` proves the zero/successor selection result for any
member of the actual universal premise, provided the distinguished `free L p`
is explicitly supplied. Construction of a finite PRA code for that
substitution remains open here; Foundation already has a separate Σ₁ graph for
`free L`. A complete nonstandard derivation traversal, full proof-compiler
correctness, PA/source-calculus calibration and machine reduction also remain
open.

The final module passed a fresh Lean 4.32 suffix rebuild against freshly
rebuilt prerequisite suffixes and the audited project and Foundation objects.
The printed theorem axioms are `[propext, Classical.choice, Quot.sound]`, with
no `sorryAx`. The full nested replay below has not yet completed; the earlier
source-shift dependency has passed its separate full replay.

From the repository root, using matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-all-fields/check.sh
```

The script rebuilds its prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.
