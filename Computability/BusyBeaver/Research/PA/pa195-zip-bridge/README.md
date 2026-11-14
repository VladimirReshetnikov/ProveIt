# PA195 full-tape and zipper bridge

`PA195ZipRun.lean` proves that the dense full two-way tape machine used in
the quotient research and the generated PA195 literal zipper machine have
the same halting behavior on blank input. In particular,
`bounded_code_iff_full` identifies the standard-natural-number existential
interpretation of `PA195Bounded.boundedCode` with the dense full-tape halting
predicate.

The proof compares all 390 dense transition rows directly in the kernel and
establishes synchronization at every standard finite clock. It relates a
zipper to a complete tape by equality of the control and every cell relative
to the head, and checks both movement directions, writes, and trimming. The
source-validity invariant ensures that literal halt controls are exactly 195
on reachable runs.

This is a Lean theorem about standard finite runs. It does not prove that the
code has the same meaning in arbitrary nonstandard models, or establish a
PRA/iPRA reduction or a consistency equivalence.

To run the independent clean build from the repository root, set
`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` to the matching audited
Lean object directories, then run:

```sh
Computability/BusyBeaver/Research/PA/pa195-zip-bridge/check.sh
```

The script regenerates the pinned literal table from the archive, builds its
own dependencies in a temporary directory, checks the theorem, rejects any
`sorryAx` in its reported dependencies, and removes the temporary directory.
