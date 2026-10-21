# A short, checked proof for the existing M124 215-state machine

The primary result is an unconditional, kernel-checked equivalence between the
exact K215 and M124 tables on every binary initial tape, from control state zero.
M124 is an existing candidate in the repository's DR215 incoming archive. This
packet adds its compact Rocq proof and exact input binding, not a new machine.

Read `COMPARISON_AND_INTEGRATION.md` for the candidate ranking, mathematical
argument, full verification scope, and the precise remaining upstream-model
adapter needed to import K215's ZFC endpoint.

## Reproduction

Python 3 and Coq 8.18.0 suffice; no external proof libraries, repository clone,
network, tactic plugins, or theorem search are needed.

```sh
python3 -B check_inputs.py
python3 -B reproduce.py --output /tmp/m124-fresh-proof
```

The output path must not already exist. The second command compiles all three
modules, checks all three closed assumption reports, and recursively checks the
result with `coqchk`. It retains sources, compiler logs, and an exact receipt.

For an existing working directory, the equivalent commands are

```sh
coqc M124Table.v
coqc M124Facts.v
coqc M124Transfer.v
coqchk -silent M124Transfer
```

`check_inputs.py --generate-table` regenerates the exact old-table declaration
from the pinned native file. The default checks it without modifying any file.

The new code follows ProveIt's MIT No Attribution license. Inherited machine
and predecessor-marker attribution is retained in `UPSTREAM_NOTICE.md` and
`upstream_marker_proof.md`. The three native/dense files and two JSON receipts
from the older archive are preserved unchanged.
