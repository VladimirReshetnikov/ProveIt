# Context and runtime reduction research capsule

This packet contains a new finite-window invariant, independently checkable
local-search infrastructure, and a reproducible counterexample to a tempting
207-state shortcut. **It does not contain an accepted 207-state Con(PA)
construction.** The full research outcomes and search limitations are in
`FINDINGS.md`.

## Fast offline reproduction

From this directory run:

```sh
python3 -B reproduce.py
```

Only Python 3.10+ and its standard library are needed. The default run
independently checks all 1,923,274 abstract successor cases of the saved
radius-7 invariant, verifies its complete DNF representation, and executes
the concrete seven-zero/six-zero scanner counterexample. It normally takes
a few seconds. Checks remain active under Python's `-O` switch.

To retain fresh receipts:

```sh
python3 -B reproduce.py --output /tmp/context-research-checks
```

## Optional searches

A C++17 compiler is required only for these options:

```sh
python3 -B reproduce.py --discover-window
python3 -B reproduce.py --search-folds
python3 -B reproduce.py --search-reachable-folds
```

`--discover-window` recomputes the complete abstract fixed point from the
literal transition table and requires exact agreement with the saved
certificate. `--search-folds` repeats 389,376 one-row representative
modifications across 468 compatible state/read-row pairs. It uses targeted
finite primitive cases followed by all 15,252 cases on each survivor;
it reproduced no accepted finite survivor. This search has a 5,000-step
per-case cap and is explicitly incomplete. It is not a minimality proof.
The scripts compile into a temporary directory and leave this packet
unchanged.

## Contents

- `data/u208.native.tm`: exact History/class-A 208-state baseline, with
  historical native labels and separate halt 254.
- `data/sites.json` and `sites.tsv`: complete 3,909-primitive source.
- `data/provenance.json`: pinned repository snapshot and source identities.
- `evidence/window7.bin.gz`: 29,968-byte lossless encoding of the 6,815,744-byte
  abstract membership array.
- `evidence/window7.contexts.json`: 2,692 Boolean cylinders representing
  exactly the same invariant.
- `code/check_window.py`: independent standard-library finite verifier.
- `code/window_reach.cpp`: fixed-point discovery program.
- `code/window_contexts.py`: optional decision-diagram path conversion.
- `code/global_fold_scan.cpp` and `finite_support.cpp`: full primitive
  endpoint regression search. Final halting tape/head are unconstrained
  for a CH primitive.
- `code/sixzero_counterexample.py`: exact whole-tape failure of shortening
  the detector by deleting native state 34.
- `licenses/`: upstream notices and licenses retained from the supplied
  History archive.

## Mathematical scope

A state/window pair records a state and the 15 cells at offsets -7 through
7. Each abstract step writes the center, moves the head, and admits both
values for the newly exposed boundary cell. All initial windows at state 0
are included, and the verifier checks closure. Ordinary induction then
proves that every real run from state 0 on every initial tape lies in the
invariant. The invariant has 961,765 abstract state/window pairs.

This invariant check is complete for its finite certificate, but it is not
a Lean, Rocq, or MM0 kernel proof. The other searches are finite research
experiments. They establish neither a lower bound of 208 states nor the
full logical calibration of the supplied baseline to Con(PA).

The rejected scanner shortcut produces the same full tape but returns to
the dispatcher eight cells too far right on the first CD8-zero primitive.
Trailing source zeros are therefore relevant: transient runtime words can
extend a trailing zero suffix by one cell.

The optional `--search-reachable-folds` mode constructs 71,622 finite cases
using the supplied source zero/positive and register6 trit invariant files,
then repeats the complete one-row fold family. Its saved receipt is
`evidence/reachable_mask_fold_receipt.json`. These source invariant files
come from the accompanying source-optimization work; this capsule checks
their dimensions and trit conversion, while their closure proof is supplied
there. The mask sample uses C++ `std::shuffle`, so an alternative standard
library may choose different samples. The referenced run used GCC/libstdc++.
