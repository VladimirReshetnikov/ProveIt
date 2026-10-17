# Pinned machine audit and reproduction

This directory contains the machine-related part of the report. The comparison
point is the public 253-state machine at Jeff's PR 20, exact head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. The 252-state table in
`data/machine/runtime252_known_oldlabels.tm` is an already known runtime fold.
Its blank initialization is **not calibrated** by these artifacts.

The additional results are a complete fixed-gap census (all 8,391 cases pass
at each tested gap 36, 37, 38, and 40), bounded full-table inspection through
100 million blank-tape moves, and exact prepared-tape traces illustrating
why certain smaller-gap cases change the register interpretation. None of
these files is a new proof-assistant certificate. See `AUDIT_NOTES.md` for
the findings, limitations, and prior-work credit.

## Run from the root of the extracted report bundle

Python 3 and its standard library suffice. Do not use Python's `-O` option:
the attributed input code uses assertions for its pinned hash checks.

Check the public 253-state table against the preserved upstream generator:

```sh
python code/machine/upstream/ZF/m253/tools/generate_candidate.py --check
```

Reproduce the one-million-move tape checkpoints or the full 100-million-move
audit. The latter took approximately one minute on the research environment;
wall-clock time is not a mathematical claim or part of a result hash.

```sh
python code/machine/inspect_runtime252.py --start 0 --limit 1000000 --output data/machine/runtime252_seed0_1m.json
python code/machine/inspect_runtime252.py --start 0 --limit 100000000 --output data/machine/runtime252_seed0_100m.json
```

Reproduce all affine and fixed-gap local contracts:

```sh
python code/machine/affine_gap_audit.py --output data/machine/runtime252_gaps.json
python code/machine/exact_gap_audit.py --source35 code/machine/source35_runtime252_short_gap.py --output data/machine/runtime252_exact_gaps.json
```

Reproduce the 20 selected literal prepared-tape traces and source 35's
previously reported 2,794-move positive check:

```sh
python code/machine/representative_gap_checks.py --source35 code/machine/source35_runtime252_short_gap.py --census data/machine/runtime252_exact_gaps.json --output data/machine/runtime252_representative_gaps.json
```

The original source-35 diagnostic is also preserved byte for byte. To run
that prior experiment itself, give its upstream directory explicitly:

```sh
python code/machine/source35_runtime252_short_gap.py --upstream code/machine/upstream --limit 1000000 --output data/machine/prior_source35_reproduction.json
```

Recomputed JSON files contain elapsed-time fields and may contain additional
diagnostic fields introduced after the stored long run. Their byte hashes
are therefore not expected to reproduce from a new run. Compare the logical
counts, exact configurations and trace digests instead. The manifest hashes
identify the stored files as supplied.

## File map

| File under `data/machine/` | Meaning |
|---|---|
| `runtime252_known_oldlabels.tm` | Generated known fold, 252 working states, old labels preserved; uncalibrated blank start 0. |
| `runtime252_seed0_1m.json` | Complete record-setting frame tapes and short prefix observations. |
| `runtime252_seed0_100m.json` | Long bounded run, complete final tape, recent frame samples, and gap counts. |
| `runtime252_gaps.json` | All 8,391 affine cases per tested gap, including every rejection. |
| `runtime252_exact_gaps.json` | All 8,391 fixed-gap cases per tested gap, plus deepest-path suffix census. |
| `runtime252_representative_gaps.json` | Whole input, intended and actual tapes for 20 literal traces, with executed-row SHA256 digests. |
| `machine_manifest.json` | Exact source pins, public benchmark conventions, file hashes, scope and provenance. |

The local scripts import one another from this directory. The upstream
subtree preserves the relative paths used by the public generator and the
source-35 executor. No network access or installed proof assistant is needed.

## Attribution and notices

Mira-Cult supplied the 254-state machine; Jeff supplied the upstream
verification and symbolic-execution development; PR 20 supplied the public
253-state modification and generator. The source-35 fixed-gap adapter and
its dirty-root and safe-start background are prior ProveIt work at
`ba00775e2bf56b184d071346867db74f2eb0c621`. The four short audit scripts in
this directory extend these attributed inputs; they do not independently
establish correctness of the register-box summaries.

The retrieved upstream tree had no repository-wide top-level license.
Original component notices are preserved at their source-relative paths:
Wade's MIT No Attribution notice, busycoq's MIT notice, LibTactics' MIT-X11
notice, and Undecidability's MPL-2.0 notice. The public m253 README states
that it makes no new license grant. No blanket license for the assembled
source excerpt or for all upstream contributions is asserted here.
