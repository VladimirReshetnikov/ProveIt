# Recovering and replaying batch 187

Run from the repository root with Python 3.10 or later and assertions enabled.
The selected checks use the standard library. Do not use `-O` or
`PYTHONOPTIMIZE`. Always use new scratch directories outside the repository;
verification scripts can overwrite their own evidence.

## Restore the delivered layouts

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover-intake187.py /tmp/zfc187-packets
```

The helper reads the three exact ZIPs from arrivals `ffcdff81ad` and
`0b0cec2d0d`, checks safe extraction paths, and executes nothing. Each archive
has its own extraction directory; original wrappers are retained. The fresh
[intake recovery receipt](data/intake187-recovery.json) records 111, 38 and
125 members, all 274 accounted for by the [placement map](data/intake187-placement.json).
Original main manuscripts, PDFs and article inputs remain available through
this recovery even where the host's existing-report procedure leaves them
archive-only.

The resulting packet roots are:

- `/tmp/zfc187-packets/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20`
- `/tmp/zfc187-packets/research218_progress_latex/research218_companion`
- `/tmp/zfc187-packets/research218_encoding_supplement_latex`

These paths replace historical author-side paths in preserved receipts.
Do not run the flattened `141-alt219-`, `142-toward218-` or `143-enc218-`
archival scripts in place. The map gives their exact delivered names.

## Source 141: complete alternative construction checks

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake187-fresh-alternatives/prepare_replay.py \
  --packet /tmp/zfc187-packets/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20 \
  --output-dir /tmp/zfc187-alternatives
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake187-fresh-alternatives/run_replay.py \
  --workdir /tmp/zfc187-alternatives
```

Preparation copies the packet, safely extracts the embedded exact K219
baseline, and obtains the exact runtime library/map members from its nested
K220/K221 archives. It runs no ancestor preparation or calibration script.
The generated plan has 14 explicit jobs: reconstruction; complete independent
source/patch transport; three source checks; three complete startups; a small
independent audit; three complete generic runtimes; independent runtime audit;
and malformed controls. The runtime deadline is 180 seconds per variant and
small-job deadline 60 seconds. The serial runner uses separate logs and process
groups, stops on failure or timeout, and preserves partial evidence.

The [actual record](data/intake187-fresh-alternatives/actual.json) and
[review](data/intake187-fresh-alternatives/review.json) record all 14 passing.
Zero-terminal/retagged/composed cover 6,175 / 6,167 / 6,175 cases and
1,518,671 / 1,514,311 / 1,518,914 symbolic rules. Their complete blank prefixes
have 313,845 / 312,707 / 314,043 steps; all reach the identical 277-one-cell
tape. No positive generic guard is omitted. Ten negative controls pass.

The original scratch adapters, portable successors and narrow differences
are preserved. Portable preparation was tested against the actual plan and
input identities after path substitution; the costly runtime was not repeated
solely for the portable path change. Stored supplied-script snapshots document
provenance but are not a standalone flattened packet. The 4,000-rule runtime
limit bounds proof construction, not the natural parameters or represented
machine running time.

The inherited calibration and ordinary source contracts remain prerequisites,
with independent mathematical review. No proof assistant, recursive ancestor
suite, checksum manifest or supplied omnibus wrapper was executed.

## Source 142: selected finite checks

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/intake187-source142-replay.py \
  --packet /tmp/zfc187-packets/research218_progress_latex/research218_companion \
  --output /tmp/zfc187-theory
```

This copies the packet and invokes only the six reviewed finite checkers:
`recheck`, `check_dag`, `audit_fragment_leaves`, `derive_lr_peirce`,
`audit_cd59_conditional_replay`, and `audit_cd59_and_B_conditional_replay`.
It removes only the original rechecker's per-file provenance-manifest
validation loop in the execution copy; the original, adapted file and exact
diff are retained. Substantive checks are unchanged. Every job has a
120-second cap and separate stdout/stderr. The original
[execution record](data/intake187-source142-finite-replay.json) reports six
passes. The [portable-wrapper replay](data/intake187-source142-portable-replay.json)
also passes on a freshly recovered packet. The last two **assume unproved cd59** and the listed earlier fragment
replacements. Neither proves a complete classical basis.

The finite source tests and abstract baseline invariant do not themselves prove
the HC model or all-natural equality theorem. Those arguments were read and
independently reviewed as ordinary mathematics. The provisional machine and
included Rocq source files were read as inert inputs and not compiled or
executed. The supplied formal snippets are not a complete proof-assistant
project. Some hash-identified upstream review texts are absent; the included
manuscript contains the arguments used here.

## Source 143 and new combinations

The supplement's original scripts and historical receipts remain recoverable.
Its baseline runtime was already checked with the accepted K219 and was not
repeated during this intake. No full rerun of its 872-action cooperative
family is claimed. The four wrong-branch examples and three divergence
certificates were instead independently transferred to all six new layouts.
The [alternative publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/alternatives/README.md)
contains the exact comparison, three row157 stacks, fresh equivalence checks,
seven-failure transfer and their reproduction instructions.

The [shifted-head search](../../../../../../Computability/BusyBeaver/Research/ZFC/k219-shifted-fold/README.md)
is a separate intake experiment. Its scripts, controls, full rejection streams
and census audit reproduce the fixed family and its explicit bounds. No
bounded failure is promoted to an impossible machine or an incorrect blank
run. The source/table proofs, runtime checks, startup and consistency
calibration remain distinct acceptance obligations.
