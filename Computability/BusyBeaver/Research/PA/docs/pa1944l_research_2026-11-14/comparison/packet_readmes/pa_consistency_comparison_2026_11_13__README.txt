# PA-consistency machines: comparison and new reduction experiments

**Result: no verified machine with fewer than 196 working states was obtained.**
This archive is the completed research record for the requested comparison and
construction attempt. It does not claim that a 195-state machine is impossible,
and it does not contain an accepted 195-state table or a new end-to-end Lean
proof of the PA consistency biconditional.

## Read first

- `report.pdf` is the compiled research report.
- `report.tex` and `sections/*.tex` are its complete LaTeX sources.
- `comparison/` contains the exact comparison inputs and checker: 30 selected
  tables, 20 U208 graph classes, 16 explicit renaming maps, 18 helper
  equivalences, five source layouts, and two complete finite startups.
- `combinations/` contains the new composition experiments and actual tables
  with their real counts and explicitly limited proof status.
- `logic/` contains the checked Hilbert templates and the finite controls for
  the two rewrite-head countermodels.
- `physical_search/` contains the new physical deletion screens and their
  exact scope, input pins, receipts, and reproduction instructions.
- `grammar/` contains the split-head and truth-padding grammar screens and
  the minimal attributed support sources used to run them.
- `results/` records the fresh checks and grammar search summaries.
- `provenance/` and `licenses/` retain source attribution and notices.

The main new mathematical result is an equivalent split of the first
quantifier head into a modal B form plus an explicit explosion family. Both
directions have checked finite Hilbert certificates. The report also proves
that neither membership-rewrite head is derivable after simply deleting it,
and that replacing the original quantifier head by reflexivity fails even when
explosion is added. These results narrow particular optimization routes; they
are not a state-count lower bound.

## Frozen sources

| Repository / construction | Revision |
| --- | --- |
| ProveIt | `dc523e7b06ffb414093c90aa035500ca283e5f75` |
| BusyBeaver PA196 | `407cdc356f6b586635e71ac92be394255f4bfea4` |
| Requested BusyBeaver PA209 | `69d98241a721ead20b4f0b17df9062950b40fbfe` |

The upstream PA196 table SHA-256 is
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
All machines use a single binary tape initially zero, one-cell L/R moves, and
a separate halt control excluded from the working-state count. Native sparse
labels are identifiers, not state counts.

## Default verification

Python 3.10 or later is sufficient for the default checks. Run from the
extracted archive directory:

```sh
python3 verify.py
```

This validates the manifest, replays the complete reference comparison,
checks the finite Hilbert derivations and countermodel controls, reconstructs
the 189-token joint emitter, replays the baseline physical symbolic checks
and exact startup, and checks the recorded evidence summaries. It
uses a temporary directory for newly generated reports. Do not use Python's
`-O` option: several inherited symbolic verifiers and the logical certificate
checker intentionally use assertions.

This default verification does not rerun all large exploratory searches or
the complete upstream Lean development. The successful upstream default
source check is recorded in `results/upstream_check.txt`; the optional full
Lean build and axiom audit were not run for this report.

## Optional reproduction

The twelve combined source/table checks take longer:

```sh
python3 combinations/replay.py
```

The copied combination checker writes only `combinations/replayed/`. These
checks cover arbitrary register values under the documented engine contracts
and the exact startup. They do not discharge the separate scratch-zero,
changed command-compiler, and PA-internal proof-code obligations by themselves.
See `COMPARISON_REPRODUCTION.txt` for details.

The grammar screens have deterministic random seeds and explicit finite
budgets. The following reproduces the recorded families; an optional fourth
argument supplies a destination for newly generated results:

```sh
python3 grammar/split_head_search.py 50000 split /tmp/pa-split
python3 grammar/split_head_search.py 75000 split_positive /tmp/pa-split-positive
python3 grammar/split_head_search.py 50000 padding /tmp/pa-padding
```

The recorded split screens attained 74 raw AX grammar nodes. The padding
screen attained 68, but its promising samples failed the imposed path-layout
screen. No physical allocation was accepted in those searches. `null` in
`best_physical` means no eligible layout was priced; it does not encode a
machine or a lower bound. The 196-state original is checked as a positive
compiler control before each search.

See `physical_search/README.md` for the independent predecessor-boundary,
source-context, head-offset, and adjacent-bit encoding screens. Some require
a C++17 compiler. Their finite search limits are part of the result.

## Rebuild the PDF

With a standard TeX distribution providing the packages listed at the top of
`report.tex`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The final PDF was rendered and visually inspected. The report and code keep
the published one-way internal PA theorem separate from the proposed route
to its converse. Finite startup execution is never used as a nonhalting proof.

## Attribution

James Chang's machine and supporting source retain their MIT notice. The
ProveIt sources and incoming research retain their included licenses and
notices. Existing comparisons, source rewrites, and helper proofs are credited
as prior work. New files are identified in the report by the work they perform;
neither upstream author is represented as having reviewed these experiments.
