# PA194GH and PA194GHS

**Two new 194-state physical designs; no sub-194 blank-start construction was obtained.**

Start with `report/pa194gh_report.pdf`. The complete editable LaTeX source is
`report/pa194gh_report.tex`; every included fragment is beside it. The report
prints both full transition tables, explains the new command compiler, compares
the current collection, and records the exact scope of the unsuccessful
reduction searches.

## Exact result and proof boundary

PA194GH combines an explicit AX operand as the binder of the saved
generalization, no-push modus ponens, and a Shift instruction that halts only
when its cached theorem is code one. PA194GHS implements the same commands
using a symmetric physical comparison. These are new recurring program
interfaces/implementations, not state renamings, reflected copies, alternate
start states, or padded machines.

Both are complete binary, single-tape, blank-start machines with states
0 through 193, initial state 0, and separate halt label 194. Every transition
writes a bit and moves left or right. The tape is two-way infinite and starts
entirely zero, with the head at coordinate zero.

| Property | PA194GH | PA194GHS |
|---|---:|---:|
| Working states / transition rows | 194 / 388 | 194 / 388 |
| Fixed controls + readers - folds | 134 + 67 - 7 | 135 + 67 - 8 |
| Primitive source sites | 3,653 | 3,650 |
| Universally checked source outcomes | 4,754 | 4,750 |
| Exact whole-tape startup | 57,922 steps | 57,768 steps |
| Independent literal symbolic steps | 1,102,232 | 1,106,146 |

The new abstract command/refutation equivalence has a written constructive
proof, including an all-store halting compiler of length at most `122n + 13`
for an `n`-node proof tree. The physical implementations have universal
symbolic runtime certificates and independent literal-table replay, including
all four unary-list induction lemmas. These do not constitute a completed
end-to-end Lean theorem.

**The absolute machine-specific iPRA equivalence with `Con(PA)` is not claimed
as completed.** The repository's primary calibration still has explicit
physical and logical internalization obligations at the pinned commit. The
new designs inherit the target after those weak-arithmetic bridges are
supplied. Assuming only the older written PA calibration gives only its
PA-level scope. The report distinguishes these statements throughout.

Dense table SHA-256:

```text
PA194GH  b9fadcb197c33895603c71b7119bc92b1772c01960804e8850e2a66dd39a995e
PA194GHS 68442e304616894c14f0e256624208c89fc9e84897d678b1c809f0c27a4ca471
```

## Comparison

The audit is pinned to ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`. It covers 77 filed research packets
and all five current incoming archives. All 10,090 selected tracked files
were available. Recursive literal/explicit-JSON recognition finds 3,594 table
occurrences, 778 normalized tables, and 658 spanning one-terminal graph
classes, including 94 at 194 controls and 53 at 193.

The latter include rejected or uncalibrated experiments. These are inventory
counts, not counts of proved consistency machines. Disconnected diagnostics,
unusual terminal conventions, intended starts, and duplicate deliveries are
recorded separately. Both new graphs differ from all 94 previous 194-state
classes, even under the stronger structural symmetries described in the report.

## Reproduce

Python 3.10 or newer and the standard library suffice. Keep assertions enabled.

```sh
python3 verify.py
```

The full independent literal replay, with output kept separate from the
delivered receipts, is:

```sh
python3 -B machines/PA194GH/independent/check.py \
  machines/PA194GH machines/PA194GHS --output /tmp/pa194gh-replay
```

It may take several minutes. Optional C++17 searches have exact commands and
limits in `research/physical/README.txt`; the stochastic source-search
documentation is in `machines/PA194GH/search/README.txt`. The accepted tables
are frozen and do not depend on rediscovering a stochastic winner.

The complete `verify.py --literal` run passed from a clean ZIP extraction.
Its receipt is in `verification/clean_extraction_replay.json`; the earlier
quick run and the 29-page PDF layout check are recorded beside it. These
receipts precede final packaging; the root `SHA256SUMS` covers the final
release, including the receipts themselves.

To rebuild the report:

```sh
cd report
python3 make_tables.py
pdflatex -interaction=nonstopmode -halt-on-error pa194gh_report.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194gh_report.tex
```

## New reduction work

The physical research includes 11,287,605 paired-edit/start combinations for
the known 193-state runtime, a 6,440,096-triple repair search, coupled marker
repairs, all 40,320 physical allocations fixing the initial nonzero slot,
two complete bounded local-contraction sweeps on GH, and a clear-loop-aware
register-liveness analysis. None produced a valid 193-state machine.

The paired search leaves 492 bounded runs after exact cycle detection; the
triple search leaves 1,066. Bounds are explicit. A bounded failure is not
treated as a proof of permanent failure, and no global state lower bound is
claimed. The pre-existing `runtime193.native.tm` is clearly identified as a
rejected blank-start research input.

## Contents and attribution

- `machines/`: literal tables, dense/native maps, grammars, full source graphs,
  constructors, symbolic command checkers, proof and independent certificates.
- `comparison/`: all-packet and all-class ledgers, 194-state representatives,
  exact novelty checker, start metadata and provenance.
- `research/physical/`: new reduction searches, exact inputs, logs and limits.
- `report/`: complete LaTeX report, generated tables and compiled PDF.
- `references/`: pinned project status and attributed inherited calibration.
- `RESULTS.json` and `SHA256SUMS`: exact result scope and release integrity.

Imported material remains attributed to James Chang, the inherited runtime
authors, and the supplied ProveIt research packets. Relevant licenses and
Git/source hashes are retained. The current result adds the GH composition,
the GHS implementation, their command proof and verification, the current
comparison, and the documented searches. Reference `.tex` fragments preserve
their original context and are not standalone papers.
