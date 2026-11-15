# Two symmetric witness machines for PA consistency

**Result:** two new complete 194-state machines, **PA194H5XS** and
**PA194JH5XS**. No justified machine with fewer than 194 states was found.
The report is `report/report.pdf`; all LaTeX sources are included.

Each machine uses two symbols, one two-way infinite tape initially filled
with zero, head position 0, initial state 0, and working states 0–193.
Terminal label 194 is separate and has no transition rows. Every transition
writes a bit and moves left or right. Each table has 388 rows.

The new implementations remove the cache-restoration transfer loop from
Shift. They compare `(1,h)` instead of `(h,1)`, preserving the complete
command effect for every clean incoming store. The source saving is 0
steps for h=0, 4 for h=1, and 2h+4 for h≥2. A checked additional context
fold pays for the extra physical controller: 135 fixed controls + 69
reader controls − 10 folds = 194. The axiom emitters are preserved exactly.

## The theorem and its status

For each new machine M, the report establishes the ordinary mathematical
claim `iPRA ⊢ Con(PA) ↔ ¬Halt_blank(M)` by composing:

1. A new relative iPRA proof of positive blank-halting equivalence to the
   exact H5X or JH5X parent, with primitive-recursive witness maps.
2. The explicitly retained witness-calculus translations and revised
   AX11H **written** absolute iPRA calibration.

The new source/physical certificates, complete blank startup, construction,
and graph novelty were checked. This is **not** a new end-to-end Lean or
Rocq theorem. The report and `references/written_calibration_review.md`
identify the imported mathematical dependency and the scope of its review.
The retained consistency predicate is the current-Foundation
`DiophantineConsistency.IPRAPA196Consistency.nativePAConsistency`.

## Main files

| Path | Contents |
|---|---|
| `report/report.pdf` | Comparison, new construction and proof, search results, both complete transition tables, all 35 design families |
| `report/report.tex` and `symmetric_preservation.tex` | Complete editable LaTeX source |
| `machines/PA194H5XS/machine.tm` | First complete dense table |
| `machines/PA194JH5XS/machine.tm` | Second complete dense table |
| `machines/*/` | Native tables, labels, grammar, source instructions, fold traces, symbolic contracts and receipts |
| `construction/` | Deterministic reconstruction from frozen parent inputs |
| `verification/` | Source binding, independent literal tape checker and physical frame audit |
| `comparison/` | Complete recognized-corpus ledgers and offline exact novelty replay against 528 prior 194-state graphs |
| `comparison/census/` | All 5,686 recognized table occurrences and census identities |
| `research/startup/` | Reproducible failed 193-state reductions and precise bounded-search results |
| `research/grammar/` | New grammar search sources, fixed inputs, seeds, logs and receipt |
| `references/` | Unchanged witness packet, its written calibration ancestry, and focused review |
| `evidence/` | Fresh aggregate replay result and logs |
| `SHA256SUMS` | Exact file identities, excluding this manifest itself |

## Offline reproduction

Python 3.10 or later with the standard library suffices for the positive
construction and novelty checks. Keep assertions enabled. Choose a new
nonexistent output directory **outside this archive**:

```sh
python3 -B verify_release.py --work /absolute/path/new-replay
```

This checks integrity, the exact imported archive hash, the link from the
novelty candidates to the actual machine tables, construction and all
simultaneous folds, source and AX emitter contracts, whole-tape startup,
independent literal symbolic execution, physical frame closure, and exact
graph nonidentity. It does not run a proof assistant or rerun stochastic
discovery. It writes logs and a `verification.json` to the work directory.

The reduction research has a separate verifier requiring a C++17 compiler:

```sh
python3 -B research/startup/verify.py
python3 -B research/startup/verify.py --full
```

The second command also replays the two broad startup screens. Runs
classified as bounded limits remain inconclusive; none of the searches
proves a lower bound of 194. See `research/startup/RESEARCH_NOTE.md`.

To regenerate the report's tables and compile the PDF:

```sh
cd report
python3 -B generate_inputs.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Exact table identities

```text
PA194H5XS:
e4941ef9961b7184f18d01162889a45742be97da271ca9692a17c833628d8640
PA194JH5XS:
a10f76ac7bf8d3d473a3eaad82756353ae9ba7118225a12de52f10c80c625474
```

## Scope and attribution

The comparison is pinned to ProveIt commit
`3c3bf00e3132d31d328a7bcfe79761ef238eced3`. It covers the PA research tree
and `docs/incoming`: 100 delivered packets, 91 named positive-claim graphs,
35 mechanism families, and 528 recognized spanning 194-state action-graph
classes including auxiliary, rejected and seed graphs. Explicit numeric
tables and four JSON encodings are recognized; arbitrary generators and
prose-only tables are not executed or inferred. Newness means absence from
this pinned recognized corpus, even after enlarged structural symmetries.

The new contribution combines existing attributed mechanisms and supplies
new complete implementations, source-cost analysis, relative proof,
verification, comparison and reduction searches. It does not claim the
witness calculus or symmetric comparison idea as an independent invention.
The underlying work by James Chang, Andrew James Wade, Elliot Glazer,
Vladimir Reshetnikov and the other credited contributors remains attributed
in `PROVENANCE.json`, the `WITNESS_*` files, and the unchanged source packet.
Original licenses are in `verification/reference/` and retained packets.
No upstream repository file was changed.
