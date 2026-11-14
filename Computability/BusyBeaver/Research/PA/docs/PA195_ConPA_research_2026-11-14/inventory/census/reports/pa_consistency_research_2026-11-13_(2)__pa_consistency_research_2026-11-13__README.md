# PA consistency machines: comparison and search below 196 states

**The requested machine with fewer than 196 working states was not obtained.**
This archive records the comparison, two new verified layouts with 196 and
198 states, a new command-level reduction, and the unsuccessful searches.
It does not claim a lower bound or a newly kernel-checked PA biconditional.

Start with **report.pdf**. Its editable source is **report.tex**, together
with the included TeX fragments. The report explains the construction and
proof obligations, numerical results, and limits of each certificate.

## Contents

| Directory | Contents and scope |
| --- | --- |
| `comparison/` | Twenty accepted U208 representatives, the requested James Chang PA196 and PA209 tables, provenance, canonical graph comparison, and the two complete U208 source maps. Nine principal named outputs reduce to two graph classes; eighteen helper variants give twenty in the expanded family. |
| `rotated196/` | New 196-state layout, native and dense tables, twelve literal reader rotations, unchanged 3,812-site ordinal source graph, standalone symbolic verifier, and exact startup check. |
| `diagonal198/` | New 198-state layout of the supplied 199-state diagonal-vacuity source; raw 203-state allocation with five compatible folds; reconstruction, symbolic contracts, and startup. |
| `command_reduction/` | Manuscript proof of a calculus that halts at a successful MP deriving code 1, executable examples, an exact source reconstruction, and source-register regression checks. This is not a new binary TM. |
| `abstract_analysis/` | Sound finite abstractions of all nine source registers jointly, C++17 closure checker, source graphs, and deterministic receipts for radices 3 and 4. |
| `association_search/` | Portable AX association search, original timed-run receipts, best grammars, and a saved-witness checker. |
| `engine_search/` | Portable local-fold and register-order searches, context datasets, negative receipts, and a replay runner. |
| `search_results/` | Search receipts, logs, and scope notes. An unsuccessful bounded search is not a state lower bound. |
| `reference_notes/` | Three unmodified, attributed excerpts from supplied manuscripts: diagonal-vacuity calibration and syntactic reverse-implication arguments. These are not new results. |
| `licenses/` | Original licenses and attribution for reused sources. |

The term **verified layout** means exact reconstruction and renumbering,
matching source control flow, all symbolic primitive contracts relative
to the preserved register-engine specifications, and a literal startup
trace to the required clean frame. It does not mean that the new table
has an exported Lean theorem establishing the full PA equivalence.

## Model and table format

All new tables are deterministic binary, single-tape machines on a two-way
infinite tape, initially all zero. Each row has five fields:

```text
current_state  read_symbol  write_symbol  L_or_R  next_state
```

`rotated196/machine.tm` starts in state 0, has working states 0 through
195, and halts at label 196. `diagonal198/machine.tm` starts in state 0,
has working states 0 through 197, and halts at label 198. The halting
label has no outgoing rows and is excluded from the working-state count.
Native tables use historical sparse labels, initial state 74, and halt
254. Their explicit bijections are included.

The dense table SHA-256 values are:

```text
rotated196/machine.tm
b9873b89df4189414d0f443922ca9227bf2f76d8c81a0d0951c06cd608d6a90b

diagonal198/machine.tm
ad3cef693b0a5d3bb4e3804acd0b9092cfbefdba53cffa9783b7e582c48815e8
```

## Reproduction

Python 3.10 or newer and its standard library suffice for the main suite.
No network access, repository checkout, or Lean installation is needed:

```sh
python3 verify_all.py
```

The command verifies the checksummed inputs when `SHA256SUMS` is present,
runs all table and source checks, reconstructs the command candidate from
the pinned upstream source, and binds the stored abstract graphs to that
same source. It writes readable logs and a deterministic summary. Python
`-O` and `-OO` modes are rejected because assertions implement inherited
certificate checks.

To recompute both larger abstract closures, install a C++17 compiler and run:

```sh
python3 verify_all.py --full
```

The radix-4 closure contains 32,947,398 abstract states. It uses several
hundred megabytes of memory and may take longer on a slower machine.
The emitted JSON must match the supplied receipts exactly. The abstractions
are inductive overapproximations, not finite samples of the blank run.

To rebuild the PDF, from this directory run:

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

A conventional TeX installation providing `lmodern`, `geometry`, `amsmath`,
`amsthm`, `booktabs`, `microtype`, `xurl`, `hyperref`, `enumitem`, and
`fancyhdr` is sufficient. Compilation does not require shell escape.

## Exact inputs and formal status

The source commits are:

* James Chang PA196: `407cdc356f6b586635e71ac92be394255f4bfea4`.
* Requested James Chang PA209: `69d98241a721ead20b4f0b17df9062950b40fbfe`.
* ProveIt incoming research and ConciseIPRA: `dc523e7b06ffb414093c90aa035500ca283e5f75`.

The requested PA209 is different from the Joint U209 parent of the U208
family. Their source programs have 3,948 and 3,909 primitive sites,
respectively. Shared ancestry does not license transplanting native
control labels or contextual folds between them.

The published PA196 development explicitly exports PA-provable
`nonhalting -> Con(PA)`. External model soundness and nonhalting are
different from an exported PA proof of the converse. Supplied incoming
manuscripts describe syntactic routes to that converse. This investigation
does not claim to have rebuilt the full upstream Lean project or added
that endpoint. The new command theorem is an ordinary mathematical
argument with executable checks, not a proof-assistant artifact.

ConciseIPRA's native scalar core concerns iPRA. Replacing the PA refutation
search with its small checker would require a separate PA-strength
calibration; checker byte length is not a binary TM state count.

Original authors have not reviewed or endorsed the new layouts or report.
